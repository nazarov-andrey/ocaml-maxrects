open ExtList;

module Point =
  struct
    type t = (int * int);

    value create x y = (x, y);
    value x (x, _) = x;
    value y (_, y) = y;
    value between val low high = (low <= val) && (val <= high);
    value xBetween pnt endA endB =
      let xA = x endA in
      let xB = x endB in
      let x = x pnt in
        between x (min xA xB) (max xA xB);

    value yBetween pnt endA endB =      
      let yA = y endA in
      let yB = y endB in
      let y = y pnt in
        between y (min yA yB) (max yA yB);

    value toString pnt = Printf.sprintf "(%d, %d)" (x pnt) (y pnt);

    value equal pntA pntB = x pntA = x pntB && y pntA = y pntB;
  end;

module Rectangle = 
  struct
    type t = (Point.t * Point.t);

    value fromPnts lb rt = (lb, rt);
    value fromCoords lbX lbY rtX rtY = fromPnts (Point.create lbX lbY) (Point.create rtX rtY);
    value fromCoordsAndDims x y w h = fromPnts (Point.create x y) (Point.create (x + w) (y + h));
    value fromPntAndDims pnt w h = fromPnts pnt Point.(create (x pnt + w) (y pnt + h));

    value leftBottom (lb, _) = lb;
    value rightTop (_, rt) = rt;
    value width rect = Point.(x (rightTop rect) - x (leftBottom rect));
    value height rect = Point.(y (rightTop rect) - y (leftBottom rect));
    value x rect = let (x, _) = leftBottom rect in x;
    value y rect = let (_, y) = leftBottom rect in y;

    value isDegenerate rect =
      let lb = leftBottom rect in
      let rt = rightTop rect in
        Point.(x lb = x rt || y lb = y rt);

    value pntInside rect pnt =
      let lb = leftBottom rect in
      let rt = rightTop rect in
        Point.(xBetween pnt lb rt && yBetween pnt lb rt);

    value rectInside outer inner = pntInside outer (leftBottom inner) && pntInside outer (rightTop inner);

    value intersects rectA rectB =
      let lbA = leftBottom rectA in
      let rtA = rightTop rectA in
      let lbB = leftBottom rectB in
      let rtB = rightTop rectB in
        not Point.(x rtA < x lbB || x rtB < x lbA || y rtA < y lbB || y rtB < y lbA);

    value areContiguous rectA rectB =
      let lbA = leftBottom rectA in
      let rtA = rightTop rectA in
      let lbB = leftBottom rectB in
      let rtB = rightTop rectB in
        Point.((x lbA = x lbB || x lbA = x rtB) && (yBetween lbA lbB rtB || yBetween rtA lbB rtB)
                || (y lbA = y lbB || y lbA = y rtB) && (xBetween lbA lbB rtB || xBetween rtA lbB rtB));

    value toString rect = Printf.sprintf "(%d, %d, %d, %d)" (x rect) (y rect) (width rect) (height rect);

    value equal rectA rectB = Point.(equal (leftBottom rectA) (leftBottom rectB) && equal (rightTop rectA) (rightTop rectB));
  end;

module Hole =
  struct
    value plus holeA holeB =
(*       if Rectangle.intersects holeA holeB
      then *)

        let lbHA = Rectangle.leftBottom holeA in
        let rtHA = Rectangle.rightTop holeA in

        let lbHB = Rectangle.leftBottom holeB in
        let rtHB = Rectangle.rightTop holeB in

          Point.(
            let newHoleA = Rectangle.fromCoords (max (x lbHA) (x lbHB)) (min (y lbHA) (y lbHB)) (min (x rtHA) (x rtHB)) (max (y rtHA) (y rtHB)) in
            let newHoleB = Rectangle.fromCoords (min (x lbHA) (x lbHB)) (max (y lbHA) (y lbHB)) (max (x rtHA) (x rtHB)) (min (y rtHA) (y rtHB)) in

            let holes = if Rectangle.isDegenerate newHoleA then [] else [ newHoleA ] in
              if Rectangle.isDegenerate newHoleB then holes else [ newHoleB :: holes ];
(*             let holes =
              if Rectangle.(isDegenerate newHoleA || equal newHoleA holeA || equal newHoleA holeB || rectInside holeA newHoleA || rectInside holeB newHoleA)
              then []
              else [ newHoleA ]
            in
              if Rectangle.(isDegenerate newHoleB || equal newHoleA holeA || equal newHoleA holeB || rectInside holeA newHoleB || rectInside holeB newHoleB)
              then holes
              else [ newHoleB :: holes ]; *)
          );
      (* else []; *)

    value minus hole rect =
      let lbH = Rectangle.leftBottom hole in
      let rtH = Rectangle.rightTop hole in

      let lbR = Rectangle.leftBottom rect in
      let rtR = Rectangle.rightTop rect in

        Point.(
          let holes = if x rtR < x rtH then [ Rectangle.fromCoords (x rtR) (y lbH) (x rtH) (y rtH) ] else [] in
          let holes = if y rtR < y rtH then [ Rectangle.fromCoords (x lbH) (y rtR) (x rtH) (y rtH) :: holes ] else holes in
          let holes = if x lbH < x lbR then [ Rectangle.fromCoords (x lbH) (y lbH) (x lbR) (y rtH) :: holes ] else holes in
            let holes = if y lbH < y lbR then [ Rectangle.fromCoords (x lbH) (y lbH) (x rtH) (y lbR) :: holes ] else holes in
            let () = Printf.printf "cut %s from hole %s: %s\n%!" (Rectangle.toString rect) (Rectangle.toString hole) (String.concat "," (List.map (fun rect -> Rectangle.toString rect) holes)) in
              holes; 
        );
  end;

module Bin =
  struct
    exception CantPlace;

    type t = {
      width: int;
      height: int;
      holes: mutable list Rectangle.t;
      rects: mutable list Rectangle.t;
    };

    value create width height = { width; height; holes = [ Rectangle.fromCoordsAndDims 0 0 width height ]; rects = [] };
    value rects bin = bin.rects;
    value holes bin = bin.holes;
    value getRect bin indx = List.nth bin.rects (indx mod (List.length bin.rects));
    value getHole bin indx = List.nth bin.holes (indx mod (List.length bin.holes));
    value width bin = bin.width;
    value height bin = bin.height;

    value add bin width height =
      let holeToPlace = 
        List.fold_left (fun holeToPlace hole ->
          if Rectangle.width hole >= width && Rectangle.height hole >= height
          then
            let bestPos = Rectangle.leftBottom holeToPlace in
            let holeLb = Rectangle.leftBottom hole in
              if Point.(y holeLb < y bestPos || y holeLb = y bestPos && x holeLb < x bestPos)
              then hole
              else holeToPlace
          else holeToPlace
        ) (Rectangle.fromCoordsAndDims max_int max_int max_int max_int) bin.holes
      in
        if Point.x (Rectangle.leftBottom holeToPlace) = max_int
        then raise CantPlace
        else
          let rectPos = Rectangle.leftBottom holeToPlace in
          let placedRect = Rectangle.fromPntAndDims rectPos width height in

          let filterHoles hole maxHoles = 
            let rec filterHoles hole maxHoles retval =
              if maxHoles = []
              then [ hole :: retval]
              else
                let maxHole = List.hd maxHoles in
                  if Rectangle.rectInside hole maxHole
                  then filterHoles hole (List.tl maxHoles) retval
                  else
                    if Rectangle.rectInside maxHole hole
                    then retval @ maxHoles
                    else filterHoles hole (List.tl maxHoles) [ maxHole :: retval ]
            in
              filterHoles hole maxHoles [] 
          in

          let splitHoles holes =
            let () = Printf.printf "split holes call\n%!" in
            let rec splitHoles holes (maxHoles, notAffected) =
              if holes = []
              then maxHoles @ notAffected
              else
                let hole = List.hd holes in
                let () = Printf.printf "scan hole %s, %B\n%!" (Rectangle.toString hole) (Rectangle.intersects placedRect hole) in
                  if Rectangle.intersects placedRect hole
                  then
                    let cuttings = Hole.minus hole placedRect in
                    let maxHoles = List.fold_left (fun maxHoles cutting -> filterHoles cutting maxHoles) maxHoles cuttings in
                      splitHoles (List.tl holes) (maxHoles, notAffected)
                  else splitHoles (List.tl holes) (maxHoles, [ hole :: notAffected ])
            in
              splitHoles holes ([], [])
          in (
            bin.holes := splitHoles bin.holes;

            Printf.printf "holes: %s\n%!" (String.concat "," (List.map (fun rect -> Rectangle.toString rect) bin.holes));

            bin.rects := [ placedRect :: bin.rects ];
            rectPos;
          );

    value remove bin rect =

      let rec putNewHole holes newHole retval =
        match holes with
        [ [ hole :: _holes ] ->
          if Rectangle.rectInside hole newHole
          then (False, retval @ holes)
          else
            if Rectangle.rectInside newHole hole
            then putNewHole _holes newHole retval
            else putNewHole _holes newHole [ hole :: retval ]
        | _ -> (True, [ newHole :: retval ])
        ]
      in

      let rec putNewHoles holes newHoles holePairs =        
        match newHoles with
        [ [ newHole :: newHoles ] ->
          let () = Printf.printf "putNewHoles call, newHole %s\n%!" (Rectangle.toString newHole) in
          let (isMaxHole, holes) = putNewHole holes newHole [] in
          let () = Printf.printf "is max hole %B, holes %s\n%!" (isMaxHole) (String.concat ";" (List.map (fun hole -> Rectangle.toString hole) holes)) in
            if isMaxHole
            then putNewHoles holes newHoles holePairs
            else
              let newHolePairs = List.map (fun hole -> (newHole, hole)) holes in
                putNewHoles holes newHoles (newHolePairs @ holePairs)
        | _ -> (holes, holePairs) 
        ]
      in

      let rec updateHoles holes holePairs =
        match holePairs with
        [ [ (holeA, holeB) :: holePairs ] ->
          let newHoles = Hole.plus holeA holeB in
          let () = Printf.printf "new holes: %s\n%!" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) newHoles)) in
          let (holes, holePairs) = putNewHoles holes newHoles holePairs in
            updateHoles holes holePairs
        | _ -> holes 
        ]
      in

(*       let rec merge holeA holes retval =
        match holes with
        [ [ holeB :: holes ] ->
          let () = Printf.printf "merge call %s %s\n%!" (Rectangle.toString holeA) (Rectangle.toString holeB) in
          if Rectangle.equal holeA holeB
          then merge holeA holes retval
          else
            let newHoles = Hole.plus holeA holeB in
            let () = Printf.printf "newHoles: %s\n%!" (String.concat "," (List.map (fun rect -> Rectangle.toString rect) newHoles)) in
              merge holeA holes (retval @ newHoles)
        | _ -> retval
        ]
      in

      let rec makeHoleCorrection holes retval =        
        match holes with
        [ [ hole :: holes ] ->
          let () = Printf.printf "makeHoleCorrection %s\n%!" (Rectangle.toString hole) in
          let holes = merge hole holes [] in
            makeHoleCorrection holes [ hole :: retval ]
        | _ -> retval
        ]
      in *)

      let rec merge changedHoles restHoles =
        let () = Printf.printf "merge call\n%!" in
        let () = Printf.printf "\tchanged holes: %s\n%!" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) changedHoles)) in
        let () = Printf.printf "\trest holes: %s\n%!" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) restHoles)) in
        match changedHoles with
        [ [ rect :: holes ] ->
          let (neighbours, other) = List.partition (fun hole -> Rectangle.areContiguous hole rect) (holes @ restHoles) in
          let holePairs = List.map (fun hole -> (rect, hole)) neighbours in (
            Printf.printf "neighbours: %s\n%!" (String.concat ";" (List.map (fun hole -> Rectangle.toString hole) neighbours));
            Printf.printf "hole pairs: %s\n%!" (String.concat ";" (List.map (fun (holeA, holeB) -> Printf.sprintf "[%s, %s]" (Rectangle.toString holeA) (Rectangle.toString holeB)) holePairs));

            let affeted = updateHoles neighbours holePairs in
              if holes = []
              then affeted @ other
              else merge (holes @ affeted) other;
          )
        | _ -> assert False
        ]
      in

      let rects = List.remove bin.rects rect in
        if rects <> bin.rects
        then (
          bin.rects := rects;
          bin.holes := merge [ rect ] bin.holes;

          Printf.printf "bin holes %s\n%!" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) bin.holes));
        )
        else ();

    value clean bin = (
      bin.holes := [ Rectangle.fromCoordsAndDims 0 0 bin.width bin.height ];
      bin.rects := [];
    );
  end;

value binSize = 200;
value scale = 2;
value toScreen pnt = Point.(create (scale * (x pnt) + 100) (600 - scale * (y pnt) - 10));
value drawRect rect =
  let lb = toScreen (Rectangle.leftBottom rect) in
    Graphics.draw_rect (Point.x lb) (Point.y lb - scale * (Rectangle.height rect)) (scale * Rectangle.width rect) (scale * Rectangle.height rect);

value showHolesMode = ref False;
value holeIndx = ref 0;
value rects = ref [];
value cnt = ref 0;

let bin = Bin.create binSize binSize in (
  try
    Graphics.open_graph " 800X600"
  with [ Graphics.Graphic_failure reason -> ( Printf.printf "fail %s\n%!" reason; exit 0; ) ];

  Graphics.set_color Graphics.red;
  Graphics.set_line_width 2;

  drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

  (* Bin.iterRects (fun rect -> drawRect rect) bin; *)


  Printf.printf "pizda\n%!";
  (* List.iter (fun rect -> Printf.printf "%s\n%!" (Rectangle.toString rect)) (Hole.plus (Rectangle.fromCoordsAndDims 20 0 34 200) (Rectangle.fromCoordsAndDims 20 0 73 35)); *)
  List.iter (fun rect -> Printf.printf "%s\n%!" (Rectangle.toString rect)) (Hole.plus (Rectangle.fromCoordsAndDims 0 20 20 20) (Rectangle.fromCoordsAndDims 20 0 30 30));
  Printf.printf "pizda\n%!";

  Printf.printf "%B\n%!" (Rectangle.areContiguous (Rectangle.fromCoordsAndDims 0 0 50 15) (Rectangle.fromCoordsAndDims 0 120 200 80));
  Printf.printf "%B\n%!" (Rectangle.areContiguous (Rectangle.fromCoordsAndDims 0 0 50 15) (Rectangle.fromCoordsAndDims 80 0 120 200));
  Printf.printf "%B\n%!" (Rectangle.areContiguous (Rectangle.fromCoordsAndDims 0 0 50 15) (Rectangle.fromCoordsAndDims 0 15 50 185));

  let showHole () =
    let hole = Bin.getHole bin !holeIndx in (
      if !holeIndx > 0
      then (
        Graphics.set_color Graphics.white;
        drawRect (Bin.getHole bin (!holeIndx - 1));

        Graphics.set_color Graphics.red;
        drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

        Graphics.set_color Graphics.green;
        List.iter (fun rect -> drawRect rect) (Bin.rects bin);
      )
      else ();

      Graphics.set_color Graphics.magenta;
      drawRect hole;
      incr holeIndx;
    )
  in
    while True do {
      let c = Char.code (Graphics.read_key ()) in
        if c = 13
        then
          if !showHolesMode
          then showHole ()
          else
(*           (
            if !cnt = 0
            then
              let pos = Bin.add bin 50 15 in (
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos 50 15);
              )
            else

            if !cnt = 1
            then
              let pos = Bin.add bin 30 120 in (
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos 30 120);
              )
            else

            if !cnt = 2
            then
              let pos = Bin.add bin 60 30 in (
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos 60 30);
              )
            else            

            if !cnt = 3
            then (
              Bin.remove bin (Bin.getRect bin 1);

              Graphics.clear_graph ();

              Graphics.set_color Graphics.red;
              drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

              Graphics.set_color Graphics.green;
              List.iter (fun rect -> drawRect rect) (Bin.rects bin);              
            )
            else ();

            incr cnt;            
          ) *)


            let (w, h) = if !rects = [] then (Random.int 40 + 15, Random.int 40 + 15) else let rect = List.hd !rects in ( rects.val := List.tl !rects; rect ) in
              try (          
                Printf.printf "trying to add %d %d... \n%!" w h;
                let pos = Bin.add bin w h in (
                  Printf.printf "ok, added at %s\n%!" (Point.toString pos);
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos w h);
                )
              )          
              with [ Bin.CantPlace -> Printf.printf "cannot place\n%!" ]
        else

        if c = 100
        then
          let rects = Bin.rects bin in
          let indx = Random.int (List.length rects) in (
            Printf.printf "removing %d-th rect...\n%!" indx;
            Bin.remove bin (Bin.getRect bin indx);
            Printf.printf "done, holes %s\n%!" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) (Bin.holes bin)));

            showHolesMode.val := False;

            Graphics.clear_graph ();

            Graphics.set_color Graphics.red;
            drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

            Graphics.set_color Graphics.green;
            List.iter (fun rect -> drawRect rect) (Bin.rects bin);
          )
        else

        if c = 104 && not !showHolesMode
        then (
          Printf.printf "show hole\n%!";
          showHolesMode.val := True;
          holeIndx.val := 0;
          showHole ();
        )
        else

        if c = 27 
        then
          if !showHolesMode
          then (
            showHolesMode.val := False;

            Graphics.set_color Graphics.white;
            drawRect (Bin.getHole bin (!holeIndx - 1));

            Graphics.set_color Graphics.red;
            drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

            Graphics.set_color Graphics.green;
            List.iter (fun rect -> drawRect rect) (Bin.rects bin);
        ) else exit 0
        else ();
    };
);

