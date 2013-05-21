open ExtList;

module Point =
  struct
    type t = (int * int);

    value create x y = (x, y);
    value x (x, _) = x;
    value y (_, y) = y;
    value toString pnt = Printf.sprintf "(%d, %d)" (x pnt) (y pnt);

    value xBetween (x, _) (xA, _) (xB, _) = ((min xA xB) <= x) && (x <= (max xA xB));
    value yBetween (_, y) (_, yA) (_, yB) = ((min yA yB) <= y) && (y <= (max yA yB));
    value equal (xA, yA) (xB, yB) = xA = xB && yA = yB;
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
    value width (lb, rt) = Point.(x rt - x lb);
    value height (lb, rt) = Point.(y rt - y lb);
    value x (lb, _) = Point.x lb;
    value y (lb, _) = Point.y lb;

    value toString rect = Printf.sprintf "(%d, %d, %d, %d)" (x rect) (y rect) (width rect) (height rect);

    value isDegenerate (lb, rt) = Point.(x lb = x rt || y lb = y rt);

    value pntInside (lb, rt) pnt = Point.(xBetween pnt lb rt && yBetween pnt lb rt);

    value rectInside outer (lb, rt) = pntInside outer lb && pntInside outer rt;

    value intersects (lbA, rtA) (lbB, rtB) = not Point.(x rtA < x lbB || x rtB < x lbA || y rtA < y lbB || y rtB < y lbA);

    value intersection (lbA, rtA) (lbB, rtB) =
      let left = Point.(max (x lbA) (x lbB)) in
      let right = Point.(min (x rtA) (x rtB)) in
        if left > right
        then None
        else
          let bottom = Point.(max (y lbA) (y lbB)) in
          let top = Point.(min (y rtA) (y rtB)) in
          if top < bottom
          then None
          else
            (* let () = debug "left %d bottom %d right %d top %d" left bottom right top in *)
            let intersection = fromCoords left bottom right top in
              if isDegenerate intersection then None else Some intersection;

    value minus (lbFrom, rtFrom) (lbRect, rtRect) =
      let addRect lbx lby rtx rty retval =
        let rect = fromCoords lbx lby rtx rty in
          if isDegenerate rect then retval else [ rect :: retval ]
      in
        Point.(
          let retval = addRect (x lbFrom) (y lbFrom) (x lbRect) (y rtFrom) [] in
          let retval = addRect (x lbRect) (y lbFrom) (x rtRect) (y lbRect) retval in
          let retval = addRect (x lbRect) (y rtRect) (x rtRect) (y rtFrom) retval in
            addRect (x rtRect) (y lbFrom) (x rtFrom) (y rtFrom) retval;
        );

    value areContiguous (lbA, rtA) (lbB, rtB) =
      Point.((x lbA = x lbB || x lbA = x rtB) && (yBetween lbA lbB rtB || yBetween rtA lbB rtB)
        || (y lbA = y lbB || y lbA = y rtB) && (xBetween lbA lbB rtB || xBetween rtA lbB rtB));

    value equal (lbA, rtA) (lbB, rtB) = Point.(equal lbA lbB && equal rtA rtB);
  end;

module Hole =
  struct
    value plus holeA holeB =
      let lbHA = Rectangle.leftBottom holeA in
      let rtHA = Rectangle.rightTop holeA in

      let lbHB = Rectangle.leftBottom holeB in
      let rtHB = Rectangle.rightTop holeB in

        Point.(
          let newHoleA = Rectangle.fromCoords (max (x lbHA) (x lbHB)) (min (y lbHA) (y lbHB)) (min (x rtHA) (x rtHB)) (max (y rtHA) (y rtHB)) in
          let newHoleB = Rectangle.fromCoords (min (x lbHA) (x lbHB)) (max (y lbHA) (y lbHB)) (max (x rtHA) (x rtHB)) (min (y rtHA) (y rtHB)) in

          let holes = if Rectangle.isDegenerate newHoleA then [] else [ newHoleA ] in
            if Rectangle.isDegenerate newHoleB then holes else [ newHoleB :: holes ];
        );

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
            let () = debug "cut %s from hole %s: %s" (Rectangle.toString rect) (Rectangle.toString hole) (String.concat "," (List.map (fun rect -> Rectangle.toString rect) holes)) in
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
      needRepair: mutable bool;
    };

    value create width height = { width; height; holes = [ Rectangle.fromCoordsAndDims 0 0 width height ]; rects = []; needRepair = False };
    value rects bin = bin.rects;
    value holes bin = bin.holes;
    value getRect bin indx = List.nth bin.rects (indx mod (List.length bin.rects));
    value getHole bin indx = List.nth bin.holes (indx mod (List.length bin.holes));
    value width bin = bin.width;
    value height bin = bin.height;

    value holesSquare holes =
      let rec prepare holeA holes nextPassHoles retval =
        match holes with 
        [ [ holeB :: holes ] ->
          match Rectangle.intersection holeA holeB with
          [ Some intersection ->
            let cuttingsA = Rectangle.minus holeA intersection in
            let cuttingsB = Rectangle.minus holeB intersection in
              prepare intersection holes (cuttingsA @ cuttingsB @ nextPassHoles) retval
          | _ -> prepare holeA holes [ holeB :: nextPassHoles ] retval
          ]
        | _ ->
          match nextPassHoles with
          [ [] -> [ holeA :: retval ]
          | nextPassHoles -> prepare (List.hd nextPassHoles) (List.tl nextPassHoles) [] [ holeA :: retval ]
          ]
        ]
      in

      let rects = prepare (List.hd holes) (List.tl holes) [] [] in
        List.fold_left (fun square rect -> square + Rectangle.(width rect * height rect)) 0 rects;

    value rectsSquare rects = List.fold_left (fun square rect -> square + Rectangle.(width rect * height rect)) 0 rects;

    value repair bin =
      if bin.needRepair
      then 
        let () = debug "+++rects %s" (String.concat ";" (List.map (fun hole -> Rectangle.toString hole) bin.rects)) in
        let () = debug "+++holes %s" (String.concat ";" (List.map (fun hole -> Rectangle.toString hole) bin.holes)) in

        let rec mergePass holes retval =
          let () = debug "mergePass call %s" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) holes)) in
          let () = debug:holes "mergePass call %d %d" (List.length holes) (List.length retval) in
          match holes with
          [ [ holeA :: holes ] -> merge holeA holes [] retval False
          | _ -> assert False
          ]

        and merge holeA holes checkedHoles retval changed =
          let () = debug "\t-------------------------------" in
          let () = debug "\tholes %s" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) holes)) in
          let () = debug "\tcheckedHoles %s" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) checkedHoles)) in
          let () = debug "\tretval %s" (String.concat "," (List.map (fun hole -> Rectangle.toString hole) retval)) in
          (* let () = debug "\trects square + holes square %d" (holesSquare [ holeA :: (holes @ checkedHoles) ] + rectsSquare bin.rects) in *)
          match holes with
          [ [] ->
              let () = debug "\tchanged %B" changed in
              if changed
              then mergePass ((List.rev retval) @ (List.rev checkedHoles) @ [ holeA ]) []
              else
                match checkedHoles with
                [ [] -> [ holeA :: retval ]
                | _ -> mergePass checkedHoles [ holeA :: retval ] 
                ]
          | _ ->
            let holeB = List.hd holes in
              let () = debug "\tholeA = %s holeB = %s" (Rectangle.toString holeA) (Rectangle.toString holeB) in
              let () = debug "\t%s inside %s: %B" (Rectangle.toString holeB) (Rectangle.toString holeA) (Rectangle.rectInside holeA holeB) in

              if Rectangle.rectInside holeA holeB
              then merge holeA (List.tl holes) checkedHoles retval changed
              else

              let () = debug "\t%s inside %s: %B" (Rectangle.toString holeA) (Rectangle.toString holeB) (Rectangle.rectInside holeB holeA) in
              if Rectangle.rectInside holeB holeA
              then merge holeB (List.tl holes) checkedHoles retval True
              else

              let () = debug "\t%s and %s intersects: %B" (Rectangle.toString holeA) (Rectangle.toString holeB) (Rectangle.intersects holeA holeB) in
              if Rectangle.intersects holeA holeB
              then              
                let () = debug "\t%s plus %s: %s" (Rectangle.toString holeA) (Rectangle.toString holeB) (String.concat ";" (List.map (fun hole -> Rectangle.toString hole) (Hole.plus holeA holeB))) in
                match Hole.plus holeA holeB with
                [ [ newHoleA; newHoleB ] when Rectangle.(equal newHoleA holeA && equal newHoleB holeB || equal newHoleA holeB && equal newHoleB holeA) ->
                  let () = debug "\tcase 0" in
                    merge holeA (List.tl holes) [ holeB :: checkedHoles ] retval changed
                | [ newHoleA; newHoleB ] ->
                  let () = debug "\tcase 1" in
                  let allHoles = [ holeA :: holes @ checkedHoles @ retval ] in
                  let (changed, checkedHoles) =
                    if List.exists (fun hole -> Rectangle.rectInside hole newHoleB) allHoles
                    then let () = debug "\t%s or it's shell rect already in max rects" (Rectangle.toString newHoleB) in (changed, checkedHoles)
                    else let () = debug "\tadding %s to max rects" (Rectangle.toString newHoleB) in (True, [ newHoleB :: checkedHoles ])
                  in
                  let (changed, checkedHoles) =
                    if List.exists (fun hole -> Rectangle.rectInside hole newHoleA) allHoles
                    then let () = debug "\t%s or it's shell rect already in max rects" (Rectangle.toString newHoleA) in (changed, checkedHoles)
                    else let () = debug "\tadding %s to max rects" (Rectangle.toString newHoleA) in (True, [ newHoleA :: checkedHoles ])
                  in
                    merge holeA (List.tl holes) [ holeB :: checkedHoles ] retval changed
                | [ newHole ] when Rectangle.rectInside newHole holeA && Rectangle.rectInside newHole holeB -> let () = debug "\tcase 2" in merge newHole (List.tl holes) checkedHoles retval True
                | [ newHole ] when Rectangle.rectInside newHole holeA -> let () = debug "\tcase 3" in merge newHole (List.tl holes) [ holeB :: checkedHoles ] retval True
                | [ newHole ] when Rectangle.rectInside newHole holeB -> let () = debug "\tcase 4" in merge holeA (List.tl holes) [ newHole :: checkedHoles ] retval True
                | [ newHole ] ->
                  let () = debug "\tcase 5" in
                  let allHoles = [ holeA :: holes @ checkedHoles @ retval ] in
                  let (changed, checkedHoles) =
                    if List.exists (fun hole -> Rectangle.rectInside hole newHole) allHoles
                    then let () = debug "\t%s or it's shell rect already in max rects" (Rectangle.toString newHole) in (changed, checkedHoles)
                    else let () = debug "\tadding %s to max rects" (Rectangle.toString newHole) in (True, [ newHole :: checkedHoles ])
                  in
                   merge holeA (List.tl holes) [ holeB :: checkedHoles] retval changed
                | [] -> let () = debug "\t case 6" in merge holeA (List.tl holes) [ holeB :: checkedHoles ] retval changed (* this case is when rects contacts by single vertex *)
                | _ -> assert False
                ]
              else merge holeA (List.tl holes) [ holeB :: checkedHoles ] retval changed
          ]
        in (
          bin.holes := mergePass bin.holes [];
          bin.needRepair := False;
        )
      else ();

    value add bin width height = (
      if bin.needRepair
      then repair bin
      else ();

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
            let () = debug "split holes call" in
            let rec splitHoles holes (maxHoles, notAffected) =
              if holes = []
              then maxHoles @ notAffected
              else
                let hole = List.hd holes in
                let () = debug "scan hole %s, %B" (Rectangle.toString hole) (Rectangle.intersects placedRect hole) in
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
            bin.rects := [ placedRect :: bin.rects ];

            debug "holes: %s" (String.concat "," (List.map (fun rect -> Rectangle.toString rect) bin.holes));
            rectPos;
          );      
    );

    value remove bin rect =
      let rects = List.remove bin.rects rect in
        if rects <> bin.rects
        then (
          bin.rects := rects;
          bin.holes := [ rect :: bin.holes ];
          bin.needRepair := True;
        )
        else ();

    value clean bin = (
      bin.holes := [ Rectangle.fromCoordsAndDims 0 0 bin.width bin.height ];
      bin.rects := [];
      bin.needRepair = False;
    );

    value isConsistent bin = (holesSquare bin.holes) + (rectsSquare bin.rects) = bin.width * bin.height;
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
  with [ Graphics.Graphic_failure reason -> ( debug "fail %s" reason; exit 0; ) ];

  debug:pizda "%s" (String.concat "," (List.map (fun rect -> Rectangle.toString rect) (Hole.plus (Rectangle.fromCoordsAndDims 0 0 20 20) (Rectangle.fromCoordsAndDims 20 20 40 40))));

  Graphics.set_color Graphics.red;
  Graphics.set_line_width 2;

  drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

  Graphics.set_color Graphics.green;
  Graphics.set_line_width 2;

(*   drawRect (Rectangle.fromCoordsAndDims 28 0 38 200);
  drawRect (Rectangle.fromCoordsAndDims 50 18 150 182);

  Graphics.set_color Graphics.magenta; *)
  (* drawRect (Rectangle.fromCoordsAndDims 50 0 16 200); *)

  debug "++++ %B" (Rectangle.rectInside (Rectangle.fromCoordsAndDims 28 0 38 200) (Rectangle.fromCoordsAndDims 50 0 16 200));
  

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


            let (w, h) = if !rects = [] then (Random.int 20 + 10, Random.int 20 + 10) else let rect = List.hd !rects in ( rects.val := List.tl !rects; rect ) in
              try (          
                debug "trying to add %d %d... " w h;
                let pos = Bin.add bin w h in (
                  debug "ok, added at %s, is consistent %B" (Point.toString pos) (Bin.isConsistent bin);
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos w h);
                )
              )          
              with [ Bin.CantPlace -> debug "cannot place" ]
        else

        if c = 100
        then
          let rects = Bin.rects bin in
          let indx = Random.int (List.length rects) in (
            debug "removing %d-th rect..." indx;
            Bin.remove bin (Bin.getRect bin indx);

            let isConsistent = Bin.isConsistent bin in (
              assert isConsistent;
              debug "done, is consistent %B" isConsistent;
            );
              

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
          debug "show hole";
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

