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

    value create width height =
      let aholes = [(67,254,317,16);(0,267,512,3);(67,259,445,11);(67,242,95,100);(0,267,168,75);(67,244,101,98);(67,244,197,26);(155,166,44,12);(155,166,7,176);(143,166,56,1);(120,192,42,150);(315,106,5,25);(301,156,109,15);(320,155,90,16);(192,99,7,79);(143,115,8,23);(504,132,8,296);(427,132,42,22);(427,132,85,21);(499,132,13,67);(509,51,3,461);(508,132,4,380);(169,99,136,7);(169,99,91,12);(485,45,9,6);(485,77,27,3);(503,51,9,29);(295,71,115,9);(295,69,40,11);(408,45,2,35);(408,45,86,1);(363,45,27,1);(390,70,20,10);(466,0,28,23);(363,17,1,6);(230,17,134,4);(366,147,44,24);(366,147,146,6);(366,147,103,7);(254,506,107,6);(0,298,233,44);(428,372,44,56);(499,259,13,169);(185,244,79,94);(0,372,308,82);(120,359,67,105);(384,194,26,5);(470,176,42,23);(0,398,361,56);(0,398,472,30);(185,254,86,84);(281,480,80,32);(287,372,21,140);(82,508,430,4);(0,298,271,40);(185,244,48,98);(82,492,137,20);(185,254,199,57);(0,398,512,2);(428,372,84,28);(478,474,34,5);(0,372,86,115);(219,368,14,112);(287,398,74,114);(120,368,113,96);(502,474,10,38);(0,298,394,13);(219,372,16,108);(0,372,235,92);(0,426,512,2);(0,451,443,3);(254,507,258,5);(185,259,209,52);(185,259,327,27);(495,259,17,141);(489,259,23,79);(0,509,512,3);(287,451,156,28);(82,372,4,140);(431,259,81,52);(102,24,31,2);(120,0,13,26);(180,26,50,20);(351,71,15,58);(315,106,51,23);(295,46,10,60);(221,98,39,13);(239,73,15,38);(221,98,84,8);(169,99,30,13);(169,87,11,25);(264,182,33,12);(260,157,4,21);(283,157,127,14);(283,157,14,37);(73,192,89,20);(0,199,162,13);(73,174,29,38);(162,178,102,66);(410,46,75,34);(199,111,61,67);(297,171,113,23);(410,154,59,22);(410,176,60,23);(469,153,30,23);(264,194,120,30);(384,199,120,30);(0,212,120,30);(264,224,120,30);(384,229,120,30);(233,338,75,34);(308,338,120,30);(0,342,120,30);(308,368,120,30);(428,338,67,17);(120,342,67,17);(428,355,67,17);(297,0,67,17);(361,428,147,23);(235,454,52,26);(230,0,67,17);(86,464,71,28);(157,464,62,28);(361,479,88,28);(449,479,53,28);(0,487,82,22);(394,286,18,25);(478,451,30,23);(254,480,27,26);(102,0,18,24);(364,0,102,23);(180,46,74,27);(363,23,131,22);(305,46,30,23);(335,46,55,25);(494,0,18,26);(494,26,18,25);(390,45,18,25);(254,46,41,26);(254,72,41,26);(180,73,41,26);(427,80,41,26);(102,87,49,28);(468,80,41,26);(260,106,55,25);(485,51,18,26);(221,73,18,25);(151,87,18,25);(412,286,19,25);(427,106,41,26);(468,106,41,26);(151,112,41,26);(102,115,41,26);(260,131,41,26);(143,138,49,28);(102,141,41,26);(301,131,19,25);(264,157,19,25);(102,167,53,25);(0,174,73,25);(219,480,35,28);(168,270,17,28);(305,80,46,26);(320,129,46,26);(187,342,46,26);(443,451,35,28);(366,80,61,67);(102,26,78,61)] in
      let aholes = List.map (fun (x, y, w, h) -> Rectangle.fromCoordsAndDims x y w h) aholes in
      let arects = [(133,0,97,26);(271,311,218,27);(230,21,133,25);(472,400,27,26);(0,0,102,174);(0,242,67,25)] in
      let arects = List.map (fun (x, y, w, h) -> Rectangle.fromCoordsAndDims x y w h) arects in
        { width; height; holes = aholes; rects = arects; needRepair = True };
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

value binSize = 512;
value scale = 1;
value toScreen pnt = Point.(create (scale * (x pnt) + 100) (1200 - scale * (y pnt) - 10));
value drawRect rect =
  let lb = toScreen (Rectangle.leftBottom rect) in
    Graphics.draw_rect (Point.x lb) (Point.y lb - scale * (Rectangle.height rect)) (scale * Rectangle.width rect) (scale * Rectangle.height rect);

value showHolesMode = ref False;
value holeIndx = ref 0;
(* value rects = ref []; *)
value cnt = ref 0;

let bin = Bin.create binSize binSize in (
  try
    Graphics.open_graph " 1200X1200"
  with [ Graphics.Graphic_failure reason -> ( debug "fail %s" reason; exit 0; ) ];

  debug:pizda "%s" (String.concat "," (List.map (fun rect -> Rectangle.toString rect) (Hole.plus (Rectangle.fromCoordsAndDims 0 0 20 20) (Rectangle.fromCoordsAndDims 20 20 40 40))));

  Graphics.set_color Graphics.red;
  Graphics.set_line_width 2;

  drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

  
  Graphics.set_line_width 1;

(*   drawRect (Rectangle.fromCoordsAndDims 28 0 38 200);
  drawRect (Rectangle.fromCoordsAndDims 50 18 150 182);

  Graphics.set_color Graphics.magenta; *)
  (* drawRect (Rectangle.fromCoordsAndDims 50 0 16 200); *)


(* drawRect (Rectangle.fromCoordsAndDims 61 19 100 94);
drawRect (Rectangle.fromCoordsAndDims 261 23 81 1001);
drawRect (Rectangle.fromCoordsAndDims 0 113 161 911);
drawRect (Rectangle.fromCoordsAndDims 161 18 68 5);
drawRect (Rectangle.fromCoordsAndDims 0 117 1024 907);
drawRect (Rectangle.fromCoordsAndDims 261 112 763 912);
drawRect (Rectangle.fromCoordsAndDims 261 100 586 924);
drawRect (Rectangle.fromCoordsAndDims 448 92 399 932);
drawRect (Rectangle.fromCoordsAndDims 394 15 70 3);
drawRect (Rectangle.fromCoordsAndDims 448 15 16 1009);
drawRect (Rectangle.fromCoordsAndDims 937 0 87 1024);
drawRect (Rectangle.fromCoordsAndDims 734 73 113 951);
drawRect (Rectangle.fromCoordsAndDims 577 0 22 92);
drawRect (Rectangle.fromCoordsAndDims 464 73 135 19);
drawRect (Rectangle.fromCoordsAndDims 567 0 10 73);
drawRect (Rectangle.fromCoordsAndDims 464 56 113 17);
drawRect (Rectangle.fromCoordsAndDims 0 20 61 1004);
drawRect (Rectangle.fromCoordsAndDims 135 18 94 1); *)

(* drawRect (Rectangle.fromCoordsAndDims 937 0 87 372);
drawRect (Rectangle.fromCoordsAndDims 996 502 28 522);
drawRect (Rectangle.fromCoordsAndDims 570 92 277 20);
drawRect (Rectangle.fromCoordsAndDims 383 100 24 130);
drawRect (Rectangle.fromCoordsAndDims 61 19 168 4);
drawRect (Rectangle.fromCoordsAndDims 383 100 65 122);
drawRect (Rectangle.fromCoordsAndDims 0 20 161 93);
drawRect (Rectangle.fromCoordsAndDims 610 998 122 26);
drawRect (Rectangle.fromCoordsAndDims 261 23 81 77);
drawRect (Rectangle.fromCoordsAndDims 1017 0 7 1024);
drawRect (Rectangle.fromCoordsAndDims 0 243 142 4);
drawRect (Rectangle.fromCoordsAndDims 936 112 88 260);
drawRect (Rectangle.fromCoordsAndDims 61 19 100 94);
drawRect (Rectangle.fromCoordsAndDims 0 1022 1024 2);
drawRect (Rectangle.fromCoordsAndDims 610 482 20 126);
drawRect (Rectangle.fromCoordsAndDims 0 897 122 127);
drawRect (Rectangle.fromCoordsAndDims 773 348 41 24);
drawRect (Rectangle.fromCoordsAndDims 651 92 41 256);
drawRect (Rectangle.fromCoordsAndDims 366 360 20 122);
drawRect (Rectangle.fromCoordsAndDims 734 73 80 145);
drawRect (Rectangle.fromCoordsAndDims 732 608 20 24);
drawRect (Rectangle.fromCoordsAndDims 752 478 21 24);
drawRect (Rectangle.fromCoordsAndDims 135 18 26 212);
drawRect (Rectangle.fromCoordsAndDims 734 73 113 39);
drawRect (Rectangle.fromCoordsAndDims 135 18 7 342);
drawRect (Rectangle.fromCoordsAndDims 567 0 32 92);
drawRect (Rectangle.fromCoordsAndDims 0 1010 732 14);
drawRect (Rectangle.fromCoordsAndDims 394 15 70 3);
drawRect (Rectangle.fromCoordsAndDims 570 92 244 126);
drawRect (Rectangle.fromCoordsAndDims 122 19 20 341);
drawRect (Rectangle.fromCoordsAndDims 366 1002 366 22);
drawRect (Rectangle.fromCoordsAndDims 122 117 139 113);
drawRect (Rectangle.fromCoordsAndDims 570 0 29 222);
drawRect (Rectangle.fromCoordsAndDims 386 100 21 252);
drawRect (Rectangle.fromCoordsAndDims 122 19 39 211);
drawRect (Rectangle.fromCoordsAndDims 0 20 229 3);
drawRect (Rectangle.fromCoordsAndDims 135 18 94 5);
drawRect (Rectangle.fromCoordsAndDims 630 352 21 126);
drawRect (Rectangle.fromCoordsAndDims 448 15 16 77);
drawRect (Rectangle.fromCoordsAndDims 448 56 151 36);
drawRect (Rectangle.fromCoordsAndDims 976 632 48 392); *)

  
(* drawRect (Rectangle.fromCoordsAndDims 906 87 34 270);
drawRect (Rectangle.fromCoordsAndDims 672 181 134 176);
drawRect (Rectangle.fromCoordsAndDims 772 87 34 270);
drawRect (Rectangle.fromCoordsAndDims 806 181 134 176);
drawRect (Rectangle.fromCoordsAndDims 773 70 120 17);
drawRect (Rectangle.fromCoordsAndDims 288 85 29 278);
drawRect (Rectangle.fromCoordsAndDims 207 23 86 62);
drawRect (Rectangle.fromCoordsAndDims 61 118 146 119);
drawRect (Rectangle.fromCoordsAndDims 128 19 79 218);
drawRect (Rectangle.fromCoordsAndDims 207 203 110 160);
drawRect (Rectangle.fromCoordsAndDims 439 18 1 194);
drawRect (Rectangle.fromCoordsAndDims 342 108 98 104);
drawRect (Rectangle.fromCoordsAndDims 440 23 95 58);
drawRect (Rectangle.fromCoordsAndDims 540 81 46 218);
drawRect (Rectangle.fromCoordsAndDims 440 168 146 131);
drawRect (Rectangle.fromCoordsAndDims 440 15 24 66);
drawRect (Rectangle.fromCoordsAndDims 293 23 49 62);
drawRect (Rectangle.fromCoordsAndDims 317 23 25 189);
drawRect (Rectangle.fromCoordsAndDims 394 15 70 3);
drawRect (Rectangle.fromCoordsAndDims 773 0 86 70);
drawRect (Rectangle.fromCoordsAndDims 0 455 118 86);
drawRect (Rectangle.fromCoordsAndDims 360 422 67 95);
drawRect (Rectangle.fromCoordsAndDims 146 363 171 59);
drawRect (Rectangle.fromCoordsAndDims 146 237 61 185);
drawRect (Rectangle.fromCoordsAndDims 573 299 99 58);
drawRect (Rectangle.fromCoordsAndDims 207 18 22 5);
drawRect (Rectangle.fromCoordsAndDims 135 18 94 1);
drawRect (Rectangle.fromCoordsAndDims 1013 0 11 1024);
drawRect (Rectangle.fromCoordsAndDims 427 212 13 87);
drawRect (Rectangle.fromCoordsAndDims 940 87 84 270);
drawRect (Rectangle.fromCoordsAndDims 1001 87 23 937);
drawRect (Rectangle.fromCoordsAndDims 0 541 146 483);
drawRect (Rectangle.fromCoordsAndDims 118 455 28 569);
drawRect (Rectangle.fromCoordsAndDims 0 640 478 384);
drawRect (Rectangle.fromCoordsAndDims 478 517 95 58);
drawRect (Rectangle.fromCoordsAndDims 360 603 118 421);
drawRect (Rectangle.fromCoordsAndDims 744 575 280 449);
drawRect (Rectangle.fromCoordsAndDims 0 897 1024 127);
drawRect (Rectangle.fromCoordsAndDims 478 575 266 322);
drawRect (Rectangle.fromCoordsAndDims 146 422 214 218);
drawRect (Rectangle.fromCoordsAndDims 787 357 214 218);
drawRect (Rectangle.fromCoordsAndDims 573 357 214 218);
drawRect (Rectangle.fromCoordsAndDims 427 299 146 218);
drawRect (Rectangle.fromCoordsAndDims 0 237 146 218);
drawRect (Rectangle.fromCoordsAndDims 317 212 110 210);
drawRect (Rectangle.fromCoordsAndDims 0 20 61 217);
drawRect (Rectangle.fromCoordsAndDims 535 23 71 58);
drawRect (Rectangle.fromCoordsAndDims 535 56 119 25);
drawRect (Rectangle.fromCoordsAndDims 653 0 1 81);
drawRect (Rectangle.fromCoordsAndDims 586 143 86 214);
drawRect (Rectangle.fromCoordsAndDims 672 81 101 6);
drawRect (Rectangle.fromCoordsAndDims 586 81 86 62);
 *)
Graphics.set_color Graphics.magenta;

let bholes = [(0,81,450,40);(0,121,450,5);(0,61,450,14);(0,75,450,6);(0,299,450,7);(0,287,450,11);(0,298,450,1);(0,348,450,2);(0,306,450,12);(0,318,450,30);(0,150,450,11);(0,161,450,4);(0,127,450,17);(0,144,450,6);(0,261,450,19);(0,280,450,7);(0,165,450,62);(0,227,450,34);(0,387,100,2);(0,376,100,10);(0,386,100,1);(0,389,100,2);(0,364,100,4);(0,350,100,12);(0,362,100,2);(0,368,100,8);(0,391,100,9);(450,27,50,7);(450,15,50,10);(450,25,50,2);(450,52,50,16);(450,68,50,2);(450,34,50,16);(450,50,50,2);(450,10,50,1);(450,0,50,10);(450,11,50,4);(450,247,50,36);(450,283,50,5);(450,124,50,62);(450,186,50,61);(450,299,50,1);(450,288,50,10);(450,298,50,1);(450,100,50,5);(450,70,50,21);(450,91,50,9);(450,121,50,3);(450,105,50,13);(450,118,50,3)] in
List.iter (fun (x, y, w, h) -> drawRect (Rectangle.fromCoordsAndDims x y w h)) bholes;

(* let aholes = [(0,338,472,174);(0,426,512,86);(67,174,204,338);(102,26,128,486);(499,0,13,512);(102,0,31,512);(102,46,169,466);(489,0,23,400);(0,267,271,245);(230,0,282,21);(0,338,512,62);(363,0,149,311);(67,174,445,137);(102,46,410,265);(0,174,512,68);(0,267,512,44)] in
List.iter (fun (x, y, w, h) -> drawRect (Rectangle.fromCoordsAndDims x y w h)) aholes;
 *)
Graphics.set_color Graphics.green;
(* let brects = [(133,0,97,26);(271,311,218,27);(230,21,133,25);(472,400,27,26);(0,0,102,174);(0,242,67,25)] in
List.iter (fun (x, y, w, h) -> drawRect (Rectangle.fromCoordsAndDims x y w h)) brects; *)

(* let arects = [(133,0,97,26);(271,311,218,27);(0,242,67,25)] in
List.iter (fun (x, y, w, h) -> drawRect (Rectangle.fromCoordsAndDims x y w h)) arects; *)
  




(* drawRect (Rectangle.fromCoordsAndDims 806 87 100 94);
drawRect (Rectangle.fromCoordsAndDims 672 87 100 94);
drawRect (Rectangle.fromCoordsAndDims 207 85 81 118);
drawRect (Rectangle.fromCoordsAndDims 606 0 47 56);
drawRect (Rectangle.fromCoordsAndDims 440 81 100 87);
drawRect (Rectangle.fromCoordsAndDims 61 19 67 99);
drawRect (Rectangle.fromCoordsAndDims 342 18 97 90);
drawRect (Rectangle.fromCoordsAndDims 360 517 118 86);
drawRect (Rectangle.fromCoordsAndDims 535 0 71 23);
drawRect (Rectangle.fromCoordsAndDims 893 0 120 87);
drawRect (Rectangle.fromCoordsAndDims 654 0 119 81);
drawRect (Rectangle.fromCoordsAndDims 464 0 71 23);
drawRect (Rectangle.fromCoordsAndDims 394 0 70 15);
drawRect (Rectangle.fromCoordsAndDims 342 0 52 18);
drawRect (Rectangle.fromCoordsAndDims 229 0 113 23);
drawRect (Rectangle.fromCoordsAndDims 135 0 94 18);
drawRect (Rectangle.fromCoordsAndDims 61 0 74 19);
drawRect (Rectangle.fromCoordsAndDims 0 0 61 20); *)

(* drawRect (Rectangle.fromCoordsAndDims 161 23 100 94);
drawRect (Rectangle.fromCoordsAndDims 342 18 106 82);
drawRect (Rectangle.fromCoordsAndDims 522 0 45 56);
drawRect (Rectangle.fromCoordsAndDims 847 0 90 112);
drawRect (Rectangle.fromCoordsAndDims 464 0 58 56);
drawRect (Rectangle.fromCoordsAndDims 734 0 113 73);
drawRect (Rectangle.fromCoordsAndDims 599 0 135 92);
drawRect (Rectangle.fromCoordsAndDims 394 0 70 15);
drawRect (Rectangle.fromCoordsAndDims 342 0 52 18);
drawRect (Rectangle.fromCoordsAndDims 229 0 113 23);
drawRect (Rectangle.fromCoordsAndDims 135 0 94 18);
drawRect (Rectangle.fromCoordsAndDims 61 0 74 19);
drawRect (Rectangle.fromCoordsAndDims 0 0 61 20); *)


  (* debug "++++ %B" (Rectangle.rectInside (Rectangle.fromCoordsAndDims 28 0 38 200) (Rectangle.fromCoordsAndDims 50 0 16 200)); *)
  
(*   Graphics.set_color Graphics.magenta;
  List.iter (fun rect -> drawRect rect) bin.Bin.holes; 

  Graphics.set_color Graphics.green;
  List.iter (fun rect -> drawRect rect) bin.Bin.rects;  *)

  

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
        then ()
(*           let () = Bin.repair bin in (
            Graphics.clear_graph ();
            Graphics.set_color Graphics.red;
            drawRect (Rectangle.fromCoordsAndDims 0 0 binSize binSize);

            Graphics.set_color Graphics.magenta;
            List.iter (fun rect -> drawRect rect) bin.Bin.holes; 

            Graphics.set_color Graphics.green;
            List.iter (fun rect -> drawRect rect) bin.Bin.rects;

            let () = Printf.printf "bholes = [%s]\n" ((String.concat ";" (List.map (fun rect -> Rectangle.(Printf.sprintf "(%d,%d,%d,%d)" (x rect) (y rect) (width rect) (height rect))) (bin.holes @ bin.reuseRects))))) in
          ) *)
(*           if !showHolesMode
          then showHole ()
          else
            let (w, h) = if !rects = [] then (Random.int 20 + 10, Random.int 20 + 10) else let rect = List.hd !rects in ( rects.val := List.tl !rects; rect ) in
              try (          
                debug "trying to add %d %d... " w h;
                let pos = Bin.add bin w h in (
                  debug "ok, added at %s, is consistent %B" (Point.toString pos) (Bin.isConsistent bin);
                  Graphics.set_color Graphics.green;
                  drawRect (Rectangle.fromPntAndDims pos w h);
                )
              )          
              with [ Bin.CantPlace -> debug "cannot place" ] *)
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

