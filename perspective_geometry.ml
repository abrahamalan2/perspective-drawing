#use "topfind";;
#require "graphics";;
#load "graphics.cma";;

let (<<) f g x = f(g(x));;

let size_x = ref 800
let size_y = ref 800
let _ = Graphics.open_graph (Printf.sprintf "%ix%i" (!size_x) (!size_y))
let _ = Graphics.set_window_title "Window"
let _ = Graphics.set_line_width 1


type coordinate = float * float
type point = 
  | Coordinate of coordinate 
  | Intersection of (line ref * line ref * (coordinate option))
  | Incident of (line ref * float * (coordinate option))
and line = 
  | Endpoints of (point ref * point ref * ((coordinate * coordinate) option))


let rec getCoord (p : point ref) = match !p with 
  | Coordinate (u,v) -> (u,v)
  | Intersection (_,_,Some (u,v)) -> (u,v)
  | Intersection (l1,l2,None) -> p := Intersection (l1,l2,Some (getIntersection l1 l2)); getCoord p 
  | Incident (_,_,Some (u,v)) -> (u,v)
  | Incident (l,t,None) -> let ((x1,y1),(x2,y2)) = getEndpts l in
    p := Incident (l,t,Some (t*.x1 +. (1.-.t)*.x2,t*.y1 +. (1.-.t)*.y2));
    getCoord p
and getEndpts (l : line ref) = match !l with
  | Endpoints (_,_,Some ((a,b),(c,d))) -> ((a,b),(c,d))
  | Endpoints (a,b,None) -> l := Endpoints (a,b,Some (getCoord a, getCoord b)); getEndpts l
and getIntersection (l1: line ref) (l2 : line ref) = let (((x1,y1),(x2,y2)),((x3,y3),(x4,y4))) = (getEndpts l1, getEndpts l2) in
  (*formula found on wikipedia*)
  (((x1*.y2-.y1*.x2)*.(x3-.x4)-.(x1-.x2)*.(x3*.y4-.y3*.x4))/.((x1-.x2)*.(y3-.y4)-.(y1-.y2)*.(x3-.x4)),((x1*.y2-.y1*.x2)*.(y3-.y4)-.(y1-.y2)*.(x3*.y4-.y3*.x4))/.((x1-.x2)*.(y3-.y4)-.(y1-.y2)*.(x3-.x4)))

let point_to_point_distance x y p = let (u,v) = getCoord p in Float.sqrt ((x-.u)*.(x-.u) +. (y-.v)*.(y-.v))

let point_to_line_distance x y l = let ((x1,y1),(x2,y2)) = getEndpts l in
  (*formula found on wikipedia*)
  (Float.abs ((x2-.x1)*.(y1-.y) -. (x1-.x)*.(y2-.y1))) /. (Float.sqrt ((x2-.x1)*.(x2-.x1) +. (y2-.y1)*.(y2-.y1)))

let getClosestPt x y l = let ((x1,y1),(x2,y2)) = getEndpts l in
  (*If P=(x,y) and l has endpoints A,B then t minimizes the magnitude of P-tA-(1-t)B*)
  let t = ((x2-.x1)*.(x2-.x) +. (y2-.y1)*.(y2-.y)) /. ((x2-.x1)*.(x2-.x1) +. (y2-.y1)*.(y2-.y1)) in
    (t,(t*.x1 +. (1.-.t)*.x2, t*.y1 +. (1.-.t)*.y2))





(*
N: nothing
P: nearest point
L: nearest line
I: nearest intersection   
*)
type snap_option = N | P | I | L
let snap = ref N

let geo_list: ((point ref list ref) * (line ref list ref)) ref = ref (ref [], ref [])
(*
p: plot a point
l: plot a line from two endpoints
I: plot a point that is the intersection of two lines
L: plot a point incident on a line
m: move a point
+,-: zoom in/out
*)
let updateKey (k : char ref) (c : char) (mode: int ref) = try (k := List.find (fun x -> c=x) ['p'; 'l'; 'I'; 'L'; 'm'; '+'; '-'; '!'; '@'; '#'; '1'; '2'; '3']; mode := 0) with Not_found -> ()
let key = ref 'p'

let mode = ref 0

let drawPoint x y =
  Graphics.set_color Graphics.red;
  Graphics.fill_ellipse (Float.to_int x) (Float.to_int y) 5 5

let drawLine x1 y1 x2 y2 = let (dx,dy) = (x2-.x1,y2-.y1) in
  let scale = Float.min (1.+.Float.abs ((Float.of_int (Graphics.size_x ())) /. dx)) (1.+.Float.abs ((Float.of_int (Graphics.size_y ())) /. dy)) in
    Graphics.set_line_width 2;
    Graphics.set_color Graphics.red;
    Graphics.moveto (Float.to_int x1) (Float.to_int y1);
    Graphics.rmoveto (Float.to_int (scale *. (-.dx))) (Float.to_int (scale *. (-.dy)));
    Graphics.rlineto (Float.to_int (3. *. scale *. dx)) (Float.to_int (3. *. scale *. dy))

let drawGeo (g: ((point ref list ref) * (line ref list ref)) ref) = let (ps,ls) = !g in
  List.fold_left (fun _ p -> match !p with
    | Coordinate (u,v) -> ()
    | Intersection (a,b,_) -> p := Intersection (a,b,None)
    | Incident (a,b,_) -> p := Incident (a,b,None)) () (!ps);
  List.fold_left (fun _ l -> match !l with
    | Endpoints (a,b,_) -> l := Endpoints (a,b,None)) () (!ls);
  List.fold_left (fun _ p -> let (x,y) = getCoord p in drawPoint x y) () (!ps);
  List.fold_left (fun _ l -> let ((x1,y1),(x2,y2)) = getEndpts l in drawLine x1 y1 x2 y2) () (!ls)

let snapPosition x y snap g = let (ps,ls) = !g in match !snap with
  | N -> (x,y)
  | P -> let (coord,mindist) = List.fold_left (fun acc p -> 
    let (_,mindist) = acc in 
      let dist = point_to_point_distance x y p in
        if dist < mindist then (getCoord p,dist) else acc) ((0.0,0.0), Float.max_float) (!ps)
    in coord
  | I -> let rec findIntersections (lineList: line ref list) = match lineList with
    | [] | [_] -> []
    | l::ls -> List.append (List.fold_left (fun acc l' -> (getIntersection l l') :: acc) [] ls) (findIntersections ls) in
      let intersectionPts = findIntersections (!ls) in
        let (coord,mindist) = List.fold_left (fun acc p -> 
          let (_,mindist) = acc in 
            let dist = point_to_point_distance x y (ref (Coordinate p)) in
              if dist < mindist then (p, dist) else acc) ((0.0,0.0), Float.max_float) (intersectionPts)
          in coord
  | L -> let (coord,mindist) = List.fold_left (fun acc l -> 
    let (_,mindist) = acc in 
      let dist = point_to_line_distance x y l in
        if dist < mindist then (snd (getClosestPt x y l), dist) else acc) ((0.0,0.0), Float.max_float) (!ls)
    in coord
        
let hotkeyToNum k = match k with
  | '!' | '1' -> 0
  | '@' | '2' -> 1
  | '#' | '3' -> 2
  | _ -> raise (failwith "you're using this function wrong")

let message k m snap = match (k,!m) with
  | ('p',0) -> snap := N; "point: click to place a point"
  | ('l',0) -> snap := P; "line: select first endpoint"
  | ('l',1) -> snap := P; "line: select second endpoint"
  | ('I',0) -> snap := I; "Intersection: select intersection"
  | ('L',0) -> snap := L; "Line: select a point on a line"
  | ('m',0) -> snap := P; "move: select a point"
  | ('m',1) -> snap := N; "move: click to place new position of point"
  | ('m',2) -> snap := L; "move: click to place new position of point on line"
  | ('+',0) -> snap := N; "Zoom: click to zoom in"
  | ('-',0) -> snap := N; "Zoom: click to zoom out"
  | ('!',0) | ('@',0) | ('#',0) -> snap := P; "Hotkey "^(Int.to_string (hotkeyToNum k))^": select vanishing point hotkey"
  | ('1',0) | ('2',0) | ('3',0) -> snap := P; "Hotkey "^(Int.to_string (hotkeyToNum k))^": select point to draw line to"
  | _ -> "probably an error"

let addGeometry = let hotkeyArray: point ref option array = [|None; None; None|] in 
  let (ptbuffer, lnbuffer): (point ref option ref * line ref option ref) = (ref None,ref None) in
    fun (k : char) (mode : int ref) x y (snap : snap_option ref) g -> let (ps,ls) = !g in match (k,!mode) with
    | ('p',_) -> mode := 0; 
      begin
        ps := (ref (Coordinate (x, y))) :: !ps;
        drawPoint x y
      end
    | ('l',0) -> mode := 1;
      begin
        let (closest_pt,mindist) = List.fold_left (fun acc p -> 
          let (_,mindist) = acc in 
            let dist = point_to_point_distance x y p in
              if dist < mindist then (p,dist) else acc) ((try List.hd (!ps) with _ -> failwith "don't use \'l\' when you don't have any points"), Float.max_float) (!ps)
          in ptbuffer := Some closest_pt
      end
    | ('l',1) -> mode := 0;
    begin
      let (closest_pt,mindist) = List.fold_left (fun acc p -> 
        let (_,mindist) = acc in 
          let dist = point_to_point_distance x y p in
            if dist < mindist then (p,dist) else acc) (List.hd (!ps), Float.max_float) (!ps)
        in let (a,b) = (Option.get (!ptbuffer),closest_pt) in
          let ((a1,a2),(b1,b2)) = (getCoord a, getCoord b) in
          begin
            ls := (ref (Endpoints (a, b, Some ((a1, a2), (b1, b2))))) :: !ls;
            drawLine a1 a2 b1 b2
          end
    end
    | ('I',_) -> mode := 0; let rec findIntersections (lineList: line ref list) = match lineList with
      | [] | [_] -> []
      | l::ls -> List.append (List.fold_left (fun acc l' -> (Intersection (l, l', (Some (getIntersection l l')))) :: acc) [] ls) (findIntersections ls) in
        let intersectionPts = findIntersections (!ls) in
          let (closest_intersect,mindist) = List.fold_left (fun acc p -> 
            let (_,mindist) = acc in 
              let dist = point_to_point_distance x y (ref p) in
                if dist < mindist then (p,dist) else acc) ((try List.hd (intersectionPts) with _ -> failwith "don't use \'I\' when you don't have enough lines"), Float.max_float) (intersectionPts)
            in ps := (ref closest_intersect) :: !ps;
            let (a,b) = (getCoord (ref closest_intersect)) in drawPoint a b
    | ('L',_) -> mode := 0; let (line, (t,(x,y)), mindist) = List.fold_left (fun acc l -> 
      let (_,_,mindist) = acc in 
        let dist = point_to_line_distance x y l in
          if dist < mindist then (l, getClosestPt x y l, dist) else acc) (((try List.hd (!ls) with _ -> failwith "don't use \'I\' when you don't have enough lines")), (0.0,(0.0,0.0)), Float.max_float) (!ls)
      in ps := (ref (Incident (line, t, Some (x,y)))) :: !ps;
      drawPoint x y
    | ('m',0) -> mode := 1;
    begin
      let (closest_pt,mindist) = List.fold_left (fun acc p -> 
        let (_,mindist) = acc in match !p with
          | Coordinate _ | Incident _ -> let dist = point_to_point_distance x y p in
            if dist < mindist then (p,dist) else acc
          | _ -> acc) ((try List.hd (!ps) with _ -> failwith "don't use \'l\' when you don't have any points"), Float.max_float) (!ps)
        in ptbuffer := Some closest_pt; match !closest_pt with
          | Incident _ -> mode := 2;
          | _ -> ()
    end
    | ('m',1) -> mode := 0;
    begin
      (Option.get (!ptbuffer)) := (Coordinate (x, y));
      Graphics.clear_graph ();
      drawGeo g
    end
    | ('m',2) -> mode := 0;
    begin
      let p = (Option.get (!ptbuffer)) in
        let Incident(l,_,_) = !p in
          let (t,_) = getClosestPt x y l in
          p := Incident (l,t,None);
          Graphics.clear_graph ();
          drawGeo g
    end
    | ('+',0) -> mode := 0; 
    begin
      List.fold_left (fun _ p -> match !p with
        | Coordinate (a,b) -> p := Coordinate (1.1 *. (a -. x) +. x, 1.1 *. (b -. y) +. y)
        | _ -> ()) () (!ps);
        Graphics.clear_graph ();
        drawGeo g
    end
    | ('-',0) -> mode := 0; 
    begin
      List.fold_left (fun _ p -> match !p with
        | Coordinate (a,b) -> p := Coordinate (0.9 *. (a -. x) +. x, 0.9 *. (b -. y) +. y)
        | _ -> ()) () (!ps);
        Graphics.clear_graph ();
        drawGeo g
    end
    | ('!',0) | ('@',0) | ('#',0) -> mode := 0;
    begin
      let (closest_pt,mindist) = List.fold_left (fun acc p -> 
        let (_,mindist) = acc in 
          let dist = point_to_point_distance x y p in
            if dist < mindist then (p,dist) else acc) ((try List.hd (!ps) with _ -> failwith "don't use hotkeys when you don't have any points"), Float.max_float) (!ps)
        in Array.set hotkeyArray (hotkeyToNum k) (Some closest_pt)
    end
    | ('1',0) | ('2',0) | ('3',0) -> mode := 0;
    begin
      let (closest_pt,mindist) = List.fold_left (fun acc p -> 
        let (_,mindist) = acc in 
          let dist = point_to_point_distance x y p in
            if dist < mindist then (p,dist) else acc) (List.hd (!ps), Float.max_float) (!ps)
        in let (a,b) = try (Option.get (Array.get hotkeyArray (hotkeyToNum k)),closest_pt) with _ -> failwith "don't use hotkeys before initializing them" in
          let ((a1,a2),(b1,b2)) = (getCoord a, getCoord b) in
          begin
            ls := (ref (Endpoints (a, b, Some ((a1, a2), (b1, b2))))) :: !ls;
            drawLine a1 a2 b1 b2
          end
    end
    | _ -> ()


let draw (st : Graphics.status) (key : char ref) (mode : int ref) (snap : snap_option ref) g = let k = !key in
  (*clear window and redraw if resized*)
  let (a,b) = (Graphics.size_x (), Graphics.size_y ()) in if (a,b) <> (!size_x,!size_y) then
    begin
      size_x := a;
      size_y := b;
      Graphics.clear_graph ();
      drawGeo g
    end;

  (*text on the lower left*)
  begin
    let text = message k mode snap in
      let (_,h) = Graphics.text_size text in
        Graphics.remember_mode true;
        Graphics.set_color Graphics.white;
        Graphics.fill_rect 0 0 (Graphics.size_x ()) h;
        Graphics.set_color Graphics.black;
        Graphics.moveto 0 0;
        Graphics.draw_string (text)
  end;

  (*mouse drawings*)
  if st.button then let st = Graphics.wait_next_event [Graphics.Button_up] in 
  begin
    let (x,y) = snapPosition (Float.of_int st.mouse_x) (Float.of_int st.mouse_y) snap g in
      Graphics.remember_mode true;
      addGeometry k mode x y snap g
  end else 
  begin
    let (x,y) = snapPosition (Float.of_int st.mouse_x) (Float.of_int st.mouse_y) snap g in
      Graphics.remember_mode false;
      Graphics.set_color Graphics.blue;
      Graphics.fill_ellipse (Float.to_int x) (Float.to_int y) 5 5
  end





let _ =
  while true do
    let st = Graphics.wait_next_event [Graphics.Button_down; Graphics.Button_up; Graphics.Key_pressed; Graphics.Mouse_motion] in
      Graphics.synchronize ();
      if true then updateKey key st.key mode;
      draw st key mode snap (geo_list)
  done