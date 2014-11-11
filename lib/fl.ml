let rec fless x y = x < y +. 0.0
let rec fispos x = x > 0.0
let rec fisneg x = x < 0.0
let rec fiszero x = x = 0.0
let rec fneg x = -. x
let rec fsqr x = x *. x
let rec fhalf x = x *. 0.5
let rec fabs x = if x < 0.0 then -. x else x
let rec abs_float x = if x < 0.0 then -. x else x
let rec atan x = 
  let rec atan_sub x =
    x *. (1.0 /. 1. -. x *. x *. (1.0 /. 3. -. x *. x *. (1.0 /. 5. -. x *. x *. (1.0 /. 7. -. x *. x *. (1.0 /. 9. -. x *. x *. (1.0 /. 11. -. x *. x *. (1.0 /. 13. -. x *. x *. (1.0 /. 15. -. x *. x *. (1.0 /. 17. -. x *. x *. (1.0 /. 19. -. x *. x *. (1.0 /. 21. -. x *. x *. (1.0 /. 23.)))))))))))) in
  let pi = 3.1415926535898 in
  if fisneg x then -. atan (-. x)
  else if fless x 0.41421356 then atan_sub x
  else if fless x 1.0 then pi /. 4.0 -. atan_sub ((1.0 -. x) /. (1.0 +. x))
  else if fless x 2.41421356 then pi /. 4.0 +. atan_sub ((x -. 1.) /. (x +. 1.0))
  else pi /. 2.0 -. atan_sub (1.0 /. x)
let rec sin x = 
  let rec sin_sub x n f = if n >= 31 then 0.0 else
    f +. sin_sub x (n + 1) (-. f /. float_of_int (n * 2) /. float_of_int (n * 2 + 1) *. x *. x)
  in
  let pi = 3.1415926535898 in
  let q = floor (x /. 2.0 /. pi) in
  let r = x -. 2.0 *. pi *. q in
  sin_sub r 1 r

let rec cos x =
  let pi = 3.1415926535898 in
  sin (x +. pi /. 2.0)


