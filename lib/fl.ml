let rec fless x y = x < y +. 0.0
let rec fispos x = x > 0.0
let rec fisneg x = x < 0.0
let rec fiszero x = x = 0.0
let rec fneg x = -. x
let rec fsqr x = x *. x
let rec fhalf x = x *. 0.5
let rec fabs x = if x < 0.0 then -. x else x
let rec abs_float x = if x < 0.0 then -. x else x

