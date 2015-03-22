let rec f x y = x +. x *. y in
    let x = read_float () in
    print_float (f x 2.0)
