let rec dummyfun2 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
  x1 + x2 +x3 +x4 + x5 + x6 + x7 + x8 + x9  in
let rec  dummyfun x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 =
  let x21 = read_int () in
  let x22 = read_int () in
  let x23 = read_int () in
  let x24 = read_int () in
  let x25 = read_int () in
  let x26 = read_int () in
  let x27 = read_int () in
  let x28 = read_int () in
  let x29 = read_int () in
  let x30 = dummyfun2 x21 x22 x23 x24 x25 x26 x27 x28 x29 in
  x1 + x2 + x3 + x4 + x5+ x6 + x7 + x8 + x9 + x10  + x11 + x12 + x13 + x14 + x15+ x16 + x17 + x18 + x19 + x20 + x30 in
    
    print_int (dummyfun 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0)
