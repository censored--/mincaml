module List = struct
  include List
  let remove x list =
    let rec _rm x l = match l with
      |lx::ls->if x = lx then _rm x ls else lx::ls
      |[]->[] in
    _rm x list
  let take n x =
    let rec _t n x = 
      if n <= 0 then [] else
	match x with
	|xx::xs->xx::_t (n-1) xs
	|[]->[] in
    _t n x
  let drop n x =
    let rec _d n x = 
      if n <= 0 then x else
	match x with
	|xx::xs->_d (n-1) xs
	|[]->[] in
    _d n x
end
