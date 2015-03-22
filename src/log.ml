let logfile = Format.formatter_of_out_channel(open_out "log.txt")
let print fmt = Format.fprintf logfile fmt
