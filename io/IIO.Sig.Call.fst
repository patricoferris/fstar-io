module IIO.Sig.Call

open IIO.Sig

(** This file is replaced during linking with a file that contains the real
implementation of the commands. **)
let iio_call (cmd:cmds) (arg:iio_sig.args cmd) : iio (iio_sig.res cmd arg) =
  Call cmd arg Return
