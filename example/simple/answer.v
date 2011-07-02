Require Import CoqExec.OCaml.Prelude.

Definition answer := run_main (fun _ => print_int (c 42)).
