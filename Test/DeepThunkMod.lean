import Qpf
import Qpf.Builtins.List
import Qpf.Qpf.Multivariate.Constructions.DeepThunk

open MvQPF
open MvQPF.List
open MvQPF.DeepThunk

example :
    (β → UncurriedMod List' PUnit (α := !![]) (β := β)) →
      β → Cofix List' (!![]) :=
  corecMod_id (F := List') (α := !![])
