import Qpf.ITree.Basic

-- Ensure the macro-generated base functor has a QPF instance.
#synth MvQPF (TypeFun.ofCurried (ITree.Base (α := Unit)))
