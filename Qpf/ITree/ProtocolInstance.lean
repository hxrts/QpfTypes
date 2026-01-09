import Qpf.Coinduction.Protocol
import Qpf.ITree.Basic

open CoinductiveTreeProtocol

namespace ITree

private def casesITree {α ε ρ : Type} (t : ITree α ε ρ) :
    (∃ r, t = ITree.ret r) ∨ (∃ x, t = ITree.tau x) ∨ (∃ e k, t = ITree.vis e k) := by
  match h : MvQPF.Cofix.dest t with
  | .ret r =>
      have ht : t = ITree.ret r := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      exact Or.inl ⟨r, ht⟩
  | .tau x =>
      have ht : t = ITree.tau x := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      exact Or.inr (Or.inl ⟨x, ht⟩)
  | .vis e k =>
      have ht : t = ITree.vis e k := by
        apply_fun MvQPF.Cofix.mk at h
        simpa [MvQPF.Cofix.mk_dest] using h
      exact Or.inr (Or.inr ⟨e, k, ht⟩)

instance : CoinductiveTreeProtocol ITree where
  ret := ITree.ret
  tau := ITree.tau
  vis := ITree.vis
  ret_ne_tau := ITree.ret_ne_tau
  ret_ne_vis := ITree.ret_ne_vis
  tau_ne_vis := ITree.tau_ne_vis
  ret_inj := ITree.ret_inj
  tau_inj := ITree.tau_inj
  vis_inj := ITree.vis_inj

instance : CoinductiveTreeProtocolWithCases ITree where
  cases := casesITree
  ret := ITree.ret
  tau := ITree.tau
  vis := ITree.vis
  ret_ne_tau := ITree.ret_ne_tau
  ret_ne_vis := ITree.ret_ne_vis
  tau_ne_vis := ITree.tau_ne_vis
  ret_inj := ITree.ret_inj
  tau_inj := ITree.tau_inj
  vis_inj := ITree.vis_inj

end ITree
