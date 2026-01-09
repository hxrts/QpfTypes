/-!
# Coinductive Tree Protocol (Abstract)

This module defines an abstract interface for coinductive tree-like types with
three constructors (`ret`, `tau`, `vis`) and the usual injectivity/distinctness
properties. It is designed as a reusable spec layer that concrete coinductive
implementations (e.g. QPF/Cofix-based ITrees) can instantiate.
-/-

/-- Binary relations on a type. -/
def Rel (α : Type) := α → α → Prop

/-- Abstract protocol for coinductive tree types. -/
class CoinductiveTreeProtocol (T : Type → Type → Type → Type) where
  ret {α ε ρ : Type} : ρ → T α ε ρ
  tau {α ε ρ : Type} : T α ε ρ → T α ε ρ
  vis {α ε ρ : Type} : ε → (α → T α ε ρ) → T α ε ρ

  ret_ne_tau {α ε ρ : Type} {r : ρ} {t : T α ε ρ} : ret r ≠ tau t
  ret_ne_vis {α ε ρ : Type} {r : ρ} {e : ε} {k : α → T α ε ρ} : ret r ≠ vis e k
  tau_ne_vis {α ε ρ : Type} {t : T α ε ρ} {e : ε} {k : α → T α ε ρ} : tau t ≠ vis e k

  ret_inj {α ε ρ : Type} {r₁ r₂ : ρ} : (ret r₁ : T α ε ρ) = ret r₂ → r₁ = r₂
  tau_inj {α ε ρ : Type} {t₁ t₂ : T α ε ρ} : (tau t₁ : T α ε ρ) = tau t₂ → t₁ = t₂
  vis_inj {α ε ρ : Type} {e₁ e₂ : ε} {k₁ k₂ : α → T α ε ρ} :
    (vis e₁ k₁ : T α ε ρ) = vis e₂ k₂ → e₁ = e₂ ∧ k₁ = k₂

export CoinductiveTreeProtocol
  (ret tau vis ret_ne_tau ret_ne_vis tau_ne_vis ret_inj tau_inj vis_inj)

/-- Extension with a case analysis axiom, useful for proof automation. -/
class CoinductiveTreeProtocolWithCases (T : Type → Type → Type → Type)
    extends CoinductiveTreeProtocol T where
  cases {α ε ρ : Type} (t : T α ε ρ) :
    (∃ r, t = ret r) ∨ (∃ x, t = tau x) ∨ (∃ e k, t = vis e k)

export CoinductiveTreeProtocolWithCases (cases)
