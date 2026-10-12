import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.MonoOp` — the algebra of the anti-normal monomials and their symbols

The two objects through which FS `eq:HLambdaSecond` / `eq:Kz` are consumed are

* `monoOp p q B = a₀^p ∘ (a₀†)^q ∘ lift B`  — one term of the second-quantised
  Hamiltonian, with `B : E →ₗ[ℂ] E` acting on the non-condensate modes, and
* `symbol p q B z = (z^p z̄^q) • B`  — its anti-Wick symbol at the coherent
  parameter `z` (FS `eq:subst-z`).

This module records that both are ℂ-linear in `B` and additive in finite sums, so
that a Hamiltonian given as a finite sum of monomials can be assembled term by
term, and the `(p,q) = (0,0)` case (`a₀`-free terms, e.g. `∫ τ(k) a_k†a_k dk`) is
just `lift B`.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## The anti-normal monomials -/

@[simp]
lemma monoOp_zero_zero (B : E →ₗ[ℂ] E) : monoOp 0 0 B = lift B := by
  ext Ψ
  simp [monoOp]

@[simp]
lemma monoOp_add (p q : ℕ) (B B' : E →ₗ[ℂ] E) :
    monoOp p q (B + B') = monoOp p q B + monoOp p q B' := by
  simp only [monoOp, lift_add]
  rw [LinearMap.comp_add, LinearMap.comp_add]

@[simp]
lemma monoOp_smul (p q : ℕ) (c : ℂ) (B : E →ₗ[ℂ] E) :
    monoOp p q (c • B) = c • monoOp p q B := by
  simp only [monoOp, lift_smul]
  rw [LinearMap.comp_smul, LinearMap.comp_smul]

@[simp]
lemma monoOp_zero_fn (p q : ℕ) : monoOp p q (0 : E →ₗ[ℂ] E) = 0 := by
  have h : lift (0 : E →ₗ[ℂ] E) = 0 := by
    ext Ψ n
    simp
  rw [monoOp, h, LinearMap.comp_zero, LinearMap.comp_zero]

/-! ## The anti-Wick symbols -/

@[simp]
lemma symbol_zero_zero (B : E →ₗ[ℂ] E) (z : ℂ) : symbol 0 0 B z = B := by
  simp [symbol]

@[simp]
lemma symbol_add (p q : ℕ) (B B' : E →ₗ[ℂ] E) (z : ℂ) :
    symbol p q (B + B') z = symbol p q B z + symbol p q B' z := by
  simp [symbol, smul_add]

@[simp]
lemma symbol_smul (p q : ℕ) (c : ℂ) (B : E →ₗ[ℂ] E) (z : ℂ) :
    symbol p q (c • B) z = c • symbol p q B z := by
  simp [symbol, smul_smul, mul_comm]

@[simp]
lemma symbol_zero_fn (p q : ℕ) (z : ℂ) : symbol p q (0 : E →ₗ[ℂ] E) z = 0 := by
  simp [symbol]

lemma symbol_apply (p q : ℕ) (B : E →ₗ[ℂ] E) (z : ℂ) (v : E) :
    symbol p q B z v = (z ^ p * (starRingEnd ℂ z) ^ q) • (B v) := rfl

/-- The symbol of a finite sum of monomials: FS's `𝓚(z)`. -/
lemma sum_symbol_apply {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E)
    (z : ℂ) (v : E) :
    ((∑ i ∈ s, symbol (p i) (q i) (B i) z) v)
      = ∑ i ∈ s, (z ^ (p i) * (starRingEnd ℂ z) ^ (q i)) • (B i v) := by
  rw [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => symbol_apply (p i) (q i) (B i) z v

end Work.BoseB4
