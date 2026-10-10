/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Arithmetic
-/
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The basic API of `Work.Arithmetic.Torsor`

Elementary consequences of the definitions in `Submission/Work/Arithmetic/Defs.lean`: the
period/index bookkeeping (`period`, `index`, `DivisorOfDegree`), the transport `Jac^d`
(`jacPow`, `jacSq`), and the isomorphism criterion `IsIso` of Shinder–Zhang §2.

Vocabulary (paper §"Elliptic curves", `ssec-dim3`, and Shinder–Zhang §2):
* `T.period` is the order of the class `[C] ∈ H¹(𝕜,E)`;
* `T.DivisorOfDegree n` says `n · [C] = 0`, i.e. `C` carries a `𝕜`-rational divisor of
  degree `n`, i.e. `Jac^n(C) ≅ E = Jac⁰(C)`;
* `T.Pointless` says `[C] ≠ 0`, i.e. `C(𝕜) = ∅`;
* `T.jacPow d` is `Jac^d(C)`, and `T.jacSq` is `Jac²C`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Order

namespace Work.Arithmetic

noncomputable section

namespace Torsor

variable {𝕜 : Type} [Field 𝕜]

theorem index_eq_period (T : Torsor 𝕜) : T.index = T.period := rfl

theorem hasPoint_iff (T : Torsor 𝕜) : T.HasPoint ↔ T.cls = 1 := Iff.rfl

theorem pointless_iff (T : Torsor 𝕜) : T.Pointless ↔ T.cls ≠ 1 := Iff.rfl

theorem divisorOfDegree_iff (T : Torsor 𝕜) (n : ℕ) :
    T.DivisorOfDegree n ↔ T.cls ^ n = 1 := Iff.rfl

theorem divisorOfDegree_one (T : Torsor 𝕜) : T.DivisorOfDegree 1 ↔ T.HasPoint := by
  rw [divisorOfDegree_iff, hasPoint_iff, pow_one]

/-- `C` carries a `𝕜`-rational divisor of degree `n` iff `n` is a multiple of the period. -/
theorem divisorOfDegree_iff_dvd (T : Torsor 𝕜) (n : ℕ) :
    T.DivisorOfDegree n ↔ T.period ∣ n := by
  rw [divisorOfDegree_iff, period, orderOf_dvd_iff_pow_eq_one]

theorem divisorOfDegree_of_dvd (T : Torsor 𝕜) {m n : ℕ} (h : m ∣ n)
    (hm : T.DivisorOfDegree m) : T.DivisorOfDegree n := by
  rw [divisorOfDegree_iff_dvd] at hm ⊢
  exact hm.trans h

/-- `Torsor.jacPow_cls`, with the type of the right-hand side pinned to `T.W` (the `W`-field
of `T.jacPow d` is definitionally, but not syntactically, `T.W`). -/
theorem jacPow_cls' (T : Torsor 𝕜) (d : ℤ) :
    ((T.jacPow d).cls : T.W) = T.cls ^ d := rfl

/-- `Torsor.jacSq_cls`, with the type of the right-hand side pinned to `T.W`. -/
theorem jacSq_cls' (T : Torsor 𝕜) : (T.jacSq.cls : T.W) = T.cls ^ (2 : ℤ) := rfl

/- Note: `Jac⁰C = E` (the degree-`0` transport is the trivial torsor).  We record it as the
docstring rather than a lemma, because `Jac⁰` is represented by `Torsor.jacPow 0`, whose `W`
field is only definitionally `T.W`, which makes such statements awkward to state. -/

/-! ### Periodicity of `Jac^d` for a degree-five curve

For a curve of degree (and period) `5`, `Jac^{k+5}C ≅ Jac^k C` and `Jac^{-k}C ≅ Jac^{5-k}C`
(Shinder–Zhang §2: tensoring with the degree-`5` line bundle and dualizing). -/

/-- For a curve of period `5`: `[C] ^ 5 = 1` in `H¹`, i.e. `Jac⁵C ≅ Jac⁰C = E`. -/
theorem zpow_five_eq_one (T : Torsor 𝕜) (h : T.period = 5) : T.cls ^ (5 : ℤ) = 1 := by
  have h5n : T.cls ^ (5 : ℕ) = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  simpa using h5n

/-- `Jac^{k+5}C ≅ Jac^kC` for a curve of period `5`. -/
theorem jacPow_shift_cls (T : Torsor 𝕜) (h : T.period = 5) (k : ℤ) :
    T.cls ^ (k + 5) = T.cls ^ k := by
  rw [zpow_add, T.zpow_five_eq_one h, mul_one]

/-- `Jac^{-k}C ≅ Jac^{5-k}C` for a curve of period `5`. -/
theorem jacPow_neg_cls (T : Torsor 𝕜) (h : T.period = 5) (k : ℤ) :
    T.cls ^ (-k) = T.cls ^ (5 - k) := by
  rw [show (5 - k : ℤ) = 5 + (-k) by ring, zpow_add, T.zpow_five_eq_one h, one_mul]

/-- The isomorphism criterion of Shinder–Zhang §2 in the form used in the paper:
`Jac²C ≅ C` iff the class of `Jac²C` lies in the `Aut(E)`-orbit of the class of `C`. -/
theorem isIso_jacSq_iff (T : Torsor 𝕜) :
    T.IsIso T.jacSq.cls ↔ ∃ σ : Aut 𝕜 T.E, T.act σ T.cls = T.cls ^ (2 : ℤ) := Iff.rfl

theorem notIsoJacSq_iff (T : Torsor 𝕜) : T.NotIsoJacSq ↔ ¬ T.IsIso T.jacSq.cls := Iff.rfl

/-- `C ≅ C`. -/
theorem isIso_refl (T : Torsor 𝕜) (η : T.W) (h : η = T.cls) : T.IsIso η := h ▸ T.isIso_cls

end Torsor

end

end Work.Arithmetic
