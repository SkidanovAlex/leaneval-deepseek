import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Ann_cre_ccr` — the canonical commutation relation `[a_l, a_{l'}^†] = δ_{ll'}`

In the monomial-coefficient (occupation-number) model of the bosonic Fock space over
`m` modes (`Submission/Work/BoseB4/RealFock.lean`), the two one-mode operators act on
the basis vector `Finsupp.single α b` (`α` a multi-index, `b` a coefficient) by

* `ann m l (single α b) = single (α - e m l) ((α l : ℝ) * b)`,
* `cre m l (single α b) = single (α + e m l) b`,

i.e. they shift the multi-index by `∓ e m l` and annihilate with the occupation number.
Consequently

* `ann m l (cre m l (single α b)) = ((α l : ℝ) + 1) • single α b`,
* `cre m l (ann m l (single α b)) = (α l : ℝ) • single α b`,

where in the second identity the only non-trivial point is the index identity
`(α - e m l) + e m l = α`, valid as soon as `α l ≠ 0`; if `α l = 0` both sides vanish
because the scalar factor `(α l : ℝ)` is `0`.  Hence `ann m l ∘ cre m l = cre m l ∘ ann m l + 1`.
For `l ≠ l'` the two shifts move different coordinates and therefore commute exactly,
`ann m l ∘ cre m l' = cre m l' ∘ ann m l` (note `(α + e l') - e l = (α - e l) + e l'`).

Since a linear map out of the free module `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` is determined
by its values on the basis vectors `Finsupp.single α b` (`Finsupp.lhom_ext`), the two
cases combine into the operator identity `[a_l, a_{l'}^†] = δ_{ll'}`.
-/

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. The two operators on a basis vector -/

/-- `ann m l` on a basis vector: it lowers the `l`-th occupation and multiplies by it. -/
private lemma ccr_ann_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (b : ℝ) :
    ann m l (Finsupp.single α b) = Finsupp.single (α - e m l) ((α l : ℝ) * b) := by
  simp only [ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single,
    smul_eq_mul, one_mul, mul_comm]

/-- `cre m l` on a basis vector: it raises the `l`-th occupation. -/
private lemma ccr_cre_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (b : ℝ) :
    cre m l (Finsupp.single α b) = Finsupp.single (α + e m l) b := by
  simp only [cre, Finsupp.lsum_single, Finsupp.lsingle_apply]

/-! ## 2. Index identities for the shifts `α ↦ α ± e m l` -/

/-- `(α + e_l) - e_l = α`: raising then lowering the `l`-th occupation is the identity. -/
private lemma ccr_add_e_sub_e_self {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    (α + e m l) - e m l = α := by
  ext i
  by_cases hi : i = l <;> simp [e, hi]

/-- `(α - e_l) + e_l = α` whenever `α l ≠ 0`.  (For `α l = 0` the identity is false, but
then the scalar factor `(α l : ℝ)` kills the term.) -/
private lemma ccr_sub_e_add_e_self {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (h : α l ≠ 0) :
    (α - e m l) + e m l = α := by
  ext i
  by_cases hi : i = l
  · subst hi
    simp [Finsupp.add_apply, e]
    omega
  · simp [Finsupp.add_apply, e, hi]

/-- For `l ≠ l'` the shifts along `e_l` and `e_{l'}` move different coordinates. -/
private lemma ccr_add_e_sub_e_ne {m : ℕ} (l l' : Fin m) (h : l ≠ l') (α : Fin m →₀ ℕ) :
    (α + e m l') - e m l = (α - e m l) + e m l' := by
  ext i
  by_cases hil : i = l
  · subst hil
    simp [Finsupp.add_apply, e, h]
  · by_cases hil' : i = l'
    · subst hil'
      simp [Finsupp.add_apply, e, hil]
    · simp [Finsupp.add_apply, e, hil, hil']

/-- Evaluation of a raised multi-index at its own raising coordinate. -/
private lemma ccr_add_e_apply_self {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    (α + e m l) l = α l + 1 := by
  simp [Finsupp.add_apply, e]

/-- Evaluation of a raised multi-index at a different coordinate. -/
private lemma ccr_add_e_apply_ne {m : ℕ} (l l' : Fin m) (h : l ≠ l') (α : Fin m →₀ ℕ) :
    (α + e m l') l = α l := by
  simp [Finsupp.add_apply, e, h]

/-! ## 3. The commutation relation -/

theorem Ann_cre_ccr {m : ℕ} (l l' : Fin m) :
    (Work.BoseB4.ann m l).comp (Work.BoseB4.cre m l')
      = (Work.BoseB4.cre m l').comp (Work.BoseB4.ann m l)
        + ((if l = l' then (1:ℝ) else 0) • (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)) := by
  refine Finsupp.lhom_ext fun α b => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, Finsupp.smul_single]
  rw [ccr_cre_single, ccr_ann_single, ccr_ann_single, ccr_cre_single]
  by_cases h : l = l'
  · subst h
    rw [if_pos rfl, ccr_add_e_sub_e_self, ccr_add_e_apply_self, one_smul]
    by_cases hα : α l = 0
    · rw [hα]
      simp
    · rw [ccr_sub_e_add_e_self l α hα, ← Finsupp.single_add]
      congr 1
      push_cast
      ring
  · rw [if_neg h, ccr_add_e_sub_e_ne l l' h, ccr_add_e_apply_ne l l' h]
    rw [zero_smul, Finsupp.single_zero, add_zero]

end Work.BoseB4
