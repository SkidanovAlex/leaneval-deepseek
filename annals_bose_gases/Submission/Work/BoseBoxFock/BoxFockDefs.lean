import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
import Submission.Work.BoseBoxFock.slotCountsComplex
import Submission.Work.BoseDict.boxRealise_dGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.BoxFockDefs` — the vocabulary of the condensate row

The box ↔ model dictionary row `bomb m Ψ (n₀ Ψ) = cS1 ℓ (boxRealise e d Ψ)` (BF3b, row 1 of
`BF3B_PLAN_S6.md` §4) is the statement that the model's condensate number operator `n₀ = a₀†a₀`
— i.e. the second quantisation of the rank-one one-particle projection onto the coordinate
`0 : Fin m`, whose one-particle vector is FS's `θ = e 0` (pinned by `hc`: `e 0 = c·θ`) — is the
box's condensate count `S₁ = Σ_j ‖P_jΘ‖²`.

This module carries the two names of the row:

* `proj0 m` — the rank-one one-particle projection `v ↦ v 0 • evec 0`, so that
  `n₀ = dGamma m (proj0 m)` (`n0_apply_eq_dGamma`), which is how the dictionary
  (`Work.BoseDict.bomb_dGamma_slot`) sees `n₀`;
* `uSlot u j Θ` — the `j`-th slot of the rank-one slot operator with kernel `u(x_j)·conj(u z)`,
  i.e. exactly `Work.BoseDict.boxSlotOf e (evec 0) (evec 0) j` for `u = e 0`
  (`boxSlotOf_evec0_eq_uSlot`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The rank-one one-particle projection onto the condensate coordinate `0 : Fin m`:
`proj0 m v = v 0 • evec 0`. -/
noncomputable def proj0 (m : ℕ) [NeZero m] : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun := fun v => v 0 • Work.BoseB4.evec m 0
  map_add' := by intro a b; simp [add_smul]
  map_smul' := by intro c v; simp [mul_smul]

/-- The `j`-th slot of the rank-one slot operator of the one-particle vector `u`, i.e. the
first-quantised rank-one operator `|u⟩⟨u|` acting in the `j`-th slot:
`(uSlot u j Θ) x = u (x j) · ∫_z conj (u z) · Θ (x[j ↦ z])`. -/
noncomputable def uSlot {d : ℕ} (u : Work.BoseDict.Sp → ℂ) (j : Fin d)
    (Θ : Work.BoseDict.Xn d → ℂ) : Work.BoseDict.Xn d → ℂ :=
  fun x => u (x j) * ∫ z : Work.BoseDict.Sp,
    (starRingEnd ℂ) (u z) * Θ (Function.update x j z)

/-! ## The model side: `n₀ = dΓ(proj0)` -/

/-- The matrix elements of `proj0` in the coordinate basis. -/
theorem proj0_evec (m : ℕ) [NeZero m] (i j : Fin m) :
    proj0 m (Work.BoseB4.evec m j) i = if i = 0 ∧ j = 0 then 1 else 0 := by
  have h1 : (Work.BoseB4.evec m j) 0 = if j = 0 then 1 else 0 := by
    rw [Work.BoseB4.evec]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg hj, Pi.single_eq_of_ne (Ne.symm hj)]
  have h2 : (Work.BoseB4.evec m 0) i = if i = 0 then 1 else 0 := by
    rw [Work.BoseB4.evec]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg hi, Pi.single_eq_of_ne hi]
  rw [show proj0 m (Work.BoseB4.evec m j)
        = (Work.BoseB4.evec m j) 0 • Work.BoseB4.evec m 0 from rfl]
  simp only [Pi.smul_apply]
  rw [h1, h2, smul_eq_mul]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

/-- **The condensate number operator is the second quantisation of `proj0`.** -/
theorem n0_apply_eq_dGamma (m : ℕ) [NeZero m] (Ψ : Work.BoseB4.RealFock m) :
    n0 (m := m) Ψ = Work.BoseB4.dGamma m (proj0 m) Ψ := by
  unfold Work.BoseBoxFock.n0 Work.BoseB4.dGamma
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    proj0_evec]
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [Finset.sum_eq_single (0 : Fin m)]
    · simp
    · intro j _ hj
      rw [if_neg (fun h : (0 : Fin m) = 0 ∧ j = 0 => hj h.2), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg (fun h : i = 0 ∧ j = 0 => hi h.1), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The box side: the slot operators of the dictionary are `uSlot`'s -/

/-- The dictionary's slot operator at the coordinate vector `evec 0` is `uSlot (e 0)`. -/
theorem boxSlotOf_evec0_eq_uSlot {m d : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ)
    (j : Fin d) (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m 0) (Work.BoseB4.evec m 0) j Θ
      = uSlot (e 0) j Θ := by
  funext x
  simp only [Work.BoseDict.boxSlotOf, uSlot, Work.BoseB4.evec, Work.BoseDict.etaOf_pi_single]

/-- **The box image of `n₀ Ψ` is the sum of the slot projections onto `e 0`.** -/
theorem boxSlotSum_proj0 {m d : ℕ} [NeZero m] (e : Fin m → Work.BoseDict.Sp → ℂ)
    (Θ : Work.BoseDict.Xn d → ℂ) :
    Work.BoseDict.boxSlotSum e (proj0 m) Θ
      = fun x => ∑ j : Fin d, uSlot (e 0) j Θ x := by
  funext x
  simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, proj0_evec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (0 : Fin m)]
  · rw [Finset.sum_eq_single (0 : Fin m)]
    · rw [if_pos (And.intro rfl rfl), one_smul]
      exact congrFun (boxSlotOf_evec0_eq_uSlot e j Θ) x
    · intro l' _ hl'
      have hcond : ¬ ((0 : Fin m) = 0 ∧ l' = 0) := fun h => hl' h.2
      rw [if_neg hcond]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    refine Finset.sum_eq_zero (fun l' _ => ?_)
    have hcond : ¬ (l = 0 ∧ l' = 0) := fun h => hl h.1
    rw [if_neg hcond]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The box indicator in the `uSlot` vocabulary -/

/-- `thetaFun ℓ` is the indicator of the cube `acube ℓ`. -/
theorem thetaFun_eq_indicator {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Submission.BoseGases.acube ℓ) (fun _ => (1 : ℂ)) := by
  funext x
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  have hmem : x ∈ Work.BoseK15.corpusBox.boxL ℓ ↔ x ∈ Submission.BoseGases.acube ℓ := by
    rw [Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ]
  by_cases hx : x ∈ Submission.BoseGases.acube ℓ
  · rw [Set.indicator_of_mem hx, if_pos (hmem.mpr hx)]
  · rw [Set.indicator_of_notMem hx, if_neg (fun h => hx (hmem.mp h))]

end Work.BoseBoxFock
