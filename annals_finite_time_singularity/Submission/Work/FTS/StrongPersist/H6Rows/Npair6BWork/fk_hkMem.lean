/-
# `Npair6BWork/fk_hkMem` — the angular moment `FK f` is in `ℋ⁶`

The angular moment `FK f z = ∫_θ K(θ)·f(z,θ) dθ` is the radial function `Qang f 0`.  For a
datum `f` which is `C^∞` on the open quadrant and lies in `ℋ⁶`, the radial function
`z ↦ FK f z` also lies in `ℋ⁶`.  This is the membership half of the (`α`-free)
`Work.FTS.StrongPersist.N6_fkH`; unlike the latter it needs no zero-mode hypothesis and no
`α`-range restriction.

The argument is verbatim the one of `N6_fkH_of`: a function of `z` alone has no angular
derivatives, so only the pure `D_z`-summands of `HkIntegrand α 6 (fun z _ => FK f z)`
survive (`Work.FTS.H2.HkIntegrand_rad'`), and each of them is the angular moment
`D_z^i (FK f) = Qang f i` almost everywhere (`QangAe6`).  The weighted `L²`-bound
`∫_z (Qang f i z)² w² ≤ (∫_θ Kθ²)·|f|²_{ℋ⁶}` for `i ≤ 6` is `QangSq6Full`, which gives
the integrability of every `z`-slot and hence of the whole sum.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.QangAe6
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem fk_hkMem : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 6 (fun z _ => Work.Construction.FK f z) := by
  intro α _ f hsm hmem
  -- the angular moment is the radial function `u := Qang f 0`
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang f 0 z with hudef
  -- ## the a.e. identity `D_z^i (Qang f 0) = Qang f i` on `Iz`, `i ≤ 6`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang f i z := by
    filter_upwards [QangAe6 hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 7))]
  -- ## the per-slot integrability
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (QangSq6Full (α := α) hsm hmem i hi).1.congr (htransfer i hi)
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the angular weight is integrable
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  -- ## membership in `ℋ⁶`
  have hHkMem : Work.Spaces.HkMem α 6 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 7, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 7) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun
          (f := fun θ => Work.Spaces.HkIntegrand α 6 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 7,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 6 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## `FK f` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK f z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun]
  exact hHkMem

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
