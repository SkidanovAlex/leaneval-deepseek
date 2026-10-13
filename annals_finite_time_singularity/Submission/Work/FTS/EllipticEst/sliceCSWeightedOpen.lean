/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted Cauchy–Schwarz step, with continuity only on the *open* slice

`sliceCSWeightedOpen` is `Work.FTS.EllipticEst.slice_cs_weighted` with the hypothesis
`ContinuousOn g Iθ` weakened to `ContinuousOn g (Ioo 0 (π/2))`.  The proof of the closed
version uses continuity of `g` only on the open interval (where `sin (2·) > 0` makes the
weight `sin(2θ)^{-η/2}` continuous), so the same proof adapts verbatim: the single
occurrence of `(hg.mono hsub)` becomes `hg`.  The weight of the statement,
`Work.FTS.EllipticEst.sEta`, is the same function as `Work.FTS.EllipticEst.thEta` used by
the closed version (`sEta θ = thEta θ = sin(2θ)^{-η}` by definitional unfolding).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.slice_cs_weighted
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_of_pos_open (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

theorem sliceCSWeightedOpen {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |g θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  -- ## Step 0: the two endpoints form a null set, hence the integral over `Iθ = [0, π/2]`
  -- equals the integral over the open interval `Ioo 0 (π/2)`, where `sin (2·) > 0`.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ (x : ℝ), x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
        lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  rw [hms]
  -- ## Step 1: Cauchy–Schwarz over `Ioo 0 (π/2)`.
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hIoomeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hη : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) :=
    fun θ hθ => sin_two_pos hθ
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hvcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inr (by rw [Work.Spaces.eta]; norm_num))
  -- the only difference from the closed version: `hg` is already on the open interval
  have hucont : ContinuousOn
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hg.abs.mul hwcont
  have huaesm : AEStronglyMeasurable
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hucont.aestronglyMeasurable hIoomeas
  have hvaesm : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hvcont.aestronglyMeasurable hIoomeas
  -- the two squares are exactly the two weights of the statement
  have hEq1 : Set.EqOn (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hx : 0 < Real.sin (2 * θ) := hsinpos θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
    rw [mul_pow, sq_abs, rpow_sq_of_pos_open _ _ hx,
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have hEq2 : Set.EqOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
    rw [rpow_sq_of_pos_open _ _ (hsinpos θ hθ),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  have hu2int : MeasureTheory.Integrable
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hint.mono_set hsub).congr_fun hEq1 hIoomeas
  have hv2int : MeasureTheory.Integrable
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((integrableOn_sin_two_rpow hη).1.mono_set hsub).congr_fun hEq2 hIoomeas
  have humem : MeasureTheory.MemLp
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr hu2int
  have hvmems : MeasureTheory.MemLp
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvaesm).mpr hv2int
  have hcs := Work.Spaces.cs_integral humem hvmems
  -- ## Step 2: identify the three integrals of the Cauchy–Schwarz inequality
  have e1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
          * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |g x| := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
        * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2) = |g x|
    rw [mul_assoc, ← Real.rpow_add hx',
      show -(Work.Spaces.eta / 2) + Work.Spaces.eta / 2 = 0 by ring, Real.rpow_zero,
      mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (g x) ^ 2 * Work.FTS.EllipticEst.sEta x := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (g x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    rw [mul_pow, sq_abs, rpow_sq_of_pos_open _ _ hx',
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sin (2 * x)) ^ (Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    show ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    rw [rpow_sq_of_pos_open _ _ (hsinpos x hx),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  rw [e1, e2, e3] at hcs
  exact hcs

end Work.FTS.EllipticEst
