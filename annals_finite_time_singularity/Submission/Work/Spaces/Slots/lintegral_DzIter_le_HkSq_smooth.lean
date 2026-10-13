/-
Copyright: work module for the Elgindi finite-time singularity project.

# The ENNReal `D_z`-slot estimate **with the smoothness hypothesis**

`Work.Spaces.Slots.lintegral_DzIter_le_HkSq` asks for

  `∫⁻_θ ∫⁻_s ofReal (D_z^i f(s,θ)² w(s)²) ≤ ofReal (HkSq α 4 f)`

under `HkMem α 4 f` alone.  Identifying the swapped iterated `∫⁻` with `ofReal (HkSq α 4 f)`
requires Tonelli's theorem for the uncurried integrand
`(s,θ) ↦ ofReal (D_z^i f(s,θ)² w(s)²)`, i.e. its a.e. strong measurability for the product
of the two restricted measures.  `HkMem α 4 f` supplies only the measurability of the
*angular* slices `θ ↦ HkIntegrand α 4 f z θ` (for each `z ∈ Iz`) together with the
integrability of the *partially integrated* function `z ↦ ∫_θ HkIntegrand α 4 f z θ`; it
says nothing about the `s`-slices, and no proof of the corresponding "one-sided Tonelli"
statement exists (that statement is false in general).

This file therefore proves the statement in the form in which it is *used* in this
development, namely with the standing smoothness hypothesis `SmoothNbhd f` — the same
hypothesis carried by every other place where these two integrations are exchanged
(`Work.Spaces.HkSqSwap`, `Work.Spaces.HardyZLin.hardyZ_lintegral`, `Work.Elliptic.L12Aux`,
`Work.Coercivity.CommutZ_HkIntegrand_prod`, …).  Under it the uncurried
`(s,θ) ↦ D_z^i f(s,θ)² w(s)²` is continuous on the open quadrant (hence a.e. strongly
measurable for the product measure), and the proof is:

* Tonelli swaps the two `∫⁻`: the left-hand side is `∫⁻_s ∫⁻_θ ofReal (D_z^i f² w²)`;
* for every `s ∈ Iz` the angular slice is continuous on `Iθ`, so
  `∫⁻_θ ofReal (D_z^i f(s,θ)² w(s)²) = ofReal (∫_θ D_z^i f(s,θ)² w(s)²)`;
* pointwise on the *open* interval `(0,π/2)` (the two endpoints are null)
  `D_z^i f² w² ≤ (D_z^i f · w / sin(2θ)^{η/2})² ≤ HkIntegrand α 4 f`, because
  `sin(2θ)^{-η} ≥ 1`; integrating in `θ` gives the slicewise comparison;
* `∫⁻_s ofReal (∫_θ HkIntegrand α 4 f s θ) = ofReal (HkSq α 4 f)` by `HkMem` and
  `ofReal_integral_eq_lintegral_ofReal`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.Spaces.Slots

set_option autoImplicit false

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem Qd_subset_nbhU : Qd ⊆ Work.Spaces.nbhU := by
  intro p hp
  obtain ⟨hz, hθ⟩ := hp
  rw [Set.mem_Ioi] at hz
  rw [Set.mem_Ioo] at hθ
  simp only [Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith, by linarith, by linarith [Real.pi_pos]⟩

theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1) (π / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- A point of `nbhU` in the open quadrant, with the angular component in `Iθ`. -/
theorem mem_nbhU_of_pos {s θ : ℝ} (hs : 0 < s) (hθ : θ ∈ Set.Ioo (-1) (π / 2 + 1)) :
    (s, θ) ∈ Work.Spaces.nbhU := by
  simp only [Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi]
  exact ⟨by linarith, hθ⟩

/-- A.e. statement for the restricted measure on `Iθ`: it suffices to prove the statement on
the open interval, where the angular weight `sin(2θ)` does not vanish. -/
theorem ae_restrict_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => h θ hθ.1 hθ.2)

/-- `sin(2θ)^{-η} ≥ 1` for `θ` in the open interval. -/
theorem one_le_sin_two_rpow_neg_eta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have := Real.rpow_le_rpow_of_nonpos hsin hle
    (by linarith [Work.Spaces.eta_pos] : -(Work.Spaces.eta) ≤ 0)
  rwa [Real.one_rpow] at this

/-- **ENNReal form of the `D_z`-slot estimate, with the standing smoothness hypothesis.**
For `f` smooth on a neighbourhood of the closed quadrant with `HkMem α 4 f` and `i ≤ 4`, the
iterated ENNReal integral `∫⁻_θ ∫⁻_s ofReal (D_z^i f(s,θ)² w(s)²)` over the closed quadrant
(with respect to `dθ dz`) is bounded by `ofReal (HkSq α 4 f)`. -/
theorem lintegral_DzIter_le_HkSq_of_smooth (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd f) (hmem : Work.Spaces.HkMem α 4 f)
    (i : ℕ) (hi : i ≤ 4) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
        MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
          ENNReal.ofReal ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := by
  -- Continuity of the two factors on the open quadrant.
  have hcontD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
    ((Work.Spaces.SmoothNbhd.DzIter hsm i).continuousOn).mono Qd_subset_nbhU
  have hcontw : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Qd := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
      simp only [Work.Spaces.w]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt hp.1)
    exact h1.pow 2
  have hcontQ : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2) Qd :=
    (hcontD.pow 2).mul hcontw
  have hcontQ' : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [Qd] using hcontQ
  -- Joint a.e. strong measurability of the uncurried integrand, and of its `ofReal`.
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcontQ'
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      ((Work.Spaces.DzIter i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    haesm.aemeasurable.ennreal_ofReal
  -- Angular slices are continuous, hence integrable.
  have hslice_int : ∀ s ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        Work.Spaces.Iθ := by
    intro s hs
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | h0
    · rw [← h0]
      have hzero : (fun θ => (Work.Spaces.DzIter i f 0 θ) ^ 2 * (Work.Spaces.w 0) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.w]
      rw [hzero]
      exact integrableOn_zero
    · have hnb : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter i f))
          Work.Spaces.nbhU := Work.Spaces.SmoothNbhd.DzIter hsm i
      have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter i f s θ)
          Work.Spaces.Iθ := by
        have h2 : ContDiffOn ℝ ⊤ (fun θ : ℝ => (s, θ)) (Set.Ioo (-1) (π / 2 + 1)) :=
          contDiffOn_const.prodMk contDiffOn_id
        have h3 : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.DzIter i f s θ)
            (Set.Ioo (-1) (π / 2 + 1)) := by
          have h4 := hnb.comp h2 (fun θ hθ => mem_nbhU_of_pos h0 hθ)
          have hfun : (Function.uncurry (Work.Spaces.DzIter i f) ∘ fun θ : ℝ => (s, θ))
              = fun θ => Work.Spaces.DzIter i f s θ := rfl
          rwa [hfun] at h4
        exact h3.continuousOn.mono Iθ_subset_Ioo
      exact ((hslice.pow 2).mul continuousOn_const).integrableOn_Icc
  -- Pointwise domination on the open interval.
  have hpt : ∀ s θ : ℝ, 0 < θ → θ < π / 2 →
      (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 f s θ := by
    intro s θ h0 h1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      one_le_sin_two_rpow_neg_eta h0 h1
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ i hi
    have heq : (Work.Spaces.DzIter i f s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
      have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
        norm_num
      rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
      ring
    calc (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
        = (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hone (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.DzIter i f s θ
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
      _ ≤ Work.Spaces.HkIntegrand α 4 f s θ := hkey
  -- Slicewise comparison of the two angular integrals.
  have hslide_le : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs =>
      integral_mono_ae (hslice_int s hs) (hmem.1 s hs)
        (ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => hpt s θ h0 h1)))
  -- The single-slice `ofReal` bridge.
  have hbridge : ∀ s ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
    intro s hs
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice_int s hs)
      (Filter.Eventually.of_forall
        fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  -- The marginal bridge, with `HkSq`.
  have hfinal : (∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := by
    rw [Work.Spaces.HkSq]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Filter.Eventually.of_forall fun s =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f s θ)).symm
  -- Assembly.
  have hswap : (∫⁻ s in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
          ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
    let Gp : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
      ((Work.Spaces.DzIter i f p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
    have hGp : AEMeasurable Gp
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := hmeas
    calc (∫⁻ s in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2))
        = ∫⁻ p : ℝ × ℝ, Gp p
            ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
          (MeasureTheory.lintegral_prod Gp hGp).symm
      _ = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
            ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) :=
          MeasureTheory.lintegral_prod_symm Gp hGp
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ) (fun θ =>
          MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz) (fun s =>
            ENNReal.ofReal ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)))
      = ∫⁻ s in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := hswap.symm
    _ = ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) := by
        refine lintegral_congr_ae ?_
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
          (fun s hs => hbridge s hs)
    _ ≤ ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ) :=
        lintegral_mono_ae (hslide_le.mono fun s hs => ENNReal.ofReal_le_ofReal hs)
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 4 f) := hfinal

end Work.Spaces.Slots
