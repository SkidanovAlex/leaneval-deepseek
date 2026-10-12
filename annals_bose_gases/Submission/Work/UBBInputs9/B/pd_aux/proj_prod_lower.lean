import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.B.pd_aux.boxMean_abs_le
import Submission.Work.UBBInputs9.B.pd_aux.integrable_boxMean_sq_kinIntD
import Submission.Work.UBBInputs9.B.pd_aux.integrable_kinInt
import Submission.Work.UBBInputs9.B.pd_aux.proj_int
import Submission.Work.UBBInputs9.B.pd_aux.proj_meas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.proj_prod_lower`

The projection-defect inequality for the sliding kinetic localisation: for the plateau witness
`kwPhi ℓ cc` (`2/ℓ < cc`) and `0 < δ < 1`,

    `(1-δ)·∫ kinInt - ((1-δ)/δ)·∫ boxMean²·kinIntD ≤ ∫ kinIntPrj`

against the product measure `pdMu ℓ = volume_u ⊗ (volume_x ↾ abox 1 ℓ)`.

The pointwise content (the completion of squares `χ_BΦ = χ_B(Φ-c_u) + c_uχ_B`) is in
`pd_aux/proj_decomp`; here it is integrated.  The `L¹`-inputs are
`integrable_kinInt` (the sliding Dirichlet square is `L¹`), `integrable_kinIntD` (the
window-derivative square is `L¹`), `boxMean_abs_le`/`aemeasurable_boxMean_aux` (the box mean is
bounded and measurable) and `integrable_kinIntPrj_aux` below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `kinIntPrj` is a sum of squares, hence nonnegative. -/
lemma kinIntPrj_nonneg (ℓ d : ℝ) (Φ : X1 → ℝ) (u : ℝ³) (x : X1) :
    0 ≤ kinIntPrj ℓ d Φ u x := by
  unfold kinIntPrj
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- Almost every point of `pdMu ℓ` has its second coordinate in `abox 1 ℓ`. -/
lemma ae_mem_abox_pdMu (ℓ : ℝ) :
    ∀ᵐ p ∂(pdMu ℓ), p.2 ∈ abox 1 ℓ := by
  have hs : MeasurableSet (abox 1 ℓ) := abox_measurable 1 ℓ
  have h1 : ∀ᵐ x ∂((volume : Measure X1).restrict (abox 1 ℓ)), x ∈ abox 1 ℓ :=
    ae_restrict_mem hs
  exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
    (ν := (volume : Measure X1).restrict (abox 1 ℓ))).ae h1

/-- The projected Dirichlet integrand is a.e. strongly measurable: the Leibniz decomposition
`proj_decomp.kinIntPrj_eq` exhibits it as a sum of squares of continuous functions of `(u,x)`
and the box mean, which is `AEMeasurable` in `u`. -/
lemma aestronglyMeasurable_kinIntPrj {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    AEStronglyMeasurable (fun p : ℝ³ × X1 => kinIntPrj ℓ d Φ p.1 p.2) (pdMu ℓ) := by
  have hcm : AEMeasurable (fun p : ℝ³ × X1 => boxMean ℓ d p.1 Φ) (pdMu ℓ) :=
    (aemeasurable_boxMean_aux hℓ hd hΦ.continuous).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure X1).restrict (abox 1 ℓ)))
  have hterm : ∀ k : Fin 3, AEMeasurable (fun p : ℝ³ × X1 =>
      chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) (pdMu ℓ) := by
    intro k
    exact ((continuous_chiBLc hℓ hd Φ hΦ k).aemeasurable).sub
      (hcm.mul (continuous_chiBLb hℓ hd k).aemeasurable)
  have hterm2 : ∀ k : Fin 3, AEMeasurable (fun p : ℝ³ × X1 =>
      (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2) (pdMu ℓ) := by
    intro k
    exact (hterm k).pow measurable_const.aemeasurable
  have hsum : AEMeasurable (fun p : ℝ³ × X1 => ∑ k : Fin 3,
      (chiBLc ℓ d Φ k p - boxMean ℓ d p.1 Φ * chiBLb ℓ d k p) ^ 2) (pdMu ℓ) := by
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun k _ => hterm2 k)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp [Finset.sum_apply]
  exact (hsum.congr (Filter.Eventually.of_forall (fun p => by
    obtain ⟨u, x⟩ := p
    exact (kinIntPrj_eq hℓ hd u hΦ x).symm))).aestronglyMeasurable

/-- The projected (mean-free) sliding Dirichlet integrand is `L¹` for `pdMu ℓ`. -/
theorem integrable_kinIntPrj_aux {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) :
    Integrable (fun p : ℝ³ × X1 => kinIntPrj ℓ d Φ p.1 p.2) (pdMu ℓ) := by
  obtain ⟨M, hMb⟩ := hcs.exists_bound_of_continuous hΦ.continuous
  have hM : ∀ u : ℝ³, |boxMean ℓ d u Φ| ≤ M :=
    boxMean_abs_le hℓ hd hΦ.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hMb x)
  have hIk : Integrable (fun p : ℝ³ × X1 => kinInt ℓ d Φ p.1 p.2) (pdMu ℓ) :=
    integrable_kinInt hℓ hd hΦ hcs
  have hId : Integrable (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2) (pdMu ℓ) :=
    integrable_kinIntD_aux hℓ hd
  have hdom : Integrable (fun p : ℝ³ × X1 =>
      2 * kinInt ℓ d Φ p.1 p.2 + 2 * M ^ 2 * kinIntD ℓ d p.1 p.2) (pdMu ℓ) :=
    (hIk.const_mul 2).add (hId.const_mul (2 * M ^ 2))
  refine hdom.mono' (aestronglyMeasurable_kinIntPrj hℓ hd hΦ) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (kinIntPrj_nonneg ℓ d Φ p.1 p.2)]
  exact kinIntPrj_le_bound hℓ hd hΦ hM p.1 p.2

theorem proj_prod_lower {ℓ d cc δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hcc : 2 / ℓ < cc)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) * (∫ p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1,
          Work.UBBInputs9.B.kinInt ℓ d (Work.SmallBoxA0.kwPhi ℓ cc) p.1 p.2
            ∂(Work.UBBInputs9.B.pdMu ℓ))
      - ((1 - δ) / δ) * (∫ p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1,
          (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
            Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2
            ∂(Work.UBBInputs9.B.pdMu ℓ))
      ≤ ∫ p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1,
          Work.UBBInputs9.B.kinIntPrj ℓ d (Work.SmallBoxA0.kwPhi ℓ cc) p.1 p.2
            ∂(Work.UBBInputs9.B.pdMu ℓ) := by
  set Φ : X1 → ℝ := Work.SmallBoxA0.kwPhi ℓ cc with hΦdef
  obtain ⟨hΦcd, hΦsupp, hΦvan, hΦlam, hΦL2, hΦkin⟩ := Work.SmallBoxA0.kwPhi_props hℓ hcc
  have hcs : HasCompactSupport Φ :=
    HasCompactSupport.of_support_subset_isCompact (Work.UBBInputs9.B.abox_isCompact 1 ℓ)
      (fun x hx => hΦsupp (subset_closure hx))
  obtain ⟨M, hMb⟩ := hcs.exists_bound_of_continuous hΦcd.continuous
  have hM : ∀ u : ℝ³, |boxMean ℓ d u Φ| ≤ M :=
    boxMean_abs_le hℓ hd hΦcd.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hMb x)
  have hEm : AEMeasurable (fun u : ℝ³ => boxMean ℓ d u Φ) (volume : Measure ℝ³) :=
    aemeasurable_boxMean_aux hℓ hd hΦcd.continuous
  have hIk : Integrable (fun p : ℝ³ × X1 => kinInt ℓ d Φ p.1 p.2) (pdMu ℓ) :=
    integrable_kinInt hℓ hd hΦcd hcs
  have hId : Integrable (fun p : ℝ³ × X1 => kinIntD ℓ d p.1 p.2) (pdMu ℓ) :=
    integrable_kinIntD_aux hℓ hd
  have hIc : Integrable (fun p : ℝ³ × X1 =>
      (boxMean ℓ d p.1 Φ) ^ 2 * kinIntD ℓ d p.1 p.2) (pdMu ℓ) :=
    integrable_boxMean_sq_kinIntD hℓ hd hEm hM hId
  have hIp : Integrable (fun p : ℝ³ × X1 => kinIntPrj ℓ d Φ p.1 p.2) (pdMu ℓ) :=
    integrable_kinIntPrj_aux hℓ hd hΦcd hcs
  have hFint : Integrable (fun p : ℝ³ × X1 =>
      (1 - δ) * kinInt ℓ d Φ p.1 p.2
        - ((1 - δ) / δ) * ((boxMean ℓ d p.1 Φ) ^ 2 * kinIntD ℓ d p.1 p.2)) (pdMu ℓ) :=
    (hIk.const_mul (1 - δ)).sub (hIc.const_mul ((1 - δ) / δ))
  have hpt : ∀ p : ℝ³ × X1,
      (1 - δ) * kinInt ℓ d Φ p.1 p.2
        - ((1 - δ) / δ) * ((boxMean ℓ d p.1 Φ) ^ 2 * kinIntD ℓ d p.1 p.2)
      ≤ kinIntPrj ℓ d Φ p.1 p.2 :=
    fun p => proj_le_pointwise hℓ hd hδ hδ1 hΦcd p.1 p.2
  have hmono := integral_mono_ae hFint hIp (Filter.Eventually.of_forall hpt)
  have hlin : (∫ p : ℝ³ × X1,
        ((1 - δ) * kinInt ℓ d Φ p.1 p.2
          - ((1 - δ) / δ) * ((boxMean ℓ d p.1 Φ) ^ 2 * kinIntD ℓ d p.1 p.2)) ∂(pdMu ℓ))
      = (1 - δ) * (∫ p : ℝ³ × X1, kinInt ℓ d Φ p.1 p.2 ∂(pdMu ℓ))
        - ((1 - δ) / δ) * (∫ p : ℝ³ × X1,
            (boxMean ℓ d p.1 Φ) ^ 2 * kinIntD ℓ d p.1 p.2 ∂(pdMu ℓ)) := by
    rw [integral_sub (hIk.const_mul (1 - δ)) (hIc.const_mul ((1 - δ) / δ)),
      integral_const_mul, integral_const_mul]
  rw [hlin] at hmono
  exact hmono

end Work.UBBInputs9.B.pd_aux
