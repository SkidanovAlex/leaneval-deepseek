import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseFixB2.DvApriori.integrable_uncurry_of_radial_bound
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
import Submission.Work.hlocWire.tBdiagFormInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.wSwapPBoxTBamp`

The weighted `p ↔ abox` Fubini exchange for the windowed amplitude of the mean-free
box state `Q_{B,i}Ψ`, with a radial weight `F(‖p‖)` of at most quadratic growth:

    `∫_p F(‖p‖)·∫_{abox N s}‖tBamp χ p (Q_{B,i}Ψ) i x‖²`
    = `∫_{abox N s}∫_p F(‖p‖)·‖tBamp χ p (Q_{B,i}Ψ) i x‖²`,

together with the joint integrability of the two-variable integrand.

This is the `F`-weighted companion of `Work.hlocWire2.swap_p_abox_tBamp_one` (which is the
`F ≡ 1` case, but with the `(2π)⁻³` prefactor kept).  The content is the same:
`Q_{B,i}Ψ` is smooth because `A` is compact (`boxQ_contDiff_of_compact`), so the uniform
Fourier decay `‖tBamp χ p Φ i x‖ ≤ C(1+‖p‖)⁻³` (`tBamp_decay`) holds on the ambient box;
multiplying by `|F(‖p‖)| ≤ K(1+‖p‖)²` leaves the radial majorant `K C²/(1+‖p‖)⁴`, which is
integrable in dimension three.  Joint integrability then follows from
`integrable_uncurry_of_radial_bound`, and the exchange itself is `integral_integral_swap`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "ℝ3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem wSwapPBoxTBamp {N : ℕ} {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : IsCompact A) {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχcd : ContDiff ℝ (⊤ : ENat) χ)
    (hχcs : HasCompactSupport χ)
    {F : ℝ → ℝ} (hFm : Measurable F) {K : ℝ} (hK : 0 ≤ K)
    (hFb : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨcd : ContDiff ℝ (⊤ : ENat) Ψ) (i : Fin N) :
    MeasureTheory.Integrable
        (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
          F ‖q.1‖ *
            ‖Work.SmallBoxTBWord.tBamp χ q.1 (Work.SmallBoxTBWord.boxQ volA A i Ψ) i q.2‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N s)))
    ∧ (∫ p : EuclideanSpace ℝ (Fin 3), ∫ x in Submission.BoseGases.abox N s,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox N s, ∫ p : EuclideanSpace ℝ (Fin 3),
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2 := by
  classical
  -- the mean-free projection of a smooth state is smooth
  set Ψq : Submission.BoseGases.X N → ℝ := Work.SmallBoxTBWord.boxQ volA A i Ψ with hΨq
  have hΨqcd : ContDiff ℝ (⊤ : ENat) Ψq := by
    rw [hΨq]
    exact Work.SmallBoxTBWord.boxQ_contDiff_of_compact hAc volA i hΨcd
  -- uniform Fourier decay of the amplitude on the ambient box
  obtain ⟨C, hC0, hC⟩ := Work.SmallBoxTBWord.tBamp_decay (N := N) hs hχcd hχcs hΨqcd
  -- the integrand, as a curried kernel
  set f : ℝ3 → Submission.BoseGases.X N → ℝ := fun p x =>
    F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2 with hf
  have huncurry : Function.uncurry f = fun q : ℝ3 × Submission.BoseGases.X N =>
      F ‖q.1‖ * ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψq i q.2‖ ^ 2 := by
    funext q
    rw [hf]
    rfl
  -- ## the pointwise bound: the quadratic growth of `F` times the `(1+‖p‖)⁻³` decay
  have hpointwise : ∀ x ∈ Submission.BoseGases.abox N s, ∀ p : ℝ3,
      ‖f p x‖ ≤ K * C ^ 2 / (1 + ‖p‖) ^ 4 := by
    intro x hx p
    have hb : ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ≤ C / (1 + ‖p‖) ^ 3 := hC x hx i p
    have hb2 : ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hFp : |F ‖p‖| ≤ K * (1 + ‖p‖) ^ 2 := hFb ‖p‖ (norm_nonneg p)
    have hnn : (0 : ℝ) ≤ ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2 := sq_nonneg _
    have hkey : f p x = F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2 := by rw [hf]
    rw [hkey, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc |F ‖p‖| * ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2
        ≤ (K * (1 + ‖p‖) ^ 2) * (C / (1 + ‖p‖) ^ 3) ^ 2 :=
          mul_le_mul hFp hb2 (sq_nonneg _) (mul_nonneg hK (by positivity))
      _ = K * C ^ 2 / (1 + ‖p‖) ^ 4 := by
          have h1 : (0 : ℝ) < 1 + ‖p‖ := by positivity
          field_simp
  -- ## joint measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ3)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N s))) := by
    rw [huncurry]
    have h1 : Measurable (fun q : ℝ3 × Submission.BoseGases.X N => F ‖q.1‖) :=
      hFm.comp (measurable_norm.comp measurable_fst)
    have h2 : Measurable (fun q : ℝ3 × Submission.BoseGases.X N =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1 Ψq i q.2‖ ^ 2) :=
      (((Work.SmallBoxTBWord.continuous_tBamp_pair hχcd.continuous hχcs hΨqcd.continuous
        i).norm).pow 2).measurable
    exact (h1.mul h2).aestronglyMeasurable
  -- ## the a.e. domination along the fibres
  have hboundae : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N s)),
      ∀ p : ℝ3, ‖f p x‖ ≤ K * C ^ 2 / (1 + ‖p‖) ^ 4 := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N s)]
    filter_upwards with x hx
    exact hpointwise x hx
  -- ## joint integrability of the `(p,x)`-integrand
  have hInt : MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ3)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N s))) :=
    Work.BoseFixB2.DvApriori.integrable_uncurry_of_radial_bound
      (n := N) (A := Submission.BoseGases.abox N s)
      ((Submission.BoseGases.abox_lt_top N s hs.le).ne) hmeas (mul_nonneg hK (sq_nonneg C)) hboundae
  -- ## the Fubini exchange, in the curried notation
  have hswap : (∫ p : ℝ3, ∫ x : Submission.BoseGases.X N, f p x ∂
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N s)))
      = ∫ x : Submission.BoseGases.X N, ∫ p : ℝ3, f p x ∂
          (MeasureTheory.volume : MeasureTheory.Measure (ℝ3)) ∂
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N s)) :=
    MeasureTheory.integral_integral_swap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ3)))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N s)) hInt
  refine ⟨?_, ?_⟩
  · rw [← huncurry]
    exact hInt
  · have hL : (∫ p : ℝ3, ∫ x in Submission.BoseGases.abox N s,
          F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2)
        = ∫ p : ℝ3, ∫ x : Submission.BoseGases.X N, f p x ∂
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
              (Submission.BoseGases.abox N s)) := by
      apply integral_congr_ae
      filter_upwards with p
      apply integral_congr_ae
      filter_upwards with x
      rw [hf]
    have hR : (∫ x : Submission.BoseGases.X N, ∫ p : ℝ3, f p x ∂
            (MeasureTheory.volume : MeasureTheory.Measure (ℝ3)) ∂
            ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
              (Submission.BoseGases.abox N s)))
        = ∫ x in Submission.BoseGases.abox N s, ∫ p : ℝ3,
            F ‖p‖ * ‖Work.SmallBoxTBWord.tBamp χ p Ψq i x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with p
      rw [hf]
    rw [hL, hswap, hR]

end Work.BoseFixB1S
