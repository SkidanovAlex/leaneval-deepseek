/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-slot bound `HardSlotBound` for the hard part of `SpecialTransport`

Elgindi's `SpecialTransport` (§`H2`) decomposes the pairing of `f·∂_θg` with `g` into
"easy" terms (at least one derivative falls on the multiplier) and "hard" terms, in which
all the angular derivatives fall on `g`.  A single hard slot has the shape

  `∫_θ sin(2θ)^{-q}·f(z,θ)·∂_θv(z,θ)·v(z,θ) dθ`,

where `v = D_z^j D_θ^i g` is a `g`-block of order 5 and `q = η` (the `D_z` slot) or `q = γ`
(the mixed slots).  This file proves the per-slot bound

  `|∫_θ sin(2θ)^{-q}·f·∂_θv·v| ≤ (qK + 3K/2)·∫_θ sin(2θ)^{-q}·v²`

from the pointwise bounds `|f| ≤ K sin(2θ)`, `|∂_θf| ≤ 3K`, `|v| ≤ C sin(2θ)^p` and
`|sin(2θ)·∂_θv| ≤ C'`.

The proof is the angular integration by parts of `STIbp.ibp_partial`:

  `∫_θ sin(2θ)^{-q}·f·∂_θv·v = ∫_θ (q cos(2θ) sin(2θ)^{-q-1} f − (1/2) sin(2θ)^{-q} ∂_θf)·v²`,

the boundary terms vanishing because the primitive is `O(sin(2θ)^{1+2p-q})` and
`1 + 2p - q > 0`; the coefficient is then bounded pointwise by `(qK + 3K/2)·sin(2θ)^{-q}`.

(Note `open scoped Real` is needed for the symbol `π` under `autoImplicit = false`.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.STHardSlot
import Submission.Work.FTS.H2.AesmSlices
import Submission.Work.FTS.H2.HardSlotVan
import Submission.Work.FTS.H2.HardSlotABound
import Submission.Work.FTS.H2.HardSlotBCRBounds
import Submission.Work.FTS.H2.HardSlotDBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Integrability transfer lemmas -/

/-- A function on `Iθ` dominated by `C·sin(2θ)^r` with `r > -1` is integrable on `Iθ`. -/
theorem integrableOn_Iθ_of_sin_bound {g : ℝ → ℝ} {Cmaj r : ℝ} (hr : -1 < r)
    (hmeas : AEStronglyMeasurable g (volume.restrict Spaces.Iθ))
    (h : ∀ θ ∈ Spaces.Iθ, |g θ| ≤ Cmaj * (Real.sin (2 * θ)) ^ r) :
    IntegrableOn g Spaces.Iθ volume := by
  have hmaj : IntegrableOn (fun θ : ℝ => Cmaj * (Real.sin (2 * θ)) ^ r) Spaces.Iθ volume :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0 : ℝ) ≤ π / 2)).mp
      (intervalIntegrable_sin_rpow r hr)).const_mul Cmaj
  refine hmaj.mono' hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  simpa only [Real.norm_eq_abs] using h θ hθ

/-- `IntervalIntegrable` on `0..π/2` from `IntegrableOn` on `Iθ`. -/
theorem intervalIntegrable_Iθ_of_integrableOn {g : ℝ → ℝ}
    (h : IntegrableOn g Spaces.Iθ volume) : IntervalIntegrable g volume 0 (π / 2) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity : (0 : ℝ) ≤ π / 2)).mpr h

/-- A continuous function is almost everywhere strongly measurable for the restricted
Lebesgue measure on `Iθ`. -/
theorem aestronglyMeasurable_Iθ_of_continuous {g : ℝ → ℝ} (h : Continuous g) :
    AEStronglyMeasurable g (volume.restrict Spaces.Iθ) :=
  h.aestronglyMeasurable

theorem HardSlotBound (q K C C' p : ℝ) (hq : 0 < q) (hp0 : 0 ≤ p) (hq4 : 0 < 1 + p - q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (fun θ' => f z θ') (Work.Spaces.pth f z θ) θ)
    (hv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ)
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hf2 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.pth f z θ| ≤ 3 * K)
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p)
    (hv2 : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ) * Work.Spaces.pth v z θ| ≤ C') :
    |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ|
      ≤ (q * K + 3 * K / 2) * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2 := by
  have hpq : -1 < p - q := by linarith
  have h2pq : -1 < 2 * p - q := by linarith
  -- the five integrands of the proof
  set A : ℝ → ℝ :=
    fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Spaces.pth v z θ * v z θ
  set Bb : ℝ → ℝ :=
    fun θ => q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ * (v z θ) ^ 2
  set Cc : ℝ → ℝ :=
    fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ * (v z θ) ^ 2
  set D : ℝ → ℝ :=
    fun θ => (q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
        - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ) * (v z θ) ^ 2
  set R : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2
  -- ## Almost everywhere strong measurability of the slices
  have hAESMsin (r : ℝ) :
      AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ r) (volume.restrict Spaces.Iθ) :=
    (AesmSlices (u := fun θ : ℝ => (Real.sin (2 * θ)) ^ r)
      (g := fun θ : ℝ => 2 * Real.cos (2 * θ) * r * (Real.sin (2 * θ)) ^ (r - 1))
      (fun θ hθ => hasDerivAt_sin_rpow r θ hθ)).1
  have hAESMf : AEStronglyMeasurable (fun θ : ℝ => f z θ) (volume.restrict Spaces.Iθ) :=
    (AesmSlices (u := fun θ : ℝ => f z θ) (g := fun θ : ℝ => Spaces.pth f z θ)
      (fun θ hθ => hf θ hθ)).1
  have hAESMpf : AEStronglyMeasurable (fun θ : ℝ => Spaces.pth f z θ)
      (volume.restrict Spaces.Iθ) :=
    (AesmSlices (u := fun θ : ℝ => f z θ) (g := fun θ : ℝ => Spaces.pth f z θ)
      (fun θ hθ => hf θ hθ)).2
  have hAESMv : AEStronglyMeasurable (fun θ : ℝ => v z θ) (volume.restrict Spaces.Iθ) :=
    (AesmSlices (u := fun θ : ℝ => v z θ) (g := fun θ : ℝ => Spaces.pth v z θ)
      (fun θ hθ => hv θ hθ)).1
  have hAESMpv : AEStronglyMeasurable (fun θ : ℝ => Spaces.pth v z θ)
      (volume.restrict Spaces.Iθ) :=
    (AesmSlices (u := fun θ : ℝ => v z θ) (g := fun θ : ℝ => Spaces.pth v z θ)
      (fun θ hθ => hv θ hθ)).2
  have hAESMcos : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ))
      (volume.restrict Spaces.Iθ) :=
    aestronglyMeasurable_Iθ_of_continuous (by fun_prop)
  have hAESMv2 : AEStronglyMeasurable (fun θ : ℝ => (v z θ) ^ 2) (volume.restrict Spaces.Iθ) :=
    hAESMv.pow 2
  have hAESMconst (c : ℝ) : AEStronglyMeasurable (fun _ : ℝ => c) (volume.restrict Spaces.Iθ) :=
    aestronglyMeasurable_const
  have hAESM_A : AEStronglyMeasurable A (volume.restrict Spaces.Iθ) :=
    (((hAESMsin (-q)).mul hAESMf).mul hAESMpv).mul hAESMv
  have hAESM_B : AEStronglyMeasurable Bb (volume.restrict Spaces.Iθ) :=
    ((((hAESMconst q).mul hAESMcos).mul (hAESMsin (-q - 1))).mul hAESMf).mul hAESMv2
  have hAESM_C : AEStronglyMeasurable Cc (volume.restrict Spaces.Iθ) :=
    (((hAESMconst (1 / 2)).mul (hAESMsin (-q))).mul hAESMpf).mul hAESMv2
  have hAESM_D : AEStronglyMeasurable D (volume.restrict Spaces.Iθ) :=
    ((((hAESMconst q).mul hAESMcos).mul (hAESMsin (-q - 1))).mul hAESMf).sub
      (((hAESMconst (1 / 2)).mul (hAESMsin (-q))).mul hAESMpf) |>.mul hAESMv2
  have hAESM_R : AEStronglyMeasurable R (volume.restrict Spaces.Iθ) :=
    (hAESMsin (-q)).mul hAESMv2
  -- ## Integrability of the four pieces
  have hIntA : IntegrableOn A Spaces.Iθ volume :=
    integrableOn_Iθ_of_sin_bound (r := p - q) hpq hAESM_A
      (HardSlotABound hK hC hC' hp0 hf1 hv1 hv2)
  have hIntB : IntegrableOn Bb Spaces.Iθ volume :=
    integrableOn_Iθ_of_sin_bound (r := 2 * p - q) h2pq hAESM_B
      (HardSlotBCRBounds hq hp0 hK hC hf1 hf2 hv1).1
  have hIntC : IntegrableOn Cc Spaces.Iθ volume :=
    integrableOn_Iθ_of_sin_bound (r := 2 * p - q) h2pq hAESM_C
      (HardSlotBCRBounds hq hp0 hK hC hf1 hf2 hv1).2.1
  have hIntR : IntegrableOn R Spaces.Iθ volume :=
    integrableOn_Iθ_of_sin_bound (r := 2 * p - q) h2pq hAESM_R
      (HardSlotBCRBounds hq hp0 hK hC hf1 hf2 hv1).2.2
  have hDpt : ∀ θ ∈ Spaces.Iθ,
      |D θ| ≤ (q * K + 3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
    intro θ hθ
    have h1 := HardSlotDBound hq hp0 hK hC hf1 hf2 hv1 θ hθ
    have h2 := (HardSlotBCRBounds hq hp0 hK hC hf1 hf2 hv1).2.2 θ hθ
    have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
    have hv2nn : 0 ≤ (v z θ) ^ 2 := sq_nonneg _
    have hRnn : 0 ≤ (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2 := mul_nonneg hs0 hv2nn
    have hRle : (Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by
      rw [abs_of_nonneg hRnn] at h2
      exact h2
    have hc0 : 0 ≤ q * K + 3 * K / 2 := by nlinarith [hq.le, hK]
    calc |D θ| ≤ (q * K + 3 * K / 2) * ((Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2) := h1
      _ ≤ (q * K + 3 * K / 2) * (C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q)) :=
          mul_le_mul_of_nonneg_left hRle hc0
      _ = (q * K + 3 * K / 2) * C ^ 2 * (Real.sin (2 * θ)) ^ (2 * p - q) := by ring
  have hIntD : IntegrableOn D Spaces.Iθ volume :=
    integrableOn_Iθ_of_sin_bound (Cmaj := (q * K + 3 * K / 2) * C ^ 2) (r := 2 * p - q)
      h2pq hAESM_D hDpt
  -- ## The angular integration by parts
  have hIIA : IntervalIntegrable A volume 0 (π / 2) := intervalIntegrable_Iθ_of_integrableOn hIntA
  have hIIB : IntervalIntegrable Bb volume 0 (π / 2) := intervalIntegrable_Iθ_of_integrableOn hIntB
  have hIIC : IntervalIntegrable Cc volume 0 (π / 2) := intervalIntegrable_Iθ_of_integrableOn hIntC
  have hVan := HardSlotVan hq hp0 hq4 hK hC hf1 hv1
  have hIBP : ∫ θ in Spaces.Iθ, A θ = ∫ θ in Spaces.Iθ, D θ :=
    ibp_partial q f v (z := z) hf hv hVan.1 hVan.2
      ((hIIA.sub hIIB).add hIIC) hIIA hIIC hIIB
  -- ## The final estimate
  have hnormD : Integrable (fun θ : ℝ => ‖D θ‖) (volume.restrict Spaces.Iθ) := hIntD.norm
  have hrhs : Integrable (fun θ : ℝ => (q * K + 3 * K / 2) * R θ)
      (volume.restrict Spaces.Iθ) :=
    hIntR.const_mul _
  have hae : (fun θ : ℝ => ‖D θ‖) ≤ᵐ[volume.restrict Spaces.Iθ]
      (fun θ : ℝ => (q * K + 3 * K / 2) * R θ) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      have h1 := HardSlotDBound hq hp0 hK hC hf1 hf2 hv1 θ hθ
      simpa only [Real.norm_eq_abs] using h1)
  have hmono : (∫ θ in Spaces.Iθ, ‖D θ‖) ≤ ∫ θ in Spaces.Iθ, (q * K + 3 * K / 2) * R θ :=
    integral_mono_ae hnormD hrhs hae
  calc |∫ θ in Spaces.Iθ, A θ| = |∫ θ in Spaces.Iθ, D θ| := by rw [hIBP]
    _ = ‖∫ θ in Spaces.Iθ, D θ‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ θ in Spaces.Iθ, ‖D θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Spaces.Iθ, (q * K + 3 * K / 2) * R θ := hmono
    _ = (q * K + 3 * K / 2) * ∫ θ in Spaces.Iθ, R θ := integral_const_mul _ _

end Work.FTS.H2
