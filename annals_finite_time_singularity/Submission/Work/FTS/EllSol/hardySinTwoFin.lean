import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.UopHk.powerHardyFinite
import Submission.Work.FTS.EllSol.powerHardyAll
import Submission.Work.FTS.EllSol.mirrorIooIntegrableOn
import Submission.Work.FTS.EllSol.mirrorIooIntegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `sin (2θ)`-weighted Hardy inequality on `Iθ = [0, π/2]` (finite exponent)

`Work.FTS.EllSol.hardySinTwoFin`: there is a universal constant `K > 0` such that for every
`h` of class `C¹` on `(0, π/2)` with `h → 0` at both endpoints and whose `sin(2θ)^{-η}`-weighted
squared derivative is integrable on `Iθ`, the function `θ ↦ h(θ)² sin(2θ)^{-(2+η)}` is integrable
on `Iθ` and
  `∫_{Iθ} h² sin(2θ)^{-(2+η)} ≤ K ∫_{Iθ} (h')² sin(2θ)^{-η}`,   `η = Work.Spaces.eta = 99/100`.

The proof splits `Iθ` at its midpoint `π/4`.  On each half `sin (2θ)` is comparable with the
distance to the corresponding endpoint (`sin (2θ) ≈ 2θ` for `θ ≤ π/4`, and
`sin (2θ) = sin (2(π/2 − θ))` on the right half), so Jordan's inequality
`sin x ≥ (2/π) x` turns the `sin`-weighted Hardy inequality into the power-weight Hardy
inequality `Work.FTS.EllSol.powerHardyAll` (`∫₀^a h² t^{-(2+η)} ≤ 4 ∫₀^a (h')² t^{-η}`);
the right half is mapped to the left one by the reflection `θ ↦ π/2 − θ`
(`mirrorIooIntegrableOn`, `mirrorIooIntegral`).

The stronger statement `hardySigmaFin` below (every exponent `0 ≤ λ ≤ 2` in place of `η`) is
proved in the same way; the requested lemma is its instance `λ = η`.
-/

set_option autoImplicit false
open MeasureTheory Real Set Filter
open scoped Topology

namespace Work.FTS.EllSol

/-! ## Elementary comparison lemmas on `(0, π/4)` -/

/-- `sin (2θ) > 0` on `(0, π/4)`. -/
private lemma sin2_pos_half {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Continuity of `θ ↦ θ ^ p` on `(0, π/4)`. -/
private lemma contOn_rpow_half (p : ℝ) : ContinuousOn (fun θ : ℝ => θ ^ p) (Set.Ioo 0 (Real.pi / 4)) :=
  fun x hx => (Real.continuousAt_rpow_const x p (Or.inl (ne_of_gt hx.1))).continuousWithinAt

/-- Continuity of `θ ↦ sin (2θ) ^ p` on `(0, π/4)`. -/
private lemma contOn_sin2_rpow_half (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (Real.pi / 4)) := by
  intro θ hθ
  have h1 : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) θ :=
    Real.continuous_sin.continuousAt.comp (continuous_const.mul continuous_id).continuousAt
  exact (ContinuousAt.comp (f := fun θ : ℝ => Real.sin (2 * θ)) (x := θ)
    (Real.continuousAt_rpow_const (Real.sin (2 * θ)) p
      (Or.inl (ne_of_gt (sin2_pos_half hθ)))) h1).continuousWithinAt

/-- `θ ^ (-λ) ≤ 4 * sin (2θ) ^ (-λ)` on `(0, π/4)`, for `0 ≤ λ ≤ 2`. -/
private lemma theta_rpow_le_four_sin {lam θ : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam ≤ 2)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    θ ^ (-lam) ≤ 4 * (Real.sin (2 * θ)) ^ (-lam) := by
  have hs : 0 < Real.sin (2 * θ) := sin2_pos_half hθ
  have hlt : Real.sin (2 * θ) < 2 * θ := Real.sin_lt (by linarith [hθ.1])
  have hle : Real.sin (2 * θ) / 2 ≤ θ := by linarith
  have h1 : θ ^ (-lam) ≤ (Real.sin (2 * θ) / 2) ^ (-lam) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
  have h2 : (Real.sin (2 * θ) / 2) ^ (-lam) = (Real.sin (2 * θ)) ^ (-lam) * 2 ^ lam := by
    rw [Real.div_rpow (le_of_lt hs) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) lam]
    exact div_inv_eq_mul _ _
  have h3 : (2 : ℝ) ^ lam ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlam2
    norm_num at h
    exact h
  calc θ ^ (-lam) ≤ (Real.sin (2 * θ) / 2) ^ (-lam) := h1
    _ = (Real.sin (2 * θ)) ^ (-lam) * 2 ^ lam := h2
    _ ≤ (Real.sin (2 * θ)) ^ (-lam) * 4 :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt (Real.rpow_pos_of_pos hs _))
    _ = 4 * (Real.sin (2 * θ)) ^ (-lam) := by ring

/-- `sin (2θ) ^ (-(2+λ)) ≤ θ ^ (-(2+λ))` on `(0, π/4)`, for `λ ≥ 0`. -/
private lemma sin_rpow_le_theta_rpow {lam θ : ℝ} (hlam0 : 0 ≤ lam)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    (Real.sin (2 * θ)) ^ (-(2 + lam)) ≤ θ ^ (-(2 + lam)) := by
  have h2θ : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2θ' : 2 * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
  have hsin : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) := Real.mul_le_sin h2θ h2θ'
  have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have hθle : θ ≤ Real.sin (2 * θ) := by
    have h : 2 / Real.pi * (2 * θ) = (4 / Real.pi) * θ := by ring
    rw [h] at hsin
    exact le_trans (le_mul_of_one_le_left (le_of_lt hθ.1) h4) hsin
  exact Real.rpow_le_rpow_of_nonpos hθ.1 hθle (by linarith)

/-- Pointwise domination of the power-weighted derivative by the `sin`-weighted one. -/
private lemma sq_mul_le_four {a θ lam : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam ≤ 2)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    a ^ 2 * θ ^ (-lam) ≤ 4 * (a ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by
  have hcmp := theta_rpow_le_four_sin hlam0 hlam2 hθ
  calc a ^ 2 * θ ^ (-lam) ≤ a ^ 2 * (4 * (Real.sin (2 * θ)) ^ (-lam)) :=
        mul_le_mul_of_nonneg_left hcmp (sq_nonneg a)
    _ = 4 * (a ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by ring

/-- Pointwise domination of the `sin`-weighted value by the power-weighted one. -/
private lemma sq_mul_le_sq_mul {a θ lam : ℝ} (hlam0 : 0 ≤ lam)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4)) :
    a ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)) ≤ a ^ 2 * θ ^ (-(2 + lam)) :=
  mul_le_mul_of_nonneg_left (sin_rpow_le_theta_rpow hlam0 hθ) (sq_nonneg a)

/-! ## The half-interval `sin`-weighted Hardy inequality -/

/-- On the left half interval `(0, π/4)`, where `sin (2θ)` is comparable with `2θ`, the
weighted Hardy inequality with the weight `sin (2θ) ^ (-λ)` follows from the power-weight
Hardy inequality with weight `θ ^ (-λ)`. -/
private lemma hardySin_half (Cp : ℝ) (hCp : 0 < Cp)
    (hPH : ∀ (η a : ℝ), 0 ≤ η → 0 < a → ∀ h : ℝ → ℝ,
      ContDiffOn ℝ 1 h (Set.Ioo 0 a) →
      Filter.Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a) →
      MeasureTheory.IntegrableOn (fun t : ℝ => (h t) ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a) ∧
      (∫ t in Set.Ioo 0 a, (h t) ^ 2 * t ^ (-(2 + η)))
        ≤ Cp * ∫ t in Set.Ioo 0 a, (deriv h t) ^ 2 * t ^ (-η))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam2 : lam ≤ 2) {u : ℝ → ℝ}
    (huc : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 4)))
    (hu0 : Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hug : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
      (Set.Ioo 0 (Real.pi / 4))) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
        (Set.Ioo 0 (Real.pi / 4)) ∧
      (∫ θ in Set.Ioo 0 (Real.pi / 4), (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
        ≤ 4 * Cp * ∫ θ in Set.Ioo 0 (Real.pi / 4),
            (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) := by
  have hudc : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 4)) :=
    huc.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  -- the `4`-multiple of the `sin`-weighted derivative
  have hdom4 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 4 * ((deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)))
      (Set.Ioo 0 (Real.pi / 4)) := hug.const_mul (4 : ℝ)
  -- (1) the power-weighted derivative is integrable
  have hA1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * θ ^ (-lam))
      (Set.Ioo 0 (Real.pi / 4)) := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (deriv u θ) ^ 2 * θ ^ (-lam))
        (volume.restrict (Set.Ioo 0 (Real.pi / 4))) :=
      ((hudc.pow 2).mul (contOn_rpow_half (-lam))).aestronglyMeasurable measurableSet_Ioo
    have hpt : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
        ‖(deriv u θ) ^ 2 * θ ^ (-lam)‖
          ≤ 4 * ((deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun θ hθ => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (deriv u θ)),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt hθ.1) _)]
      exact sq_mul_le_four hlam0 hlam2 hθ
    exact MeasureTheory.Integrable.mono' hdom4 haesm hpt
  -- (2) the power Hardy inequality
  obtain ⟨hB1, hB2⟩ := hPH lam (Real.pi / 4) hlam0 (by positivity) u huc hu0 hA1
  -- (3) the `sin`-weighted value is integrable, dominated by the power-weighted one
  have hC1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      (Set.Ioo 0 (Real.pi / 4)) := by
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
        (volume.restrict (Set.Ioo 0 (Real.pi / 4))) :=
      ((huc.continuousOn.pow 2).mul (contOn_sin2_rpow_half (-(2 + lam)))).aestronglyMeasurable
        measurableSet_Ioo
    have hpt : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 4))),
        ‖(u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam))‖ ≤ (u θ) ^ 2 * θ ^ (-(2 + lam)) := by
      refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall (fun θ hθ => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (u θ)),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (sin2_pos_half hθ)) _)]
      exact sq_mul_le_sq_mul hlam0 hθ
    exact MeasureTheory.Integrable.mono' hB1 haesm hpt
  -- (4) the two integral comparisons
  have hC2 : (∫ θ in Set.Ioo 0 (Real.pi / 4),
        (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 4), (u θ) ^ 2 * θ ^ (-(2 + lam)) :=
    MeasureTheory.setIntegral_mono_on hC1 hB1 measurableSet_Ioo
      (fun θ hθ => sq_mul_le_sq_mul hlam0 hθ)
  have hD : (∫ θ in Set.Ioo 0 (Real.pi / 4), (deriv u θ) ^ 2 * θ ^ (-lam))
      ≤ 4 * ∫ θ in Set.Ioo 0 (Real.pi / 4),
          (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) := by
    have hmono := MeasureTheory.setIntegral_mono_on hA1 hdom4 measurableSet_Ioo
      (fun θ hθ => sq_mul_le_four hlam0 hlam2 hθ)
    calc (∫ θ in Set.Ioo 0 (Real.pi / 4), (deriv u θ) ^ 2 * θ ^ (-lam))
        ≤ ∫ θ in Set.Ioo 0 (Real.pi / 4),
            4 * ((deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := hmono
      _ = 4 * ∫ θ in Set.Ioo 0 (Real.pi / 4),
            (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) :=
          MeasureTheory.integral_const_mul 4 _
  refine ⟨hC1, ?_⟩
  calc (∫ θ in Set.Ioo 0 (Real.pi / 4), (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ ∫ θ in Set.Ioo 0 (Real.pi / 4), (u θ) ^ 2 * θ ^ (-(2 + lam)) := hC2
    _ ≤ Cp * ∫ θ in Set.Ioo 0 (Real.pi / 4), (deriv u θ) ^ 2 * θ ^ (-lam) := hB2
    _ ≤ Cp * (4 * ∫ θ in Set.Ioo 0 (Real.pi / 4),
          (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) :=
        mul_le_mul_of_nonneg_left hD (le_of_lt hCp)
    _ = 4 * Cp * ∫ θ in Set.Ioo 0 (Real.pi / 4),
          (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) := by ring

/-! ## The main theorem -/

private theorem hardySigmaFin : ∃ K : ℝ, 0 < K ∧ ∀ (lam : ℝ), 0 ≤ lam → lam ≤ 2 → ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by
  obtain ⟨Cp, hCp, hPH⟩ := powerHardyAll
  refine ⟨4 * Cp + 4, by positivity, ?_⟩
  intro lam hlam0 hlam2 f hf hf0 hf1 hGlint
  have hpi2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsubL : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hpi2⟩
  have hsubIθL : Set.Ioo (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hpi2)⟩
  have hsubIθR : Set.Ioo (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt (lt_trans (by positivity : (0 : ℝ) < Real.pi / 4) hx.1), le_of_lt hx.2⟩
  -- ## left half
  have hf_cd : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 4)) := hf.mono hsubL
  have hfG : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
      (Set.Ioo 0 (Real.pi / 4)) := hGlint.mono_set hsubIθL
  obtain ⟨hLint, hLbd⟩ := hardySin_half Cp hCp hPH hlam0 hlam2 hf_cd hf0 hfG
  -- ## right half via the mirror `φ ↦ π/2 - φ`
  have hmap : Set.MapsTo (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo 0 (Real.pi / 4))
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun φ hφ => ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩
  have hg_cd : ContDiffOn ℝ 1 (fun φ : ℝ => f (Real.pi / 2 - φ)) (Set.Ioo 0 (Real.pi / 4)) := by
    have hcd : ContDiffOn ℝ 1 (fun φ : ℝ => Real.pi / 2 - φ) (Set.Ioo 0 (Real.pi / 4)) :=
      contDiffOn_const.sub contDiffOn_id
    have hcomp := hf.comp hcd hmap
    simpa only [Function.comp_def] using hcomp
  have hg0 : Filter.Tendsto (fun φ : ℝ => f (Real.pi / 2 - φ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcomp : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhds (0 : ℝ))
            (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub tendsto_id
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with φ hφ
        simp only [Set.mem_Iio, Set.mem_Ioi] at hφ ⊢
        linarith [hφ]
    simpa only [Function.comp_def] using hf1.comp hcomp
  have hgderiv : ∀ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      deriv (fun φ : ℝ => f (Real.pi / 2 - φ)) φ = -deriv f (Real.pi / 2 - φ) := by
    intro φ hφ
    have hmem : Real.pi / 2 - φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩
    have hdf : DifferentiableAt ℝ f (Real.pi / 2 - φ) :=
      (hf.differentiableOn one_ne_zero (Real.pi / 2 - φ) hmem).differentiableAt
        (isOpen_Ioo.mem_nhds hmem)
    have hT : HasDerivAt (fun φ : ℝ => Real.pi / 2 - φ) (-1) φ := by
      simpa using ((hasDerivAt_id' (x := φ)).const_sub (Real.pi / 2 : ℝ))
    have hc : HasDerivAt (fun φ : ℝ => f (Real.pi / 2 - φ))
        (deriv f (Real.pi / 2 - φ) * (-1)) φ := by
      simpa only [Function.comp_def] using hdf.hasDerivAt.comp φ hT
    rw [hc.deriv]
    ring
  have hgmix : MeasureTheory.IntegrableOn
      (fun φ : ℝ => (deriv f (Real.pi / 2 - φ)) ^ 2
        * (Real.sin (2 * (Real.pi / 2 - φ))) ^ (-lam)) (Set.Ioo 0 (Real.pi / 4)) :=
    (mirrorIooIntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))).mp
      (hGlint.mono_set hsubIθR)
  have hgG : MeasureTheory.IntegrableOn
      (fun φ : ℝ => (deriv (fun φ : ℝ => f (Real.pi / 2 - φ)) φ) ^ 2
        * (Real.sin (2 * φ)) ^ (-lam)) (Set.Ioo 0 (Real.pi / 4)) := by
    refine hgmix.congr_fun ?_ measurableSet_Ioo
    intro φ hφ
    dsimp only
    rw [hgderiv φ hφ]
    simp only [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]
    ring
  obtain ⟨hRintG, hRbdG⟩ := hardySin_half Cp hCp hPH hlam0 hlam2 hg_cd hg0 hgG
  -- ## mirror everything back to the right half
  have hFsR : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    (mirrorIooIntegrableOn (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))).mpr (by
      refine hRintG.congr_fun ?_ measurableSet_Ioo
      intro φ hφ
      simp only [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub])
  have hFsRint : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      = ∫ φ in Set.Ioo 0 (Real.pi / 4),
          (f (Real.pi / 2 - φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + lam)) := by
    have hmir := mirrorIooIntegral (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam))) hFsR
    rw [hmir]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
    intro φ hφ
    simp only [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]
  have hLsRint : (∫ φ in Set.Ioo 0 (Real.pi / 4),
        (deriv (fun φ : ℝ => f (Real.pi / 2 - φ)) φ) ^ 2 * (Real.sin (2 * φ)) ^ (-lam))
      = ∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) := by
    have hmir := mirrorIooIntegral (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
      (hGlint.mono_set hsubIθR)
    rw [hmir]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
    intro φ hφ
    dsimp only
    rw [hgderiv φ hφ]
    simp only [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]
    ring
  have hRbdF : (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ 4 * Cp * (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by
    rw [hFsRint, ← hLsRint]
    exact hRbdG
  -- ## glue
  have hIocUnion : Set.Ioc (0 : ℝ) (Real.pi / 4) ∪ Set.Ioc (Real.pi / 4) (Real.pi / 2)
      = Set.Ioc 0 (Real.pi / 2) := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
    · intro hx
      by_cases h : x ≤ Real.pi / 4
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨by linarith, hx.2⟩
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (Real.pi / 4)) (Set.Ioc (Real.pi / 4) (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    linarith [hx1.2, hx2.1]
  have hsubIocL : Set.Ioc (0 : ℝ) (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos]))⟩
  have hsubIocR : Set.Ioc (Real.pi / 4) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx =>
      ⟨le_trans (le_of_lt (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)) (le_of_lt hx.1),
        hx.2⟩
  have hsplit : ∀ F : ℝ → ℝ,
      MeasureTheory.IntegrableOn F (Set.Ioc 0 (Real.pi / 4)) →
      MeasureTheory.IntegrableOn F (Set.Ioc (Real.pi / 4) (Real.pi / 2)) →
      (∫ θ in Work.Spaces.Iθ, F θ)
        = (∫ θ in Set.Ioo 0 (Real.pi / 4), F θ)
          + (∫ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) := by
    intro F h1 h2
    have hsu : (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), F θ)
        = (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 4), F θ)
          + (∫ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), F θ) := by
      rw [← hIocUnion]
      exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc h1 h2
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, hsu]
    simp only [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hFsIoc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam))) (Set.Ioc 0 (Real.pi / 4)) :=
    hLint.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 4)).symm
  have hFsIoc2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      (Set.Ioc (Real.pi / 4) (Real.pi / 2)) :=
    hFsR.congr_set_ae (MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := Real.pi / 4)
      (b := Real.pi / 2)).symm
  have hFsIocAll : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      (Set.Ioc 0 (Real.pi / 2)) := by
    have h := hFsIoc.union hFsIoc2
    rwa [hIocUnion] at h
  have hFsIθ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam))) Work.Spaces.Iθ :=
    hFsIocAll.congr_set_ae (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 2)).symm
  have hLsIoc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
      (Set.Ioc 0 (Real.pi / 4)) := hGlint.mono_set hsubIocL
  have hLsIoc2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
      (Set.Ioc (Real.pi / 4) (Real.pi / 2)) := hGlint.mono_set hsubIocR
  have hFdec := hsplit (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
    hFsIoc hFsIoc2
  have hLdec := hsplit (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam))
    hLsIoc hLsIoc2
  have hB : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam) :=
    MeasureTheory.setIntegral_nonneg (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _))
  refine ⟨hFsIθ, ?_⟩
  have htot : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ 4 * Cp * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by
    rw [hFdec, hLdec]
    linarith [hLbd, hRbdF]
  calc (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + lam)))
      ≤ 4 * Cp * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := htot
    _ ≤ (4 * Cp + 4) * (∫ θ in Work.Spaces.Iθ,
          (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-lam)) := by nlinarith [hB]

theorem hardySinTwoFin : ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ),
    ContDiffOn ℝ 1 h (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (h θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
  obtain ⟨K, hK, hmain⟩ := hardySigmaFin
  exact ⟨K, hK, fun h hc h0 h1 hI =>
    hmain Work.Spaces.eta Work.Spaces.eta_nonneg (by norm_num [Work.Spaces.eta])
      h hc h0 h1 hI⟩

end Work.FTS.EllSol
