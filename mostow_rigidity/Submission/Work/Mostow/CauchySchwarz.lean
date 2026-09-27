import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.HlinPairing

/-!
# Cauchy–Schwarz bound for the Besson–Courtois–Gallot `Hlin` term (area N2)

`Hlin n φ w = ∫ ξ, ⟪φ ξ, w⟫ • φ ξ ∂(sigma n)` is the second-moment operator of the
push-forward of `sigma n` by a boundary bijection `φ`.  The chain rule for the natural map
needs the bound

`⟪(n-1) • ∫ ξ, ⟪ξ, v⟫ • φ ξ ∂σ, w⟫ ≤ ((n-1)/√n) * √⟪Hlin n φ w, w⟫ * ‖v‖`,

which is exactly the Cauchy–Schwarz (Hölder `p = q = 2`) inequality applied to the two
functions `ξ ↦ ⟪ξ, v⟫` and `ξ ↦ ⟪φ ξ, w⟫` in `L²(sigma n)`: the first integral is
`⟪v,v⟫/n = ‖v‖²/n` by the second-moment hypothesis, the second is `⟪Hlin n φ w, w⟫` by
`HlinPairing`.  The scalar calculus is done once, in `integral_mul_le_sqrt_mul_sqrt`.
-/

set_option linter.style.haveILetI false

open scoped InnerProductSpace

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- **Cauchy–Schwarz** for the Bochner integral of a product of two `L²` functions:
`∫ f g ≤ √(∫ f²) * √(∫ g²)`.  This is Hölder's inequality with `p = q = 2`, written with
square roots rather than `rpow` and with unreduced exponents. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ a, f a * g a ∂μ ≤ Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by simp
  have hfg : Integrable (fun a => f a * g a) μ := hf.integrable_mul hg
  have hfgn : Integrable (fun a => ‖f a‖ * ‖g a‖) μ := hf.norm.integrable_mul hg.norm
  have h1 : ∫ a, f a * g a ∂μ ≤ ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_mono_ae hfg hfgn (Filter.Eventually.of_forall fun a => ?_)
    calc f a * g a ≤ |f a * g a| := le_abs_self _
      _ = |f a| * |g a| := abs_mul _ _
  have hHolder : ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤
      (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    integral_mul_norm_le_Lp_mul_Lq hpq (by rw [h2]; exact hf) (by rw [h2]; exact hg)
  have hf2 : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) = ∫ a, f a ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hg2 : (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) = ∫ a, g a ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc ∫ a, f a * g a ∂μ ≤ ∫ a, ‖f a‖ * ‖g a‖ ∂μ := h1
    _ ≤ (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ a, ‖g a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hHolder
    _ = Real.sqrt (∫ a, f a ^ 2 ∂μ) * Real.sqrt (∫ a, g a ^ 2 ∂μ) := by
        simp only [hf2, hg2, Real.sqrt_eq_rpow]

theorem CauchySchwarz (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hprob : (Submission.Mostow.sigma n) Set.univ = 1)
    (hsupp : Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0)
    (hsecond : ∀ v w : Submission.Mostow.E n,
      ∫ ξ, (inner ℝ ξ v) * (inner ℝ ξ w) ∂(Submission.Mostow.sigma n) = (inner ℝ v w) / n) :
    ∀ v w : Submission.Mostow.E n,
      inner ℝ ((((n : ℝ) - 1) •
          ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(Submission.Mostow.sigma n))) w ≤
        (((n : ℝ) - 1) / Real.sqrt n) * Real.sqrt (inner ℝ ((Work.Mostow.Hlin n φ) w) w) * ‖v‖ := by
  haveI : IsFiniteMeasure (sigma n) := ⟨by rw [hprob]; exact ENNReal.one_lt_top⟩
  intro v w
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: the chart space is a subsingleton, so both sides vanish
    subst hn0
    have hv : v = 0 := Subsingleton.elim v 0
    have hw : w = 0 := Subsingleton.elim w 0
    rw [hv, hw]
    simp
  · have hc : 0 ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnpos : 1 ≤ n)
      linarith
    have hSph : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet
    have hφae : AEMeasurable φ (sigma n) :=
      aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n) hSph hcont hsupp
    have hmem : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
      rw [ae_iff]; simpa only [Set.compl_def] using hsupp
    have hunit : ∀ ξ ∈ Sph n, ‖ξ‖ = 1 := fun ξ hξ => by
      rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at hξ; exact hξ
    have hξunit : ∀ᵐ ξ ∂(sigma n), ‖ξ‖ = 1 := hmem.mono fun ξ h => hunit ξ h
    have hφunit : ∀ᵐ ξ ∂(sigma n), ‖φ ξ‖ = 1 :=
      (hmem.mono fun ξ h => hbij.1 h).mono fun ξ h => hunit (φ ξ) h
    -- integrability of the vector-valued integrand `ξ ↦ ⟪ξ,v⟫ • φ ξ`
    have hInt : Integrable (fun ξ => (inner ℝ ξ v) • φ ξ) (sigma n) := by
      have hcont1 : Continuous fun ξ : E n => inner ℝ ξ v :=
        continuous_id.inner continuous_const
      refine Integrable.of_bound (hcont1.aemeasurable.smul hφae).aestronglyMeasurable ‖v‖ ?_
      filter_upwards [hξunit, hφunit] with ξ hξ hφ
      rw [norm_smul, hφ, mul_one]
      calc ‖inner ℝ ξ v‖ ≤ ‖ξ‖ * ‖v‖ := norm_inner_le_norm _ _
        _ = ‖v‖ := by rw [hξ, one_mul]
    -- the pairing of the Bochner integral with the fixed vector `w`
    have hswap : inner ℝ (∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n)) w
        = ∫ ξ, (inner ℝ ξ v) * (inner ℝ (φ ξ) w) ∂(sigma n) := by
      rw [inner_integral_right (sigma n) hInt w]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [real_inner_smul_left]
    have hmain : inner ℝ (((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n)) w
        = ((n : ℝ) - 1) * ∫ ξ, (inner ℝ ξ v) * (inner ℝ (φ ξ) w) ∂(sigma n) := by
      rw [real_inner_smul_left, hswap]
    -- the two `L²` functions
    have hFmem : MemLp (fun ξ => inner ℝ ξ v) 2 (sigma n) := by
      have hcont1 : Continuous fun ξ : E n => inner ℝ ξ v :=
        continuous_id.inner continuous_const
      refine MemLp.of_bound hcont1.aestronglyMeasurable ‖v‖ ?_
      filter_upwards [hξunit] with ξ hξ
      calc ‖inner ℝ ξ v‖ ≤ ‖ξ‖ * ‖v‖ := norm_inner_le_norm _ _
        _ = ‖v‖ := by rw [hξ, one_mul]
    have hφmem : MemLp φ 2 (sigma n) := by
      refine MemLp.of_bound hφae.aestronglyMeasurable 1 ?_
      filter_upwards [hφunit] with ξ hφ
      rw [hφ]
    have hGmem : MemLp (fun ξ => inner ℝ (φ ξ) w) 2 (sigma n) := hφmem.inner_const w
    have hCS := integral_mul_le_sqrt_mul_sqrt hFmem hGmem
    -- evaluation of the two second moments
    have hIntF2 : ∫ ξ, (inner ℝ ξ v) ^ 2 ∂(sigma n) = ‖v‖ ^ 2 / n := by
      have h := hsecond v v
      rw [real_inner_self_eq_norm_sq] at h
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [pow_two]
    have hIntG2 : ∫ ξ, (inner ℝ (φ ξ) w) ^ 2 ∂(sigma n)
        = inner ℝ ((Hlin n φ) w) w := by
      have h := HlinPairing n φ hbij hcont hsupp w w
      rw [h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [pow_two]
    have hsqrtF : Real.sqrt (∫ ξ, (inner ℝ ξ v) ^ 2 ∂(sigma n)) = ‖v‖ / Real.sqrt n := by
      rw [hIntF2, Real.sqrt_div (sq_nonneg ‖v‖), Real.sqrt_sq (norm_nonneg v)]
    have hsqrtG : Real.sqrt (∫ ξ, (inner ℝ (φ ξ) w) ^ 2 ∂(sigma n))
        = Real.sqrt (inner ℝ ((Hlin n φ) w) w) := by
      rw [hIntG2]
    calc inner ℝ (((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n)) w
        = ((n : ℝ) - 1) * ∫ ξ, (inner ℝ ξ v) * (inner ℝ (φ ξ) w) ∂(sigma n) := hmain
      _ ≤ ((n : ℝ) - 1) *
            (Real.sqrt (∫ ξ, (inner ℝ ξ v) ^ 2 ∂(sigma n)) *
              Real.sqrt (∫ ξ, (inner ℝ (φ ξ) w) ^ 2 ∂(sigma n))) :=
          mul_le_mul_of_nonneg_left hCS hc
      _ = ((n : ℝ) - 1) / Real.sqrt n * Real.sqrt (inner ℝ ((Hlin n φ) w) w) * ‖v‖ := by
          rw [hsqrtF, hsqrtG]; ring

end

end Work.Mostow
