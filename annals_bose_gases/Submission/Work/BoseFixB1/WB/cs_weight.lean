import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.cs_weight`

The weighted Cauchy–Schwarz inequality used in FS's step 4 of `thm:aprioriHLambda`
(the passage from the a-priori inequality to the particle window), see
`Submission/Work/BoseFixB1/WB/Defs.lean`.

Pointwise the integrand is split as

  `(t − μ)·g = [ (t − μ)·√g / √(1 + t/μ) ] · [ √(1 + t/μ)·√g ]`,

and the two factors are exactly the square roots of the two weights appearing on
the right-hand side: `(1 + t/μ) > 0` and `g ≥ 0` on `G`, so the `√`'s square out.
Cauchy–Schwarz in `L²` (Hölder at `p = q = 2`) then gives the claim.

The auxiliary lemma `integral_mul_le_sqrt_mul_sqrt` below is the abstract form of
Cauchy–Schwarz for a.e. nonnegative `f, g` with square-integrable squares.
-/

open MeasureTheory Filter

namespace Work.BoseFixB1.WB

set_option linter.unusedVariables false

/-- **Cauchy–Schwarz for the integral.**  For `0 ≤ᵐ f`, `0 ≤ᵐ g` with `f²` and `g²`
integrable,
`∫ f·g ≤ √(∫ f²)·√(∫ g²)`, with the marginals written as `sqrt`s of the integrals
of the pointwise squares. -/
lemma integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hg : 0 ≤ᵐ[μ] g)
    (hfi : Integrable (fun x => f x ^ 2) μ) (hgi : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  -- `f` and `g` are a.e. strongly measurable: they are `√(·²)` on the set where they are `≥ 0`.
  have hfmeas : AEStronglyMeasurable f μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable hfi.aestronglyMeasurable).congr ?_
    filter_upwards [hf] with x hx
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx]
  have hgmeas : AEStronglyMeasurable g μ := by
    refine (Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable).congr ?_
    filter_upwards [hg] with x hx
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx]
  have hfm : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hfmeas).mpr hfi
  have hgm : MemLp g (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hgmeas).mpr hgi
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hf hg hfm hgm
  simpa only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using h

lemma cs_weight {G : Set (EuclideanSpace ℝ (Fin 3))} {t g : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hmeas : MeasurableSet G)
    (ht : ∀ u ∈ G, 0 ≤ t u) (hg : ∀ u ∈ G, 0 ≤ g u)
    (hint1 : MeasureTheory.IntegrableOn (fun u => (t u - μ) ^ 2 / (1 + t u / μ) * g u) G)
    (hint2 : MeasureTheory.IntegrableOn (fun u => (1 + t u / μ) * g u) G)
    (hint3 : MeasureTheory.IntegrableOn (fun u => (t u - μ) * g u) G) :
    |∫ u in G, (t u - μ) * g u|
      ≤ Real.sqrt (∫ u in G, (t u - μ) ^ 2 / (1 + t u / μ) * g u)
        * Real.sqrt (∫ u in G, (1 + t u / μ) * g u) := by
  classical
  -- `1 + t/μ > 0` and `g ≥ 0` on `G`, so all the `√`'s below square correctly.
  have hcpos : ∀ u ∈ G, 0 < 1 + t u / μ := by
    intro u hu
    have : 0 ≤ t u / μ := div_nonneg (ht u hu) hμ.le
    linarith
  -- The two Cauchy–Schwarz factors (not restricted to `G`, they are `0`-free anyway).
  set F : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun u => (t u - μ) * Real.sqrt (g u) / Real.sqrt (1 + t u / μ) with hF
  set H : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun u => Real.sqrt (1 + t u / μ) * Real.sqrt (g u) with hH
  have hHnonneg : ∀ u, 0 ≤ H u := by
    intro u
    simp only [hH]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- `F·H` is the original integrand on `G`.
  have hFH : ∀ u ∈ G, F u * H u = (t u - μ) * g u := by
    intro u hu
    simp only [hF, hH]
    have hc := hcpos u hu
    have hcne : Real.sqrt (1 + t u / μ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
    have hss : Real.sqrt (g u) * Real.sqrt (g u) = g u := by
      rw [← pow_two]; exact Real.sq_sqrt (hg u hu)
    rw [div_eq_mul_inv]
    calc ((t u - μ) * Real.sqrt (g u) * (Real.sqrt (1 + t u / μ))⁻¹)
          * (Real.sqrt (1 + t u / μ) * Real.sqrt (g u))
        = (t u - μ) * (Real.sqrt (g u) * Real.sqrt (g u))
            * ((Real.sqrt (1 + t u / μ))⁻¹ * Real.sqrt (1 + t u / μ)) := by ring
      _ = (t u - μ) * g u := by rw [hss, inv_mul_cancel₀ hcne, mul_one]
  -- `F²` and `H²` are the two weights of the right-hand side, on `G`.
  have hFsq : ∀ u ∈ G, F u ^ 2 = (t u - μ) ^ 2 / (1 + t u / μ) * g u := by
    intro u hu
    simp only [hF]
    rw [div_pow, mul_pow, Real.sq_sqrt (hcpos u hu).le, Real.sq_sqrt (hg u hu)]
    ring
  have hHsq : ∀ u ∈ G, H u ^ 2 = (1 + t u / μ) * g u := by
    intro u hu
    simp only [hH]
    rw [mul_pow, Real.sq_sqrt (hcpos u hu).le, Real.sq_sqrt (hg u hu)]
  -- `|F|·H = |F·H| = |(t − μ)·g|` on `G`.
  have habs : ∀ u ∈ G, |F u| * H u = |(t u - μ) * g u| := by
    intro u hu
    rw [← abs_of_nonneg (hHnonneg u), ← abs_mul, hFH u hu]
  -- Square integrability of the two factors, transferred from `hint1`, `hint2`.
  have hInt1 : Integrable (fun u => |F u| ^ 2) (volume.restrict G) :=
    hint1.congr_fun (fun u hu => by rw [sq_abs]; exact (hFsq u hu).symm) hmeas
  have hInt2 : Integrable (fun u => H u ^ 2) (volume.restrict G) :=
    hint2.congr_fun (fun u hu => (hHsq u hu).symm) hmeas
  -- Cauchy–Schwarz.
  have hcs := integral_mul_le_sqrt_mul_sqrt (volume.restrict G)
      (f := fun u => |F u|) (g := H)
      (Eventually.of_forall fun u => abs_nonneg (F u))
      (Eventually.of_forall fun u => hHnonneg u)
      hInt1 hInt2
  have hA : ∫ u, |F u| ^ 2 ∂(volume.restrict G)
      = ∫ u in G, (t u - μ) ^ 2 / (1 + t u / μ) * g u :=
    setIntegral_congr_fun hmeas (fun u hu => by rw [sq_abs]; exact hFsq u hu)
  have hB : ∫ u, H u ^ 2 ∂(volume.restrict G) = ∫ u in G, (1 + t u / μ) * g u :=
    setIntegral_congr_fun hmeas (fun u hu => hHsq u hu)
  have hAB : ∫ u, |F u| * H u ∂(volume.restrict G) = ∫ u in G, |(t u - μ) * g u| :=
    setIntegral_congr_fun hmeas (fun u hu => habs u hu)
  rw [hAB, hA, hB] at hcs
  exact le_trans (abs_integral_le_integral_abs (μ := volume.restrict G)
    (f := fun u => (t u - μ) * g u)) hcs

end Work.BoseFixB1.WB
