import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.OneBodyKin.SymAPI
import Submission.Work.OneBodyKin.continuous_kinFT
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin.Cross

open MeasureTheory
open scoped Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- `kinFTsq ψ q = ‖kinFT ψ q‖²`, the `p`-convention kinetic energy density of `ψ` at `q`. -/
noncomputable abbrev kinFTsq (ψ : ℝ³ → ℝ) (q : ℝ³) : ℝ :=
  ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2

/-- The symmetrised `profHat`-sum `(1/2)(profHat(ℓ•(p−q)) + profHat(ℓ•(p+q)))`. -/
noncomputable abbrev symPQ (ℓ : ℝ) (p q : ℝ³) : ℝ :=
  (1 / 2) * (Work.OneBodyKin.profHat (ℓ • (p - q)) + Work.OneBodyKin.profHat (ℓ • (p + q)))

/-- `q ↦ boxHat 1 (ℓ • q)` is continuous: a dominated parameter integral of `cos` over the
unit cube `acube 1`. -/
lemma continuous_boxHat_one_smul (ℓ : ℝ) :
    Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat 1 (ℓ • q)) := by
  simp only [Work.OneBodyKin.boxHat]
  refine continuous_of_dominated (bound := fun _ : ℝ³ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · intro q
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · intro q
    filter_upwards with a
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  · exact integrableOn_const (C := (1 : ℝ))
      (ne_of_lt (Submission.BoseGases.acube_lt_top 1 (by norm_num))) (by simp)
  · filter_upwards with a
    fun_prop

/-- Fubini exchange of the `p`- and `q`-integrations of the symbol integrand, written with the
symmetrised `profHat`-sum `S(p,q) = (1/2)(profHat(ℓ•(p−q)) + profHat(ℓ•(p+q)))·boxHat 1 (ℓ•q)`:
for `ℓ > 0`, `p ↦ F‖p‖ ∈ L¹`, `ψ` smooth with compact support,

`∫_p F‖p‖ profHat(ℓ•p) (∫_q S(p,q)‖kinFT ψ q‖²) = ∫_q boxHat 1 (ℓ•q) ‖kinFT ψ q‖² (∫_p F‖p‖ profHat(ℓ•p) S(p,q))`.

Route: `MeasureTheory.integral_integral_swap` for the joint function
`Ψ p q = F ‖p‖ * profHat (ℓ•p) * ((1/2)(profHat(ℓ•(p−q)) + profHat(ℓ•(p+q)))) * boxHat 1 (ℓ•q) * ‖kinFT ψ q‖²`
on `volume.prod volume`. Dominating function: `C * ‖F ‖p‖‖ * ‖kinFT ψ q‖²` with
`C = (∫|χ|)²` (from `Work.OneBodyKin.profHat_abs_le_mass` and
`Work.OneBodyKin.abs_boxHat_le` at `ℓ = 1`), a product of two `L¹` functions
(`MeasureTheory.Integrable.mul_prod`, `Work.BSKinetic.integrable_kinFT_sq`); measurability from
`hFi.aestronglyMeasurable` and continuity of `profHat`
(`Work.OneBodyKin.continuous_profHat`), of `q ↦ boxHat 1 (ℓ•q)` (a dominated parameter integral
of `cos`) and of `‖kinFT ψ ·‖²` (`Work.OneBodyKin.continuous_kinFT`). Finally pull
`boxHat 1 (ℓ•q) * ‖kinFT ψ q‖²` out of the `p`-integral with `MeasureTheory.integral_mul_const`. -/
theorem symbol_pq_swap {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
        F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) *
          (∫ q : EuclideanSpace ℝ (Fin 3),
            ((1 / 2) * (Work.OneBodyKin.profHat (ℓ • (p - q)) +
              Work.OneBodyKin.profHat (ℓ • (p + q)))) *
              Work.OneBodyKin.boxHat 1 (ℓ • q) *
              ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2))
      = ∫ q : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.boxHat 1 (ℓ • q) *
            ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 *
            (∫ p : EuclideanSpace ℝ (Fin 3),
              F ‖p‖ * Work.OneBodyKin.profHat (ℓ • p) *
                ((1 / 2) * (Work.OneBodyKin.profHat (ℓ • (p - q)) +
                  Work.OneBodyKin.profHat (ℓ • (p + q))))) := by
  change (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
      (∫ q : ℝ³, symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q))
    = ∫ q : ℝ³, boxHat 1 (ℓ • q) * kinFTsq ψ q *
      (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * symPQ ℓ p q)
  -- the complexification of `ψ` is smooth with compact support, hence integrable
  have hψc : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hcsc : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) :=
    hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hψint : Integrable (fun z : ℝ³ => (ψ z : ℂ)) :=
    hψc.continuous.integrable_of_hasCompactSupport hcsc
  have hkin : Continuous (fun q : ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q) :=
    Work.OneBodyKin.continuous_kinFT hψint
  have hkcont : Continuous (fun q : ℝ³ => kinFTsq ψ q) := by
    have hh : Continuous (fun q : ℝ³ =>
        ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ *
          ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖) :=
      hkin.norm.mul hkin.norm
    simpa only [kinFTsq, pow_two] using hh
  have hkint : Integrable (fun q : ℝ³ => kinFTsq ψ q) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  -- the mass constant
  set C : ℝ := ∫ z : ℝ³, |Submission.BoseGases.chi z| with hC
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun z => abs_nonneg _)
  have hprof : ∀ p : ℝ³, |profHat p| ≤ C := by
    intro p; rw [hC]; exact profHat_abs_le_mass p
  have hbox : ∀ q : ℝ³, |boxHat 1 (ℓ • q)| ≤ 1 := by
    intro q
    have h := abs_boxHat_le (ℓ := 1) (by norm_num : (0 : ℝ) ≤ 1) (ℓ • q)
    simpa using h
  have hkT : ∀ q : ℝ³, 0 ≤ kinFTsq ψ q := fun q => by rw [kinFTsq]; positivity
  -- the joint integrand
  let Ψ : ℝ³ → ℝ³ → ℝ := fun p q =>
    (F ‖p‖ * profHat (ℓ • p)) * (symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q)
  have hA : ∀ p q : ℝ³, |symPQ ℓ p q| ≤ C := by
    intro p q
    have h1 := hprof (ℓ • (p - q))
    have h2 := hprof (ℓ • (p + q))
    have hsq : symPQ ℓ p q =
        (1 / 2) * (profHat (ℓ • (p - q)) + profHat (ℓ • (p + q))) := rfl
    rw [hsq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
    calc (1 / 2) * |profHat (ℓ • (p - q)) + profHat (ℓ • (p + q))|
        ≤ (1 / 2) * (|profHat (ℓ • (p - q))| + |profHat (ℓ • (p + q))|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ (1 / 2) * (C + C) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
      _ = C := by ring
  -- measurability of the uncurried integrand
  have h_meas : AEStronglyMeasurable (Function.uncurry Ψ) (volume.prod volume) := by
    have hP : AEStronglyMeasurable
        (fun z : ℝ³ × ℝ³ => F ‖z.1‖ * profHat (ℓ • z.1)) (volume.prod volume) :=
      (hFi.aestronglyMeasurable.mul
        ((continuous_profHat.comp (continuous_const_smul ℓ)).aestronglyMeasurable)).comp_fst
    have hQc : Continuous (fun z : ℝ³ × ℝ³ => (1 / 2 : ℝ) *
        (profHat (ℓ • (z.1 - z.2)) + profHat (ℓ • (z.1 + z.2)))) := by
      have h1 : Continuous (fun z : ℝ³ × ℝ³ => profHat (ℓ • (z.1 - z.2))) :=
        continuous_profHat.comp
          ((continuous_const_smul ℓ).comp (continuous_fst.sub continuous_snd))
      have h2 : Continuous (fun z : ℝ³ × ℝ³ => profHat (ℓ • (z.1 + z.2))) :=
        continuous_profHat.comp
          ((continuous_const_smul ℓ).comp (continuous_fst.add continuous_snd))
      exact Continuous.const_mul (Continuous.add h1 h2) (1 / 2)
    have hQc' : Continuous (fun z : ℝ³ × ℝ³ => symPQ ℓ z.1 z.2) := hQc
    have hRc : Continuous
        (fun z : ℝ³ × ℝ³ => boxHat 1 (ℓ • z.2) * kinFTsq ψ z.2) := by
      have hb : Continuous (fun z : ℝ³ × ℝ³ => boxHat 1 (ℓ • z.2)) :=
        (continuous_boxHat_one_smul ℓ).comp
          (continuous_snd : Continuous (Prod.snd : ℝ³ × ℝ³ → ℝ³))
      have hk : Continuous (fun z : ℝ³ × ℝ³ => kinFTsq ψ z.2) :=
        hkcont.comp (continuous_snd : Continuous (Prod.snd : ℝ³ × ℝ³ → ℝ³))
      exact hb.mul hk
    have hG : AEStronglyMeasurable
        (fun z : ℝ³ × ℝ³ =>
          (F ‖z.1‖ * profHat (ℓ • z.1)) *
            (symPQ ℓ z.1 z.2 * (boxHat 1 (ℓ • z.2) * kinFTsq ψ z.2)))
        (volume.prod volume) :=
      hP.mul (hQc'.aestronglyMeasurable.mul hRc.aestronglyMeasurable)
    refine hG.congr ?_
    filter_upwards with z
    obtain ⟨p, q⟩ := z
    simp only [Function.uncurry, Ψ]
    ring
  -- integrability of the dominant function
  have hdom : Integrable
      (fun z : ℝ³ × ℝ³ => (C ^ 2 * ‖F ‖z.1‖‖) * kinFTsq ψ z.2) (volume.prod volume) :=
    ((hFi.norm).const_mul (C ^ 2)).mul_prod hkint
  -- the pointwise bound
  have hbound : ∀ᵐ z ∂(volume.prod volume), ‖Function.uncurry Ψ z‖ ≤
      (C ^ 2 * ‖F ‖z.1‖‖) * kinFTsq ψ z.2 := by
    filter_upwards with z
    obtain ⟨p, q⟩ := z
    have h1 : ‖F ‖p‖ * profHat (ℓ • p)‖ ≤ ‖F ‖p‖‖ * C := by
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprof (ℓ • p)) (abs_nonneg _)
    have h2 : ‖symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q‖ ≤ C * kinFTsq ψ q := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hkT q)]
      calc |symPQ ℓ p q| * |boxHat 1 (ℓ • q)| * kinFTsq ψ q
          ≤ (C * 1) * kinFTsq ψ q := by
            refine mul_le_mul_of_nonneg_right ?_ (hkT q)
            exact mul_le_mul (hA p q) (hbox q) (abs_nonneg _) hC0
        _ = C * kinFTsq ψ q := by ring
    have hΨpq : Function.uncurry Ψ (p, q) =
        (F ‖p‖ * profHat (ℓ • p)) * (symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q) := by
      simp only [Function.uncurry, Ψ]
    rw [hΨpq]
    calc ‖(F ‖p‖ * profHat (ℓ • p)) * (symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q)‖
        ≤ ‖F ‖p‖ * profHat (ℓ • p)‖ * ‖symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q‖ :=
          norm_mul_le _ _
      _ ≤ (‖F ‖p‖‖ * C) * (C * kinFTsq ψ q) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (C ^ 2 * ‖F ‖p‖‖) * kinFTsq ψ q := by ring
  have h_int : Integrable (Function.uncurry Ψ) (volume.prod volume) :=
    hdom.mono' h_meas hbound
  have hswap := MeasureTheory.integral_integral_swap h_int
  have hL : (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) *
        (∫ q : ℝ³, symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q))
      = ∫ p : ℝ³, ∫ q : ℝ³, Ψ p q := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change F ‖p‖ * profHat (ℓ • p) *
        (∫ q : ℝ³, symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q) = ∫ q : ℝ³, Ψ p q
    rw [show (∫ q : ℝ³, Ψ p q) = (F ‖p‖ * profHat (ℓ • p)) *
          (∫ q : ℝ³, symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q) from by
      change (∫ q : ℝ³, (F ‖p‖ * profHat (ℓ • p)) *
          (symPQ ℓ p q * boxHat 1 (ℓ • q) * kinFTsq ψ q)) = _
      exact integral_const_mul _ _]
  have hR : (∫ q : ℝ³, boxHat 1 (ℓ • q) * kinFTsq ψ q *
        (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * symPQ ℓ p q))
      = ∫ q : ℝ³, ∫ p : ℝ³, Ψ p q := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    change boxHat 1 (ℓ • q) * kinFTsq ψ q *
        (∫ p : ℝ³, F ‖p‖ * profHat (ℓ • p) * symPQ ℓ p q) = ∫ p : ℝ³, Ψ p q
    rw [show (∫ p : ℝ³, Ψ p q) = ∫ p : ℝ³, (boxHat 1 (ℓ • q) * kinFTsq ψ q) *
          (F ‖p‖ * profHat (ℓ • p) * symPQ ℓ p q) from by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Ψ]
      ring]
    rw [integral_const_mul]
  rw [hL, hR, hswap]

end Work.OneBodyKin.Cross
