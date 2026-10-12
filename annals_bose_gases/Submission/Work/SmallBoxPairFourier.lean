import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxPairIdent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SESSION-277 — D1 item (c2): the FOURIER side

The explicit value of the Fourier transform of the pair density,
`𝓕 (fun v => ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ)) (-u)`, in the position-space form matching
`core_identity`.  Route: `Real.fourier_eq'`, the definition of `pairFibreDens` (a `z`-integral),
Fubini, the per-`z` translation substitution `v ↦ v + z`, Fubini back, and finally the
restriction of the two integrals to `acube ℓ` (the bump `χ_ℓ` vanishes outside).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution FourierTransform

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The pair-density Fourier kernel `χ(z+v)χ(z)Q(z+v,z)` vanishes off the compact set
`{(v,z) : ‖v‖ ≤ √3 ℓ, z ∈ acube ℓ}`. -/
lemma supp_pairKernel {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    {i j : Fin (p + 2)} :
    HasCompactSupport (fun q : ℝ³ × ℝ³ =>
      chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2) := by
  refine HasCompactSupport.intro (K := (closedBall (0 : ℝ³) (Real.sqrt 3 * ℓ)).prod (acube ℓ)) ?_ ?_
  · exact (isCompact_closedBall _ _).prod (acube_compact hℓ)
  · intro q hq
    by_cases hz : chiScale ℓ q.2 = 0
    · rw [hz]; ring
    · have hzc : q.2 ∈ acube ℓ := chiScale_mem_acube hℓ hz
      have hyv : Real.sqrt 3 * ℓ < ‖q.1‖ := by
        by_contra hcon
        exact hq ⟨by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith, hzc⟩
      have hzn : ‖q.2‖ ≤ ℓ / 2 := chiScale_support_le hℓ hz
      have h1 : ‖q.1‖ ≤ ‖q.2 + q.1‖ + ‖q.2‖ := by
        have h := norm_add_le (q.2 + q.1) (-(q.2))
        have h' : (q.2 + q.1) + (-(q.2)) = q.1 := by abel
        simpa [h', norm_neg] using h
      have h3 : (1 : ℝ) < Real.sqrt 3 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hlt : ℓ < Real.sqrt 3 * ℓ := by nlinarith [hℓ, h3]
      have hz2 : chiScale ℓ (q.2 + q.1) = 0 := by
        refine not_ne_iff.mp fun h => absurd (chiScale_support_le hℓ h) (not_le.mpr ?_)
        linarith
      rw [hz2]; ring

/-- The same kernel times the Fourier phase still has compact support. -/
lemma supp_pairKernelPhase {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    {i j : Fin (p + 2)} (u : ℝ³) :
    HasCompactSupport (fun q : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u q.1 : ℝ) : ℂ))
        * ((chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2 : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := (closedBall (0 : ℝ³) (Real.sqrt 3 * ℓ)).prod (acube ℓ)) ?_ ?_
  · exact (isCompact_closedBall _ _).prod (acube_compact hℓ)
  · intro q hq
    by_cases hz : chiScale ℓ q.2 = 0
    · rw [hz]; simp only [zero_mul, mul_zero, Complex.ofReal_zero]
    · have hzc : q.2 ∈ acube ℓ := chiScale_mem_acube hℓ hz
      have hyv : Real.sqrt 3 * ℓ < ‖q.1‖ := by
        by_contra hcon
        exact hq ⟨by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith, hzc⟩
      have hzn : ‖q.2‖ ≤ ℓ / 2 := chiScale_support_le hℓ hz
      have h1 : ‖q.1‖ ≤ ‖q.2 + q.1‖ + ‖q.2‖ := by
        have h := norm_add_le (q.2 + q.1) (-(q.2))
        have h' : (q.2 + q.1) + (-(q.2)) = q.1 := by abel
        simpa [h', norm_neg] using h
      have h3 : (1 : ℝ) < Real.sqrt 3 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hlt : ℓ < Real.sqrt 3 * ℓ := by nlinarith [hℓ, h3]
      have hz2 : chiScale ℓ (q.2 + q.1) = 0 := by
        refine not_ne_iff.mp fun h => absurd (chiScale_support_le hℓ h) (not_le.mpr ?_)
        linarith
      rw [hz2]; simp only [zero_mul, Complex.ofReal_zero, mul_zero]

/-- The `(y,z)`-form kernel `χ(y)χ(z)Q(y,z)` (times the phase) has compact support. -/
lemma supp_pairKernelYZ {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    {i j : Fin (p + 2)} (u : ℝ³) :
    HasCompactSupport (fun q : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))
        * ((chiScale ℓ q.2 * chiScale ℓ q.1 * pairFibreFun ℓ Φ i j q.2 q.1 : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := (acube ℓ).prod (acube ℓ))
    ((acube_compact hℓ).prod (acube_compact hℓ)) ?_
  intro q hq
  by_cases hy : chiScale ℓ q.2 = 0
  · rw [hy]; simp only [zero_mul, mul_zero, Complex.ofReal_zero]
  · have hyc : q.2 ∈ acube ℓ := chiScale_mem_acube hℓ hy
    by_cases hz : chiScale ℓ q.1 = 0
    · rw [hz]; simp only [zero_mul, mul_zero, Complex.ofReal_zero]
    · have hzc : q.1 ∈ acube ℓ := chiScale_mem_acube hℓ hz
      exact absurd ⟨hzc, hyc⟩ hq

/-- **The Fourier transform of the pair density** (the second half of the D1 `(c2)`
identification): for `i ≠ j`,

`𝓕 (pairFibreDens) (-u) = ∫_{acube}∫_{acube} χ(y)χ(z)e^{i⟨2πu, y-z⟩}·pairFibreFun(y,z)`. -/
theorem fourier_pairFibreDens {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) {i j : Fin (p + 2)} (hij : i ≠ j) (u : ℝ³) :
    𝓕 (fun v => ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ)) (-u)
      = ∫ y in acube ℓ, ∫ z in acube ℓ,
          (chiScale ℓ y : ℂ) * (chiScale ℓ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ ((2 * π : ℝ) • u) (y - z) : ℝ) : ℂ))
            * ((pairFibreFun ℓ Φ i j y z : ℝ) : ℂ) := by
  have hQc : Continuous (Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z)) :=
    (contDiff_pairFibreFun hℓ i j hij hΦc).continuous
  have hχc : Continuous (chiScale ℓ) := chiScale_continuous ℓ
  have hEc : Continuous (fun v : ℝ³ => Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))) := by
    refine Complex.continuous_exp.comp ?_
    have h1 : Continuous (fun v : ℝ³ => ((2 * π * inner ℝ u v : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_const : Continuous (fun _ : ℝ³ => (2 * π : ℝ))).mul
          (continuous_inner.comp (continuous_const.prodMk continuous_id)))
    exact (continuous_const : Continuous (fun _ : ℝ³ => (Complex.I : ℂ))).mul h1
  -- Step 1: the Fourier integral
  have hFourier : 𝓕 (fun v => ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ)) (-u)
      = ∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
          * ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    rw [show (-2 * Real.pi * inner ℝ v (-u)) = 2 * Real.pi * inner ℝ u v from by
      rw [inner_neg_right, real_inner_comm v u]
      ring]
    rw [smul_eq_mul]
    ring
  -- Step 2: the pair density as an unrestricted z-integral
  have hunres : ∀ v : ℝ³, ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ)
      = ∫ z, ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ) := by
    intro v
    have hφc : Continuous (fun z : ℝ³ =>
        chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z) := by
      have h2 : Continuous (fun z : ℝ³ =>
          Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z) (z + v, z)) :=
        hQc.comp ((continuous_id.add continuous_const).prodMk continuous_id)
      exact ((hχc.comp (continuous_id.add continuous_const)).mul
        (hχc.comp continuous_id)).mul (by simpa only [Function.uncurry] using h2)
    have hcast : ((∫ z in acube ℓ,
          chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ)
        = ∫ z in acube ℓ,
          ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ) :=
      (Complex.ofRealCLM.integral_comp_comm (μ := (volume : Measure ℝ³).restrict (acube ℓ))
        (φ := fun z : ℝ³ =>
          chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z)
        (ContinuousOn.integrableOn_compact (acube_compact hℓ) hφc.continuousOn)).symm
    have hunres' : (∫ z in acube ℓ,
          ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ))
        = ∫ z, ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
      have hχz : chiScale ℓ z = 0 := not_ne_iff.mp fun h => hz (chiScale_mem_acube hℓ h)
      rw [show chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z = 0 from by
        rw [hχz]; ring, Complex.ofReal_zero]
    rw [pairFibreDens, hcast, hunres']

  -- Step 3: Fubini (v, z)
  have hHHc : Continuous (Function.uncurry (fun v z : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ))) := by
    change Continuous (fun q : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u q.1 : ℝ) : ℂ))
        * ((chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2 : ℝ) : ℂ))
    have h2 : Continuous (fun q : ℝ³ × ℝ³ =>
        Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z) (q.2 + q.1, q.2)) :=
      hQc.comp ((continuous_snd.add continuous_fst).prodMk continuous_snd)
    exact (hEc.comp continuous_fst).mul (Complex.continuous_ofReal.comp
      (((hχc.comp (continuous_snd.add continuous_fst)).mul (hχc.comp continuous_snd)).mul
        (by simpa only [Function.uncurry] using h2)))
  have hInt3 : Integrable (Function.uncurry (fun v z : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³]
    exact hHHc.integrable_of_hasCompactSupport (by
      change HasCompactSupport (fun q : ℝ³ × ℝ³ =>
        Complex.exp (Complex.I * ((2 * π * inner ℝ u q.1 : ℝ) : ℂ))
          * ((chiScale ℓ (q.2 + q.1) * chiScale ℓ q.2 * pairFibreFun ℓ Φ i j (q.2 + q.1) q.2 : ℝ) : ℂ))
      exact supp_pairKernelPhase (ℓ := ℓ) hℓ (Φ := Φ) (i := i) (j := j) u)
  have hstep1 : (∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * (∫ z, ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ)))
      = ∫ z, ∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
          * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ) := by
    rw [show (∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
          * (∫ z, ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ)))
        = ∫ v, ∫ z, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
          * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun v => by
        simp only []
        rw [MeasureTheory.integral_const_mul])]
    exact MeasureTheory.integral_integral_swap hInt3
  -- Step 4: the per-z translation substitution
  have hstep2 : ∀ z : ℝ³, (∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ))
      = ∫ y, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ) := by
    intro z
    rw [show (fun v : ℝ³ => Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
          * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ))
        = fun v : ℝ³ => (fun y : ℝ³ => Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)) (v + z) from
      funext fun v => by
        simp only []
        rw [add_sub_cancel_right, add_comm z v]]
    exact MeasureTheory.integral_add_right_eq_self (fun y : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)) z
  -- Step 5: Fubini back (z, y)
  have hYZc : Continuous (Function.uncurry (fun z y : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ))) := by
    change Continuous (fun q : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))
        * ((chiScale ℓ q.2 * chiScale ℓ q.1 * pairFibreFun ℓ Φ i j q.2 q.1 : ℝ) : ℂ))
    have h2 : Continuous (fun q : ℝ³ × ℝ³ =>
        Function.uncurry (fun y z : ℝ³ => pairFibreFun ℓ Φ i j y z) (q.2, q.1)) :=
      hQc.comp (continuous_snd.prodMk continuous_fst)
    have he : Continuous (fun q : ℝ³ × ℝ³ =>
        Complex.exp (Complex.I * ((2 * π * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))) := by
      refine Complex.continuous_exp.comp ?_
      have h1 : Continuous (fun q : ℝ³ × ℝ³ => ((2 * π * inner ℝ u (q.2 - q.1) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp
          ((continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => (2 * π : ℝ))).mul
            (continuous_inner.comp (continuous_const.prodMk (continuous_snd.sub continuous_fst))))
      exact (continuous_const : Continuous (fun _ : ℝ³ × ℝ³ => (Complex.I : ℂ))).mul h1
    exact he.mul (Complex.continuous_ofReal.comp
      (((hχc.comp continuous_snd).mul (hχc.comp continuous_fst)).mul
        (by simpa only [Function.uncurry] using h2)))
  have hInt4 : Integrable (Function.uncurry (fun z y : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³]
    exact hYZc.integrable_of_hasCompactSupport (by
      change HasCompactSupport (fun q : ℝ³ × ℝ³ =>
        Complex.exp (Complex.I * ((2 * π * inner ℝ u (q.2 - q.1) : ℝ) : ℂ))
          * ((chiScale ℓ q.2 * chiScale ℓ q.1 * pairFibreFun ℓ Φ i j q.2 q.1 : ℝ) : ℂ))
      exact supp_pairKernelYZ (ℓ := ℓ) hℓ (Φ := Φ) (i := i) (j := j) u)
  have hstep3 : (∫ z, ∫ y, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ))
      = ∫ y, ∫ z, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ) :=
    MeasureTheory.integral_integral_swap hInt4
  -- Step 6: restrict the y- and z-integrals to the cube
  have hstep4 : (∫ y, ∫ z, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ))
      = ∫ y in acube ℓ, ∫ z in acube ℓ,
          Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
            * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube ℓ) (f := fun y : ℝ³ =>
      ∫ z, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)) (by
      intro y hy
      have hχy : chiScale ℓ y = 0 := not_ne_iff.mp fun h => hy (chiScale_mem_acube hℓ h)
      have hz : (fun z : ℝ³ => Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
          * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
        funext z; rw [hχy]; simp only [zero_mul, mul_zero, Complex.ofReal_zero]
      rw [hz, MeasureTheory.integral_zero])]
    congr 1
    funext y
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube ℓ) (f := fun z : ℝ³ =>
      Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ)) (by
      intro z hz
      have hχz : chiScale ℓ z = 0 := not_ne_iff.mp fun h => hz (chiScale_mem_acube hℓ h)
      rw [hχz]; simp only [zero_mul, mul_zero, Complex.ofReal_zero])]
  rw [hFourier,
    show (∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * ((pairFibreDens ℓ Φ i j v : ℝ) : ℂ))
      = ∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * (∫ z, ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall fun v => by
        simp only []
        rw [hunres v]),
    hstep1,
    show (∫ z, ∫ v, Complex.exp (Complex.I * ((2 * π * inner ℝ u v : ℝ) : ℂ))
        * ((chiScale ℓ (z + v) * chiScale ℓ z * pairFibreFun ℓ Φ i j (z + v) z : ℝ) : ℂ))
      = ∫ z, ∫ y, Complex.exp (Complex.I * ((2 * π * inner ℝ u (y - z) : ℝ) : ℂ))
        * ((chiScale ℓ y * chiScale ℓ z * pairFibreFun ℓ Φ i j y z : ℝ) : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun z => hstep2 z),
    hstep3, hstep4]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only []
  rw [show (inner ℝ ((2 * π : ℝ) • u) (y - z) : ℝ) = 2 * π * inner ℝ u (y - z) from
    real_inner_smul_left u (y - z) (2 * π)]
  push_cast
  ring


/-- **The mean formula.**  The `(u,w)`-slot mean of the state equals `ℓ⁶` times the double
`P_iP_{i.succAbove j'}`-mean at the zero-inserted configuration. -/
lemma pairMean_eq {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) (r2 : X p) :
    pairMean ℓ Φ i j' r2
      = ((ℓ ^ 6 : ℝ) : ℂ)
        * (((aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) : ℝ) : ℂ) := by
  -- the inner `z`-integral
  have hinner : ∀ y : ℝ³, (∫ z in acube ℓ, Φ (ins2 i j' y z r2))
      = ℓ ^ 3 * (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2) := by
    intro y
    rw [show (fun z : ℝ³ => Φ (ins2 i j' y z r2)) = fun z : ℝ³ =>
        Φ (Function.update (ins2 i j' y 0 r2) (i.succAbove j') z) from
      funext fun z => congrArg Φ (ins2_update_succ i j' y 0 z r2).symm]
    simp only [aP]
    field_simp
  -- the outer `y`-integral
  have houter : (∫ y in acube ℓ, (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2))
      = ℓ ^ 3 * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (ins2 i j' 0 0 r2) := by
    rw [show (fun y : ℝ³ => (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2))
        = fun y : ℝ³ => (aP ℓ (i.succAbove j') Φ)
            (Function.update (ins2 i j' 0 0 r2) i y) from
      funext fun y => congrArg (aP ℓ (i.succAbove j') Φ)
        (ins2_update_i i j' 0 y 0 r2).symm]
    simp only [aP]
    field_simp
  have hreal : (∫ y in acube ℓ, ∫ z in acube ℓ, Φ (ins2 i j' y z r2))
      = ℓ ^ 6 * (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (ins2 i j' 0 0 r2) := by
    rw [show (fun y : ℝ³ => ∫ z in acube ℓ, Φ (ins2 i j' y z r2))
        = fun y : ℝ³ => ∫ z in acube ℓ, Φ (ins2 i j' y z r2) from rfl]
    rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, Φ (ins2 i j' y z r2))
        = ∫ y in acube ℓ, ℓ ^ 3 * (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2) from
      integral_congr_ae (Filter.Eventually.of_forall fun y => hinner y)]
    rw [show (∫ y in acube ℓ, ℓ ^ 3 * (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2))
        = ℓ ^ 3 * (∫ y in acube ℓ, (aP ℓ (i.succAbove j') Φ) (ins2 i j' y 0 r2)) from
      MeasureTheory.integral_const_mul _ _]
    rw [houter]
    ring
  have hconst : (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (ins2 i j' 0 0 r2)
      = (aP ℓ i (aP ℓ (i.succAbove j') Φ)) (rest2 i j' r2) := by
    rw [show ins2 i j' 0 0 r2 = Function.update (rest2 i j' r2) i (0 : ℝ³) from
      (ins2_update_i i j' 0 0 0 r2).symm]
    exact aP_const_in_coord hℓ i (aP_continuous hℓ (i.succAbove j') hΦc) (rest2 i j' r2) 0
  have hcast1 : ((∫ y in acube ℓ, ∫ z in acube ℓ, Φ (ins2 i j' y z r2) : ℝ) : ℂ)
      = (∫ y in acube ℓ, ((∫ z in acube ℓ, Φ (ins2 i j' y z r2) : ℝ) : ℂ)) := by
    refine (Complex.ofRealCLM.integral_comp_comm (μ := (volume : Measure ℝ³).restrict (acube ℓ))
      (φ := fun y : ℝ³ => ∫ z in acube ℓ, Φ (ins2 i j' y z r2)) ?_).symm
    have hc : Continuous (fun y : ℝ³ => ∫ z in acube ℓ, Φ (ins2 i j' y z r2)) :=
      continuous_parametric_integral_of_continuous (f := fun (y : ℝ³) (z : ℝ³) =>
        Φ (ins2 i j' y z r2)) (by
          change Continuous (fun q : ℝ³ × ℝ³ => Φ (ins2 i j' q.1 q.2 r2))
          exact hΦc.comp ((contDiff_ins2 i j').continuous.comp
            ((continuous_fst.prodMk continuous_snd).prodMk continuous_const)))
        (acube_compact hℓ)
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ) hc.continuousOn
  have hcast2 : ∀ y : ℝ³, ((∫ z in acube ℓ, Φ (ins2 i j' y z r2) : ℝ) : ℂ)
      = ∫ z in acube ℓ, ((Φ (ins2 i j' y z r2) : ℝ) : ℂ) := by
    intro y
    refine (Complex.ofRealCLM.integral_comp_comm (μ := (volume : Measure ℝ³).restrict (acube ℓ))
      (φ := fun z : ℝ³ => Φ (ins2 i j' y z r2)) ?_).symm
    have hc : Continuous (fun z : ℝ³ => Φ (ins2 i j' y z r2)) :=
      hΦc.comp (continuous_ins2_snd i j' y r2)
    exact ContinuousOn.integrableOn_compact (acube_compact hℓ) hc.continuousOn
  rw [pairMean]
  rw [show (∫ y in acube ℓ, ∫ z in acube ℓ, ((Φ (ins2 i j' y z r2) : ℝ) : ℂ))
      = ∫ y in acube ℓ, ((∫ z in acube ℓ, Φ (ins2 i j' y z r2) : ℝ) : ℂ) from
    integral_congr_ae (Filter.Eventually.of_forall fun y => (hcast2 y).symm)]
  rw [← hcast1, hreal, hconst]
  push_cast
  ring


end BoseGases
end Submission
