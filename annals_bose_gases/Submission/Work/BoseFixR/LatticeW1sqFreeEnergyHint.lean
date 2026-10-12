import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixR.ChiR0Defs
import Submission.Work.BoseFixR.SmoothApproxGradient
import Submission.Work.BoseFixR.mass_le_W1omega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeW1sqFreeEnergyHint` — the free-energy (completion of squares) hint

The target is the sharp Dirichlet/AM–GM free-energy inequality for an `L¹` kernel `W` whose
Fourier transform satisfies the finiteness hypothesis `hint`:

`2 ∫ W ψ - ∫ ‖∇ψ‖² ≤ (2π)⁻³ ∫ q, Ŵ(q)²/‖q‖²`

for every `C¹` compactly supported real test function `ψ`, where `Ŵ = Work.BoseFixR.chat W`
is the `(2π)⁻¹`-convention (cosine) Fourier transform of `W`.

## Route (all in the `kinFT`/`chat` convention)

* `LatFreeMultL1`: for `W ∈ L¹` even and `u ∈ C^∞` compactly supported,
  `∫ W u = (2π)⁻³ ∫ q, Ŵ(q) û(q)`, from the one-sided multiplication formula
  (`plancherel_one_sided_contDiff`), the scaling substitution `p = (2π)⁻¹q` and the two
  reality facts (even `W` has a real Fourier transform, real `u` has a conjugate-symmetric one).
* `LatFreeKineticKinFT`: `∫ ‖∇u‖² = (2π)⁻³ ∫ q, ‖q‖²‖kinFT u q‖²` for `u ∈ C^∞` compactly
  supported (from `Work.OneBodyKin.dSpace_eq_fourier` plus the orthonormal-basis identity
  `‖∇u x‖² = Σ_k (∂_k u x)²`), together with the integrability of the weight `kinW u`.
* The pointwise completion of squares `2 Ŵ(q)û(q) - kinW u q ≤ Ŵ(q)²/‖q‖²` for `q ≠ 0`
  (AM–GM), integrated with `integral_mono_ae`; the point `q = 0` is null.
* The `C¹` case follows by mollification: `ψ ⋆ ρ_n → ψ` uniformly and
  `∇(ψ ⋆ ρ_n) → ∇ψ` in `L²`, and the (constant) right-hand side passes to the limit.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Fourier-side vocabulary -/

/-- `chat W q` is the real part of `𝓕 W` at `(2π)⁻¹ q`. -/
lemma chat_eq_fourier_re (W : E3 → ℝ) (q : E3) :
    chat W q = (FourierTransform.fourier (fun y => (W y : ℂ)) ((2 * Real.pi)⁻¹ • q)).re := by
  rw [chat, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]

/-- `(2π)⁻¹ • (2π • q) = q`. -/
lemma inv_two_pi_smul_two_pi_smul (q : E3) :
    (2 * Real.pi)⁻¹ • ((2 * Real.pi) • q) = q :=
  inv_smul_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) q

/-- **The Fourier transform of an even real function is real.** -/
lemma fourier_im_eq_zero_of_even {W : E3 → ℝ} (hWe : ∀ x, W (-x) = W x) (q : E3) :
    (FourierTransform.fourier (fun x => (W x : ℂ)) q).im = 0 := by
  set f : E3 → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * inner ℝ v q) * Complex.I)
    * (W v : ℂ) with hf
  have hFq : FourierTransform.fourier (fun x => (W x : ℂ)) q = ∫ v, f v := by
    rw [Real.fourier_eq']
    simp only [hf, smul_eq_mul]
  have hconj : (∫ v, f (-v)) = conj (∫ v, f v) := by
    rw [← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards with v
    simp only [hf]
    have h1 : -2 * Real.pi * inner ℝ (-v) q = 2 * Real.pi * inner ℝ v q := by
      rw [inner_neg_left]; ring
    rw [h1, hWe v, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  have hneg : (∫ v, f (-v)) = ∫ v, f v := MeasureTheory.integral_neg_eq_self f volume
  have key : FourierTransform.fourier (fun x => (W x : ℂ)) q
      = conj (FourierTransform.fourier (fun x => (W x : ℂ)) q) := by
    rw [hFq, ← hconj, hneg]
  have him : (FourierTransform.fourier (fun x => (W x : ℂ)) q).im
      = -(FourierTransform.fourier (fun x => (W x : ℂ)) q).im := by
    have := congrArg Complex.im key
    simpa using this
  linarith

/-- **Evenness makes `chat` the full Fourier transform**: `𝓕W p = (chat W (2π p) : ℂ)`. -/
lemma fourier_eq_chat_of_even {W : E3 → ℝ} (hWe : ∀ x, W (-x) = W x) (p : E3) :
    FourierTransform.fourier (fun x => (W x : ℂ)) p
      = ((chat W ((2 * Real.pi) • p) : ℝ) : ℂ) := by
  have him := fourier_im_eq_zero_of_even hWe p
  have hchat : chat W ((2 * Real.pi) • p)
      = (FourierTransform.fourier (fun x => (W x : ℂ)) p).re := by
    rw [chat_eq_fourier_re, inv_two_pi_smul_two_pi_smul]
  apply Complex.ext
  · rw [hchat]; simp
  · simp [him]

/-- **Real functions have conjugate-symmetric Fourier transforms**:
`𝓕 u (-p) = conj (𝓕 u p)`. -/
lemma fourier_neg_eq_conj_ofReal {u : E3 → ℝ} (p : E3) :
    FourierTransform.fourier (fun x => (u x : ℂ)) (-p)
      = conj (FourierTransform.fourier (fun x => (u x : ℂ)) p) := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with v
  simp only [smul_eq_mul, inner_neg_right, Complex.conj_ofReal, map_mul, ← Complex.exp_conj,
    map_mul]
  congr 1
  rw [Complex.conj_I]
  push_cast
  ring

/-- **The `(2π)⁻¹`-scaling substitution for integrals on `ℝ³`.** -/
lemma integral_scale_two_pi (f : E3 → ℝ) :
    (∫ p, f p) = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, f ((2 * Real.pi)⁻¹ • q) := by
  have h3 : Module.finrank ℝ E3 = 3 := by
    rw [finrank_euclideanSpace_fin]
  have h := Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure E3)) f
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  rw [show (2 * Real.pi) ^ (Module.finrank ℝ E3)
      = (2 * Real.pi) ^ 3 from by rw [h3]] at h
  have hne : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  rw [smul_eq_mul] at h
  rw [h, inv_mul_cancel_left₀ hne]

/-- `‖∇u x‖²` is the sum of the squares of the coordinate derivatives. -/
lemma gradient_norm_sq_eq_sum (u : E3 → ℝ) (x : E3) :
    ‖gradient u x‖ ^ 2
      = ∑ k : Fin 3, (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  rw [← Submission.BoseGases.sum_inner_kcStdBasis_sq (gradient u x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_gradient_left]

/-- **The one-sided multiplication formula for `C^∞` compactly supported `g`.**  This is
`Commons.Analysis.Fourier.plancherel_one_sided_smooth` with the (analytic) smoothness
hypothesis weakened to `C^∞`, which is what a smooth compactly supported test function
provides. -/
lemma plancherel_one_sided_contDiff {f g : E3 → ℂ}
    (hf : MeasureTheory.Integrable f) (hgc : ContDiff ℝ (⊤ : ENat) g)
    (hgs : HasCompactSupport g) :
    (∫ x, f x * g x) = ∫ p, FourierTransform.fourier f p * FourierTransform.fourier g (-p) := by
  let gs : 𝓢(E3, ℂ) := hgs.toSchwartzMap hgc
  have hgs_coe : ∀ x, gs x = g x := fun _ => rfl
  have hgs_eq : (gs : E3 → ℂ) = g := funext hgs_coe
  let hinv : E3 → ℂ := fun x => (𝓕⁻ gs : 𝓢(E3, ℂ)) x
  have hFourier : 𝓕 hinv = fun x => g x := by
    rw [← SchwartzMap.fourier_coe (𝓕⁻ gs), FourierTransform.fourier_fourierInv_eq]
    exact hgs_eq
  have hInv : ∀ p, hinv p = FourierTransform.fourier g (-p) := by
    intro p
    change (𝓕⁻ gs : 𝓢(E3, ℂ)) p = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, hgs_eq]
  have hint : MeasureTheory.Integrable hinv := (𝓕⁻ gs).integrable
  have key := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (e := 𝐞) (μ := volume) (ν := volume) (L := innerₗ E3)
    (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar continuous_inner hf hint
  calc (∫ x, f x * g x)
      = ∫ x, f x * (VectorFourier.fourierIntegral 𝐞 volume (innerₗ E3).flip hinv x) := by
          apply integral_congr_ae; filter_upwards with x
          congr 1
          rw [show (innerₗ E3).flip = innerₗ E3 from flip_innerₗ E3]
          change g x = (𝓕 hinv) x
          rw [hFourier]
    _ = ∫ ξ, 𝓕 f ξ * hinv ξ := key.symm
    _ = ∫ p, FourierTransform.fourier f p * FourierTransform.fourier g (-p) := by
          apply integral_congr_ae; filter_upwards with p
          rw [hInv p]

/-! ## 2. Elementary norm facts about the Fourier transform -/

/-- `‖(r : ℂ)‖ = ‖r‖`. -/
lemma norm_ofReal_eq (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  have h : ‖(r : ℂ)‖ ^ 2 = ‖r‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, Real.norm_eq_abs, sq_abs, sq]
  nlinarith [norm_nonneg (r : ℂ), norm_nonneg r]

/-- The Fourier transform of an `L¹` real function is continuous. -/
lemma continuous_fourier_ofReal (W : E3 → ℝ) (hW : MeasureTheory.Integrable W) :
    Continuous (FourierTransform.fourier (fun x : E3 => (W x : ℂ))) :=
  VectorFourier.fourierIntegral_continuous (e := 𝐞) (L := innerₗ E3)
    Real.continuous_fourierChar continuous_inner hW.ofReal

/-- The pointwise bound `‖𝓕W‖ ≤ ‖W‖₁`. -/
lemma norm_fourier_le_integral_norm (W : E3 → ℝ) (p : E3) :
    ‖FourierTransform.fourier (fun x : E3 => (W x : ℂ)) p‖ ≤ ∫ x, ‖W x‖ := by
  rw [Real.fourier_eq']
  calc ‖∫ v, Complex.exp (↑(-2 * Real.pi * inner ℝ v p) * Complex.I) • (W v : ℂ)‖
      ≤ ∫ v, ‖Complex.exp (↑(-2 * Real.pi * inner ℝ v p) * Complex.I) • (W v : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ v, ‖W v‖ := by
        refine integral_congr_ae ?_
        filter_upwards with v
        rw [norm_smul, Complex.norm_exp]
        have hre : (↑(-2 * Real.pi * inner ℝ v p) * Complex.I).re = 0 := by simp
        rw [hre, Real.exp_zero, one_mul, norm_ofReal_eq]

/-! ## 3. Pointwise AM–GM algebra -/

/-- `2 (a / (2 b)) = a / b`. -/
lemma two_mul_div_two_mul_eq (a b : ℝ) : 2 * (a / (2 * b)) = a / b := by
  by_cases hb : b = 0
  · subst hb; simp
  · field_simp

/-- **Completion of squares (AM–GM)**: for `|C| ≤ B` and `q ≠ 0`,
`2 A C - ‖q‖²B² ≤ A²/‖q‖²`. -/
lemma two_mul_mul_sub_sq_le (A C B : ℝ) {q : E3} (hC : |C| ≤ B) (hq : 0 < ‖q‖) :
    2 * (A * C) - ‖q‖ ^ 2 * B ^ 2 ≤ A ^ 2 / ‖q‖ ^ 2 := by
  have hAC : A * C ≤ |A| * B := by
    calc A * C ≤ |A * C| := le_abs_self _
      _ = |A| * |C| := abs_mul A C
      _ ≤ |A| * B := mul_le_mul_of_nonneg_left hC (abs_nonneg A)
  have h1 : 2 * (A * C) ≤ 2 * (|A| * B) := by linarith
  have hs : (0 : ℝ) < ‖q‖ ^ 2 := by positivity
  have h2 : 2 * (|A| * B) ≤ A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 := by
    have h3 : A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 = (A ^ 2 + ‖q‖ ^ 4 * B ^ 2) / ‖q‖ ^ 2 := by
      field_simp
    rw [h3, le_div_iff₀ hs]
    nlinarith [sq_nonneg (|A| - ‖q‖ ^ 2 * B), sq_abs A]
  linarith

/-- The absolute-value form of the same bound: `|A C| ≤ A²/‖q‖² + ‖q‖²B²`. -/
lemma abs_mul_le_div_add (A C B : ℝ) {q : E3} (hC : |C| ≤ B) (hq : 0 < ‖q‖) :
    |A * C| ≤ A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 := by
  have h1 : |A * C| ≤ |A| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hC (abs_nonneg A)
  have hs : (0 : ℝ) < ‖q‖ ^ 2 := by positivity
  have h2 : 2 * (|A| * B) ≤ A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 := by
    have h3 : A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 = (A ^ 2 + ‖q‖ ^ 4 * B ^ 2) / ‖q‖ ^ 2 := by
      field_simp
    rw [h3, le_div_iff₀ hs]
    nlinarith [sq_nonneg (|A| - ‖q‖ ^ 2 * B), sq_abs A]
  have h3 : 0 ≤ A ^ 2 / ‖q‖ ^ 2 + ‖q‖ ^ 2 * B ^ 2 := by positivity
  nlinarith [abs_nonneg (A * C)]

/-! ## 4. The momentum-side abbreviations -/

/-- The momentum-side amplitude `‖kinFT u q‖`. -/
def kinA (u : E3 → ℝ) (q : E3) : ℝ :=
  ‖Submission.BoseGases.kinFT (fun y => (u y : ℂ)) q‖

/-- The momentum-side kinetic weight `‖q‖²‖kinFT u q‖²`. -/
def kinW (u : E3 → ℝ) (q : E3) : ℝ :=
  ‖q‖ ^ 2 * kinA u q ^ 2

lemma kinW_apply (u : E3 → ℝ) (q : E3) :
    kinW u q = ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun y => (u y : ℂ)) q‖ ^ 2 := rfl

/-- `|chat W q| ≤ ‖kinFT W q‖`. -/
lemma abs_chat_le_kinA (W : E3 → ℝ) (q : E3) : |chat W q| ≤ kinA W q := by
  rw [chat, kinA]
  exact Complex.abs_re_le_norm _

/-! ## 5. The multiplication identity for `W ∈ L¹` -/

/-- **The multiplication formula with only `L¹` on the kernel side.** For real even `W ∈ L¹`
and `u ∈ C^∞` compactly supported,
`∫ W u = (2π)⁻³ ∫ q, Ŵ(q) û(q)`. -/
lemma LatFreeMultL1 {W u : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (hWe : ∀ x, W (-x) = W x)
    (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u) :
    (∫ x, W x * u x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, chat W q * chat u q := by
  have huC : ContDiff ℝ (⊤ : ENat) (fun x : E3 => (u x : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ENat))).comp hu
  have hucC : HasCompactSupport (fun x : E3 => (u x : ℂ)) :=
    huc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hkey := plancherel_one_sided_contDiff
    (f := fun x : E3 => (W x : ℂ)) (g := fun x : E3 => (u x : ℂ)) hW.ofReal huC hucC
  -- `𝓕 u (-·)` is integrable (it is a Schwartz function)
  have hFu1 : MeasureTheory.Integrable
      (fun p : E3 => FourierTransform.fourier (fun x : E3 => (u x : ℂ)) (-p)) := by
    let S : 𝓢(E3, ℂ) := hucC.toSchwartzMap huC
    have hcoe : ⇑S = fun x : E3 => (u x : ℂ) := rfl
    have h1 := (𝓕 S).integrable (μ := (volume : Measure E3))
    rw [SchwartzMap.fourier_coe, hcoe] at h1
    refine (h1.comp_smul (R := (-1 : ℝ)) (by norm_num)).congr ?_
    filter_upwards with p
    rw [neg_one_smul]
  -- the complex integrand of the multiplication formula is integrable
  have hIntZ : MeasureTheory.Integrable
      (fun p : E3 => FourierTransform.fourier (fun x : E3 => (W x : ℂ)) p
        * FourierTransform.fourier (fun x : E3 => (u x : ℂ)) (-p)) := by
    refine ((hFu1.norm).const_mul (∫ x, ‖W x‖)).mono' ?_ ?_
    · exact (continuous_fourier_ofReal W hW).aestronglyMeasurable.mul hFu1.aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_fourier_le_integral_norm W p) (norm_nonneg _)
  -- the pointwise identification of the real part
  have hpt : ∀ p : E3, (FourierTransform.fourier (fun x : E3 => (W x : ℂ)) p
        * FourierTransform.fourier (fun x : E3 => (u x : ℂ)) (-p)).re
      = chat W ((2 * Real.pi) • p) * chat u ((2 * Real.pi) • p) := by
    intro p
    rw [fourier_eq_chat_of_even hWe p, fourier_neg_eq_conj_ofReal (u := u) p,
      chat_eq_fourier_re u ((2 * Real.pi) • p), inv_two_pi_smul_two_pi_smul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.conj_re]
  -- the scaling substitution
  have hscale : (∫ p : E3, chat W ((2 * Real.pi) • p) * chat u ((2 * Real.pi) • p))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, chat W q * chat u q := by
    rw [integral_scale_two_pi
      (fun p : E3 => chat W ((2 * Real.pi) • p) * chat u ((2 * Real.pi) • p))]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with q
    rw [smul_smul, mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  -- the complex identity, its real part, and the L¹ reality of the left-hand side
  have hcongr : (∫ x : E3, ((W x : ℂ) * (u x : ℂ)))
      = ∫ x : E3, ((W x * u x : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x =>
      (Complex.ofReal_mul (W x) (u x)).symm)
  have hreal : (∫ x : E3, ((W x : ℂ) * (u x : ℂ))) = ((∫ x : E3, W x * u x : ℝ) : ℂ) :=
    hcongr.trans (integral_ofReal (f := fun x : E3 => W x * u x) (μ := volume))
  have hRe := integral_re hIntZ
  calc (∫ x : E3, W x * u x)
      = (∫ x : E3, (W x : ℂ) * (u x : ℂ)).re := by rw [hreal]; simp
    _ = (∫ p : E3, FourierTransform.fourier (fun x : E3 => (W x : ℂ)) p
          * FourierTransform.fourier (fun x : E3 => (u x : ℂ)) (-p)).re := by rw [hkey]
    _ = ∫ p : E3, (FourierTransform.fourier (fun x : E3 => (W x : ℂ)) p
          * FourierTransform.fourier (fun x : E3 => (u x : ℂ)) (-p)).re := hRe.symm
    _ = ∫ p : E3, chat W ((2 * Real.pi) • p) * chat u ((2 * Real.pi) • p) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, chat W q * chat u q := hscale

/-! ## 6. The free kinetic energy in the `kinFT` convention -/

/-- **The free kinetic identity** for `u ∈ C^∞` compactly supported, together with the
integrability of the momentum-side weight. -/
lemma LatFreeKineticKinFT {u : E3 → ℝ} (hu : ContDiff ℝ (⊤ : ENat) u)
    (huc : HasCompactSupport u) :
    MeasureTheory.Integrable (kinW u)
      ∧ (∫ x, ‖gradient u x‖ ^ 2) = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q, kinW u q) := by
  have huC : ContDiff ℝ (⊤ : ENat) (fun x : E3 => (u x : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ENat))).comp hu
  have hucC : HasCompactSupport (fun x : E3 => (u x : ℂ)) :=
    huc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  -- integrability of the momentum-side integrand in the `𝓕` convention
  have hIntF : MeasureTheory.Integrable
      (fun ξ : E3 => ‖ξ‖ ^ 2 * ‖FourierTransform.fourier (fun x : E3 => (u x : ℂ)) ξ‖ ^ 2) := by
    let S : 𝓢(E3, ℂ) := hucC.toSchwartzMap huC
    have hcoe : ⇑S = fun x : E3 => (u x : ℂ) := rfl
    have hk : ∀ k : Fin 3, MeasureTheory.Integrable (fun ξ : E3 =>
        (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
          * ‖FourierTransform.fourier (fun x : E3 => (u x : ℂ)) ξ‖ ^ 2) := by
      intro k
      have h := Work.SmallBoxBridge.Resolve.integrable_inner_sq_mul_norm_sq
        (FourierTransform.fourier S) (Submission.BoseGases.kcStdBasis k)
      rwa [SchwartzMap.fourier_coe, hcoe] at h
    have hsum : MeasureTheory.Integrable (fun ξ : E3 => ∑ k : Fin 3,
        (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
          * ‖FourierTransform.fourier (fun x : E3 => (u x : ℂ)) ξ‖ ^ 2) :=
      integrable_finsetSum _ (fun k _ => hk k)
    refine hsum.congr ?_
    filter_upwards with ξ
    rw [← Finset.sum_mul, Submission.BoseGases.sum_inner_kcStdBasis_sq]
  -- transfer to the `kinFT` (i.e. `(2π)⁻¹`) convention
  have hInt_kin : MeasureTheory.Integrable (fun q : E3 =>
      ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun y => (u y : ℂ)) q‖ ^ 2) := by
    have hscaled : MeasureTheory.Integrable (fun p : E3 =>
        ‖(2 * Real.pi) • p‖ ^ 2
          * ‖FourierTransform.fourier (fun x : E3 => (u x : ℂ)) p‖ ^ 2) := by
      refine (hIntF.const_mul ((2 * Real.pi) ^ 2)).congr ?_
      filter_upwards with p
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), mul_pow]
      ring
    have hpt : ∀ q : E3,
        ‖(2 * Real.pi) • ((2 * Real.pi)⁻¹ • q)‖ ^ 2
            * ‖FourierTransform.fourier (fun x : E3 => (u x : ℂ)) ((2 * Real.pi)⁻¹ • q)‖ ^ 2
          = ‖q‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun y => (u y : ℂ)) q‖ ^ 2 := by
      intro q
      rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
        smul_inv_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) q]
    exact (hscaled.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)).congr
      (Filter.Eventually.of_forall hpt)
  -- the identity, from `dSpace_eq_fourier` and the coordinate form of `‖∇u‖²`
  have hgrad : (∫ x, ‖gradient u x‖ ^ 2) = Work.BSKinetic.dSpace u := by
    have hInt : ∀ k ∈ (Finset.univ : Finset (Fin 3)), MeasureTheory.Integrable
        (fun x : E3 => (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
      intro k _
      have hc : Continuous (fun x : E3 =>
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
        ((hu.continuous_fderiv (n := (⊤ : ENat)) (by simp)).clm_apply
          continuous_const).pow 2
      have hcs : HasCompactSupport (fun x : E3 =>
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) :=
        (huc.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis k)).comp_left
          (g := fun t : ℝ => t ^ 2) (by simp)
      exact hc.integrable_of_hasCompactSupport hcs
    rw [Work.BSKinetic.dSpace, ← integral_finsetSum (Finset.univ)
      (f := fun k (x : E3) => (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2) hInt]
    refine integral_congr_ae ?_
    filter_upwards with x
    exact gradient_norm_sq_eq_sum u x
  refine ⟨?_, ?_⟩
  · exact hInt_kin.congr (Filter.Eventually.of_forall fun q => (kinW_apply u q).symm)
  · rw [hgrad, Work.OneBodyKin.dSpace_eq_fourier u hu huc]
    rfl

/-! ## 7. Integrability of the cross term -/

/-- **The cross term is integrable**: `Ŵ` and `û` are dominated by `Ŵ²/‖q‖²` and `kinW u`,
which `hint` and `hkin` make integrable. -/
lemma ChatCrossIntegrable {W u : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (hu : MeasureTheory.Integrable u)
    (hint : MeasureTheory.Integrable
      (fun q : E3 => chat W q ^ 2 / (2 * ‖q‖ ^ 2)))
    (hkin : MeasureTheory.Integrable (kinW u)) :
    MeasureTheory.Integrable (fun q : E3 => chat W q * chat u q) := by
  have hI : MeasureTheory.Integrable (fun q : E3 => chat W q ^ 2 / ‖q‖ ^ 2) :=
    (hint.const_mul 2).congr
      (Filter.Eventually.of_forall fun q => two_mul_div_two_mul_eq (chat W q ^ 2) (‖q‖ ^ 2))
  have hdom : MeasureTheory.Integrable
      (fun q : E3 => chat W q ^ 2 / ‖q‖ ^ 2 + kinW u q) := hI.add hkin
  refine hdom.mono' (((continuous_chat W hW).mul (continuous_chat u hu)).aestronglyMeasurable) ?_
  have hne : ∀ᵐ q : E3 ∂(volume : Measure E3), q ≠ 0 := by
    rw [MeasureTheory.ae_iff, show {q : E3 | ¬q ≠ 0} = {0} by ext q; simp]
    exact measure_singleton 0
  filter_upwards [hne] with q hq
  rw [Real.norm_eq_abs]
  exact abs_mul_le_div_add (chat W q) (chat u q) (kinA u q) (abs_chat_le_kinA u q)
    (norm_pos_iff.mpr hq)

/-! ## 8. The smooth case -/

/-- **The free-energy inequality for a smooth compactly supported test function.** -/
lemma freeEnergy_smooth {W : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hWe : ∀ x, W (-x) = W x)
    (hint : MeasureTheory.Integrable (fun q : E3 => chat W q ^ 2 / (2 * ‖q‖ ^ 2)))
    {u : E3 → ℝ} (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u) :
    2 * (∫ x, W x * u x) - ∫ x, ‖gradient u x‖ ^ 2
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, chat W q ^ 2 / ‖q‖ ^ 2 := by
  obtain ⟨hInt_kin, hKin⟩ := LatFreeKineticKinFT hu huc
  have hMult := LatFreeMultL1 hW hWe hu huc
  have huInt : MeasureTheory.Integrable u :=
    hu.continuous.integrable_of_hasCompactSupport huc
  have hCross := ChatCrossIntegrable hW huInt hint hInt_kin
  have hI_int : MeasureTheory.Integrable (fun q : E3 => chat W q ^ 2 / ‖q‖ ^ 2) :=
    (hint.const_mul 2).congr
      (Filter.Eventually.of_forall fun q => two_mul_div_two_mul_eq (chat W q ^ 2) (‖q‖ ^ 2))
  have hne : ∀ᵐ q : E3 ∂(volume : Measure E3), q ≠ 0 := by
    rw [MeasureTheory.ae_iff, show {q : E3 | ¬q ≠ 0} = {0} by ext q; simp]
    exact measure_singleton 0
  have hpt : ∀ᵐ q ∂(volume : Measure E3),
      2 * (chat W q * chat u q) - kinW u q ≤ chat W q ^ 2 / ‖q‖ ^ 2 := by
    filter_upwards [hne] with q hq
    exact two_mul_mul_sub_sq_le (chat W q) (chat u q) (kinA u q)
      (abs_chat_le_kinA u q) (norm_pos_iff.mpr hq)
  have hIntL : MeasureTheory.Integrable
      (fun q : E3 => 2 * (chat W q * chat u q) - kinW u q) :=
    (hCross.const_mul 2).sub hInt_kin
  have hmono := MeasureTheory.integral_mono_ae hIntL hI_int hpt
  rw [MeasureTheory.integral_sub (hCross.const_mul 2) hInt_kin,
    MeasureTheory.integral_const_mul] at hmono
  have hkey : 2 * (∫ q, chat W q * chat u q) - (∫ q, kinW u q)
      ≤ ∫ q, chat W q ^ 2 / ‖q‖ ^ 2 := hmono
  have hgoal : 2 * (∫ x, W x * u x) - ∫ x, ‖gradient u x‖ ^ 2
      = ((2 * Real.pi) ^ 3)⁻¹
          * (2 * (∫ q, chat W q * chat u q) - ∫ q, kinW u q) := by
    rw [hMult, hKin]
    ring
  rw [hgoal]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

theorem LatticeW1sqFreeEnergyHint {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hW0 : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hWe : ∀ x, W (-x) = W x)
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.chat W q) ^ 2 / (2 * ‖q‖ ^ 2)))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    2 * (∫ x, W x * ψ x) - ∫ x, ‖gradient ψ x‖ ^ 2
      ≤ ((2 * Real.pi) ^ 3)⁻¹
          * ∫ q, (Work.BoseFixR.chat W q) ^ 2 / ‖q‖ ^ 2 := by
  obtain ⟨u, hu_smooth, hu_cs, _, hu_grad, hu_W⟩ := SmoothApproxGradient hW hψ hψc
  have hconst : ∀ n, 2 * (∫ x, W x * u n x) - ∫ x, ‖gradient (u n) x‖ ^ 2
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, chat W q ^ 2 / ‖q‖ ^ 2 :=
    fun n => freeEnergy_smooth hW hWe hint (hu_smooth n) (hu_cs n)
  have htend : Filter.Tendsto
      (fun n => 2 * (∫ x, W x * u n x) - ∫ x, ‖gradient (u n) x‖ ^ 2)
      Filter.atTop (nhds (2 * (∫ x, W x * ψ x) - ∫ x, ‖gradient ψ x‖ ^ 2)) :=
    (hu_W.const_mul 2).sub hu_grad
  exact le_of_tendsto htend (Filter.Eventually.of_forall hconst)

end Work.BoseFixR
