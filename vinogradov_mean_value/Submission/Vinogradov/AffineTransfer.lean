import Submission.Vinogradov.Rescaling

noncomputable section
open MeasureTheory Complex Polynomial
open scoped Real BigOperators Interval ENNReal
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Vinogradov

/-!
# The translation group of the moment curve; bounded distortion of ball weights

The affine maps `x ↦ affVec k 1 t₀ x` of `Rescaling.lean` implement the
*translation* `t ↦ t + t₀` of the curve parameter: `momPhase k x (t + t₀) =
momPhase k x t₀ + momPhase k (affVec k 1 t₀ x) t`.  This module shows that this
is a **one-parameter group** of invertible linear maps
(`affVec k 1 (-t₀) ∘ affVec k 1 t₀ = id`, obtained by identifying the two
phases as polynomials: `momPhase_injective`), and that it acts on the ball
weights `w_{B(c,R)} = (1+‖x−c‖/R)^{−100k}` with **bounded distortion**:

    `w_{B(c,R)}(x) ≤ w_{B(affVec k 1 t₀ c, R'·R)}(affVec k 1 t₀ x)`
    `w_{B(affVec k 1 t₀ c, R'·R)}(affVec k 1 t₀ x) ≤ M · w_{B(c,R)}(x)`,

with `M, R'` depending only on `k` (`ballWeight_affVec_compare`).  This is
exactly the "the linear transformation has bounded distortion for
`t₀ ∈ [0,1]`" step in BDG's proof of the lower-dimensional decoupling Lemma
(BDG §8, Lemma `nl5`), which transfers an `Lᵖ(w_B)` decoupling statement for the
curve segment near `t₀` to the translated segment.

All lemmas are proved (no sorries).
-/

/-- The polynomial `Σⱼ yⱼ X^{j+1}` whose evaluation is the phase
`momPhase k y`. -/
noncomputable def phasePoly (k : ℕ) (y : E k) : Polynomial ℝ :=
  ∑ j : Fin k, Polynomial.C (y j) * Polynomial.X ^ (j.val + 1)

/-- Evaluating `phasePoly` gives `momPhase`. -/
lemma eval_phasePoly (k : ℕ) (y : E k) (u : ℝ) :
    (phasePoly k y).eval u = momPhase k y u := by
  simp only [phasePoly, momPhase, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The coefficient of `X^{j+1}` in `phasePoly` is `y j`. -/
lemma coeff_phasePoly (k : ℕ) (y : E k) (j : Fin k) :
    (phasePoly k y).coeff (j.val + 1) = y j := by
  simp only [phasePoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul_X_pow]; simp
  · intro b _ hb
    have hne : ¬ (j.val + 1 = b.val + 1) := by
      intro h; exact hb (Fin.ext (by omega))
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The phase determines the frequency vector** (`momPhase k · u` is a
polynomial in `u` of degree `k+1`). -/
lemma momPhase_injective (k : ℕ) (y z : E k)
    (h : ∀ u : ℝ, momPhase k y u = momPhase k z u) : y = z := by
  have hp : phasePoly k y = phasePoly k z := by
    refine Polynomial.funext (fun r => ?_)
    rw [eval_phasePoly, eval_phasePoly, h r]
  ext j
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (j.val + 1)) hp
  rwa [coeff_phasePoly, coeff_phasePoly] at hc

/-- **Group law for translations** (phase form): translating by `t₀` and then by
`-t₀` returns the original phase. -/
lemma momPhase_affVec_comp (k : ℕ) (x : E k) (t₀ u : ℝ) :
    momPhase k (affVec k 1 (-t₀) (affVec k 1 t₀ x)) u = momPhase k x u := by
  have h1 : momPhase k (affVec k 1 (-t₀) (affVec k 1 t₀ x)) u
      = momPhase k (affVec k 1 t₀ x) (u + (-t₀)) - momPhase k (affVec k 1 t₀ x) (-t₀) := by
    have h := momPhase_affine k (affVec k 1 t₀ x) 1 (-t₀) u
    simp only [one_mul] at h
    linarith [h]
  have h2 : momPhase k (affVec k 1 t₀ x) (u + (-t₀))
      = momPhase k x ((u + (-t₀)) + t₀) - momPhase k x t₀ := by
    have h := momPhase_affine k x 1 t₀ (u + (-t₀))
    simp only [one_mul] at h
    linarith [h]
  have h3 : momPhase k (affVec k 1 t₀ x) (-t₀)
      = momPhase k x ((-t₀) + t₀) - momPhase k x t₀ := by
    have h := momPhase_affine k x 1 t₀ (-t₀)
    simp only [one_mul] at h
    linarith [h]
  rw [h1, h2, h3]
  have e1 : (u + (-t₀)) + t₀ = u := by ring
  have e2 : (-t₀) + t₀ = 0 := by ring
  rw [e1, e2]
  unfold momPhase
  simp

/-- **`affVec k 1 (-t₀)` is a left inverse of `affVec k 1 t₀`.** -/
lemma affVec_one_neg_comp (k : ℕ) (x : E k) (t₀ : ℝ) :
    affVec k 1 (-t₀) (affVec k 1 t₀ x) = x :=
  momPhase_injective k _ _ (fun u => momPhase_affVec_comp k x t₀ u)

/-- **`affVec k 1 (-t₀)` is also a right inverse of `affVec k 1 t₀`.** -/
lemma affVec_neg_one_comp (k : ℕ) (x : E k) (t₀ : ℝ) :
    affVec k 1 t₀ (affVec k 1 (-t₀) x) = x := by
  have h := affVec_one_neg_comp k x (-t₀)
  simpa using h

/-- `affVec k 1 t₀` is additive. -/
lemma affVec_sub (k : ℕ) (t₀ : ℝ) (x c : E k) :
    affVec k 1 t₀ x - affVec k 1 t₀ c = affVec k 1 t₀ (x - c) := by
  ext l
  have hL : (affVec k 1 t₀ x - affVec k 1 t₀ c) l = affVec k 1 t₀ x l - affVec k 1 t₀ c l := rfl
  rw [hL, affVec_apply, affVec_apply, affVec_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PiLp.sub_apply]
  ring

/-- **Lipschitz bound for the translation matrix**: for `|t₀| ≤ 1`,
`‖affVec k 1 t₀ x − affVec k 1 t₀ c‖ ≤ C‖x − c‖` with `C` depending only on `k`. -/
lemma affVec_norm_sub_le (k : ℕ) (t₀ : ℝ) (ht : |t₀| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x c : E k, ‖affVec k 1 t₀ x - affVec k 1 t₀ c‖ ≤ C * ‖x - c‖ := by
  obtain ⟨C, hC, h⟩ := norm_affVec_one_le k
  exact ⟨C, hC, fun x c => by rw [affVec_sub]; exact h t₀ ht (x - c)⟩

/-- **Bounded distortion of the ball weight under the translation matrix.**  For
`|t₀| ≤ 1` there are constants `M, R' > 0` (depending only on `k`) such that for
all `c`, `R > 0` and `x`,

    `w_{B(c,R)}(x) ≤ w_{B(affVec k 1 t₀ c, R'·R)}(affVec k 1 t₀ x)`
    `w_{B(affVec k 1 t₀ c, R'·R)}(affVec k 1 t₀ x) ≤ M · w_{B(c,R)}(x)`.

(The map distorts distances by at most `C = max 1 C₀` in both directions,
`C₀` being the bound of `norm_affVec_one_le k` applied to `t₀` and to `-t₀`.) -/
lemma ballWeight_affVec_compare (k : ℕ) (t₀ : ℝ) (ht : |t₀| ≤ 1) :
    ∃ M R' : ℝ, 0 < M ∧ 0 < R' ∧ ∀ (c : E k) (R : ℝ), 0 < R → ∀ x : E k,
      ballWeight k c R x ≤ ballWeight k (affVec k 1 t₀ c) (R' * R) (affVec k 1 t₀ x) ∧
      ballWeight k (affVec k 1 t₀ c) (R' * R) (affVec k 1 t₀ x) ≤ M * ballWeight k c R x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := norm_affVec_one_le k
  refine ⟨(max 1 C₀) ^ (200 * k), max 1 C₀, by positivity, by positivity, ?_⟩
  intro c R hR x
  set C : ℝ := max 1 C₀ with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC₀C : C₀ ≤ C := le_max_right _ _
  have hnorm : ∀ z : E k, ‖affVec k 1 t₀ z‖ ≤ C * ‖z‖ := by
    intro z
    exact le_trans (hC₀ t₀ ht z) (mul_le_mul_of_nonneg_right hC₀C (norm_nonneg z))
  have hnorm' : ∀ z : E k, ‖affVec k 1 (-t₀) z‖ ≤ C * ‖z‖ := by
    intro z
    have ht' : |(-t₀)| ≤ 1 := by rw [abs_neg]; exact ht
    exact le_trans (hC₀ (-t₀) ht' z) (mul_le_mul_of_nonneg_right hC₀C (norm_nonneg z))
  set d : ℝ := ‖x - c‖ with hd
  set e : ℝ := ‖affVec k 1 t₀ x - affVec k 1 t₀ c‖ with he
  have he_le : e ≤ C * d := by
    rw [he, hd, affVec_sub]; exact hnorm (x - c)
  have hd_le : d ≤ C * e := by
    have hkey : x - c = affVec k 1 (-t₀) (affVec k 1 t₀ x - affVec k 1 t₀ c) := by
      rw [affVec_sub, affVec_one_neg_comp]
    rw [hd, he, hkey]
    exact hnorm' _
  have hR0 : 0 < R := hR
  have hCR0 : 0 < C * R := mul_pos hCpos hR
  have hw1 : ballWeight k c R x = ((1 + d / R) ^ (100 * k))⁻¹ := by
    simp only [ballWeight, hd]
  have hw2 : ballWeight k (affVec k 1 t₀ c) (C * R) (affVec k 1 t₀ x)
      = ((1 + e / (C * R)) ^ (100 * k))⁻¹ := by
    simp only [ballWeight, he]
  constructor
  · rw [hw1, hw2]
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    have hdiv : e / (C * R) ≤ d / R := by
      rw [div_le_div_iff₀ hCR0 hR0]
      nlinarith [he_le, hR0]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  · rw [hw1, hw2]
    have hstep : 1 + d / R ≤ C ^ 2 * (1 + e / (C * R)) := by
      have h1 : d / R ≤ C * e / R := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hR0); linarith
      have h2 : C ^ 2 * (1 + e / (C * R)) = C ^ 2 + C * e / R := by
        field_simp
      rw [h2]
      have h3 : (1 : ℝ) ≤ C ^ 2 := one_le_pow₀ hC1
      linarith
    have hM2 : (C ^ 2) ^ (100 * k) = C ^ (200 * k) := by
      rw [← pow_mul]; congr 1; ring
    have hfin : (1 + d / R) ^ (100 * k) ≤ C ^ (200 * k) * (1 + e / (C * R)) ^ (100 * k) := by
      have hpow := pow_le_pow_left₀ (by positivity) hstep (100 * k)
      rwa [mul_pow, hM2] at hpow
    have hD : 0 < (1 + d / R) ^ (100 * k) := by positivity
    have hCA : 0 < C ^ (200 * k) * (1 + e / (C * R)) ^ (100 * k) := by positivity
    have hEq : (C ^ (200 * k) * (1 + e / (C * R)) ^ (100 * k))⁻¹ * C ^ (200 * k)
        = ((1 + e / (C * R)) ^ (100 * k))⁻¹ := by
      field_simp
    calc ((1 + e / (C * R)) ^ (100 * k))⁻¹
        = (C ^ (200 * k) * (1 + e / (C * R)) ^ (100 * k))⁻¹ * C ^ (200 * k) := hEq.symm
      _ ≤ ((1 + d / R) ^ (100 * k))⁻¹ * C ^ (200 * k) :=
          mul_le_mul_of_nonneg_right ((inv_le_inv₀ hCA hD).mpr hfin) (by positivity)
      _ = C ^ (200 * k) * ((1 + d / R) ^ (100 * k))⁻¹ := by ring


/-! ## The translation maps as linear maps

`x ↦ affVec k 1 t₀ x` is linear (`affLin`), its determinant is `1` (it is an
upper triangular unipotent matrix in the standard basis, with diagonal entries
`C(j+1,j+1) t₀⁰ = 1`), so it is **measure preserving**: the change of variables
`x ↦ affLin k t₀ x` leaves Lebesgue measure invariant
(`measure_map_affLin`, `integral_comp_affLin`). -/

/-- The linear map `x ↦ affVec k 1 t₀ x`. -/
noncomputable def affLin (k : ℕ) (t₀ : ℝ) : E k →ₗ[ℝ] E k where
  toFun := affVec k 1 t₀
  map_add' := by
    intro x y
    ext l
    have hR : ((affVec k 1 t₀ x) + (affVec k 1 t₀ y)) l
        = affVec k 1 t₀ x l + affVec k 1 t₀ y l := rfl
    rw [hR, affVec_apply, affVec_apply, affVec_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    ext l
    simp only [RingHom.id_apply]
    have hR : ((c : ℝ) • (affVec k 1 t₀ x)) l = c * affVec k 1 t₀ x l := rfl
    rw [hR, affVec_apply, affVec_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PiLp.smul_apply]
    ring

/-- Defining equation of `affLin`. -/
lemma affLin_apply (k : ℕ) (t₀ : ℝ) (x : E k) : affLin k t₀ x = affVec k 1 t₀ x := rfl

/-- **Determinant one**: `affLin k t₀` is upper triangular unipotent in the
standard basis. -/
lemma affLin_det (k : ℕ) (t₀ : ℝ) : LinearMap.det (affLin k t₀) = 1 := by
  have hentry : ∀ i j : Fin k,
      (LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (PiLp.basisFun 2 ℝ (Fin k))
        (affLin k t₀)) i j
      = ((Nat.choose (j.val + 1) (i.val + 1) : ℕ) : ℝ) * t₀ ^ (j.val - i.val) := by
    intro i j
    rw [LinearMap.toMatrix_apply, PiLp.basisFun_repr, PiLp.basisFun_apply]
    rw [show affLin k t₀ (PiLp.single 2 j 1) = affVec k 1 t₀ (PiLp.single 2 j 1) from rfl]
    rw [affVec_apply]
    rw [Finset.sum_eq_single j]
    · rw [PiLp.single_apply]; simp
    · intro b _ hb
      rw [PiLp.single_apply, if_neg hb]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin k)) (affLin k t₀)]
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one (fun i _ => ?_)
    rw [hentry i i, Nat.sub_self, pow_zero, mul_one, Nat.choose_self]
    norm_num
  · intro i j hij
    rw [hentry i j]
    have hji : j.val < i.val := hij
    rw [Nat.choose_eq_zero_of_lt (Nat.succ_lt_succ hji)]
    norm_num

/-- **The translation map is measure preserving.** -/
lemma measure_map_affLin (k : ℕ) (t₀ : ℝ) :
    Measure.map (affLin k t₀) (volume : Measure (E k)) = volume := by
  have hdet : LinearMap.det (affLin k t₀) ≠ 0 := by rw [affLin_det]; norm_num
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, affLin_det]
  simp

/-- **Change of variables** for the translation map:
`∫ x, g (affLin k t₀ x) dx = ∫ y, g y dy`. -/
lemma integral_comp_affLin (k : ℕ) (t₀ : ℝ) {g : E k → ℂ}
    (hg : AEStronglyMeasurable g (volume : Measure (E k))) :
    ∫ x, g (affLin k t₀ x) ∂(volume : Measure (E k)) = ∫ y, g y ∂volume := by
  have h := integral_map (φ := affLin k t₀) (μ := (volume : Measure (E k))) (f := g)
    ((affLin k t₀).continuous_of_finiteDimensional.aemeasurable)
    (by rw [measure_map_affLin]; exact hg)
  rw [measure_map_affLin] at h
  exact h.symm


/-! ## Bounded-distortion transfer of weighted integrals

Combining the measure preservation with the pointwise comparison of
`ballWeight_affVec_compare` gives the transfer of weighted integrals
(`∫⁻`, i.e. nonnegative/`ℝ≥0∞` form, so that no integrability issue arises):
for `|t₀| ≤ 1` there are `M, R' > 0` with

`∫ x, f(affVec k 1 t₀ x)·w_{B(c,R)}(x)`
  `≤ ∫ y, f(y)·w_{B(affVec k 1 t₀ c, R'·R)}(y)`
  `≤ M · ∫ x, f(affVec k 1 t₀ x)·w_{B(c,R)}(x)`

for every nonnegative measurable `f`.  This is the precise form of the
"bounded distortion" step transferring an `Lᵖ(w_B)` statement for the curve
segment near `t₀` to the translated segment (BDG §8, Lemma `nl5`). -/

/-- **Transfer of weighted integrals under the translation map.** -/
lemma lintegral_affVec_compare (k : ℕ) (t₀ : ℝ) (ht : |t₀| ≤ 1) :
    ∃ M R' : ℝ, 0 < M ∧ 0 < R' ∧ ∀ (f : E k → ℝ≥0∞) (_hf : Measurable f) (c : E k)
      (R : ℝ), 0 < R →
      (∫⁻ x, f (affLin k t₀ x) * ENNReal.ofReal (ballWeight k c R x))
        ≤ ∫⁻ y, f y * ENNReal.ofReal (ballWeight k (affVec k 1 t₀ c) (R' * R) y) ∧
      (∫⁻ y, f y * ENNReal.ofReal (ballWeight k (affVec k 1 t₀ c) (R' * R) y))
        ≤ ENNReal.ofReal M * ∫⁻ x, f (affLin k t₀ x) * ENNReal.ofReal (ballWeight k c R x) := by
  obtain ⟨M, R', hM, hR', hcomp⟩ := ballWeight_affVec_compare k t₀ ht
  refine ⟨M, R', hM, hR', fun f hf c R hR => ⟨?_, ?_⟩⟩
  · have hmeas : Measurable (affLin k (-t₀)) :=
      (affLin k (-t₀)).continuous_of_finiteDimensional.measurable
    have hF : Measurable (fun x : E k => f (affLin k t₀ x) * ENNReal.ofReal (ballWeight k c R x)) :=
      (hf.comp (affLin k t₀).continuous_of_finiteDimensional.measurable).mul
        ((ballWeight_continuous k c hR).measurable.ennreal_ofReal)
    conv_lhs => rw [← measure_map_affLin k (-t₀)]
    rw [lintegral_map hF hmeas]
    refine lintegral_mono (fun y => ?_)
    simp only [affLin_apply]
    have hy : affVec k 1 t₀ (affVec k 1 (-t₀) y) = y := affVec_neg_one_comp k y t₀
    have h1 : ballWeight k c R (affVec k 1 (-t₀) y)
        ≤ ballWeight k (affVec k 1 t₀ c) (R' * R) y := by
      have h := (hcomp c R hR (affVec k 1 (-t₀) y)).1
      rwa [hy] at h
    rw [hy]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h1) (bot_le : (0 : ENNReal) ≤ f y)
  · have hmeas : Measurable (affLin k t₀) :=
      (affLin k t₀).continuous_of_finiteDimensional.measurable
    have hF : Measurable (fun y : E k =>
        f y * ENNReal.ofReal (ballWeight k (affVec k 1 t₀ c) (R' * R) y)) :=
      hf.mul ((ballWeight_continuous k (affVec k 1 t₀ c) (mul_pos hR' hR)).measurable.ennreal_ofReal)
    calc ∫⁻ y, f y * ENNReal.ofReal (ballWeight k (affVec k 1 t₀ c) (R' * R) y)
        = ∫⁻ x, f (affLin k t₀ x) *
            ENNReal.ofReal (ballWeight k (affVec k 1 t₀ c) (R' * R) (affLin k t₀ x)) := by
          conv_lhs => rw [← measure_map_affLin k t₀]
          exact lintegral_map hF hmeas
      _ ≤ ∫⁻ x, f (affLin k t₀ x) *
            (ENNReal.ofReal M * ENNReal.ofReal (ballWeight k c R x)) := by
          refine lintegral_mono (fun x => ?_)
          simp only [affLin_apply]
          refine mul_le_mul_of_nonneg_left ?_ (bot_le : (0 : ENNReal) ≤ f (affVec k 1 t₀ x))
          rw [← ENNReal.ofReal_mul (le_of_lt hM)]
          exact ENNReal.ofReal_le_ofReal ((hcomp c R hR x).2)
      _ = ENNReal.ofReal M * ∫⁻ x, f (affLin k t₀ x) * ENNReal.ofReal (ballWeight k c R x) := by
          rw [← lintegral_const_mul' (ENNReal.ofReal M)
            (fun x => f (affLin k t₀ x) * ENNReal.ofReal (ballWeight k c R x)) ENNReal.ofReal_ne_top]
          refine lintegral_congr (fun x => ?_)
          ring

end Submission.Vinogradov
