/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Hölder data for the unfolding map `discUnfold2`

`discUnfold2 q = (q.1.1, q.1.2 * exp (discTau q.1.2 - q.2))` is the unfolding
`(X × ℂ) × ℝ → X × ℂ` introduced in `DiscExtFlat.lean`.  This file provides the quantitative
data needed to run the fixed point / Schauder arguments on the half space `{q.2 > 0}`:
`discUnfold2` is Lipschitz there, all its iterated derivatives are bounded there, and the
derivatives are Hölder continuous with any exponent `α ≤ 1`.

The proof is by decomposing `discUnfold2 p = (p.1.1, dUf (p.1.2, p.2))` into its `X`-part
(a continuous linear projection) and the `ℂ`-valued inner function
`dUf (z,t) = z * exp (discTau z - t)`; the latter lives on the convex set
`ball(0,R) × (0,∞) ⊂ ℂ × ℝ`, where the mean value theorem together with explicit bounds for
the iterated derivatives produces Lipschitz/bounded/Hölder data, which is then transported
back along the linear isometry `(X × ℂ) × ℝ ≃ₗᵢ[ℝ] X × (ℂ × ℝ)`.
-/
import Mathlib
import Submission.Work.NN.Final.DiscExtFlat
import Submission.Work.NN.Final.holderDataConvex

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 1. Iterated derivatives of continuous linear maps

The iterated derivatives of a continuous linear map `L` are constant (for order `≥ 1`) and
bounded by `‖L‖`. -/

private lemma iteratedFDeriv_clm_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    ∀ n : ℕ, iteratedFDeriv ℝ (n+1) (fun z : E => L z) =
      fun _ => iteratedFDeriv ℝ (n+1) (fun z : E => L z) 0 := by
  intro n
  induction n with
  | zero =>
    funext x; ext m
    rw [iteratedFDeriv_one_apply, L.hasFDerivAt.fderiv, iteratedFDeriv_one_apply,
        L.hasFDerivAt.fderiv]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_fun_const]
    ext x m
    simp

private lemma iteratedFDeriv_clm_succ_succ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (n : ℕ) :
    iteratedFDeriv ℝ (n+2) (fun z : E => L z) = 0 := by
  rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_clm_const L n, fderiv_fun_const]
  ext x m
  simp

private lemma norm_iteratedFDeriv_clm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (fun z : E => L z) x‖ ≤ ‖L‖ := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [← h, norm_iteratedFDeriv_one, L.hasFDerivAt.fderiv]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    rw [iteratedFDeriv_clm_succ_succ]
    simp

/-! ## 2. Derivative bounds for the radial profile `discTau`

`discTau z = (1 - ‖z‖²)/2` is a polynomial of degree two in the real coordinates of `ℂ`, so
every derivative of order `≥ 1` is uniformly bounded on `ball(0,R)`, geometrically in the
order.  We prove this by writing `discTau` through `z.re` and `z.im` and using the product
rule bound `norm_iteratedFDeriv_mul_le`. -/

private lemma norm_reCLM_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul, Complex.reCLM_apply, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm z

private lemma norm_imCLM_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul, Complex.imCLM_apply, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm z

private lemma re_iteratedFDeriv_bound {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z : ℂ => z.re) z‖ ≤ max R 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact le_trans (le_trans (Complex.abs_re_le_norm z) (le_of_lt hz)) (le_max_left _ _)
  · calc ‖iteratedFDeriv ℝ j (fun z : ℂ => z.re) z‖ ≤ ‖Complex.reCLM‖ :=
          norm_iteratedFDeriv_clm_le Complex.reCLM h z
      _ ≤ 1 := norm_reCLM_le_one
      _ ≤ max R 1 := le_max_right _ _

private lemma im_iteratedFDeriv_bound {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun z : ℂ => z.im) z‖ ≤ max R 1 := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact le_trans (le_trans (Complex.abs_im_le_norm z) (le_of_lt hz)) (le_max_left _ _)
  · calc ‖iteratedFDeriv ℝ j (fun z : ℂ => z.im) z‖ ≤ ‖Complex.imCLM‖ :=
          norm_iteratedFDeriv_clm_le Complex.imCLM h z
      _ ≤ 1 := norm_imCLM_le_one
      _ ≤ max R 1 := le_max_right _ _

private lemma sq_re_iteratedFDeriv_bound {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z‖ ≤ 2^i * (max R 1)^2 := by
  have hf : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hM : (0:ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right _ _)
  have key : ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z‖ ≤
      ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) * ((max R 1) * (max R 1)) := by
    refine le_trans (norm_iteratedFDeriv_mul_le hf hf z le_rfl) ?_
    apply Finset.sum_le_sum
    intro j hj
    have h1 := re_iteratedFDeriv_bound hz j
    have h2 := re_iteratedFDeriv_bound hz (i-j)
    have hc : (0:ℝ) ≤ (i.choose j : ℝ) := by positivity
    have hn2 : (0:ℝ) ≤ ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.re) z‖ := norm_nonneg _
    have hb : ‖iteratedFDeriv ℝ j (fun z : ℂ => z.re) z‖ *
        ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.re) z‖ ≤ (max R 1) * (max R 1) :=
      mul_le_mul h1 h2 hn2 hM
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z : ℂ => z.re) z‖ *
          ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.re) z‖
        = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (fun z : ℂ => z.re) z‖ *
          ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.re) z‖) := by ring
      _ ≤ (i.choose j : ℝ) * ((max R 1) * (max R 1)) := mul_le_mul_of_nonneg_left hb hc
  have hsum : (∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)) = 2^i := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z‖
      ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) * ((max R 1) * (max R 1)) := key
    _ = (∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)) * ((max R 1) * (max R 1)) := by
          rw [Finset.sum_mul]
    _ = 2^i * (max R 1)^2 := by rw [hsum]; ring

private lemma sq_im_iteratedFDeriv_bound {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖ ≤ 2^i * (max R 1)^2 := by
  have hf : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hM : (0:ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right _ _)
  have key : ‖iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖ ≤
      ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) * ((max R 1) * (max R 1)) := by
    refine le_trans (norm_iteratedFDeriv_mul_le hf hf z le_rfl) ?_
    apply Finset.sum_le_sum
    intro j hj
    have h1 := im_iteratedFDeriv_bound hz j
    have h2 := im_iteratedFDeriv_bound hz (i-j)
    have hc : (0:ℝ) ≤ (i.choose j : ℝ) := by positivity
    have hn2 : (0:ℝ) ≤ ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.im) z‖ := norm_nonneg _
    have hb : ‖iteratedFDeriv ℝ j (fun z : ℂ => z.im) z‖ *
        ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.im) z‖ ≤ (max R 1) * (max R 1) :=
      mul_le_mul h1 h2 hn2 hM
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z : ℂ => z.im) z‖ *
          ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.im) z‖
        = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (fun z : ℂ => z.im) z‖ *
          ‖iteratedFDeriv ℝ (i-j) (fun z : ℂ => z.im) z‖) := by ring
      _ ≤ (i.choose j : ℝ) * ((max R 1) * (max R 1)) := mul_le_mul_of_nonneg_left hb hc
  have hsum : (∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)) = 2^i := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc ‖iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖
      ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) * ((max R 1) * (max R 1)) := key
    _ = (∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)) * ((max R 1) * (max R 1)) := by
          rw [Finset.sum_mul]
    _ = 2^i * (max R 1)^2 := by rw [hsum]; ring

/-- Bound for the iterated derivatives of `Real.exp` on the half line `(-∞,1)`. -/
private lemma realExp_iteratedFDerivWithin_bound (n : ℕ) {x : ℝ} (hx : x < 1) :
    ‖iteratedFDerivWithin ℝ n Real.exp (Iio (1:ℝ)) x‖ ≤ Real.exp 1 := by
  have h1 : iteratedFDerivWithin ℝ n Real.exp (Iio (1:ℝ)) x = iteratedFDeriv ℝ n Real.exp x :=
    iteratedFDerivWithin_of_isOpen n isOpen_Iio hx
  have h2 : iteratedDeriv n Real.exp x = Real.exp x := by
    have := congrFun (iteratedDeriv_exp_const_mul n 1) x
    simpa using this
  rw [h1, norm_iteratedFDeriv_eq_norm_iteratedDeriv, h2, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos x).le]
  exact Real.exp_le_exp.mpr hx.le

/-- The radial profile has geometrically bounded iterated derivatives on `ball(0,R)`. -/
private lemma discTau_iteratedFDeriv_bound {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i discTau z‖ ≤ (2 * (max R 1)^2)^i := by
  have hM1 : (1:ℝ) ≤ max R 1 := le_max_right _ _
  have hCre : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.re) := by
    have h := Complex.reCLM.contDiff (n := (i:ℕ∞ω))
    rwa [show (⇑Complex.reCLM : ℂ → ℝ) = fun z => z.re from funext Complex.reCLM_apply] at h
  have hCim : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.im) := by
    have h := Complex.imCLM.contDiff (n := (i:ℕ∞ω))
    rwa [show (⇑Complex.imCLM : ℂ → ℝ) = fun z => z.im from funext Complex.imCLM_apply] at h
  have hCre2 : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.re * z.re) := by
    simpa only [Pi.mul_apply] using hCre.mul hCre
  have hCim2 : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.im * z.im) := by
    simpa only [Pi.mul_apply] using hCim.mul hCim
  have hCX : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => z.re*z.re + z.im*z.im) := by
    simpa only [Pi.add_apply] using hCre2.add hCim2
  have hA : ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z‖ ≤ 2^i * (max R 1)^2 :=
    sq_re_iteratedFDeriv_bound hz i
  have hB : ‖iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖ ≤ 2^i * (max R 1)^2 :=
    sq_im_iteratedFDeriv_bound hz i
  have hX : ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re*z.re + z.im*z.im) z‖
      ≤ 2 * (2^i * (max R 1)^2) := by
    rw [show (fun z : ℂ => z.re*z.re + z.im*z.im)
          = (fun z : ℂ => z.re * z.re) + (fun z : ℂ => z.im * z.im) from
        funext (fun z => by simp only [Pi.add_apply])]
    rw [iteratedFDeriv_add hCre2 hCim2]
    calc ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z +
            iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖
        ≤ ‖iteratedFDeriv ℝ i (fun z : ℂ => z.re * z.re) z‖ +
          ‖iteratedFDeriv ℝ i (fun z : ℂ => z.im * z.im) z‖ := norm_add_le _ _
      _ ≤ 2^i * (max R 1)^2 + 2^i * (max R 1)^2 := add_le_add hA hB
      _ = 2 * (2^i * (max R 1)^2) := by ring
  have hY : ‖iteratedFDeriv ℝ i (fun z : ℂ => 1 - (z.re*z.re + z.im*z.im)) z‖
      ≤ 2 * (2^i * (max R 1)^2) := by
    have hfeq : (fun z : ℂ => 1 - (z.re*z.re + z.im*z.im))
        = (fun _ : ℂ => (1:ℝ)) - (fun z : ℂ => z.re*z.re + z.im*z.im) :=
      funext (fun z => by simp only [Pi.sub_apply])
    rw [hfeq, iteratedFDeriv_sub (contDiff_const : ContDiff ℝ (i : ℕ∞ω) (fun _ : ℂ => (1:ℝ))) hCX,
        Pi.sub_apply, iteratedFDeriv_const_of_ne (by omega : i ≠ 0) (1:ℝ), Pi.zero_apply, zero_sub,
        norm_neg]
    exact hX
  have hCY : ContDiff ℝ (i : ℕ∞ω) (fun z : ℂ => 1 - (z.re*z.re + z.im*z.im)) := by
    simpa only [Pi.sub_apply] using
      (contDiff_const : ContDiff ℝ (i : ℕ∞ω) (fun _ : ℂ => (1:ℝ))).sub hCX
  have hZ : ‖iteratedFDeriv ℝ i discTau z‖ ≤ (1/2) * (2 * (2^i * (max R 1)^2)) := by
    have hdt : discTau = (1/2:ℝ) • (fun z : ℂ => 1 - (z.re*z.re + z.im*z.im)) := by
      funext z
      simp only [discTau, Complex.normSq_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdt,
        iteratedFDeriv_const_smul_apply (f := fun z : ℂ => 1 - (z.re*z.re + z.im*z.im))
          (a := (1/2:ℝ)) hCY.contDiffAt,
        norm_smul]
    have hnorm : ‖((1/2:ℝ))‖ = (1/2:ℝ) := by rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hY (by norm_num)
  calc ‖iteratedFDeriv ℝ i discTau z‖ ≤ (1/2) * (2 * (2^i * (max R 1)^2)) := hZ
    _ = 2^i * (max R 1)^2 := by ring
    _ ≤ (2 * (max R 1)^2)^i := by
        rw [mul_pow]
        have hp : ((max R 1)^2)^i = (max R 1)^(2*i) := by rw [← pow_mul]
        rw [hp]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 (by omega)) (by positivity)

/-! ## 3. The inner function `dUf (z,t) = z * exp (discTau z - t)` -/

/-- The exponent `discTau z - t`. -/
private def uKappa (w : ℂ × ℝ) : ℝ := discTau w.1 - w.2

/-- The `ℂ`-valued inner part of the unfolding `discUnfold2`. -/
private def dUf (w : ℂ × ℝ) : ℂ := w.1 * (Real.exp (uKappa w) : ℂ)

@[simp] lemma uKappa_apply (w : ℂ × ℝ) : uKappa w = discTau w.1 - w.2 := rfl
@[simp] lemma dUf_apply (w : ℂ × ℝ) : dUf w = w.1 * (Real.exp (uKappa w) : ℂ) := rfl

private lemma contDiff_uKappa : ContDiff ℝ ∞ uKappa := by
  unfold uKappa
  exact (contDiff_discTau.comp (by fun_prop)).sub (by fun_prop)

private lemma contDiff_dUf : ContDiff ℝ ∞ dUf := by
  unfold dUf uKappa
  have h2 : ContDiff ℝ ∞ (fun w : ℂ × ℝ => (Real.exp (discTau w.1 - w.2) : ℂ)) := by
    apply Complex.ofRealCLM.contDiff.comp
    exact Real.contDiff_exp.comp ((contDiff_discTau.comp (by fun_prop)).sub (by fun_prop))
  exact (by fun_prop : ContDiff ℝ ∞ (fun w : ℂ × ℝ => w.1)).mul h2

/-- `discTau` is a polynomial, hence real analytic. -/
private lemma contDiff_omega_discTau : ContDiff ℝ ω discTau := by
  have h : discTau = fun z : ℂ => (1 - (z.re * z.re + z.im * z.im)) * (1/2 : ℝ) := by
    funext z; rw [discTau, Complex.normSq_apply]; ring
  rw [h]
  have hre : ContDiff ℝ ω (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ω (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  exact (contDiff_const.sub ((hre.mul hre).add (him.mul him))).mul contDiff_const

private lemma contDiff_omega_dUf : ContDiff ℝ ω dUf := by
  unfold dUf uKappa
  have h2 : ContDiff ℝ ω (fun w : ℂ × ℝ => (Real.exp (discTau w.1 - w.2) : ℂ)) := by
    apply Complex.ofRealCLM.contDiff.comp
    exact Real.contDiff_exp.comp ((contDiff_omega_discTau.comp (by fun_prop)).sub (by fun_prop))
  exact (by fun_prop : ContDiff ℝ ω (fun w : ℂ × ℝ => w.1)).mul h2

/-- `discTau z ≤ 1/2`. -/
private lemma discTau_le_half (z : ℂ) : discTau z ≤ 1/2 := by
  rw [discTau_eq]; nlinarith [sq_nonneg ‖z‖]

/-- The exponent stays below `1` on the half space `{t > 0}`. -/
private lemma uKappa_lt_one {w : ℂ × ℝ} (hw : 0 < w.2) : uKappa w < 1 := by
  have h := discTau_le_half w.1
  rw [uKappa_apply]; linarith

/-- Geometric bound for the iterated derivatives of the exponent, on `{‖z‖ < R, t > 0}`. -/
private lemma uKappa_iteratedFDeriv_le {R : ℝ} {w : ℂ × ℝ} (hw1 : ‖w.1‖ < R) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i uKappa w‖ ≤ (4 * (max R 1)^2)^i := by
  have hC : (0:ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC0le : ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => discTau w.1) w‖
      ≤ (2 * (max R 1)^2)^i := by
    have hcd : ContDiff ℝ ((i:ℕ):ℕ∞ω) discTau := contDiff_discTau.of_le (by exact_mod_cast le_top)
    rw [show (fun w : ℂ × ℝ => discTau w.1)
          = discTau ∘ (⇑(ContinuousLinearMap.fst ℝ ℂ ℝ)) from rfl,
        ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ ℂ ℝ) hcd w le_rfl]
    calc ‖(iteratedFDeriv ℝ i discTau w.1).compContinuousLinearMap
              (fun _ => ContinuousLinearMap.fst ℝ ℂ ℝ)‖
        ≤ ‖iteratedFDeriv ℝ i discTau w.1‖ * ∏ _ : Fin i, ‖ContinuousLinearMap.fst ℝ ℂ ℝ‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i discTau w.1‖ * ‖ContinuousLinearMap.fst ℝ ℂ ℝ‖^i := by
          rw [Finset.prod_const, Finset.card_fin]
      _ ≤ ‖iteratedFDeriv ℝ i discTau w.1‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℂ ℝ)
      _ = ‖iteratedFDeriv ℝ i discTau w.1‖ := mul_one _
      _ ≤ (2 * (max R 1)^2)^i := discTau_iteratedFDeriv_bound hw1 hi
  have hS : ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => w.2) w‖ ≤ 1 := by
    refine le_trans (norm_iteratedFDeriv_clm_le (ContinuousLinearMap.snd ℝ ℂ ℝ) hi w) ?_
    rw [ContinuousLinearMap.norm_snd]
  have hsub : ‖iteratedFDeriv ℝ i uKappa w‖
      ≤ ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => discTau w.1) w‖
        + ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => w.2) w‖ := by
    have hcd1 : ContDiff ℝ ((i:ℕ):ℕ∞ω) (fun w : ℂ × ℝ => discTau w.1) :=
      (contDiff_discTau.of_le (by exact_mod_cast le_top)).comp (ContinuousLinearMap.fst ℝ ℂ ℝ).contDiff
    have hcd2 : ContDiff ℝ ((i:ℕ):ℕ∞ω) (fun w : ℂ × ℝ => w.2) :=
      (ContinuousLinearMap.snd ℝ ℂ ℝ).contDiff
    rw [show uKappa = (fun w : ℂ × ℝ => discTau w.1) - (fun w : ℂ × ℝ => w.2) from rfl,
        iteratedFDeriv_sub hcd1 hcd2, Pi.sub_apply]
    exact norm_sub_le _ _
  calc ‖iteratedFDeriv ℝ i uKappa w‖
      ≤ ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => discTau w.1) w‖
        + ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => w.2) w‖ := hsub
    _ ≤ (2 * (max R 1)^2)^i + 1 := add_le_add hC0le hS
    _ ≤ (4 * (max R 1)^2)^i := by
        have hM1 : (1:ℝ) ≤ max R 1 := le_max_right _ _
        have hC0ge1 : (1:ℝ) ≤ 2 * (max R 1)^2 := by nlinarith [sq_nonneg (max R 1), hM1]
        have h1 : (1:ℝ) ≤ (2 * (max R 1)^2)^i := one_le_pow₀ hC0ge1
        have h2 : (2:ℝ) ≤ 2^i := by
          calc (2:ℝ) = 2^1 := by ring
            _ ≤ 2^i := pow_le_pow_right₀ (by norm_num) hi
        calc (2 * (max R 1)^2)^i + 1
            ≤ (2 * (max R 1)^2)^i + (2 * (max R 1)^2)^i := add_le_add (le_refl _) h1
          _ = 2 * (2 * (max R 1)^2)^i := by ring
          _ ≤ 2^i * (2 * (max R 1)^2)^i := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = (4 * (max R 1)^2)^i := by rw [← mul_pow]; ring_nf

/-- The explicit derivative bound for `dUf`. -/
private def dUfBound (R : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m+1), (m.choose i : ℝ) * (max R 1) *
    (((m - i).factorial : ℝ) * Real.exp 1 * (4 * (max R 1)^2)^(m - i))

private lemma dUfBound_nonneg (R : ℝ) (m : ℕ) : 0 ≤ dUfBound R m := by
  unfold dUfBound
  exact Finset.sum_nonneg (fun i _ => by positivity)

private lemma dUf_iteratedFDeriv_le {R : ℝ} {w : ℂ × ℝ} (hw1 : ‖w.1‖ < R) (hw2 : 0 < w.2) (m : ℕ) :
    ‖iteratedFDeriv ℝ m dUf w‖ ≤ dUfBound R m := by
  have hUb : ∀ j : ℕ, ‖iteratedFDeriv ℝ j (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ)) w‖
      ≤ (j.factorial : ℝ) * Real.exp 1 * (4 * (max R 1)^2)^j := by
    intro j
    have hEq : ‖iteratedFDeriv ℝ j (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ)) w‖
        = ‖iteratedFDeriv ℝ j (Real.exp ∘ uKappa) w‖ := by
      rw [show (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ))
            = (⇑Complex.ofRealLI) ∘ (Real.exp ∘ uKappa) from rfl]
      exact LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI
        ((Real.contDiff_exp.comp contDiff_uKappa).contDiffAt) (by exact_mod_cast le_top)
    rw [hEq]
    refine le_trans (norm_iteratedFDeriv_comp_le (g := Real.exp) (f := uKappa) (n := j)
      Real.contDiff_exp contDiff_uKappa (by exact_mod_cast le_top : (↑j : ℕ∞ω) ≤ ∞) w
      (C := Real.exp 1) (D := 4 * (max R 1)^2) ?_ ?_) (by rfl)
    · intro i _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have he : iteratedDeriv i Real.exp (uKappa w) = Real.exp (uKappa w) := by
        simpa using congrFun (iteratedDeriv_exp_const_mul i 1) (uKappa w)
      rw [he, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (le_of_lt (uKappa_lt_one hw2))
    · intro i hi _
      exact uKappa_iteratedFDeriv_le hw1 hi
  have hfst : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => (w.1 : ℂ)) w‖ ≤ max R 1 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [norm_iteratedFDeriv_zero]
      exact le_trans (le_of_lt hw1) (le_max_left _ _)
    · refine le_trans (norm_iteratedFDeriv_clm_le (ContinuousLinearMap.fst ℝ ℂ ℝ) hpos w) ?_
      exact le_trans (ContinuousLinearMap.norm_fst_le ℝ ℂ ℝ) (le_max_right _ _)
  have hdf : dUf = (fun w : ℂ × ℝ => (w.1 : ℂ)) * (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ)) :=
    funext (fun w => by rw [dUf_apply, Pi.mul_apply])
  have hf : ContDiff ℝ ((m:ℕ):ℕ∞ω) (fun w : ℂ × ℝ => (w.1 : ℂ)) :=
    (ContinuousLinearMap.fst ℝ ℂ ℝ).contDiff
  have hg : ContDiff ℝ ((m:ℕ):ℕ∞ω) (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ)) :=
    (Complex.ofRealCLM.contDiff (n := ((m:ℕ):ℕ∞ω))).comp
      ((Real.contDiff_exp.comp contDiff_uKappa).of_le (by exact_mod_cast le_top))
  rw [hdf]
  refine le_trans (norm_iteratedFDeriv_mul_le hf hg w le_rfl) ?_
  unfold dUfBound
  apply Finset.sum_le_sum
  intro i hi
  have h1 := hfst i
  have h2 := hUb (m - i)
  have hc : (0:ℝ) ≤ (m.choose i : ℝ) := by positivity
  have hM : (0:ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right _ _)
  have hb2 : (0:ℝ) ≤ ((m - i).factorial : ℝ) * Real.exp 1 * (4 * (max R 1)^2)^(m - i) := by positivity
  have hb1 : (0:ℝ) ≤ ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => (w.1 : ℂ)) w‖ := norm_nonneg _
  calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : ℂ × ℝ => (w.1 : ℂ)) w‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun w : ℂ × ℝ => (Real.exp (uKappa w) : ℂ)) w‖
      ≤ (m.choose i : ℝ) * (max R 1) *
          (((m - i).factorial : ℝ) * Real.exp 1 * (4 * (max R 1)^2)^(m - i)) := by
        gcongr
    _ = (m.choose i : ℝ) * (max R 1) *
          (((m - i).factorial : ℝ) * Real.exp 1 * (4 * (max R 1)^2)^(m - i)) := rfl

/-! ## 4. Transport to `discUnfold2` -/

/-- Projection `((x,z),t) ↦ x`. -/
private def unProjX : (((X × ℂ) × ℝ)) →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X ℂ).comp (ContinuousLinearMap.fst ℝ (X × ℂ) ℝ)

/-- Projection `((x,z),t) ↦ (z,t)`. -/
private def unTau : ((X × ℂ) × ℝ) →L[ℝ] ℂ × ℝ :=
  (ContinuousLinearMap.snd ℝ X ℂ).prodMap (ContinuousLinearMap.id ℝ ℝ)

@[simp] lemma unProjX_apply (p : (X × ℂ) × ℝ) : unProjX p = p.1.1 := rfl
@[simp] lemma unTau_apply (p : (X × ℂ) × ℝ) : unTau p = (p.1.2, p.2) := rfl

private lemma discUnfold2_eq_dUf (p : (X × ℂ) × ℝ) :
    discUnfold2 p = (unProjX p, dUf (unTau p)) := rfl

/-- For `m ≥ 1` the iterated derivatives of a continuous linear map do not depend on the point. -/
private lemma iteratedFDeriv_clm_const' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {m : ℕ} (hm : 1 ≤ m) (x y : E) :
    iteratedFDeriv ℝ m (fun z : E => L z) x = iteratedFDeriv ℝ m (fun z : E => L z) y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [iteratedFDeriv_clm_const L n]

/-- Splitting a `prod` of multilinear maps and subtracting. -/
private lemma cmm_prod_sub_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X']
    (K : ContinuousMultilinearMap ℝ E X') (A B : ContinuousMultilinearMap ℝ E ℂ) :
    K.prod A - K.prod B = (0 : ContinuousMultilinearMap ℝ E X').prod (A - B) := by
  ext m <;> simp [ContinuousMultilinearMap.prod_apply, Function.comp_apply]

/-- `compContinuousLinearMap` is additive in the multilinear map. -/
private lemma cmm_sub_comp {ι : Type*} [Fintype ι] {E E' : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace ℝ (E' i)]
    (A B : ContinuousMultilinearMap ℝ E' ℂ) (g : ∀ i, E i →L[ℝ] E' i) :
    A.compContinuousLinearMap g - B.compContinuousLinearMap g
      = (A - B).compContinuousLinearMap g := by
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-! ## 5. The target theorem -/

set_option maxHeartbeats 1600000 in
theorem discUnfold2HolderData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {R : ℝ} (hR : 0 < R) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, ∃ D E : ℕ → ℝ,
      (∀ (U : Set X), IsOpen U → ∀ p : (X × ℂ) × ℝ,
        p ∈ (U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ) →
        ∀ q : (X × ℂ) × ℝ, q ∈ (U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ) →
        ‖Work.NN.Final.discUnfold2 p - Work.NN.Final.discUnfold2 q‖ ≤ L * ‖p - q‖) ∧
      (∀ (U : Set X), IsOpen U → ∀ m : ℕ, 1 ≤ m → ∀ p : (X × ℂ) × ℝ,
        p ∈ (U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ) →
        ‖iteratedFDerivWithin ℝ m Work.NN.Final.discUnfold2
          ((U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ)) p‖ ≤ D m) ∧
      (∀ (U : Set X), IsOpen U → ∀ m : ℕ, 1 ≤ m → ∀ p : (X × ℂ) × ℝ,
        p ∈ (U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ) →
        ∀ q : (X × ℂ) × ℝ, q ∈ (U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ) →
        ‖iteratedFDerivWithin ℝ m Work.NN.Final.discUnfold2
            ((U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ)) p
          - iteratedFDerivWithin ℝ m Work.NN.Final.discUnfold2
            ((U ×ˢ Metric.ball (0 : ℂ) R) ×ˢ Set.Ioi (0 : ℝ)) q‖
          ≤ E m * ‖p - q‖ ^ α) := by
  set s : Set (ℂ × ℝ) := Metric.ball (0:ℂ) R ×ˢ Set.Ioi (0:ℝ) with hsdef
  have hsopen : IsOpen s := by rw [hsdef]; exact isOpen_ball.prod isOpen_Ioi
  have hconv : Convex ℝ s := by rw [hsdef]; exact (convex_ball _ _).prod (convex_Ioi _)
  have hA : ∀ m, ∀ w ∈ s, ‖iteratedFDeriv ℝ m dUf w‖ ≤ dUfBound R m := by
    intro m w hw
    rw [hsdef, mem_prod] at hw
    obtain ⟨hw1, hw2⟩ := hw
    exact dUf_iteratedFDeriv_le (by simpa only [mem_ball, dist_eq_norm, sub_zero] using hw1)
      (by simpa only [mem_Ioi] using hw2) m
  obtain ⟨L0, D0, E0, hL0, hD0, hE0⟩ :=
    holderDataConvex hsopen hconv contDiff_omega_dUf hA (dUfBound_nonneg R) hα hα1
  refine ⟨max ‖unProjX (X := X)‖ (L0 * ‖unTau (X := X)‖),
          (fun m => max ‖unProjX (X := X)‖ (D0 m * ‖unTau (X := X)‖^m)),
          (fun m => max (E0 m) 0 * ‖unTau (X := X)‖^α * ‖unTau (X := X)‖^m), ?_, ?_, ?_⟩
  · -- Lipschitz
    intro U hU p hp q hq
    have hτp : unTau p ∈ s := by
      rw [hsdef, mem_prod, unTau_apply]
      exact ⟨by simpa only [mem_ball, dist_eq_norm, sub_zero] using hp.1.2,
             by simpa only [mem_Ioi] using hp.2⟩
    have hτq : unTau q ∈ s := by
      rw [hsdef, mem_prod, unTau_apply]
      exact ⟨by simpa only [mem_ball, dist_eq_norm, sub_zero] using hq.1.2,
             by simpa only [mem_Ioi] using hq.2⟩
    have h1 := hL0.2 (unTau p) hτp (unTau q) hτq
    have hpq : 0 ≤ ‖p - q‖ := norm_nonneg _
    have hτ : ‖unTau p - unTau q‖ ≤ ‖unTau (X := X)‖ * ‖p - q‖ := by
      rw [← map_sub]; exact (unTau (X := X)).le_opNorm (p - q)
    calc ‖discUnfold2 p - discUnfold2 q‖
        = max ‖unProjX p - unProjX q‖ ‖dUf (unTau p) - dUf (unTau q)‖ := by
          simp only [discUnfold2_eq_dUf, Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
      _ ≤ max (‖unProjX (X := X)‖ * ‖p - q‖) (L0 * (‖unTau (X := X)‖ * ‖p - q‖)) := by
          apply max_le_max
          · rw [← map_sub]; exact (unProjX (X := X)).le_opNorm (p - q)
          · exact le_trans h1 (mul_le_mul_of_nonneg_left hτ hL0.1)
      _ ≤ max ‖unProjX (X := X)‖ (L0 * ‖unTau (X := X)‖) * ‖p - q‖ := by
          apply max_le
          · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpq
          · calc L0 * (‖unTau (X := X)‖ * ‖p - q‖) = (L0 * ‖unTau (X := X)‖) * ‖p - q‖ := by ring
              _ ≤ max ‖unProjX (X := X)‖ (L0 * ‖unTau (X := X)‖) * ‖p - q‖ :=
                  mul_le_mul_of_nonneg_right (le_max_right _ _) hpq
  · -- derivative bounds
    intro U hU m hm p hp
    have hΩ : IsOpen ((U ×ˢ Metric.ball (0:ℂ) R) ×ˢ Set.Ioi (0:ℝ)) :=
      (hU.prod isOpen_ball).prod isOpen_Ioi
    rw [iteratedFDerivWithin_of_isOpen m hΩ hp]
    have hτp : unTau p ∈ s := by
      rw [hsdef, mem_prod, unTau_apply]
      exact ⟨by simpa only [mem_ball, dist_eq_norm, sub_zero] using hp.1.2,
             by simpa only [mem_Ioi] using hp.2⟩
    have hf : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => unProjX p) p :=
      (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unProjX (X := X))).contDiffAt
    have hg : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => dUf (unTau p)) p :=
      ((contDiff_dUf.of_le (by exact_mod_cast le_top)).comp
        (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unTau (X := X)))).contDiffAt
    have hprod : iteratedFDeriv ℝ m discUnfold2 p
        = (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => unProjX p) p).prod
          (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => dUf (unTau p)) p) := by
      rw [show discUnfold2 = (fun p : (X × ℂ) × ℝ => (unProjX p, dUf (unTau p))) from
            funext discUnfold2_eq_dUf]
      exact iteratedFDeriv_prodMk hf hg le_rfl
    rw [hprod, ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact le_trans (norm_iteratedFDeriv_clm_le (unProjX (X := X)) hm p) (le_max_left _ _)
    · rw [show (fun p : (X × ℂ) × ℝ => dUf (unTau p)) = dUf ∘ ⇑(unTau (X := X)) from rfl,
          ContinuousLinearMap.iteratedFDeriv_comp_right (unTau (X := X))
            (contDiff_dUf.of_le (by exact_mod_cast le_top)) p le_rfl]
      calc ‖(iteratedFDeriv ℝ m dUf (unTau p)).compContinuousLinearMap (fun _ => (unTau (X := X)))‖
          ≤ ‖iteratedFDeriv ℝ m dUf (unTau p)‖ * ∏ _ : Fin m, ‖unTau (X := X)‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ m dUf (unTau p)‖ * ‖unTau (X := X)‖^m := by
            rw [Finset.prod_const, Finset.card_fin]
        _ ≤ D0 m * ‖unTau (X := X)‖^m := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [← iteratedFDerivWithin_of_isOpen m hsopen hτp]
            exact hD0 m hm (unTau p) hτp
        _ ≤ max ‖unProjX (X := X)‖ (D0 m * ‖unTau (X := X)‖^m) := le_max_right _ _
  · -- Hölder
    intro U hU m hm p hp q hq
    have hΩ : IsOpen ((U ×ˢ Metric.ball (0:ℂ) R) ×ˢ Set.Ioi (0:ℝ)) :=
      (hU.prod isOpen_ball).prod isOpen_Ioi
    rw [iteratedFDerivWithin_of_isOpen m hΩ hp, iteratedFDerivWithin_of_isOpen m hΩ hq]
    have hτp : unTau p ∈ s := by
      rw [hsdef, mem_prod, unTau_apply]
      exact ⟨by simpa only [mem_ball, dist_eq_norm, sub_zero] using hp.1.2,
             by simpa only [mem_Ioi] using hp.2⟩
    have hτq : unTau q ∈ s := by
      rw [hsdef, mem_prod, unTau_apply]
      exact ⟨by simpa only [mem_ball, dist_eq_norm, sub_zero] using hq.1.2,
             by simpa only [mem_Ioi] using hq.2⟩
    obtain ⟨L0', hL0'⟩ := hL0
    have hf : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => unProjX p) p :=
      (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unProjX (X := X))).contDiffAt
    have hg : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => dUf (unTau p)) p :=
      ((contDiff_dUf.of_le (by exact_mod_cast le_top)).comp
        (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unTau (X := X)))).contDiffAt
    have hf' : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => unProjX p) q :=
      (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unProjX (X := X))).contDiffAt
    have hg' : ContDiffAt ℝ ((m:ℕ):ℕ∞ω) (fun p : (X × ℂ) × ℝ => dUf (unTau p)) q :=
      ((contDiff_dUf.of_le (by exact_mod_cast le_top)).comp
        (ContinuousLinearMap.contDiff (n := ((m:ℕ):ℕ∞ω)) (unTau (X := X)))).contDiffAt
    have hfp : iteratedFDeriv ℝ m discUnfold2 p
        = (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => unProjX p) p).prod
          (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => dUf (unTau p)) p) := by
      rw [show discUnfold2 = (fun p : (X × ℂ) × ℝ => (unProjX p, dUf (unTau p))) from
            funext discUnfold2_eq_dUf]
      exact iteratedFDeriv_prodMk hf hg le_rfl
    have hfq : iteratedFDeriv ℝ m discUnfold2 q
        = (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => unProjX p) q).prod
          (iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => dUf (unTau p)) q) := by
      rw [show discUnfold2 = (fun p : (X × ℂ) × ℝ => (unProjX p, dUf (unTau p))) from
            funext discUnfold2_eq_dUf]
      exact iteratedFDeriv_prodMk hf' hg' le_rfl
    have hK : iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => unProjX p) p
        = iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => unProjX p) q :=
      iteratedFDeriv_clm_const' (unProjX (X := X)) hm p q
    have hAB : iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => dUf (unTau p)) p
        - iteratedFDeriv ℝ m (fun p : (X × ℂ) × ℝ => dUf (unTau p)) q
        = ((iteratedFDeriv ℝ m dUf (unTau p)) - (iteratedFDeriv ℝ m dUf (unTau q))).compContinuousLinearMap
            (fun _ => (unTau (X := X))) := by
      rw [show (fun p : (X × ℂ) × ℝ => dUf (unTau p)) = dUf ∘ ⇑(unTau (X := X)) from rfl]
      rw [ContinuousLinearMap.iteratedFDeriv_comp_right (unTau (X := X))
            (contDiff_dUf.of_le (by exact_mod_cast le_top)) p le_rfl,
          ContinuousLinearMap.iteratedFDeriv_comp_right (unTau (X := X))
            (contDiff_dUf.of_le (by exact_mod_cast le_top)) q le_rfl,
          cmm_sub_comp]
    have hstep : iteratedFDeriv ℝ m discUnfold2 p - iteratedFDeriv ℝ m discUnfold2 q
        = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) X).prod
            ((iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)).compContinuousLinearMap
              (fun _ => (unTau (X := X)))) := by
      rw [hfp, hfq, hK, cmm_prod_sub_prod, hAB]
    have hmain : ‖iteratedFDeriv ℝ m discUnfold2 p - iteratedFDeriv ℝ m discUnfold2 q‖
        ≤ ‖iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)‖ * ‖unTau (X := X)‖^m := by
      rw [hstep, ContinuousMultilinearMap.opNorm_prod, norm_zero, max_eq_right (norm_nonneg _)]
      calc ‖((iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)).compContinuousLinearMap
              (fun _ => (unTau (X := X))))‖
          ≤ ‖iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)‖ *
              ∏ _ : Fin m, ‖unTau (X := X)‖ := ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ = ‖iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)‖ * ‖unTau (X := X)‖^m := by
            rw [Finset.prod_const, Finset.card_fin]
    have hHolder : ‖iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)‖
        ≤ E0 m * ‖unTau p - unTau q‖^α := by
      rw [← iteratedFDerivWithin_of_isOpen m hsopen hτp,
          ← iteratedFDerivWithin_of_isOpen m hsopen hτq]
      exact hE0 m hm (unTau p) hτp (unTau q) hτq
    have hτ : ‖unTau p - unTau q‖ ≤ ‖unTau (X := X)‖ * ‖p - q‖ := by
      rw [← map_sub]; exact (unTau (X := X)).le_opNorm (p - q)
    calc ‖iteratedFDeriv ℝ m discUnfold2 p - iteratedFDeriv ℝ m discUnfold2 q‖
        ≤ ‖iteratedFDeriv ℝ m dUf (unTau p) - iteratedFDeriv ℝ m dUf (unTau q)‖ * ‖unTau (X := X)‖^m := hmain
      _ ≤ (E0 m * ‖unTau p - unTau q‖^α) * ‖unTau (X := X)‖^m :=
          mul_le_mul_of_nonneg_right hHolder (by positivity)
      _ ≤ (max (E0 m) 0 * ‖unTau (X := X)‖^α * ‖unTau (X := X)‖^m) * ‖p - q‖^α := by
          have hd : ‖unTau p - unTau q‖^α ≤ ‖unTau (X := X)‖^α * ‖p - q‖^α := by
            calc ‖unTau p - unTau q‖^α ≤ (‖unTau (X := X)‖ * ‖p - q‖)^α :=
                  Real.rpow_le_rpow (norm_nonneg _) hτ (le_of_lt hα)
              _ = ‖unTau (X := X)‖^α * ‖p - q‖^α :=
                  Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
          calc (E0 m * ‖unTau p - unTau q‖^α) * ‖unTau (X := X)‖^m
              ≤ (max (E0 m) 0 * ‖unTau p - unTau q‖^α) * ‖unTau (X := X)‖^m := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
            _ ≤ (max (E0 m) 0 * (‖unTau (X := X)‖^α * ‖p - q‖^α)) * ‖unTau (X := X)‖^m :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hd (le_max_right _ _)) (by positivity)
            _ = (max (E0 m) 0 * ‖unTau (X := X)‖^α * ‖unTau (X := X)‖^m) * ‖p - q‖^α := by ring

end Work.NN.Final
