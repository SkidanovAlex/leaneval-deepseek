import Mathlib
import Submission.Commons.Analysis.Complex.hadamard_three_lines
import Submission.Commons.Analysis.Integral.holder_complex_finset
import Submission.Commons.Analysis.Integral.exists_dual_witness
import Submission.Commons.Analysis.Integral.exists_unit_witness_l1
import Submission.Commons.Analysis.Real.lpn_smul_eq

open scoped BigOperators

namespace Commons.Analysis.Integral

noncomputable section

/-- Phase function `w / ‖w‖` (and `0` when `w = 0`). -/
private def ph (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

private lemma norm_ph_eq_one {w : ℂ} (hw : w ≠ 0) : ‖ph w‖ = 1 := by
  rw [ph, norm_div, show ‖(((‖w‖ : ℝ)) : ℂ)‖ = ‖w‖ by simp,
    div_self (norm_ne_zero_iff.mpr hw)]

private lemma ph_eq_zero {w : ℂ} (hw : w = 0) : ph w = 0 := by
  subst hw; simp [ph]

private lemma norm_ph_le_one (w : ℂ) : ‖ph w‖ ≤ 1 := by
  rcases eq_or_ne w 0 with h | h
  · subst h; simp [ph]
  · rw [norm_ph_eq_one h]

private lemma norm_mul_ph (w : ℂ) : ((‖w‖ : ℝ) : ℂ) * ph w = w := by
  rcases eq_or_ne w 0 with h | h
  · subst h; simp [ph]
  · rw [ph, ← mul_div_assoc]
    exact mul_div_cancel_left₀ w (by simpa using (norm_ne_zero_iff.mpr h : ‖w‖ ≠ 0))

/-- Interpolation vector: `a ↦ ‖φ a‖ ^ (t z) · ph (φ a)`. -/
private def interp {ι : Type*} (φ : ι → ℂ) (t : ℂ → ℂ) (z : ℂ) : ι → ℂ :=
  fun a => ((‖φ a‖ : ℝ) : ℂ) ^ (t z) * ph (φ a)

private lemma interp_apply {ι : Type*} (φ : ι → ℂ) (t : ℂ → ℂ) (z : ℂ) (a : ι) :
    interp φ t z a = ((‖φ a‖ : ℝ) : ℂ) ^ (t z) * ph (φ a) := rfl

private lemma norm_interp {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} {z : ℂ} (hz : 0 < (t z).re) (a : ι) :
    ‖interp φ t z a‖ = ‖φ a‖ ^ (t z).re := by
  rcases eq_or_ne (φ a) 0 with h | h
  · rw [interp_apply, h]
    simp only [norm_zero, Complex.ofReal_zero]
    rw [ph_eq_zero rfl, mul_zero, norm_zero, Real.zero_rpow (ne_of_gt hz)]
  · rw [interp_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr h),
      norm_ph_eq_one h, mul_one]

private lemma interp_self {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} {θ : ℂ} (hθ : t θ = 1) :
    interp φ t θ = φ := by
  funext a
  rw [interp_apply, hθ, Complex.cpow_one]
  exact norm_mul_ph (φ a)

private lemma differentiable_interp {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} (ht : Differentiable ℂ t) (a : ι) :
    Differentiable ℂ (fun z => interp φ t z a) := by
  rcases eq_or_ne (φ a) 0 with h | h
  · have hzero : (fun z => interp φ t z a) = fun _ => (0 : ℂ) := by
      funext z
      rw [interp_apply, h]
      simp only [norm_zero, Complex.ofReal_zero]
      rw [ph_eq_zero rfl, mul_zero]
    rw [hzero]; exact differentiable_const 0
  · have hc : ((‖φ a‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr h
    have hd : Differentiable ℂ (fun z => ((‖φ a‖ : ℝ) : ℂ) ^ (t z)) :=
      ht.const_cpow (Or.inl hc)
    simpa [interp] using hd.mul_const (ph (φ a))

/-- The affine map `z ↦ A + B*z`. -/
private def affine (A B : ℝ) (z : ℂ) : ℂ := (A : ℂ) + (B : ℂ) * z

private lemma affine_re (A B : ℝ) (z : ℂ) : (affine A B z).re = A + B * z.re := by
  simp [affine, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma differentiable_affine (A B : ℝ) : Differentiable ℂ (affine A B) := by
  unfold affine; fun_prop

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

private lemma linearMap_apply_eq_sum (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (v : α → ℂ) (b : β) :
    T v b = ∑ a, v a * (T (Pi.single a 1)) b := by
  have hv : v = ∑ a, Pi.single a (v a) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : Pi.single a (v a) = (v a) • Pi.single a (1:ℂ) := by
    ext c
    rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hc : c = a <;> simp [hc]
  rw [hs, map_smul]
  simp [Pi.smul_apply, smul_eq_mul]

private lemma differentiable_linearMap_interp (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (φ : α → ℂ)
    {t : ℂ → ℂ} (ht : Differentiable ℂ t) (b : β) :
    Differentiable ℂ (fun z => (T (interp φ t z)) b) := by
  have h : (fun z => (T (interp φ t z)) b)
      = fun z => ∑ a, interp φ t z a * (T (Pi.single a 1)) b := by
    funext z; exact linearMap_apply_eq_sum T (interp φ t z) b
  rw [h]
  exact Differentiable.fun_sum fun a _ => (differentiable_interp φ ht a).mul_const _


private lemma norm_interp_of_ne {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} {z : ℂ} {a : ι} (h : φ a ≠ 0) :
    ‖interp φ t z a‖ = ‖φ a‖ ^ (t z).re := by
  rw [interp_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr h),
    norm_ph_eq_one h, mul_one]

private lemma norm_interp_le {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hz0 : 0 ≤ (t z).re) (hz1 : (t z).re ≤ M) (a : ι) :
    ‖interp φ t z a‖ ≤ max 1 (‖φ a‖ ^ M) := by
  by_cases h : φ a = 0
  · have hL : ‖interp φ t z a‖ = 0 := by
      rw [interp_apply, h]
      simp only [norm_zero, Complex.ofReal_zero]
      rw [ph_eq_zero rfl, mul_zero, norm_zero]
    rw [hL]
    exact le_trans zero_le_one (le_max_left (1:ℝ) (‖φ a‖ ^ M))
  · rw [norm_interp_of_ne φ h]
    rcases lt_or_ge 1 (‖φ a‖) with h1 | h1
    · have hX : 1 ≤ ‖φ a‖ ^ M := by
        simpa [Real.one_rpow] using Real.rpow_le_rpow (zero_le_one (α := ℝ)) h1.le hM
      rw [max_eq_right hX]
      exact Real.rpow_le_rpow_of_exponent_le h1.le hz1
    · have hX : ‖φ a‖ ^ M ≤ 1 := Real.rpow_le_one (norm_nonneg _) h1 hM
      rw [max_eq_left hX]
      exact Real.rpow_le_one (norm_nonneg _) h1 hz0

private lemma sum_norm_interp_rpow {ι : Type*} [Fintype ι] (φ : ι → ℂ) {t : ℂ → ℂ} {z : ℂ}
    {R P : ℝ} (hR : 0 < R) (hP : 0 < P) (hz : (t z).re = R) :
    (∑ a, ‖interp φ t z a‖ ^ P) = ∑ a, ‖φ a‖ ^ (R * P) := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : φ a = 0
  · rw [interp_apply, h]
    simp only [norm_zero, Complex.ofReal_zero]
    rw [ph_eq_zero rfl, mul_zero, norm_zero, Real.zero_rpow (ne_of_gt hP),
      Real.zero_rpow (ne_of_gt (mul_pos hR hP))]
  · rw [norm_interp_of_ne φ h, hz, ← Real.rpow_mul (norm_nonneg _) R P]

private lemma norm_interp_le_one {ι : Type*} (φ : ι → ℂ) {t : ℂ → ℂ} {z : ℂ}
    (hz : (t z).re = 0) (a : ι) : ‖interp φ t z a‖ ≤ 1 := by
  by_cases h : φ a = 0
  · have hL : ‖interp φ t z a‖ = 0 := by
      rw [interp_apply, h]
      simp only [norm_zero, Complex.ofReal_zero]
      rw [ph_eq_zero rfl, mul_zero, norm_zero]
    rw [hL]; exact zero_le_one
  · rw [norm_interp_of_ne φ h, hz, Real.rpow_zero]

/-- The three-lines generating function. -/
private def F (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (f : α → ℂ) (g : β → ℂ) (t s : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ b, (T (interp f t z)) b * (interp g s z) b

private lemma differentiable_F (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (f : α → ℂ) (g : β → ℂ)
    {t s : ℂ → ℂ} (ht : Differentiable ℂ t) (hs : Differentiable ℂ s) :
    Differentiable ℂ (F T f g t s) := by
  unfold F
  exact Differentiable.fun_sum fun b _ =>
    (differentiable_linearMap_interp T f ht b).mul (differentiable_interp g hs b)

private lemma three_lines_F (T : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (f : α → ℂ) (g : β → ℂ) {t s : ℂ → ℂ}
    {M0 M1 Bb θ : ℝ} (hM0 : 0 < M0) (hM1 : 0 < M1)
    (ht : Differentiable ℂ t) (hs : Differentiable ℂ s)
    (hBdd : ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖F T f g t s z‖ ≤ Bb)
    (hb0 : ∀ y : ℝ, ‖F T f g t s ((y : ℂ) * Complex.I)‖ ≤ M0)
    (hb1 : ∀ y : ℝ, ‖F T f g t s (1 + (y : ℂ) * Complex.I)‖ ≤ M1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (htθ : t (θ : ℂ) = 1) (hsθ : s (θ : ℂ) = 1) :
    ‖∑ b, (T f) b * g b‖ ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  have hd := differentiable_F T f g ht hs
  have h := Commons.Analysis.Complex.hadamard_three_lines (F T f g t s) hd hM0 hM1 hBdd hb0 hb1 (θ : ℂ)
    (by simp [Complex.ofReal_re, hθ0]) (by simp [Complex.ofReal_re, hθ1])
  rw [Complex.ofReal_re] at h
  have hFθ : F T f g t s (θ : ℂ) = ∑ b, (T f) b * g b := by
    simp only [F]
    rw [interp_self f htθ, interp_self g hsθ]
  rwa [hFθ] at h

private lemma self_le_lp {ι : Type*} [Fintype ι] (u : ι → ℂ) {q : ℝ} (hq : 0 < q) (b : ι) :
    ‖u b‖ ≤ (∑ i, ‖u i‖ ^ q) ^ (1 / q) := by
  have h1 : ‖u b‖ ^ q ≤ ∑ i, ‖u i‖ ^ q :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (norm_nonneg _) q) (Finset.mem_univ b)
  have hb : ‖u b‖ = (‖u b‖ ^ q) ^ (1 / q) := by
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div,
      div_self (ne_of_gt hq), Real.rpow_one]
  rw [hb]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) q) h1 (by positivity)

private lemma core_gt
    (T : (α → ℂ) →ₗ[ℂ] (β → ℂ))
    {p0 p1 q0 q1 : ℝ} (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) (hq0 : 1 ≤ q0) (hq1 : 1 ≤ q1)
    {M0 M1 : ℝ} (hM0 : 0 < M0) (hM1 : 0 < M1)
    (hT0 : ∀ f : α → ℂ, (∑ b, ‖T f b‖ ^ q0) ^ (1 / q0) ≤ M0 * (∑ a, ‖f a‖ ^ p0) ^ (1 / p0))
    (hT1 : ∀ f : α → ℂ, (∑ b, ‖T f b‖ ^ q1) ^ (1 / q1) ≤ M1 * (∑ a, ‖f a‖ ^ p1) ^ (1 / p1))
    {θ pθ qθ Q : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpθ1 : 1 ≤ pθ) (hqθ1 : 1 < qθ) (hQ1 : 1 < Q)
    (hpθ : pθ⁻¹ = (1 - θ) * p0⁻¹ + θ * p1⁻¹)
    (hqθ : qθ⁻¹ = (1 - θ) * q0⁻¹ + θ * q1⁻¹)
    (hQ : qθ⁻¹ + Q⁻¹ = 1) :
    ∀ (f : α → ℂ) (g : β → ℂ), (∑ a, ‖f a‖ ^ pθ) = 1 → (∑ b, ‖g b‖ ^ Q) = 1 →
      ‖∑ b, (T f) b * g b‖ ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  classical
  intro f g hf hg
  set A : ℝ := pθ / p0 with hA
  set B : ℝ := pθ / p1 - pθ / p0 with hB
  set A0 : ℝ := (q0 - 1) * Q / q0 with hA0
  set A1 : ℝ := (q1 - 1) * Q / q1 with hA1
  have hpθpos : 0 < pθ := by linarith
  have hp0pos : 0 < p0 := by linarith
  have hp1pos : 0 < p1 := by linarith
  have hq0pos : 0 < q0 := by linarith
  have hq1pos : 0 < q1 := by linarith
  have hApos : 0 < A := by rw [hA]; exact div_pos hpθpos hp0pos
  have hpp1pos : 0 < pθ / p1 := div_pos hpθpos hp1pos
  have hAB : A + B = pθ / p1 := by rw [hA, hB]; ring
  have hA0nn : 0 ≤ A0 := by rw [hA0]; positivity
  have hA1nn : 0 ≤ A1 := by rw [hA1]; positivity
  set Mt : ℝ := max A (pθ / p1) with hMt
  set Ms : ℝ := max A0 A1 with hMs
  have hMtnn : 0 ≤ Mt := le_trans hApos.le (le_max_left _ _)
  have hMsnn : 0 ≤ Ms := le_trans hA0nn (le_max_left _ _)
  -- theta data
  have hkey : (1 - θ) / p0 + θ / p1 = 1 / pθ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, one_div]; exact hpθ.symm
  have hAθ : A + B * θ = 1 := by
    rw [hA, hB]
    have h : pθ / p0 + (pθ / p1 - pθ / p0) * θ = pθ * ((1 - θ) / p0 + θ / p1) := by ring
    rw [h, hkey, mul_one_div, div_self (ne_of_gt hpθpos)]
  have htθ : affine A B (θ : ℂ) = 1 := by
    have h : affine A B (θ : ℂ) = ((A + B * θ : ℝ) : ℂ) := by
      simp only [affine]; rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [h, hAθ, Complex.ofReal_one]
  have hkey2 : (1 - θ) * ((q0 - 1) / q0) + θ * ((q1 - 1) / q1) = Q⁻¹ := by
    have h1 : (q0 - 1) / q0 = 1 - 1 / q0 := by field_simp
    have h2 : (q1 - 1) / q1 = 1 - 1 / q1 := by field_simp
    have hqθ' : (1 - θ) / q0 + θ / q1 = 1 / qθ := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_div]; exact hqθ.symm
    rw [h1, h2]
    have hrw : (1 - θ) * (1 - 1 / q0) + θ * (1 - 1 / q1) = 1 - ((1 - θ) / q0 + θ / q1) := by ring
    rw [hrw, hqθ', one_div]
    linarith [hQ]
  have hA0A1θ : A0 + (A1 - A0) * θ = 1 := by
    rw [hA0, hA1]
    have h : (q0 - 1) * Q / q0 + ((q1 - 1) * Q / q1 - (q0 - 1) * Q / q0) * θ
        = Q * ((1 - θ) * ((q0 - 1) / q0) + θ * ((q1 - 1) / q1)) := by ring
    rw [h, hkey2, mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one hQ1))]
  have hsθ : affine A0 (A1 - A0) (θ : ℂ) = 1 := by
    have h : affine A0 (A1 - A0) (θ : ℂ) = ((A0 + (A1 - A0) * θ : ℝ) : ℂ) := by
      simp only [affine]; rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [h, hA0A1θ, Complex.ofReal_one]
  -- boundary real parts
  have htre0 : ∀ z : ℂ, z.re = 0 → (affine A B z).re = pθ / p0 := by
    intro z hz; rw [affine_re, hz, mul_zero, add_zero, hA]
  have htre1 : ∀ z : ℂ, z.re = 1 → (affine A B z).re = pθ / p1 := by
    intro z hz; rw [affine_re, hz, mul_one, hAB]
  have hsre0 : ∀ z : ℂ, z.re = 0 → (affine A0 (A1 - A0) z).re = A0 := by
    intro z hz; rw [affine_re, hz, mul_zero, add_zero]
  have hsre1 : ∀ z : ℂ, z.re = 1 → (affine A0 (A1 - A0) z).re = A1 := by
    intro z hz; rw [affine_re, hz, mul_one]; ring
  -- hbound0
  have hbound0 : ∀ y : ℝ, ‖F T f g (affine A B) (affine A0 (A1 - A0)) ((y : ℂ) * Complex.I)‖ ≤ M0 := by
    intro y
    set z : ℂ := (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 0 := by rw [hzdef]; simp
    have htre : (affine A B z).re = pθ / p0 := htre0 z hzre
    have hsre : (affine A0 (A1 - A0) z).re = A0 := hsre0 z hzre
    have hsumf : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) = 1 := by
      rw [sum_norm_interp_rpow f (t := affine A B) (z := z) (R := pθ / p0) (P := p0)
        (div_pos hpθpos hp0pos) hp0pos htre]
      rw [div_mul_cancel₀ pθ (ne_of_gt hp0pos), hf]
    have hfz1 : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) ^ (1 / p0) = 1 := by
      rw [hsumf, Real.one_rpow]
    have hTnorm : (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0) ≤ M0 := by
      have h := hT0 (interp f (affine A B) z)
      rw [hfz1, mul_one] at h; exact h
    by_cases hq0one : q0 = 1
    · have hA0zero : A0 = 0 := by rw [hA0, hq0one]; ring
      have hw1 : ∀ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ≤ 1 := fun b =>
        norm_interp_le_one g (by rw [affine_re, hzre, mul_zero, add_zero, hA0zero]) b
      calc ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖
          = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ := rfl
        _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ :=
              norm_sum_le _ _
        _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine A0 (A1 - A0)) z) b‖ := by
              simp [norm_mul]
        _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b‖ * 1 := by
              apply Finset.sum_le_sum; intro b _
              exact mul_le_mul_of_nonneg_left (hw1 b) (norm_nonneg _)
        _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ := by simp
        _ ≤ (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0) := by
              rw [hq0one]; simp
        _ ≤ M0 := hTnorm
    · have hq0gt : 1 < q0 := lt_of_le_of_ne hq0 (Ne.symm hq0one)
      set r0 : ℝ := q0 / (q0 - 1) with hr0
      have hr0pos : 0 < r0 := by rw [hr0]; exact div_pos (by linarith) (by linarith)
      have hr0conj : Real.HolderConjugate q0 r0 := by
        rw [Real.holderConjugate_iff]
        refine ⟨hq0gt, ?_⟩
        rw [hr0]; field_simp; ring
      have hA0pos : 0 < A0 := by
        rw [hA0]; exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      have hsumg : (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r0) = 1 := by
        rw [sum_norm_interp_rpow g (t := affine A0 (A1 - A0)) (z := z) (R := A0) (P := r0)
          hA0pos hr0pos hsre]
        have h : A0 * r0 = Q := by rw [hA0, hr0]; field_simp
        rw [h, hg]
      have hgz1 : (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r0) ^ (1 / r0) = 1 := by
        rw [hsumg, Real.one_rpow]
      calc ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖
          = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ := rfl
        _ ≤ (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0)
              * (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r0) ^ (1 / r0) :=
              holder_complex_finset Finset.univ
                (fun b => (T (interp f (affine A B) z)) b)
                (fun b => (interp g (affine A0 (A1 - A0)) z) b) hr0conj
        _ = (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0) := by rw [hgz1, mul_one]
        _ ≤ M0 := hTnorm
  -- hbound1
  have hbound1 : ∀ y : ℝ, ‖F T f g (affine A B) (affine A0 (A1 - A0)) (1 + (y : ℂ) * Complex.I)‖ ≤ M1 := by
    intro y
    set z : ℂ := 1 + (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 1 := by rw [hzdef]; simp
    have htre : (affine A B z).re = pθ / p1 := htre1 z hzre
    have hsre : (affine A0 (A1 - A0) z).re = A1 := hsre1 z hzre
    have hsumf : (∑ a, ‖interp f (affine A B) z a‖ ^ p1) = 1 := by
      rw [sum_norm_interp_rpow f (t := affine A B) (z := z) (R := pθ / p1) (P := p1)
        hpp1pos hp1pos htre]
      rw [div_mul_cancel₀ pθ (ne_of_gt hp1pos), hf]
    have hfz1 : (∑ a, ‖interp f (affine A B) z a‖ ^ p1) ^ (1 / p1) = 1 := by
      rw [hsumf, Real.one_rpow]
    have hTnorm : (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q1) ^ (1 / q1) ≤ M1 := by
      have h := hT1 (interp f (affine A B) z)
      rw [hfz1, mul_one] at h; exact h
    by_cases hq1one : q1 = 1
    · have hA1zero : A1 = 0 := by rw [hA1, hq1one]; ring
      have hw1 : ∀ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ≤ 1 := fun b =>
        norm_interp_le_one g (by rw [affine_re, hzre, mul_one]; rw [hA1zero]; ring) b
      calc ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖
          = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ := rfl
        _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ :=
              norm_sum_le _ _
        _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine A0 (A1 - A0)) z) b‖ := by
              simp [norm_mul]
        _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b‖ * 1 := by
              apply Finset.sum_le_sum; intro b _
              exact mul_le_mul_of_nonneg_left (hw1 b) (norm_nonneg _)
        _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ := by simp
        _ ≤ (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q1) ^ (1 / q1) := by
              rw [hq1one]; simp
        _ ≤ M1 := hTnorm
    · have hq1gt : 1 < q1 := lt_of_le_of_ne hq1 (Ne.symm hq1one)
      set r1 : ℝ := q1 / (q1 - 1) with hr1
      have hr1pos : 0 < r1 := by rw [hr1]; exact div_pos (by linarith) (by linarith)
      have hr1conj : Real.HolderConjugate q1 r1 := by
        rw [Real.holderConjugate_iff]
        refine ⟨hq1gt, ?_⟩
        rw [hr1]; field_simp; ring
      have hA1pos : 0 < A1 := by
        rw [hA1]; exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      have hsumg : (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r1) = 1 := by
        rw [sum_norm_interp_rpow g (t := affine A0 (A1 - A0)) (z := z) (R := A1) (P := r1)
          hA1pos hr1pos hsre]
        have h : A1 * r1 = Q := by rw [hA1, hr1]; field_simp
        rw [h, hg]
      have hgz1 : (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r1) ^ (1 / r1) = 1 := by
        rw [hsumg, Real.one_rpow]
      calc ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖
          = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ := rfl
        _ ≤ (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q1) ^ (1 / q1)
              * (∑ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ^ r1) ^ (1 / r1) :=
              holder_complex_finset Finset.univ
                (fun b => (T (interp f (affine A B) z)) b)
                (fun b => (interp g (affine A0 (A1 - A0)) z) b) hr1conj
        _ = (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q1) ^ (1 / q1) := by rw [hgz1, mul_one]
        _ ≤ M1 := hTnorm
  -- boundedness
  set Bb : ℝ := M0 * (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) * (∑ b, max 1 (‖g b‖ ^ Ms))
    with hBbdef
  have hBdd : ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖ ≤ Bb := by
    intro z hz0 hz1
    have htreb : (affine A B z).re ≤ Mt := by
      rw [affine_re, hMt]
      rw [show A + B * z.re = (1 - z.re) * A + z.re * (pθ / p1) by rw [← hAB]; ring]
      calc (1 - z.re) * A + z.re * (pθ / p1)
          ≤ (1 - z.re) * max A (pθ / p1) + z.re * max A (pθ / p1) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hz0)
        _ = max A (pθ / p1) := by ring
    have htreb0 : 0 ≤ (affine A B z).re := by
      rw [affine_re, show A + B * z.re = (1 - z.re) * A + z.re * (pθ / p1) by rw [← hAB]; ring]
      exact add_nonneg (mul_nonneg (by linarith) hApos.le) (mul_nonneg hz0 hpp1pos.le)
    have hsreb : (affine A0 (A1 - A0) z).re ≤ Ms := by
      rw [affine_re, hMs]
      rw [show A0 + (A1 - A0) * z.re = (1 - z.re) * A0 + z.re * A1 by ring]
      calc (1 - z.re) * A0 + z.re * A1
          ≤ (1 - z.re) * max A0 A1 + z.re * max A0 A1 :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hz0)
        _ = max A0 A1 := by ring
    have hsreb0 : 0 ≤ (affine A0 (A1 - A0) z).re := by
      rw [affine_re, show A0 + (A1 - A0) * z.re = (1 - z.re) * A0 + z.re * A1 by ring]
      exact add_nonneg (mul_nonneg (by linarith) hA0nn) (mul_nonneg hz0 hA1nn)
    have hfa : ∀ a, ‖interp f (affine A B) z a‖ ≤ max 1 (‖f a‖ ^ Mt) :=
      fun a => norm_interp_le f hMtnn htreb0 htreb a
    have hgb : ∀ b, ‖interp g (affine A0 (A1 - A0)) z b‖ ≤ max 1 (‖g b‖ ^ Ms) := by
      intro b
      exact norm_interp_le g hMsnn hsreb0 hsreb b
    have hfn : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) ^ (1 / p0)
        ≤ (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) p0)
        (Finset.sum_le_sum fun a _ => Real.rpow_le_rpow (norm_nonneg _) (hfa a) hp0pos.le) ?_
      positivity
    have hTn : (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0)
        ≤ M0 * (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) := by
      refine (hT0 (interp f (affine A B) z)).trans ?_
      exact mul_le_mul_of_nonneg_left hfn hM0.le
    calc ‖F T f g (affine A B) (affine A0 (A1 - A0)) z‖
        = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ := rfl
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine A0 (A1 - A0)) z) b‖ :=
            norm_sum_le _ _
      _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine A0 (A1 - A0)) z) b‖ := by
            simp [norm_mul]
      _ ≤ ∑ b, (∑ b', ‖T (interp f (affine A B) z) b'‖ ^ q0) ^ (1 / q0)
              * (max 1 (‖g b‖ ^ Ms)) := by
            apply Finset.sum_le_sum; intro b _
            calc ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine A0 (A1 - A0)) z) b‖
                ≤ (∑ b', ‖T (interp f (affine A B) z) b'‖ ^ q0) ^ (1 / q0)
                    * ‖(interp g (affine A0 (A1 - A0)) z) b‖ :=
                  mul_le_mul_of_nonneg_right (self_le_lp _ hq0pos b) (norm_nonneg _)
              _ ≤ (∑ b', ‖T (interp f (affine A B) z) b'‖ ^ q0) ^ (1 / q0)
                    * (max 1 (‖g b‖ ^ Ms)) :=
                  mul_le_mul_of_nonneg_left (hgb b)
                    (Real.rpow_nonneg (Finset.sum_nonneg fun b' _ =>
                      Real.rpow_nonneg (norm_nonneg _) q0) _)
      _ = (∑ b, ‖T (interp f (affine A B) z) b‖ ^ q0) ^ (1 / q0)
            * (∑ b, max 1 (‖g b‖ ^ Ms)) := by rw [Finset.mul_sum]
      _ ≤ (M0 * (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0))
            * (∑ b, max 1 (‖g b‖ ^ Ms)) := by
            exact mul_le_mul_of_nonneg_right hTn
              (Finset.sum_nonneg fun b _ => le_trans zero_le_one (le_max_left _ _))
      _ = Bb := by rw [hBbdef]
  exact three_lines_F T f g hM0 hM1 (differentiable_affine A B) (differentiable_affine A0 (A1 - A0))
    hBdd hbound0 hbound1 hθ0.le hθ1.le htθ hsθ


private lemma core_eq
    (T : (α → ℂ) →ₗ[ℂ] (β → ℂ))
    {p0 p1 : ℝ} (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1)
    {M0 M1 : ℝ} (hM0 : 0 < M0) (hM1 : 0 < M1)
    (hT0 : ∀ f : α → ℂ, (∑ b, ‖T f b‖) ≤ M0 * (∑ a, ‖f a‖ ^ p0) ^ (1 / p0))
    (hT1 : ∀ f : α → ℂ, (∑ b, ‖T f b‖) ≤ M1 * (∑ a, ‖f a‖ ^ p1) ^ (1 / p1))
    {θ pθ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hpθ1 : 1 ≤ pθ)
    (hpθ : pθ⁻¹ = (1 - θ) * p0⁻¹ + θ * p1⁻¹) :
    ∀ (f : α → ℂ) (g : β → ℂ), (∑ a, ‖f a‖ ^ pθ) = 1 → (∀ b, ‖g b‖ ≤ 1) →
      ‖∑ b, (T f) b * g b‖ ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  classical
  intro f g hf hg1
  set A : ℝ := pθ / p0 with hA
  set B : ℝ := pθ / p1 - pθ / p0 with hB
  have hpθpos : 0 < pθ := by linarith
  have hp0pos : 0 < p0 := by linarith
  have hp1pos : 0 < p1 := by linarith
  have hApos : 0 < A := by rw [hA]; exact div_pos hpθpos hp0pos
  have hpp1pos : 0 < pθ / p1 := div_pos hpθpos hp1pos
  have hAB : A + B = pθ / p1 := by rw [hA, hB]; ring
  set Mt : ℝ := max A (pθ / p1) with hMt
  have hMtnn : 0 ≤ Mt := le_trans hApos.le (le_max_left _ _)
  have hkey : (1 - θ) / p0 + θ / p1 = 1 / pθ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, one_div]; exact hpθ.symm
  have hAθ : A + B * θ = 1 := by
    rw [hA, hB]
    have h : pθ / p0 + (pθ / p1 - pθ / p0) * θ = pθ * ((1 - θ) / p0 + θ / p1) := by ring
    rw [h, hkey, mul_one_div, div_self (ne_of_gt hpθpos)]
  have htθ : affine A B (θ : ℂ) = 1 := by
    have h : affine A B (θ : ℂ) = ((A + B * θ : ℝ) : ℂ) := by
      simp only [affine]; rw [← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [h, hAθ, Complex.ofReal_one]
  have hsθ : affine 1 0 (θ : ℂ) = 1 := by simp [affine]
  have htre0 : ∀ z : ℂ, z.re = 0 → (affine A B z).re = pθ / p0 := by
    intro z hz; rw [affine_re, hz, mul_zero, add_zero, hA]
  have htre1 : ∀ z : ℂ, z.re = 1 → (affine A B z).re = pθ / p1 := by
    intro z hz; rw [affine_re, hz, mul_one, hAB]
  have hsre : ∀ z : ℂ, (affine 1 0 z).re = 1 := by
    intro z; rw [affine_re]; ring
  have hw1 : ∀ z : ℂ, ∀ b, ‖interp g (affine 1 0) z b‖ ≤ 1 := by
    intro z b
    rcases eq_or_ne (g b) 0 with h | h
    · have hL : ‖interp g (affine 1 0) z b‖ = 0 := by
        rw [interp_apply, h]
        simp only [norm_zero, Complex.ofReal_zero]
        rw [ph_eq_zero rfl, mul_zero, norm_zero]
      rw [hL]; exact zero_le_one
    · rw [norm_interp_of_ne g h, hsre z, Real.rpow_one]; exact hg1 b
  have hbound0 : ∀ y : ℝ, ‖F T f g (affine A B) (affine 1 0) ((y : ℂ) * Complex.I)‖ ≤ M0 := by
    intro y
    set z : ℂ := (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 0 := by rw [hzdef]; simp
    have htre : (affine A B z).re = pθ / p0 := htre0 z hzre
    have hsumf : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) = 1 := by
      rw [sum_norm_interp_rpow f (t := affine A B) (z := z) (R := pθ / p0) (P := p0)
        (div_pos hpθpos hp0pos) hp0pos htre]
      rw [div_mul_cancel₀ pθ (ne_of_gt hp0pos), hf]
    have hfz1 : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) ^ (1 / p0) = 1 := by
      rw [hsumf, Real.one_rpow]
    have hTnorm : (∑ b, ‖T (interp f (affine A B) z) b‖) ≤ M0 := by
      have h := hT0 (interp f (affine A B) z)
      rw [hfz1, mul_one] at h; exact h
    calc ‖F T f g (affine A B) (affine 1 0) z‖
        = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := rfl
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := norm_sum_le _ _
      _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine 1 0) z) b‖ := by
            simp [norm_mul]
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b‖ * 1 := by
            apply Finset.sum_le_sum; intro b _
            exact mul_le_mul_of_nonneg_left (hw1 z b) (norm_nonneg _)
      _ = ∑ b, ‖T (interp f (affine A B) z) b‖ := by simp
      _ ≤ M0 := hTnorm
  have hbound1 : ∀ y : ℝ, ‖F T f g (affine A B) (affine 1 0) (1 + (y : ℂ) * Complex.I)‖ ≤ M1 := by
    intro y
    set z : ℂ := 1 + (y : ℂ) * Complex.I with hzdef
    have hzre : z.re = 1 := by rw [hzdef]; simp
    have htre : (affine A B z).re = pθ / p1 := htre1 z hzre
    have hsumf : (∑ a, ‖interp f (affine A B) z a‖ ^ p1) = 1 := by
      rw [sum_norm_interp_rpow f (t := affine A B) (z := z) (R := pθ / p1) (P := p1)
        hpp1pos hp1pos htre]
      rw [div_mul_cancel₀ pθ (ne_of_gt hp1pos), hf]
    have hfz1 : (∑ a, ‖interp f (affine A B) z a‖ ^ p1) ^ (1 / p1) = 1 := by
      rw [hsumf, Real.one_rpow]
    have hTnorm : (∑ b, ‖T (interp f (affine A B) z) b‖) ≤ M1 := by
      have h := hT1 (interp f (affine A B) z)
      rw [hfz1, mul_one] at h; exact h
    calc ‖F T f g (affine A B) (affine 1 0) z‖
        = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := rfl
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := norm_sum_le _ _
      _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine 1 0) z) b‖ := by
            simp [norm_mul]
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b‖ * 1 := by
            apply Finset.sum_le_sum; intro b _
            exact mul_le_mul_of_nonneg_left (hw1 z b) (norm_nonneg _)
      _ = ∑ b, ‖T (interp f (affine A B) z) b‖ := by simp
      _ ≤ M1 := hTnorm
  set Bb : ℝ := M0 * (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) with hBbdef
  have hBdd : ∀ z, 0 ≤ z.re → z.re ≤ 1 → ‖F T f g (affine A B) (affine 1 0) z‖ ≤ Bb := by
    intro z hz0 hz1
    have htreb : (affine A B z).re ≤ Mt := by
      rw [affine_re, hMt]
      rw [show A + B * z.re = (1 - z.re) * A + z.re * (pθ / p1) by rw [← hAB]; ring]
      calc (1 - z.re) * A + z.re * (pθ / p1)
          ≤ (1 - z.re) * max A (pθ / p1) + z.re * max A (pθ / p1) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hz0)
        _ = max A (pθ / p1) := by ring
    have htreb0 : 0 ≤ (affine A B z).re := by
      rw [affine_re, show A + B * z.re = (1 - z.re) * A + z.re * (pθ / p1) by rw [← hAB]; ring]
      exact add_nonneg (mul_nonneg (by linarith) hApos.le) (mul_nonneg hz0 hpp1pos.le)
    have hfa : ∀ a, ‖interp f (affine A B) z a‖ ≤ max 1 (‖f a‖ ^ Mt) :=
      fun a => norm_interp_le f hMtnn htreb0 htreb a
    have hfn : (∑ a, ‖interp f (affine A B) z a‖ ^ p0) ^ (1 / p0)
        ≤ (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) := by
      refine Real.rpow_le_rpow (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) p0)
        (Finset.sum_le_sum fun a _ => Real.rpow_le_rpow (norm_nonneg _) (hfa a) hp0pos.le) ?_
      positivity
    have hTn : (∑ b, ‖T (interp f (affine A B) z) b‖)
        ≤ M0 * (∑ a, (max 1 (‖f a‖ ^ Mt)) ^ p0) ^ (1 / p0) := by
      refine (hT0 (interp f (affine A B) z)).trans ?_
      exact mul_le_mul_of_nonneg_left hfn hM0.le
    calc ‖F T f g (affine A B) (affine 1 0) z‖
        = ‖∑ b, (T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := rfl
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b * (interp g (affine 1 0) z) b‖ := norm_sum_le _ _
      _ = ∑ b, ‖(T (interp f (affine A B) z)) b‖ * ‖(interp g (affine 1 0) z) b‖ := by
            simp [norm_mul]
      _ ≤ ∑ b, ‖(T (interp f (affine A B) z)) b‖ * 1 := by
            apply Finset.sum_le_sum; intro b _
            exact mul_le_mul_of_nonneg_left (hw1 z b) (norm_nonneg _)
      _ = ∑ b, ‖T (interp f (affine A B) z) b‖ := by simp
      _ ≤ Bb := by rw [hBbdef]; exact hTn
  exact three_lines_F T f g hM0 hM1 (differentiable_affine A B)
    (by show Differentiable ℂ (affine 1 0); exact differentiable_affine 1 0)
    hBdd hbound0 hbound1 hθ0.le hθ1.le htθ hsθ


private lemma zero_lhs {ι : Type*} [Fintype ι] {q : ℝ} (hq : 0 < q) :
    (∑ i, ‖(0 : ι → ℂ) i‖ ^ q) ^ (1 / q) = 0 := by
  have h1 : (∑ i, ‖(0 : ι → ℂ) i‖ ^ q) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [Pi.zero_apply, norm_zero, Real.zero_rpow (ne_of_gt hq)]
  rw [h1, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < 1 / q))]

theorem riesz_thorin_finite {α β : Type*} [Fintype α] [Fintype β]
    (T : (α → ℂ) →ₗ[ℂ] (β → ℂ))
    {p0 p1 q0 q1 : ℝ} (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) (hq0 : 1 ≤ q0) (hq1 : 1 ≤ q1)
    {M0 M1 : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (hT0 : ∀ f : α → ℂ, (∑ b, ‖T f b‖ ^ q0) ^ (1 / q0) ≤ M0 * (∑ a, ‖f a‖ ^ p0) ^ (1 / p0))
    (hT1 : ∀ f : α → ℂ, (∑ b, ‖T f b‖ ^ q1) ^ (1 / q1) ≤ M1 * (∑ a, ‖f a‖ ^ p1) ^ (1 / p1))
    {θ pθ qθ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hpθ1 : 1 ≤ pθ) (hqθ1 : 1 ≤ qθ)
    (hpθ : pθ⁻¹ = (1 - θ) * p0⁻¹ + θ * p1⁻¹)
    (hqθ : qθ⁻¹ = (1 - θ) * q0⁻¹ + θ * q1⁻¹) :
    ∀ f : α → ℂ, (∑ b, ‖T f b‖ ^ qθ) ^ (1 / qθ) ≤
      M0 ^ (1 - θ) * M1 ^ θ * (∑ a, ‖f a‖ ^ pθ) ^ (1 / pθ) := by
  classical
  intro f
  rcases eq_or_lt_of_le hθ0 with hθ0e | hθ0pos
  · have hpθeq : pθ = p0 := by
      have h : pθ⁻¹ = p0⁻¹ := by have hh := hpθ; rw [← hθ0e] at hh; simpa using hh
      exact inv_inj.mp h
    have hqθeq : qθ = q0 := by
      have h : qθ⁻¹ = q0⁻¹ := by have hh := hqθ; rw [← hθ0e] at hh; simpa using hh
      exact inv_inj.mp h
    rw [← hθ0e, hpθeq, hqθeq]
    simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
    exact hT0 f
  rcases eq_or_lt_of_le hθ1 with hθ1e | hθ1lt
  · have hpθeq : pθ = p1 := by
      have h : pθ⁻¹ = p1⁻¹ := by have hh := hpθ; rw [hθ1e] at hh; simpa using hh
      exact inv_inj.mp h
    have hqθeq : qθ = q1 := by
      have h : qθ⁻¹ = q1⁻¹ := by have hh := hqθ; rw [hθ1e] at hh; simpa using hh
      exact inv_inj.mp h
    rw [hθ1e, hpθeq, hqθeq]
    simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul, mul_one]
    exact hT1 f
  have hqθpos : 0 < qθ := by linarith
  by_cases hM0z : M0 = 0
  · have hTf0 : T f = 0 := by
      have hnorm0 : (∑ b, ‖T f b‖ ^ q0) = 0 := by
        have h := hT0 f
        rw [hM0z, zero_mul] at h
        have hge : 0 ≤ (∑ b, ‖T f b‖ ^ q0) ^ (1 / q0) :=
          Real.rpow_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) q0) _
        have heq : (∑ b, ‖T f b‖ ^ q0) ^ (1 / q0) = 0 := le_antisymm h hge
        by_contra hS
        have hSpos : 0 < ∑ b, ‖T f b‖ ^ q0 :=
          lt_of_le_of_ne (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) q0) (Ne.symm hS)
        exact absurd heq (ne_of_gt (Real.rpow_pos_of_pos hSpos _))
      funext b
      have hb : ‖T f b‖ ^ q0 = 0 := by
        have h1 : ‖T f b‖ ^ q0 ≤ ∑ b', ‖T f b'‖ ^ q0 :=
          Finset.single_le_sum (fun b' _ => Real.rpow_nonneg (norm_nonneg _) q0) (Finset.mem_univ b)
        rw [hnorm0] at h1
        exact le_antisymm h1 (Real.rpow_nonneg (norm_nonneg _) q0)
      have h : ‖T f b‖ = 0 := by
        by_contra hc
        exact absurd hb (ne_of_gt (Real.rpow_pos_of_pos
          (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)) q0))
      exact norm_eq_zero.mp h
    rw [hTf0, zero_lhs hqθpos, hM0z, Real.zero_rpow (by linarith : (1:ℝ) - θ ≠ 0)]
    simp
  by_cases hM1z : M1 = 0
  · have hTf0 : T f = 0 := by
      have hnorm0 : (∑ b, ‖T f b‖ ^ q1) = 0 := by
        have h := hT1 f
        rw [hM1z, zero_mul] at h
        have hge : 0 ≤ (∑ b, ‖T f b‖ ^ q1) ^ (1 / q1) :=
          Real.rpow_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) q1) _
        have heq : (∑ b, ‖T f b‖ ^ q1) ^ (1 / q1) = 0 := le_antisymm h hge
        by_contra hS
        have hSpos : 0 < ∑ b, ‖T f b‖ ^ q1 :=
          lt_of_le_of_ne (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (norm_nonneg _) q1) (Ne.symm hS)
        exact absurd heq (ne_of_gt (Real.rpow_pos_of_pos hSpos _))
      funext b
      have hb : ‖T f b‖ ^ q1 = 0 := by
        have h1 : ‖T f b‖ ^ q1 ≤ ∑ b', ‖T f b'‖ ^ q1 :=
          Finset.single_le_sum (fun b' _ => Real.rpow_nonneg (norm_nonneg _) q1) (Finset.mem_univ b)
        rw [hnorm0] at h1
        exact le_antisymm h1 (Real.rpow_nonneg (norm_nonneg _) q1)
      have h : ‖T f b‖ = 0 := by
        by_contra hc
        exact absurd hb (ne_of_gt (Real.rpow_pos_of_pos
          (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)) q1))
      exact norm_eq_zero.mp h
    rw [hTf0, zero_lhs hqθpos, hM1z, Real.zero_rpow (by linarith : θ ≠ 0)]
    simp
  have hM0pos : 0 < M0 := lt_of_le_of_ne hM0 (Ne.symm hM0z)
  have hM1pos : 0 < M1 := lt_of_le_of_ne hM1 (Ne.symm hM1z)
  by_cases hS : (∑ a, ‖f a‖ ^ pθ) = 0
  · have hf0 : f = 0 := by
      funext a
      have ha : ‖f a‖ ^ pθ = 0 := by
        have h1 : ‖f a‖ ^ pθ ≤ ∑ a', ‖f a'‖ ^ pθ :=
          Finset.single_le_sum (fun a' _ => Real.rpow_nonneg (norm_nonneg _) pθ) (Finset.mem_univ a)
        rw [hS] at h1
        exact le_antisymm h1 (Real.rpow_nonneg (norm_nonneg _) pθ)
      have h : ‖f a‖ = 0 := by
        by_contra hc
        exact absurd ha (ne_of_gt (Real.rpow_pos_of_pos
          (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hc)) pθ))
      exact norm_eq_zero.mp h
    rw [hf0, map_zero, zero_lhs hqθpos, zero_lhs (q := pθ) (by positivity : (0:ℝ) < pθ)]
    simp
  have hSpos : 0 < ∑ a, ‖f a‖ ^ pθ :=
    lt_of_le_of_ne (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) pθ) (Ne.symm hS)
  set N : ℝ := (∑ a, ‖f a‖ ^ pθ) ^ (1 / pθ) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; exact Real.rpow_pos_of_pos hSpos _
  have hNpow : N ^ pθ = ∑ a, ‖f a‖ ^ pθ := by
    rw [hNdef]
    have h := Real.rpow_mul hSpos.le (1 / pθ) pθ
    rw [show (1 / pθ) * pθ = 1 by field_simp, Real.rpow_one] at h
    exact h.symm
  set f' : α → ℂ := fun a => (N : ℂ)⁻¹ * f a with hf'def
  have hf' : (∑ a, ‖f' a‖ ^ pθ) = 1 := by
    have h1 : ∀ a, ‖f' a‖ = N⁻¹ * ‖f a‖ := by
      intro a
      rw [hf'def]
      simp only []
      rw [norm_mul, norm_inv, show ‖((N:ℝ):ℂ)‖ = N by simp [abs_of_nonneg hNpos.le]]
    calc ∑ a, ‖f' a‖ ^ pθ
        = ∑ a, (N⁻¹ * ‖f a‖) ^ pθ := Finset.sum_congr rfl (fun a _ => by rw [h1 a])
      _ = ∑ a, N⁻¹ ^ pθ * ‖f a‖ ^ pθ := Finset.sum_congr rfl (fun a _ =>
            Real.mul_rpow (inv_nonneg.mpr hNpos.le) (norm_nonneg _))
      _ = N⁻¹ ^ pθ * ∑ a, ‖f a‖ ^ pθ := by rw [Finset.mul_sum]
      _ = 1 := by
            rw [show N⁻¹ ^ pθ = (N ^ pθ)⁻¹ by rw [Real.inv_rpow hNpos.le], hNpow]
            exact inv_mul_cancel₀ (ne_of_gt hSpos)
  have hscale : T f = (N : ℂ) • T f' := by
    have hff : (N : ℂ) • f' = f := by
      funext a
      rw [hf'def]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hNpos), one_mul]
    rw [← hff, map_smul]
  have hlpn' : (∑ b, ‖T f' b‖ ^ qθ) ^ (1 / qθ) ≤ M0 ^ (1 - θ) * M1 ^ θ := by
    by_cases hqθeq1 : qθ = 1
    · have hq0inv_le : q0⁻¹ ≤ 1 := (inv_le_one_iff₀ (a := q0)).mpr (Or.inr hq0)
      have hq1inv_le : q1⁻¹ ≤ 1 := (inv_le_one_iff₀ (a := q1)).mpr (Or.inr hq1)
      have h1eq : (1 - θ) * q0⁻¹ + θ * q1⁻¹ = 1 := by
        have hh := hqθ; rw [hqθeq1, inv_one] at hh; exact hh.symm
      have ha : (1 - θ) * q0⁻¹ ≤ (1 - θ) := mul_le_of_le_one_right (by linarith) hq0inv_le
      have hb : θ * q1⁻¹ ≤ θ := mul_le_of_le_one_right hθ0pos.le hq1inv_le
      have hbe : θ * q1⁻¹ = θ := by
        apply le_antisymm hb
        linarith [h1eq, ha]
      have hae : (1 - θ) * q0⁻¹ = 1 - θ := by linarith [h1eq, hbe]
      have hq0eq1 : q0 = 1 := by
        refine inv_eq_one.mp (mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < 1 - θ)) ?_)
        rw [hae, mul_one]
      have hq1eq1 : q1 = 1 := by
        refine inv_eq_one.mp (mul_left_cancel₀ (ne_of_gt hθ0pos) ?_)
        rw [hbe, mul_one]
      have hT0' : ∀ h : α → ℂ, (∑ b, ‖T h b‖) ≤ M0 * (∑ a, ‖h a‖ ^ p0) ^ (1 / p0) := by
        intro h
        have hh := hT0 h
        rw [hq0eq1] at hh
        simpa using hh
      have hT1' : ∀ h : α → ℂ, (∑ b, ‖T h b‖) ≤ M1 * (∑ a, ‖h a‖ ^ p1) ^ (1 / p1) := by
        intro h
        have hh := hT1 h
        rw [hq1eq1] at hh
        simpa using hh
      have hcore := core_eq T hp0 hp1 hM0pos hM1pos hT0' hT1' hθ0pos hθ1lt hpθ1 hpθ
      obtain ⟨g, hg1, hg2⟩ := exists_unit_witness_l1 (T f')
      have h2 := hcore f' g hf' hg1
      have h3 : (∑ b, ‖T f' b‖ ^ qθ) ^ (1 / qθ) = ∑ b, ‖T f' b‖ := by rw [hqθeq1]; simp
      rw [h3]; exact le_trans hg2 h2
    · have hqθgt : 1 < qθ := lt_of_le_of_ne hqθ1 (Ne.symm hqθeq1)
      have hqθinv_lt : qθ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqθgt
      have hQpos : 0 < 1 - qθ⁻¹ := by linarith [inv_pos_of_pos hqθpos]
      set Q : ℝ := (1 - qθ⁻¹)⁻¹ with hQdef
      have hQgt : 1 < Q := by
        rw [hQdef, one_lt_inv₀ hQpos]
        linarith [inv_pos_of_pos hqθpos]
      have hQconj : 1 / qθ + 1 / Q = 1 := by rw [hQdef, one_div, one_div, inv_inv]; ring
      have hQconj' : qθ⁻¹ + Q⁻¹ = 1 := by rw [one_div, one_div] at hQconj; exact hQconj
      have hcore := core_gt T hp0 hp1 hq0 hq1 hM0pos hM1pos hT0 hT1 hθ0pos hθ1lt hpθ1 hqθgt hQgt hpθ hqθ hQconj'
      rcases eq_or_ne (T f') 0 with hTz | hTnz
      · rw [hTz, zero_lhs hqθpos]
        exact mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
      · obtain ⟨g, hgQ, hgnorm⟩ := exists_dual_witness hqθgt hQgt hQconj (T f') hTnz
        have hgQ' : (∑ b, ‖g b‖ ^ Q) = 1 := by
          have hSg : 0 ≤ ∑ b, ‖g b‖ ^ Q :=
            Finset.sum_nonneg (fun b _ => Real.rpow_nonneg (norm_nonneg _) Q)
          have key : ((∑ b, ‖g b‖ ^ Q) ^ (1 / Q)) ^ Q = ∑ b, ‖g b‖ ^ Q := by
            rw [← Real.rpow_mul hSg, one_div, inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < Q)),
              Real.rpow_one]
          rw [hgQ, Real.one_rpow] at key
          exact key.symm
        exact le_trans hgnorm (hcore f' g hf' hgQ')
  have hfinal : N * (∑ b, ‖T f' b‖ ^ qθ) ^ (1 / qθ) ≤ M0 ^ (1 - θ) * M1 ^ θ * N := by
    calc N * (∑ b, ‖T f' b‖ ^ qθ) ^ (1 / qθ)
        ≤ N * (M0 ^ (1 - θ) * M1 ^ θ) := mul_le_mul_of_nonneg_left hlpn' hNpos.le
      _ = M0 ^ (1 - θ) * M1 ^ θ * N := by ring
  rw [hscale]
  simp only [Pi.smul_apply]
  rw [Commons.Analysis.Real.lpn_smul_eq (T f') hqθpos N hNpos.le]
  exact hfinal


end

end Commons.Analysis.Integral
