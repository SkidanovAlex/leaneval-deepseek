import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vec_defs

/-!
# Interpolation vectors for the vector-valued Riesz--Thorin theorem

* `interpC f t z` is the interpolation vector `a ↦ ‖f a‖ ^ (t z) · ‖f a‖⁻¹ · f a` of a scalar
  function `f : σ → ℂ`; its modulus is `‖f a‖ ^ (Re (t z))` and it returns `f` at `t z = 1`.
* `vinterp g s z` is the same construction applied *fibrewise in `ι`* to a vector-valued
  function `g : β → ι → ℂ`, the scaling factor being the `ℓ²`-norm `n2 (g b)` of the fibre; its
  fibre norm is `(n2 (g b)) ^ (Re (s z))` and it returns `g` at `s z = 1`.
-/

open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

lemma norm_ofReal_eq_abs (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

lemma norm_ofReal_inv {x : ℝ} (hx : 0 ≤ x) : ‖(((x : ℝ) : ℂ))⁻¹‖ = x⁻¹ := by
  rw [norm_inv, norm_ofReal_eq_abs, abs_of_nonneg hx]

/-! ## The scalar interpolation vector -/

lemma interpC_zero {σ : Type*} (f : σ → ℂ) (t : ℂ → ℂ) (z : ℂ) (a : σ) (h : f a = 0) :
    interpC f t z a = 0 := by
  rw [interpC_apply, h]
  simp only [norm_zero, Complex.ofReal_zero, inv_zero, zero_mul, mul_zero]

lemma norm_interpC {σ : Type*} (f : σ → ℂ) {t : ℂ → ℂ} {z : ℂ} (hz : 0 < (t z).re) (a : σ) :
    ‖interpC f t z a‖ = ‖f a‖ ^ (t z).re := by
  rcases eq_or_ne (f a) 0 with h0 | h0
  · rw [interpC_zero f t z a h0, norm_zero, h0, norm_zero, Real.zero_rpow (ne_of_gt hz)]
  · have hr : 0 < ‖f a‖ := norm_pos_iff.mpr h0
    rw [interpC_apply, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by simpa using hr),
      norm_ofReal_inv hr.le, inv_mul_cancel₀ (ne_of_gt hr), mul_one]

lemma norm_interpC_le_one {σ : Type*} (f : σ → ℂ) {t : ℂ → ℂ} {z : ℂ} (hz : (t z).re = 0)
    (a : σ) : ‖interpC f t z a‖ ≤ 1 := by
  rcases eq_or_ne (f a) 0 with h0 | h0
  · rw [interpC_zero f t z a h0, norm_zero]; norm_num
  · have hr : 0 < ‖f a‖ := norm_pos_iff.mpr h0
    rw [interpC_apply, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by simpa using hr),
      norm_ofReal_inv hr.le, hz, Real.rpow_zero, one_mul, inv_mul_cancel₀ (ne_of_gt hr)]

lemma norm_interpC_le_max {σ : Type*} (f : σ → ℂ) {t : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (h0 : 0 ≤ (t z).re) (h1 : (t z).re ≤ M) (a : σ) :
    ‖interpC f t z a‖ ≤ max 1 (‖f a‖ ^ M) := by
  rcases eq_or_ne (f a) 0 with hz0 | hz0
  · rw [interpC_zero f t z a hz0, norm_zero, hz0, norm_zero]
    exact le_trans zero_le_one (le_max_left (1 : ℝ) _)
  · rcases eq_or_lt_of_le h0 with h00 | h0pos
    · exact le_trans (norm_interpC_le_one f h00.symm a) (le_max_left (1 : ℝ) _)
    · rw [norm_interpC f h0pos a]
      rcases lt_or_ge 1 (‖f a‖) with h1' | h1'
      · have hX : 1 ≤ ‖f a‖ ^ M := by
          simpa [Real.one_rpow] using Real.rpow_le_rpow (zero_le_one) h1'.le hM
        rw [max_eq_right hX]
        exact Real.rpow_le_rpow_of_exponent_le h1'.le h1
      · have hX : ‖f a‖ ^ M ≤ 1 := Real.rpow_le_one (norm_nonneg _) h1' hM
        rw [max_eq_left hX]
        exact Real.rpow_le_one (norm_nonneg _) h1' h0

lemma interpC_self {σ : Type*} (f : σ → ℂ) {t : ℂ → ℂ} {θ : ℂ} (h : t θ = 1) :
    interpC f t θ = f := by
  funext a
  rcases eq_or_ne (f a) 0 with h0 | h0
  · rw [interpC_zero f t θ a h0, h0]
  · have hr : ‖f a‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    rw [interpC_apply, h, Complex.cpow_one, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]

lemma differentiable_interpC {σ : Type*} (f : σ → ℂ) {t : ℂ → ℂ} (ht : Differentiable ℂ t)
    (a : σ) : Differentiable ℂ (fun z => interpC f t z a) := by
  rcases eq_or_ne (f a) 0 with h0 | h0
  · have hzero : (fun z => interpC f t z a) = fun _ => (0 : ℂ) := by
      funext z; exact interpC_zero f t z a h0
    rw [hzero]; exact differentiable_const 0
  · have hr : 0 < ‖f a‖ := norm_pos_iff.mpr h0
    have hc : ((‖f a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    have hd : Differentiable ℂ (fun z => ((‖f a‖ : ℝ) : ℂ) ^ (t z)) := ht.const_cpow (Or.inl hc)
    have hd2 : Differentiable ℂ
        (fun z => ((‖f a‖ : ℝ) : ℂ) ^ (t z) * ((((‖f a‖ : ℝ) : ℂ))⁻¹ * f a)) :=
      hd.mul_const _
    simpa [interpC_apply] using hd2

/-! ## The vector-valued interpolation vector -/

lemma vinterp_eq_smul {β ι : Type*} [Fintype ι] (g : β → ι → ℂ) (s : ℂ → ℂ) (z : ℂ) (b : β) :
    vinterp g s z b
      = ((((n2 (g b) : ℝ) : ℂ)) ^ (s z)) • (((((n2 (g b) : ℝ) : ℂ))⁻¹) • (g b)) := by
  funext i
  simp only [vinterp_apply, Pi.smul_apply, smul_eq_mul]

lemma vinterp_zero {β ι : Type*} [Fintype ι] (g : β → ι → ℂ) (s : ℂ → ℂ) (z : ℂ) (b : β)
    (h : g b = 0) : vinterp g s z b = 0 := by
  funext i
  rw [vinterp_apply, h]
  simp only [n2_zero, Complex.ofReal_zero, inv_zero, zero_mul, mul_zero, Pi.zero_apply]

lemma n2_vinterp {β ι : Type*} [Fintype β] [Fintype ι] (g : β → ι → ℂ) {s : ℂ → ℂ} {z : ℂ}
    (hz : 0 < (s z).re) (b : β) : n2 (vinterp g s z b) = (n2 (g b)) ^ (s z).re := by
  rcases eq_or_ne (n2 (g b)) 0 with hr | hr
  · rw [vinterp_zero g s z b ((n2_eq_zero_iff (g b)).mp hr), n2_zero, hr,
      Real.zero_rpow (ne_of_gt hz)]
  · have hrpos : 0 < n2 (g b) := lt_of_le_of_ne (n2_nonneg (g b)) (Ne.symm hr)
    rw [vinterp_eq_smul g s z b, n2_smul, n2_smul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by simpa using hrpos), norm_ofReal_inv hrpos.le,
      inv_mul_cancel₀ (ne_of_gt hrpos), mul_one]

lemma n2_vinterp_le_one {β ι : Type*} [Fintype β] [Fintype ι] (g : β → ι → ℂ) {s : ℂ → ℂ}
    {z : ℂ} (hz : (s z).re = 0) (b : β) : n2 (vinterp g s z b) ≤ 1 := by
  rcases eq_or_ne (n2 (g b)) 0 with hr | hr
  · rw [vinterp_zero g s z b ((n2_eq_zero_iff (g b)).mp hr), n2_zero]; norm_num
  · have hrpos : 0 < n2 (g b) := lt_of_le_of_ne (n2_nonneg (g b)) (Ne.symm hr)
    rw [vinterp_eq_smul g s z b, n2_smul, n2_smul,
      Complex.norm_cpow_eq_rpow_re_of_pos (by simpa using hrpos), norm_ofReal_inv hrpos.le, hz,
      Real.rpow_zero, one_mul, inv_mul_cancel₀ (ne_of_gt hrpos)]

lemma n2_vinterp_le_max {β ι : Type*} [Fintype β] [Fintype ι] (g : β → ι → ℂ) {s : ℂ → ℂ}
    {z : ℂ} {M : ℝ} (hM : 0 ≤ M) (h0 : 0 ≤ (s z).re) (h1 : (s z).re ≤ M) (b : β) :
    n2 (vinterp g s z b) ≤ max 1 ((n2 (g b)) ^ M) := by
  rcases eq_or_ne (n2 (g b)) 0 with hr | hr
  · rw [vinterp_zero g s z b ((n2_eq_zero_iff (g b)).mp hr), n2_zero, hr]
    exact le_trans zero_le_one (le_max_left (1 : ℝ) _)
  · rcases eq_or_lt_of_le h0 with h00 | h0pos
    · exact le_trans (n2_vinterp_le_one g h00.symm b) (le_max_left (1 : ℝ) _)
    · rw [n2_vinterp g h0pos b]
      rcases lt_or_ge 1 (n2 (g b)) with h1' | h1'
      · have hX : 1 ≤ (n2 (g b)) ^ M := by
          simpa [Real.one_rpow] using Real.rpow_le_rpow (zero_le_one) h1'.le hM
        rw [max_eq_right hX]
        exact Real.rpow_le_rpow_of_exponent_le h1'.le h1
      · have hX : (n2 (g b)) ^ M ≤ 1 := Real.rpow_le_one (n2_nonneg _) h1' hM
        rw [max_eq_left hX]
        exact Real.rpow_le_one (n2_nonneg _) h1' h0

lemma vinterp_self {β ι : Type*} [Fintype β] [Fintype ι] (g : β → ι → ℂ) {s : ℂ → ℂ} {θ : ℂ}
    (h : s θ = 1) : vinterp g s θ = g := by
  funext b i
  rcases eq_or_ne (g b) 0 with h0 | h0
  · rw [vinterp_zero g s θ b h0, h0]
  · have hr : n2 (g b) ≠ 0 := fun hh => h0 ((n2_eq_zero_iff (g b)).mp hh)
    rw [vinterp_apply, h, Complex.cpow_one, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]

lemma differentiable_vinterp {β ι : Type*} [Fintype β] [Fintype ι] (g : β → ι → ℂ) {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (b : β) (i : ι) :
    Differentiable ℂ (fun z => vinterp g s z b i) := by
  rcases eq_or_ne (n2 (g b)) 0 with hr | hr
  · have hgb : g b = 0 := (n2_eq_zero_iff (g b)).mp hr
    have hzero : (fun z => vinterp g s z b i) = fun _ => (0 : ℂ) := by
      funext z
      rw [vinterp_zero g s z b hgb]
      rfl
    rw [hzero]; exact differentiable_const 0
  · have hrpos : 0 < n2 (g b) := lt_of_le_of_ne (n2_nonneg (g b)) (Ne.symm hr)
    have hc : (((n2 (g b) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)
    have hd : Differentiable ℂ (fun z => (((n2 (g b) : ℝ) : ℂ)) ^ (s z)) :=
      hs.const_cpow (Or.inl hc)
    have hd2 : Differentiable ℂ
        (fun z => (((n2 (g b) : ℝ) : ℂ)) ^ (s z) * ((((n2 (g b) : ℝ) : ℂ))⁻¹ * g b i)) :=
      hd.mul_const _
    simpa [vinterp_apply] using hd2

end

end Work.BourgainPlan.IonescuWainger
