import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution

namespace Commons.Geometry.Ulam

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

/-- The vertical-profile integrand `(f t)^2 - (s₀ t)^2` at anchor slope `s₀`. -/
def anchorA (s₀ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun t => f t ^ 2 - (s₀ * t) ^ 2

/-- The reference integrand `(1 - t^2) - (s₀ t)^2` at anchor slope `s₀`. -/
def anchorB (s₀ : ℝ) : ℝ → ℝ := fun t => (1 - t ^ 2) - (s₀ * t) ^ 2

/-- `profileX` is positive. -/
lemma profileX_pos' (s : ℝ) : 0 < profileX s := by
  unfold profileX; positivity

/-- `(a * t^2)^k = a^k * t^(2k)`. -/
lemma mul_sq_pow (a t : ℝ) (k : ℕ) : (a * t ^ 2) ^ k = a ^ k * t ^ (2 * k) := by
  rw [mul_pow, ← pow_mul]

/-- `t^k * t⁻¹ = t^(k-1)` for `k ≥ 2` (the case `k = 1` fails at `t = 0`). -/
lemma pow_mul_inv (t : ℝ) {k : ℕ} (hk : 2 ≤ k) : t ^ k * t⁻¹ = t ^ (k - 1) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [zero_pow (by omega : k ≠ 0), zero_mul, zero_pow (by omega : k - 1 ≠ 0)]
  · have hk' : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk', pow_succ]
    rw [mul_assoc, mul_inv_cancel₀ ht, mul_one]

/-! ### Helper lemmas for `moment_eqs_below_of_relations` -/

/-- `profileX` is antitone on `[0,∞)`. -/
lemma profileX_le_profileX {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    profileX b ≤ profileX a := by
  unfold profileX
  apply one_div_le_one_div_of_le
  · exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg a])
  · exact Real.sqrt_le_sqrt (by nlinarith)

/-- `(1 + s^2) * (profileX s)^2 = 1`. -/
lemma one_add_sq_mul_profileX_sq (s : ℝ) : (1 + s ^ 2) * (profileX s) ^ 2 = 1 := by
  rw [profileX_sq s]
  field_simp

/-- An integral of an odd function over a symmetric interval vanishes. -/
lemma intervalIntegral_eq_zero_of_odd {a : ℝ} {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) :
    (∫ x in (-a)..a, g x) = 0 := by
  have h1 : (∫ x in (-a)..a, g (-x)) = ∫ x in (-a)..a, g x := by
    have := intervalIntegral.integral_comp_neg (f := g) (a := -a) (b := a)
    simpa using this
  have h2 : (∫ x in (-a)..a, g (-x)) = ∫ x in (-a)..a, - g x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hg x
  have h3 : (∫ x in (-a)..a, - g x) = - ∫ x in (-a)..a, g x := by
    simpa using intervalIntegral.integral_neg (a := -a) (b := a) (f := g)
  have h4 : (∫ x in (-a)..a, g x) = - ∫ x in (-a)..a, g x := h1.symm.trans (h2.trans h3)
  linarith


/-- An interval integral, over a larger interval, of a function supported in the smaller
interval, equals the integral over the smaller interval. -/
lemma integral_eq_of_eq_zero_outside {a c d b : ℝ} (hac : a ≤ c) (hdb : d ≤ b) (hcd : c ≤ d)
    {f : ℝ → ℝ} (hzero : ∀ x : ℝ, x ∈ Set.Icc a b → (x < c ∨ d < x) → f x = 0)
    (hf : IntegrableOn f (Set.Ioc c d) volume) :
    (∫ x in a..b, f x) = ∫ x in c..d, f x := by
  have haec : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc a c → f x = 0 := by
    rw [ae_iff]
    apply measure_mono_null _ (by simp : volume ({c} : Set ℝ) = 0)
    intro x hx
    have hx' : x ∈ Set.Ioc a c ∧ f x ≠ 0 := Classical.not_imp.mp hx
    simp only [Set.mem_singleton_iff]
    rw [Set.mem_Ioc] at hx'
    by_contra hne
    have hxb : x ∈ Set.Icc a b := ⟨le_of_lt hx'.1.1, le_trans hx'.1.2 hcd |>.trans hdb⟩
    exact hx'.2 (hzero x hxb (Or.inl (lt_of_le_of_ne hx'.1.2 hne)))
  have haeb : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc d b → f x = 0 :=
    Filter.Eventually.of_forall fun x hx =>
      hzero x ⟨le_trans (le_trans hac hcd) (Set.mem_Ioc.mp hx).1.le, (Set.mem_Ioc.mp hx).2⟩
        (Or.inr (Set.mem_Ioc.mp hx).1)
  have hic_ac0 : f =ᵐ[volume.restrict (Set.Ioc a c)] 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mpr haec
  have hic_db0 : f =ᵐ[volume.restrict (Set.Ioc d b)] 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mpr haeb
  have hic_ac : IntegrableOn f (Set.Ioc a c) volume :=
    Integrable.congr (integrable_zero ℝ ℝ (volume.restrict (Set.Ioc a c))) hic_ac0.symm
  have hic_db : IntegrableOn f (Set.Ioc d b) volume :=
    Integrable.congr (integrable_zero ℝ ℝ (volume.restrict (Set.Ioc d b))) hic_db0.symm
  have hic_cd : IntegrableOn f (Set.Ioc c d) volume := hf
  have II_ac : IntervalIntegrable f volume a c := (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mpr hic_ac
  have II_cd : IntervalIntegrable f volume c d := (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr hic_cd
  have II_db : IntervalIntegrable f volume d b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hdb).mpr hic_db
  have hic_ad : IntegrableOn f (Set.Ioc a d) volume := by
    have hun : Set.Ioc a c ∪ Set.Ioc c d = Set.Ioc a d := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, le_trans h2 hcd⟩
        · exact ⟨lt_of_le_of_lt hac h1, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hxc : x ≤ c
        · exact Or.inl ⟨h1, hxc⟩
        · exact Or.inr ⟨not_le.mp hxc, h2⟩
    rw [← hun]
    exact IntegrableOn.union hic_ac hic_cd
  have II_ad : IntervalIntegrable f volume a d :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans hac hcd)).mpr hic_ad
  have h_ac0 : (∫ x in a..c, f x) = 0 := by
    rw [intervalIntegral.integral_of_le hac]
    exact setIntegral_eq_zero_of_ae_eq_zero haec
  have h_db0 : (∫ x in d..b, f x) = 0 := by
    rw [intervalIntegral.integral_of_le hdb]
    exact setIntegral_eq_zero_of_ae_eq_zero haeb
  have h1 := intervalIntegral.integral_add_adjacent_intervals II_ac II_cd
  have h2 := intervalIntegral.integral_add_adjacent_intervals II_ad II_db
  linarith [h1, h2, h_ac0, h_db0]


/-- Companion of `integral_eq_of_eq_zero_outside`: integrability transfers from the small
interval to the large one when the function vanishes off the small interval. -/
lemma integrableOn_Icc_of_eq_zero_outside {a c d b : ℝ} (hac : a ≤ c) (hdb : d ≤ b) (hcd : c ≤ d)
    {f : ℝ → ℝ} (hzero : ∀ x : ℝ, x ∈ Set.Icc a b → (x < c ∨ d < x) → f x = 0)
    (hf : IntegrableOn f (Set.Ioc c d) volume) :
    IntegrableOn f (Set.Ioc a b) volume := by
  have haec : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc a c → f x = 0 := by
    rw [ae_iff]
    apply measure_mono_null _ (by simp : volume ({c} : Set ℝ) = 0)
    intro x hx
    have hx' : x ∈ Set.Ioc a c ∧ f x ≠ 0 := Classical.not_imp.mp hx
    simp only [Set.mem_singleton_iff]
    rw [Set.mem_Ioc] at hx'
    by_contra hne
    have hxb : x ∈ Set.Icc a b := ⟨le_of_lt hx'.1.1, le_trans hx'.1.2 hcd |>.trans hdb⟩
    exact hx'.2 (hzero x hxb (Or.inl (lt_of_le_of_ne hx'.1.2 hne)))
  have haeb : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc d b → f x = 0 :=
    Filter.Eventually.of_forall fun x hx =>
      hzero x ⟨le_trans (le_trans hac hcd) (Set.mem_Ioc.mp hx).1.le, (Set.mem_Ioc.mp hx).2⟩
        (Or.inr (Set.mem_Ioc.mp hx).1)
  have hac0 : f =ᵐ[volume.restrict (Set.Ioc a c)] 0 := (ae_restrict_iff' measurableSet_Ioc).mpr haec
  have hdb0 : f =ᵐ[volume.restrict (Set.Ioc d b)] 0 := (ae_restrict_iff' measurableSet_Ioc).mpr haeb
  have hic_ac : IntegrableOn f (Set.Ioc a c) volume :=
    Integrable.congr (integrable_zero ℝ ℝ (volume.restrict (Set.Ioc a c))) hac0.symm
  have hic_db : IntegrableOn f (Set.Ioc d b) volume :=
    Integrable.congr (integrable_zero ℝ ℝ (volume.restrict (Set.Ioc d b))) hdb0.symm
  have hic_cd : IntegrableOn f (Set.Ioc c d) volume := hf
  have hus : Set.Ioc a c ∪ Set.Ioc c d ∪ Set.Ioc d b = Set.Ioc a b := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 (le_trans hcd hdb)⟩
      · exact ⟨lt_of_le_of_lt hac h1, le_trans h2 hdb⟩
      · exact ⟨lt_of_le_of_lt (le_trans hac hcd) h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hxc : x ≤ c
      · exact Or.inl (Or.inl ⟨h1, hxc⟩)
      · by_cases hxd : x ≤ d
        · exact Or.inl (Or.inr ⟨not_le.mp hxc, hxd⟩)
        · exact Or.inr ⟨not_le.mp hxd, h2⟩
  rw [← hus]
  exact IntegrableOn.union (IntegrableOn.union hic_ac hic_cd) hic_db

/-- Positivity of the anchor moments. -/
lemma anchor_moment_pos (n : ℕ) {s₀ : ℝ} (hs₀ : 0 < s₀) {i : ℕ} (hi : i ≤ n) :
    0 < ∫ t in (-(profileX s₀))..(profileX s₀),
      ((1 - t ^ 2) - (s₀ * t) ^ 2) ^ i * t ^ (2 * (n - i)) := by
  have hp : 0 < profileX s₀ := profileX_pos s₀ hs₀
  have hsq : (1 + s₀ ^ 2) * (profileX s₀) ^ 2 = 1 := one_add_sq_mul_profileX_sq s₀
  have hcont : ContinuousOn
      (fun t : ℝ => ((1 - t ^ 2) - (s₀ * t) ^ 2) ^ i * t ^ (2 * (n - i)))
      (Set.Icc (-(profileX s₀)) (profileX s₀)) := by fun_prop
  have hnonneg : ∀ x ∈ Set.Ioc (-(profileX s₀)) (profileX s₀),
      0 ≤ ((1 - x ^ 2) - (s₀ * x) ^ 2) ^ i * x ^ (2 * (n - i)) := by
    intro x hx
    rw [Set.mem_Ioc] at hx
    have hxabs : |x| ≤ profileX s₀ := by rw [abs_le]; exact ⟨le_of_lt hx.1, hx.2⟩
    have hx2 : x ^ 2 ≤ (profileX s₀) ^ 2 := by
      nlinarith [abs_le.mp hxabs, abs_nonneg x, sq_abs x]
    have h1 : (1 + s₀ ^ 2) * x ^ 2 ≤ 1 := by
      calc (1 + s₀ ^ 2) * x ^ 2 ≤ (1 + s₀ ^ 2) * (profileX s₀) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hx2 (by positivity)
        _ = 1 := hsq
    have hb : 0 ≤ 1 - (1 + s₀ ^ 2) * x ^ 2 := by linarith
    have hrew : (1 - x ^ 2) - (s₀ * x) ^ 2 = 1 - (1 + s₀ ^ 2) * x ^ 2 := by ring
    rw [hrew]
    rw [show x ^ (2 * (n - i)) = (x ^ 2) ^ (n - i) from pow_mul x 2 (n - i)]
    exact mul_nonneg (pow_nonneg hb _) (pow_nonneg (sq_nonneg x) _)
  have hpos : ∃ c ∈ Set.Icc (-(profileX s₀)) (profileX s₀),
      0 < ((1 - c ^ 2) - (s₀ * c) ^ 2) ^ i * c ^ (2 * (n - i)) := by
    refine ⟨profileX s₀ / 2, ?_, ?_⟩
    · rw [Set.mem_Icc]; constructor <;> linarith
    · have hc : (1 - (profileX s₀ / 2) ^ 2) - (s₀ * (profileX s₀ / 2)) ^ 2 = 3 / 4 := by
        nlinarith [hsq]
      rw [hc]
      exact mul_pos (pow_pos (by norm_num) _) (pow_pos (by positivity) _)
  exact intervalIntegral.integral_pos (by linarith) hcont hnonneg hpos

/-- From a non-vanishing interval integral one gets interval integrability. -/
lemma intervalIntegrable_of_integral_ne_zero {f : ℝ → ℝ} {a b R : ℝ}
    (h : (∫ x in a..b, f x) = R) (hR : R ≠ 0) : IntervalIntegrable f volume a b := by
  by_contra hc
  rw [intervalIntegral.integral_undef hc] at h
  exact hR h.symm

theorem moment_eqs_below_of_relations (n : ℕ) (hn : 2 ≤ n) {s₀ : ℝ} (hs₀ : 0 < s₀) {h x y f : ℝ → ℝ} (hh : ∀ s ∈ Set.Icc 0 s₀, h s = 0) (hdh : ∀ s ∈ Set.Icc 0 s₀, deriv h s = 0) (hx : ∀ s ∈ Set.Icc 0 s₀, x s = profileX s) (hy : ∀ s ∈ Set.Icc 0 s₀, y s = profileX s) (hf : ∀ t : ℝ, profileX s₀ ≤ |t| → f t = semicircle t) (hrel : (∀ k : ℕ, k ≤ n → (∫ t in (-(profileX s₀))..(profileX s₀), (f t ^ 2 - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k)) = (∫ t in (-(profileX s₀))..(profileX s₀), ((1 - t ^ 2) - (s₀ * t) ^ 2) ^ (n - k) * t ^ (2 * k))) ∧ (∀ k : ℕ, k ≤ n - 1 → (∫ t in (-(profileX s₀))..(profileX s₀), (f t ^ 2 - (s₀ * t) ^ 2) ^ (n - 1 - k) * t ^ (2 * k + 1)) = 0)) : ∀ s ∈ Set.Icc 0 s₀, (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) = (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)), ((1 - t ^ 2) - (s * t) ^ 2) ^ n) ∧ (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0 := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hss : s ≤ s₀ := hs.2
  have hp0pos : 0 < profileX s₀ := profileX_pos s₀ hs₀
  have hp0le1 : profileX s₀ ≤ 1 := (profileX_mem_Icc s₀).2
  have hpss : profileX s₀ ≤ profileX s := profileX_le_profileX hs0 hss
  have hpspos : 0 < profileX s := profileX_pos' s
  have hpsle1 : profileX s ≤ 1 := (profileX_mem_Icc s).2
  have hI : ∀ i ≤ n, (∫ t in (-(profileX s₀))..(profileX s₀), anchorA s₀ f t ^ i * t ^ (2 * (n - i)))
      = (∫ t in (-(profileX s₀))..(profileX s₀), anchorB s₀ t ^ i * t ^ (2 * (n - i))) := by
    intro i hi
    have hh1 := hrel.1 (n - i) (by omega)
    rw [Nat.sub_sub_self hi] at hh1
    simpa only [anchorA, anchorB] using hh1
  have hIpos : ∀ i ≤ n, 0 < (∫ t in (-(profileX s₀))..(profileX s₀), anchorB s₀ t ^ i * t ^ (2 * (n - i))) := by
    intro i hi
    simpa only [anchorB] using anchor_moment_pos n hs₀ hi
  have hPhiII : ∀ i ≤ n, IntervalIntegrable (fun t => anchorA s₀ f t ^ i * t ^ (2 * (n - i))) volume (-(profileX s₀)) (profileX s₀) := by
    intro i hi
    exact intervalIntegrable_of_integral_ne_zero (hI i hi) (ne_of_gt (hIpos i hi))
  have hRhoII : ∀ i ≤ n, IntervalIntegrable (fun t => anchorB s₀ t ^ i * t ^ (2 * (n - i))) volume (-(profileX s₀)) (profileX s₀) := by
    intro i hi
    exact (by simp only [anchorB]; fun_prop : Continuous (fun t : ℝ => anchorB s₀ t ^ i * t ^ (2 * (n - i)))).intervalIntegrable _ _
  have hOddI : ∀ j ≤ n - 1, (∫ t in (-(profileX s₀))..(profileX s₀), anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1)) = 0 := by
    intro j hj
    have hh1 := hrel.2 (n - 1 - j) (by omega)
    rw [Nat.sub_sub_self hj] at hh1
    simpa only [anchorA] using hh1
  rw [hx s hs, hy s hs, hh s hs, hdh s hs]
  simp only [add_zero, sub_zero]
  rw [show (1 / Real.sqrt (1 + s ^ 2)) = profileX s from rfl]
  constructor
  · -- EVEN PART
    have hFexp : ∀ t : ℝ, (f t ^ 2 - (s * t) ^ 2) ^ n =
        ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - i)) *
          (anchorA s₀ f t ^ i * t ^ (2 * (n - i))) := by
      intro t
      rw [show f t ^ 2 - (s * t) ^ 2 = anchorA s₀ f t + (s₀ ^ 2 - s ^ 2) * t ^ 2 by
            simp only [anchorA]; ring, add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_sq_pow]
      ring
    have hGexp : ∀ t : ℝ, ((1 - t ^ 2) - (s * t) ^ 2) ^ n =
        ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - i)) *
          (anchorB s₀ t ^ i * t ^ (2 * (n - i))) := by
      intro t
      rw [show (1 - t ^ 2) - (s * t) ^ 2 = anchorB s₀ t + (s₀ ^ 2 - s ^ 2) * t ^ 2 by
            simp only [anchorB]; ring, add_pow]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_sq_pow]
      ring
    have hDexp : ∀ t : ℝ, (f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n =
        ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - i)) *
          (anchorA s₀ f t ^ i * t ^ (2 * (n - i)) - anchorB s₀ t ^ i * t ^ (2 * (n - i))) := by
      intro t
      rw [hFexp t, hGexp t, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have htermII : ∀ i ∈ Finset.range (n + 1), IntervalIntegrable
        (fun t => ((n.choose i : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - i)) *
          (anchorA s₀ f t ^ i * t ^ (2 * (n - i)) - anchorB s₀ t ^ i * t ^ (2 * (n - i))))
        volume (-(profileX s₀)) (profileX s₀) := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact ((hPhiII i (by omega)).sub (hRhoII i (by omega))).const_mul _
    have hIntD0 : (∫ t in (-(profileX s₀))..(profileX s₀),
        ((f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) = 0 := by
      rw [intervalIntegral.integral_congr (fun t _ => hDexp t),
        intervalIntegral.integral_finsetSum htermII]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [intervalIntegral.integral_const_mul]
      have hsub : (∫ t in (-(profileX s₀))..(profileX s₀),
          (anchorA s₀ f t ^ i * t ^ (2 * (n - i)) - anchorB s₀ t ^ i * t ^ (2 * (n - i)))) = 0 := by
        rw [intervalIntegral.integral_sub (hPhiII i (by omega)) (hRhoII i (by omega)), hI i (by omega)]
        ring
      rw [hsub]; ring
    have hIntD0_int : IntegrableOn (fun t => (f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
        (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume := by
      have hsumint : IntegrableOn (fun t => ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - i)) *
            (anchorA s₀ f t ^ i * t ^ (2 * (n - i)) - anchorB s₀ t ^ i * t ^ (2 * (n - i))))
          (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume := by
        apply integrable_finsetSum
        intro i hi
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mp (htermII i hi)
      exact hsumint.congr_fun (fun t _ => (hDexp t).symm) measurableSet_Ioc
    have hDsupp : ∀ t : ℝ, t ∈ Set.Icc (-(profileX s)) (profileX s) →
        (t < -(profileX s₀) ∨ profileX s₀ < t) →
        (f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n = 0 := by
      intro t ht hlt
      have habs : profileX s₀ < |t| := by
        rcases hlt with hlt | hlt
        · have htn : t < 0 := by linarith
          rw [abs_of_neg htn]; linarith
        · have htp : 0 < t := by linarith
          rw [abs_of_pos htp]; linarith
      have ht1 : |t| ≤ 1 := by
        have ha : |t| ≤ profileX s := by rw [abs_le]; exact ⟨ht.1, ht.2⟩
        linarith
      have htIcc : t ∈ Set.Icc (-1) 1 := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [neg_abs_le t, ht1], by linarith [le_abs_self t, ht1]⟩
      have hsq : f t ^ 2 = 1 - t ^ 2 := by
        rw [hf t (le_of_lt habs), semicircle_sq_of_mem_Icc htIcc]
      have hFeq : f t ^ 2 - (s * t) ^ 2 = (1 - t ^ 2) - (s * t) ^ 2 := by rw [hsq]
      rw [hFeq]
      ring
    have hIntDps : (∫ t in (-(profileX s))..(profileX s),
        ((f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n)) = 0 := by
      rw [integral_eq_of_eq_zero_outside (hac := by linarith) (hdb := hpss) (hcd := by linarith)
        hDsupp hIntD0_int, hIntD0]
    have hIntDps_int : IntegrableOn
        (fun t => (f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
        (Set.Ioc (-(profileX s)) (profileX s)) volume :=
      integrableOn_Icc_of_eq_zero_outside (hac := by linarith) (hdb := hpss) (hcd := by linarith)
        hDsupp hIntD0_int
    have hGn_II : IntervalIntegrable (fun t => ((1 - t ^ 2) - (s * t) ^ 2) ^ n) volume (-(profileX s)) (profileX s) :=
      (by fun_prop : Continuous (fun t : ℝ => ((1 - t ^ 2) - (s * t) ^ 2) ^ n)).intervalIntegrable _ _
    have hFn_II : IntervalIntegrable (fun t => (f t ^ 2 - (s * t) ^ 2) ^ n) volume (-(profileX s)) (profileX s) := by
      have hsum : IntegrableOn (fun t =>
          ((f t ^ 2 - (s * t) ^ 2) ^ n - ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
            + ((1 - t ^ 2) - (s * t) ^ 2) ^ n)
          (Set.Ioc (-(profileX s)) (profileX s)) volume :=
        hIntDps_int.add ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s) ≤ profileX s)).mp hGn_II)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s) ≤ profileX s)).mpr ?_
      exact hsum.congr_fun (fun t _ => by ring) measurableSet_Ioc
    have hgoal1 := intervalIntegral.integral_sub hFn_II hGn_II
    rw [hIntDps] at hgoal1
    linarith
  · -- ODD PART
    have hSigII : ∀ j ≤ n - 1,
        IntegrableOn (fun t => anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1))
          (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume := by
      intro j hj
      have hj' : j ≤ n := by omega
      have hphij : IntegrableOn (fun t => anchorA s₀ f t ^ j * t ^ (2 * (n - j)))
          (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mp (hPhiII j hj')
      have hphin : IntegrableOn (fun t => anchorA s₀ f t ^ n * t ^ (2 * (n - n)))
          (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mp (hPhiII n le_rfl)
      haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))) :=
        ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
            exact measure_Ioc_lt_top (μ := (volume : Measure ℝ))⟩
      have hA_aesm : AEStronglyMeasurable (anchorA s₀ f)
          (volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))) := by
        have hne : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))), t ≠ 0 := by
          rw [ae_iff]
          have hset : {a : ℝ | ¬ a ≠ 0} = ({0} : Set ℝ) := by ext a; simp
          rw [hset]
          simp
        have h1 : AEStronglyMeasurable (fun t => anchorA s₀ f t ^ 1 * t ^ (2 * (n - 1)))
            (volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))) :=
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mp
            (hPhiII 1 (by omega))).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun t : ℝ => (t ^ (2 * (n - 1)))⁻¹)
            (volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))) :=
          ((measurable_id.pow_const (2 * (n - 1))).inv).aestronglyMeasurable
        refine (h1.mul h2).congr ?_
        filter_upwards [hne] with t ht
        rw [Pi.mul_apply, pow_one, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]
      have haesm : AEStronglyMeasurable (fun t => anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1))
          (volume.restrict (Set.Ioc (-(profileX s₀)) (profileX s₀))) :=
        (hA_aesm.pow j).mul ((measurable_id.pow_const (2 * (n - 1 - j) + 1)).aestronglyMeasurable)
      refine Integrable.mono' ((integrable_const (1 : ℝ)).add hphin.norm) haesm ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      apply Filter.Eventually.of_forall
      intro t ht
      have ht1 : |t| ≤ 1 := by
        have ha : |t| ≤ profileX s₀ := by rw [abs_le]; exact ⟨le_of_lt ht.1, ht.2⟩
        linarith
      have hle1 : |t| ^ (2 * (n - 1 - j) + 1) ≤ 1 := by
        have h := pow_le_pow_left₀ (abs_nonneg t) ht1 (2 * (n - 1 - j) + 1)
        simpa using h
      calc ‖anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1)‖
          = |anchorA s₀ f t| ^ j * |t| ^ (2 * (n - 1 - j) + 1) := by
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
        _ ≤ |anchorA s₀ f t| ^ j * 1 :=
            mul_le_mul_of_nonneg_left hle1 (pow_nonneg (abs_nonneg _) _)
        _ = |anchorA s₀ f t| ^ j := by rw [mul_one]
        _ ≤ 1 + |anchorA s₀ f t| ^ n := by
            by_cases hcase : |anchorA s₀ f t| ≤ 1
            · have h1 : |anchorA s₀ f t| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) hcase
              have h2 : 0 ≤ |anchorA s₀ f t| ^ n := pow_nonneg (abs_nonneg _) _
              linarith
            · have h1 : 1 ≤ |anchorA s₀ f t| := le_of_lt (not_le.mp hcase)
              have h2 : |anchorA s₀ f t| ^ j ≤ |anchorA s₀ f t| ^ n := pow_le_pow_right₀ h1 (by omega)
              have h3 : 0 < |anchorA s₀ f t| ^ n := pow_pos (lt_trans zero_lt_one (not_le.mp hcase)) n
              linarith
        _ = 1 + ‖anchorA s₀ f t ^ n * t ^ (2 * (n - n))‖ := by
            rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]; simp
    have hTauOdd : ∀ j : ℕ,
        (∫ t in (-(profileX s₀))..(profileX s₀), anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1)) = 0 := by
      intro j
      apply intervalIntegral_eq_zero_of_odd (a := profileX s₀)
      intro x
      have hB : anchorB s₀ (-x) = anchorB s₀ x := by simp only [anchorB]; ring
      have hodd : Odd (2 * (n - 1 - j) + 1) := ⟨n - 1 - j, by ring⟩
      rw [hB, hodd.neg_pow]
      ring
    have hTauII : ∀ j ≤ n - 1,
        IntervalIntegrable (fun t => anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1))
          volume (-(profileX s₀)) (profileX s₀) := by
      intro j hj
      exact (by simp only [anchorB]; fun_prop : Continuous (fun t : ℝ => anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1))).intervalIntegrable _ _
    have hSigTau0 : ∀ j ≤ n - 1, (∫ t in (-(profileX s₀))..(profileX s₀),
        (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1) - anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1))) = 0 := by
      intro j hj
      have hsigII : IntervalIntegrable (fun t => anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1))
          volume (-(profileX s₀)) (profileX s₀) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mpr (hSigII j hj)
      rw [intervalIntegral.integral_sub hsigII (hTauII j hj), hOddI j hj, hTauOdd j]
      ring
    have hWexp : ∀ t : ℝ, (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t =
        ∑ j ∈ Finset.range ((n - 1) + 1), (((n - 1).choose j : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - 1 - j)) *
          (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1) - anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1)) := by
      intro t
      have hF : (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t =
          ∑ j ∈ Finset.range ((n - 1) + 1), (((n - 1).choose j : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - 1 - j)) *
            (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1)) := by
        rw [show f t ^ 2 - (s * t) ^ 2 = anchorA s₀ f t + (s₀ ^ 2 - s ^ 2) * t ^ 2 by
              simp only [anchorA]; ring]
        rw [add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_sq_pow]
        ring
      have hG : ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t =
          ∑ j ∈ Finset.range ((n - 1) + 1), (((n - 1).choose j : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - 1 - j)) *
            (anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1)) := by
        rw [show (1 - t ^ 2) - (s * t) ^ 2 = anchorB s₀ t + (s₀ ^ 2 - s ^ 2) * t ^ 2 by
              simp only [anchorB]; ring]
        rw [add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_sq_pow]
        ring
      rw [hF, hG, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have htermW_II : ∀ j ∈ Finset.range ((n - 1) + 1), IntervalIntegrable
        (fun t => (((n - 1).choose j : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - 1 - j)) *
          (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1) - anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1)))
        volume (-(profileX s₀)) (profileX s₀) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : j ≤ n - 1 := by omega
      have hsigII : IntervalIntegrable (fun t => anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1))
          volume (-(profileX s₀)) (profileX s₀) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mpr (hSigII j hj')
      exact (hsigII.sub (hTauII j hj')).const_mul _
    have hIntW0 : (∫ t in (-(profileX s₀))..(profileX s₀),
        ((f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)) = 0 := by
      rw [intervalIntegral.integral_congr (fun t _ => hWexp t),
        intervalIntegral.integral_finsetSum htermW_II]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [intervalIntegral.integral_const_mul]
      have hsub : (∫ t in (-(profileX s₀))..(profileX s₀),
          (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1) - anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1))) = 0 :=
        hSigTau0 j (by omega)
      rw [hsub]; ring
    have hIntW0_int : IntegrableOn (fun t =>
        (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)
        (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume := by
      have hsumint : IntegrableOn (fun t => ∑ j ∈ Finset.range ((n - 1) + 1),
          (((n - 1).choose j : ℝ) * (s₀ ^ 2 - s ^ 2) ^ (n - 1 - j)) *
            (anchorA s₀ f t ^ j * t ^ (2 * (n - 1 - j) + 1) - anchorB s₀ t ^ j * t ^ (2 * (n - 1 - j) + 1)))
          (Set.Ioc (-(profileX s₀)) (profileX s₀)) volume := by
        apply integrable_finsetSum
        intro j hj
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s₀) ≤ profileX s₀)).mp (htermW_II j hj)
      exact hsumint.congr_fun (fun t _ => (hWexp t).symm) measurableSet_Ioc
    have hWsupp : ∀ t : ℝ, t ∈ Set.Icc (-(profileX s)) (profileX s) →
        (t < -(profileX s₀) ∨ profileX s₀ < t) →
        (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t = 0 := by
      intro t ht hlt
      have habs : profileX s₀ < |t| := by
        rcases hlt with hlt | hlt
        · have htn : t < 0 := by linarith
          rw [abs_of_neg htn]; linarith
        · have htp : 0 < t := by linarith
          rw [abs_of_pos htp]; linarith
      have ht1 : |t| ≤ 1 := by
        have ha : |t| ≤ profileX s := by rw [abs_le]; exact ⟨ht.1, ht.2⟩
        linarith
      have htIcc : t ∈ Set.Icc (-1) 1 := by
        rw [Set.mem_Icc]
        exact ⟨by linarith [neg_abs_le t, ht1], by linarith [le_abs_self t, ht1]⟩
      have hsq : f t ^ 2 = 1 - t ^ 2 := by
        rw [hf t (le_of_lt habs), semicircle_sq_of_mem_Icc htIcc]
      have hFeq : f t ^ 2 - (s * t) ^ 2 = (1 - t ^ 2) - (s * t) ^ 2 := by rw [hsq]
      rw [hFeq]
      ring
    have hIntWps : (∫ t in (-(profileX s))..(profileX s),
        ((f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)) = 0 := by
      rw [integral_eq_of_eq_zero_outside (hac := by linarith) (hdb := hpss) (hcd := by linarith)
        hWsupp hIntW0_int, hIntW0]
    have hIntWps_int : IntegrableOn (fun t =>
        (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)
        (Set.Ioc (-(profileX s)) (profileX s)) volume :=
      integrableOn_Icc_of_eq_zero_outside (hac := by linarith) (hdb := hpss) (hcd := by linarith)
        hWsupp hIntW0_int
    have hGn1_II : IntervalIntegrable (fun t => ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)
        volume (-(profileX s)) (profileX s) :=
      (by fun_prop : Continuous (fun t : ℝ => ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)).intervalIntegrable _ _
    have hFn1_II : IntervalIntegrable (fun t => (f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t)
        volume (-(profileX s)) (profileX s) := by
      have hsum : IntegrableOn (fun t =>
          ((f t ^ 2 - (s * t) ^ 2) ^ (n - 1) * t - ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)
            + ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t)
          (Set.Ioc (-(profileX s)) (profileX s)) volume :=
        hIntWps_int.add ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s) ≤ profileX s)).mp hGn1_II)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -(profileX s) ≤ profileX s)).mpr ?_
      exact hsum.congr_fun (fun t _ => by ring) measurableSet_Ioc
    have hIntG1 : (∫ t in (-(profileX s))..(profileX s), ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - 1) * t) = 0 := by
      apply intervalIntegral_eq_zero_of_odd (a := profileX s)
      intro x
      have hB : ((1 - (-x) ^ 2) - (s * (-x)) ^ 2) = (1 - x ^ 2) - (s * x) ^ 2 := by ring
      rw [hB]; ring
    have hgoal2 := intervalIntegral.integral_sub hFn1_II hGn1_II
    rw [hIntWps, hIntG1] at hgoal2
    linarith

end

end Commons.Geometry.Ulam