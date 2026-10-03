import Mathlib
import Submission.Work.Analysis.InverseTheory.riemann_shift

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.Analysis.InverseTheory

/-! ## Normal forms for scalar multiplication on `ℂ` -/

lemma real_smul_eq_mul (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  rw [Algebra.smul_def]; simp

lemma circle_smul_eq_mul (z : Circle) (w : ℂ) : z • w = (z : ℂ) * w := by
  rw [Circle.smul_def, Algebra.smul_def]; simp

/-- The `rpow` at the exponent `-12` is the inverse power. -/
lemma rpow_neg_twelve {x : ℝ} (hx : 0 ≤ x) : x ^ (-(12 : ℝ)) = (x⁻¹) ^ 12 := by
  have h12 : ((12 : ℕ) : ℝ) = 12 := by norm_num
  rw [← h12, Real.rpow_neg hx, Real.rpow_natCast, inv_pow]

/-- Dilation of the real Fourier transform: `𝓕(t ↦ ε ψ(εt))(ξ) = 𝓕ψ(ξ/ε)` for `0 < ε`. -/
theorem realFourier_dilation (ψ : ℝ → ℂ) {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    realFourier (fun t : ℝ => (ε : ℂ) * ψ (ε * t)) ξ = realFourier ψ (ξ / ε) := by
  have hsmul : ∀ (z : Circle) (w : ℂ), z • w = (z : ℂ) * w := circle_smul_eq_mul
  have hR : ∀ (r : ℝ) (z : ℂ), r • z = (r : ℂ) * z := real_smul_eq_mul
  simp only [realFourier]
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  simp_rw [hsmul]
  have step1 : (∫ v : ℝ, (𝐞 (-(v * ξ)) : ℂ) * ((ε : ℂ) * ψ (ε * v)))
      = (ε : ℂ) * (∫ v : ℝ, (𝐞 (-(v * ξ)) : ℂ) * ψ (ε * v)) := by
    have h : ∀ v : ℝ, (𝐞 (-(v * ξ)) : ℂ) * ((ε : ℂ) * ψ (ε * v))
        = (ε : ℂ) * ((𝐞 (-(v * ξ)) : ℂ) * ψ (ε * v)) := by
      intro v; ring
    simp_rw [h]
    rw [MeasureTheory.integral_const_mul]
  rw [step1]
  have step2 : (∫ v : ℝ, (𝐞 (-(v * ξ)) : ℂ) * ψ (ε * v))
      = |ε⁻¹| • ∫ u : ℝ, (𝐞 (-(u / ε * ξ)) : ℂ) * ψ u := by
    rw [← Measure.integral_comp_mul_left (fun u : ℝ => (𝐞 (-(u / ε * ξ)) : ℂ) * ψ u) ε]
    apply integral_congr_ae
    filter_upwards with v
    rw [mul_div_cancel_left₀ v hε.ne']
  rw [step2]
  have h4 : (∫ u : ℝ, (𝐞 (-(u / ε * ξ)) : ℂ) * ψ u)
      = ∫ u : ℝ, (𝐞 (-(u * (ξ / ε))) : ℂ) * ψ u := by
    apply integral_congr_ae
    filter_upwards with u
    congr 1
    field_simp
  rw [h4]
  have hZ : (ε : ℂ) * (|ε⁻¹| • (∫ u : ℝ, (𝐞 (-(u * (ξ / ε))) : ℂ) * ψ u))
      = ∫ u : ℝ, (𝐞 (-(u * (ξ / ε))) : ℂ) * ψ u := by
    rw [hR, ← mul_assoc, ← Complex.ofReal_mul, abs_of_pos (inv_pos.mpr hε),
      mul_inv_cancel₀ hε.ne', Complex.ofReal_one, one_mul]
  exact hZ

/-- The character `fourier m` at an integer point of the circle is `1`. -/
lemma fourier_int (m : ℤ) (x : ℤ) : fourier m ((x : ℝ) : UnitAddCircle) = 1 := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  rw [show (2 * ((Real.pi : ℂ)) * Complex.I * (m : ℂ) * ((x : ℝ) : ℂ))
      = ((m * x : ℤ) : ℂ) * (2 * ((Real.pi : ℂ)) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (m * x)

/-- The Fourier transform at `0` is the integral. -/
lemma realFourier_zero (ψ : ℝ → ℂ) : realFourier ψ 0 = ∫ t, ψ t := by
  simp only [realFourier]
  rw [Real.fourier_real_eq]
  simp

/-! ## Big-O at infinity for functions decaying like `jbDecay 12` -/

lemma isBigO_cocompact_of_le_rpow {φ : ℝ → ℂ} {D : ℝ} (_hD : 0 ≤ D)
    (h : ∀ t : ℝ, 1 ≤ |t| → ‖φ t‖ ≤ D * |t| ^ (-(12 : ℝ))) :
    φ =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
  rw [cocompact_eq_atBot_atTop, Asymptotics.isBigO_sup]
  constructor
  · refine Asymptotics.IsBigO.of_bound D (Filter.eventually_atBot.mpr ⟨-1, fun t ht => ?_⟩)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    exact h t (by rw [abs_of_nonpos (by linarith)]; linarith)
  · refine Asymptotics.IsBigO.of_bound D (Filter.eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    exact h t (by rw [abs_of_nonneg (by linarith)]; linarith)

lemma isBigO_cocompact_of_le_inv_pow {φ : ℝ → ℂ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ t : ℝ, 1 ≤ |t| → ‖φ t‖ ≤ D * (|t|⁻¹) ^ 12) :
    φ =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
  refine isBigO_cocompact_of_le_rpow hD fun t ht => ?_
  rw [rpow_neg_twelve (abs_nonneg t)]
  exact h t ht

lemma isBigO_cocompact_of_le_jbDecay {φ : ℝ → ℂ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ t : ℝ, ‖φ t‖ ≤ D * jbDecay 12 t) :
    φ =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
  refine isBigO_cocompact_of_le_inv_pow hD fun t ht => ?_
  have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le zero_lt_one ht
  have h1 : jbDecay 12 t ≤ (|t|⁻¹) ^ 12 := by
    rw [jbDecay]
    refine pow_le_pow_left₀ (jb_inv_nonneg t) ?_ 12
    rw [inv_le_inv₀ (jb_pos t) ht0]
    exact abs_le_jb t
  calc ‖φ t‖ ≤ D * jbDecay 12 t := h t
    _ ≤ D * (|t|⁻¹) ^ 12 := mul_le_mul_of_nonneg_left h1 hD

/-! ## The `ℓ¹` tail of `⟨n⟩^{-12}` -/

lemma summable_inv_pow_succ : Summable (fun n : ℕ => ((((n : ℤ) + 1 : ℤ) : ℝ))⁻¹ ^ 12) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ))⁻¹ ^ 12) := by
    refine ((Real.summable_one_div_nat_pow (p := 12)).mpr (by norm_num : (1 : ℕ) < 12)).congr
      fun n => ?_
    rw [inv_eq_one_div, ← one_div_pow]
  have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ ^ 12) :=
    (summable_nat_add_iff (f := fun m : ℕ => ((m : ℝ))⁻¹ ^ 12) 1).mpr h1
  refine h2.congr fun n => ?_
  have hcast : (((n + 1 : ℕ) : ℝ)) = ((((n : ℤ) + 1 : ℤ) : ℝ)) := by push_cast; ring
  rw [hcast]

lemma tsum_inv_pow_succ_le_two : (∑' n : ℕ, ((((n : ℤ) + 1 : ℤ) : ℝ))⁻¹ ^ 12) ≤ 2 := by
  refine tsum_le_of_forall_range_sum_le (B := 2) fun m => ?_
  have h := sum_range_inv_pow_le 11 1 m (by norm_num) (by norm_num)
  have hcast : ∀ i : ℕ, ((((i : ℤ) + 1 : ℤ) : ℝ)) = (((1 + i : ℕ) : ℝ)) := by
    intro i; push_cast; ring
  calc ∑ i ∈ Finset.range m, ((((i : ℤ) + 1 : ℤ) : ℝ))⁻¹ ^ 12
      = ∑ i ∈ Finset.range m, (((1 + i : ℕ) : ℝ))⁻¹ ^ 12 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcast i]
    _ ≤ 2 * (((1 : ℕ) : ℝ))⁻¹ ^ 11 := h
    _ = 2 := by norm_num

/-- Poisson summation approximation of the full line: if `ψ : ℝ → ℂ` is continuous, has integral
`1`, and decays like `⟨t⟩^{-12}` together with its Fourier transform `realFourier ψ` (with
constant `C ≥ 1`), then for `0 < ε ≤ 1` and `x ∈ ℤ` the Riemann-type sum
`∑_{y∈ℤ} ε ψ(ε(x-y))` is `1` up to `2 ^ 30 C ^ 2 ε ^ 10`.

Route: apply Mathlib's `Real.tsum_eq_tsum_fourier_of_rpow_decay` to `t ↦ ε ψ(εt)` (`b = 12`),
so that the sum equals `∑_m 𝓕ψ(m/ε) · fourier m x`; for `x ∈ ℤ` the character is `1`; the `m = 0`
term is `𝓕ψ(0) = ∫ψ = 1`; and the tail is bounded by the `⟨n⟩^{-12}` Riemann tail.  The dilation
identity `𝓕(t ↦ εψ(εt))(ξ) = 𝓕ψ(ξ/ε)` is proved above as `realFourier_dilation`. -/
theorem poisson_approx (ψ : ℝ → ℂ) (hcont : Continuous ψ) (C : ℝ) (hC : 1 ≤ C)
    (hint : ∫ t, ψ t = 1)
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hFdecay : ∀ t : ℝ, ‖realFourier ψ t‖ ≤ C * jbDecay 12 t)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : ℤ) :
    ‖(∑' y : ℤ, (ε : ℂ) * ψ (ε * ((x : ℝ) - y))) - 1‖ ≤ (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  set f : ℝ → ℂ := fun t => (ε : ℂ) * ψ (ε * t) with hf
  set g : ℤ → ℂ := fun m => realFourier ψ ((m : ℝ) / ε) with hg
  -- Step 1: reindex `y ↦ -y`
  have hreindex : (∑' y : ℤ, (ε : ℂ) * ψ (ε * ((x : ℝ) - y))) = ∑' n : ℤ, f ((x : ℝ) + n) := by
    rw [hf, ← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (ε : ℂ) * ψ (ε * ((x : ℝ) + n)))]
    refine tsum_congr fun y => ?_
    simp only [Equiv.neg_apply, Int.cast_neg, sub_eq_add_neg]
  rw [hreindex]
  -- Step 2: Poisson summation
  have hcont_f : Continuous f := by rw [hf]; fun_prop
  have hf_bigO : f =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    refine isBigO_cocompact_of_le_inv_pow (D := C * ε⁻¹ ^ 12 * ε) (by positivity) ?_
    intro t ht
    have h1 : ‖f t‖ ≤ ε * (C * jbDecay 12 (ε * t)) := by
      rw [hf, norm_mul, Complex.norm_of_nonneg hε0.le]
      exact mul_le_mul_of_nonneg_left (hdecay _) hε0.le
    have h2 : jbDecay 12 (ε * t) ≤ ((ε * |t|)⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      rw [inv_le_inv₀ (jb_pos _) (by positivity)]
      calc ε * |t| = |ε * t| := by rw [abs_mul, abs_of_pos hε0]
        _ ≤ jb (ε * t) := abs_le_jb _
    calc ‖f t‖ ≤ ε * (C * jbDecay 12 (ε * t)) := h1
      _ ≤ ε * (C * ((ε * |t|)⁻¹) ^ 12) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC0.le) hε0.le
      _ = (C * ε⁻¹ ^ 12 * ε) * (|t|⁻¹) ^ 12 := by
            rw [mul_inv, mul_pow]; ring
  have hFf_bigO : (𝓕 f) =O[Filter.cocompact ℝ] (fun t : ℝ => |t| ^ (-(12 : ℝ))) := by
    refine isBigO_cocompact_of_le_inv_pow (D := C * ε ^ 12) (by positivity) ?_
    intro t ht
    have h1 : 𝓕 f t = realFourier ψ (t / ε) := by
      rw [hf]; exact realFourier_dilation ψ hε0 t
    rw [h1]
    have h2 : jbDecay 12 (t / ε) ≤ (ε * |t|⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      have hq : 0 < |t / ε| :=
        abs_pos.mpr (div_ne_zero (abs_pos.mp (lt_of_lt_of_le zero_lt_one ht)) hε0.ne')
      calc (jb (t / ε))⁻¹ ≤ (|t / ε|)⁻¹ := (inv_le_inv₀ (jb_pos _) hq).mpr (abs_le_jb _)
        _ = ε * |t|⁻¹ := by rw [abs_div, abs_of_pos hε0, inv_div, div_eq_mul_inv]
    calc ‖realFourier ψ (t / ε)‖ ≤ C * jbDecay 12 (t / ε) := hFdecay _
      _ ≤ C * (ε * |t|⁻¹) ^ 12 := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = C * ε ^ 12 * (|t|⁻¹) ^ 12 := by rw [mul_pow]; ring
  have hpoisson : (∑' n : ℤ, f ((x : ℝ) + n))
      = ∑' m : ℤ, 𝓕 f (m : ℝ) * fourier m ((x : ℝ) : UnitAddCircle) :=
    Real.tsum_eq_tsum_fourier_of_rpow_decay (f := f) (b := 12) hcont_f (by norm_num)
      hf_bigO hFf_bigO ((x : ℝ))
  rw [hpoisson]
  have hterm : ∀ m : ℤ, 𝓕 f (m : ℝ) * fourier m ((x : ℝ) : UnitAddCircle) = g m := by
    intro m
    rw [fourier_int m x, mul_one, hg]
    rw [hf]
    exact realFourier_dilation ψ hε0 (m : ℝ)
  simp_rw [hterm]
  -- Step 3: split off the `m = 0` term and bound the two tails
  have hg0 : g 0 = 1 := by
    rw [hg]
    simp only [Int.cast_zero, zero_div]
    rw [realFourier_zero, hint]
  set B : ℕ → ℝ := fun n => ((((n : ℤ) + 1 : ℤ) : ℝ))⁻¹ ^ 12 with hB
  have hBs : Summable B := by rw [hB]; exact summable_inv_pow_succ
  have hB2 : (∑' n : ℕ, B n) ≤ 2 := by rw [hB]; exact tsum_inv_pow_succ_le_two
  have hg_bound : ∀ N : ℤ, N ≠ 0 → ‖g N‖ ≤ C * ε ^ 12 * ((|((N : ℝ))|)⁻¹) ^ 12 := by
    intro N hN
    have hqpos : 0 < |((N : ℝ)) / ε| := by
      rw [abs_pos]
      exact div_ne_zero (by exact_mod_cast hN) hε0.ne'
    have h1 : ‖g N‖ ≤ C * jbDecay 12 (((N : ℝ)) / ε) := by
      rw [hg]; exact hFdecay _
    have h2 : jbDecay 12 (((N : ℝ)) / ε) ≤ ((|((N : ℝ)) / ε|)⁻¹) ^ 12 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
      rw [inv_le_inv₀ (jb_pos _) hqpos]
      exact abs_le_jb _
    calc ‖g N‖ ≤ C * jbDecay 12 (((N : ℝ)) / ε) := h1
      _ ≤ C * ((|((N : ℝ)) / ε|)⁻¹) ^ 12 := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = C * ε ^ 12 * ((|((N : ℝ))|)⁻¹) ^ 12 := by
            rw [abs_div, abs_of_pos hε0, inv_div, div_pow, div_eq_mul_inv, ← inv_pow]; ring
  have hbd1 : ∀ n : ℕ, ‖g ((n : ℤ) + 1)‖ ≤ C * ε ^ 12 * B n := by
    intro n
    have h := hg_bound ((n : ℤ) + 1) (by omega)
    have h1 : (|(((↑n + 1 : ℤ)) : ℝ)|)⁻¹ = (((↑n + 1 : ℤ) : ℝ))⁻¹ := by
      rw [abs_of_pos]; push_cast; positivity
    rw [h1] at h
    rwa [hB]
  have hbd2 : ∀ n : ℕ, ‖g (-((n : ℤ) + 1))‖ ≤ C * ε ^ 12 * B n := by
    intro n
    have h := hg_bound (-((n : ℤ) + 1)) (by omega)
    have h1 : (|(((-(↑n + 1) : ℤ)) : ℝ)|) = (((↑n + 1 : ℤ) : ℝ)) := by
      rw [Int.cast_neg, abs_neg, abs_of_nonneg]
      push_cast; positivity
    rw [h1] at h
    rwa [hB]
  have hmaj : Summable (fun n : ℕ => C * ε ^ 12 * B n) := hBs.mul_left _
  have hsum1 : Summable (fun n : ℕ => g ((n : ℤ) + 1)) := Summable.of_norm_bounded hmaj hbd1
  have hsum2 : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := Summable.of_norm_bounded hmaj hbd2
  have hsplit : (∑' m : ℤ, g m) - 1
      = (∑' n : ℕ, g ((n : ℤ) + 1)) + (∑' n : ℕ, g (-((n : ℤ) + 1))) := by
    rw [tsum_of_add_one_of_neg_add_one hsum1 hsum2, hg0]
    ring
  rw [hsplit]
  have hA : ‖∑' n : ℕ, g ((n : ℤ) + 1)‖ ≤ C * ε ^ 12 * 2 := by
    refine (norm_tsum_le_tsum_norm hsum1.norm).trans ?_
    calc (∑' n : ℕ, ‖g ((n : ℤ) + 1)‖) ≤ ∑' n : ℕ, C * ε ^ 12 * B n :=
          hsum1.norm.tsum_le_tsum hbd1 hmaj
      _ = C * ε ^ 12 * (∑' n : ℕ, B n) := by rw [tsum_mul_left]
      _ ≤ C * ε ^ 12 * 2 := mul_le_mul_of_nonneg_left hB2 (by positivity)
  have hA' : ‖∑' n : ℕ, g (-((n : ℤ) + 1))‖ ≤ C * ε ^ 12 * 2 := by
    refine (norm_tsum_le_tsum_norm hsum2.norm).trans ?_
    calc (∑' n : ℕ, ‖g (-((n : ℤ) + 1))‖) ≤ ∑' n : ℕ, C * ε ^ 12 * B n :=
          hsum2.norm.tsum_le_tsum hbd2 hmaj
      _ = C * ε ^ 12 * (∑' n : ℕ, B n) := by rw [tsum_mul_left]
      _ ≤ C * ε ^ 12 * 2 := mul_le_mul_of_nonneg_left hB2 (by positivity)
  calc ‖(∑' n : ℕ, g ((n : ℤ) + 1)) + (∑' n : ℕ, g (-((n : ℤ) + 1)))‖
      ≤ ‖∑' n : ℕ, g ((n : ℤ) + 1)‖ + ‖∑' n : ℕ, g (-((n : ℤ) + 1))‖ := norm_add_le _ _
    _ ≤ C * ε ^ 12 * 2 + C * ε ^ 12 * 2 := add_le_add hA hA'
    _ ≤ (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 := by
        have h1 : ε ^ 12 ≤ ε ^ 10 := by
          have hε2 : ε ^ 2 ≤ 1 := by nlinarith
          calc ε ^ 12 = ε ^ 10 * ε ^ 2 := by ring
            _ ≤ ε ^ 10 * 1 := mul_le_mul_of_nonneg_left hε2 (by positivity)
            _ = ε ^ 10 := by ring
        have h2 : (4 : ℝ) * C ≤ (2 : ℝ) ^ 30 * C ^ 2 := by nlinarith [hC, sq_nonneg C]
        have h3 : C * ε ^ 12 * 2 + C * ε ^ 12 * 2 = 4 * C * ε ^ 12 := by ring
        rw [h3]
        calc (4 : ℝ) * C * ε ^ 12 = (4 * C) * ε ^ 12 := by ring
          _ ≤ ((2 : ℝ) ^ 30 * C ^ 2) * ε ^ 10 :=
              mul_le_mul h2 h1 (by positivity) (by positivity)
          _ = (2 : ℝ) ^ 30 * C ^ 2 * ε ^ 10 := by ring

end Work.Analysis.InverseTheory
