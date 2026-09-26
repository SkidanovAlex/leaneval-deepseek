/-
# The model pole integral over the cusp tile

For `w ∈ E = KEpsilon` and `a ≥ 0`, the model integral

  `∫_{Im w/2}^{1} 1/(i t - w) · t^j · e^{-a t} dt`

(which is the singular part of the `low`-layer contour integral of CKMRV §5.2 on the cusp tiles
`±1 + E`) obeys a uniform bound `C (scale w)^N (1 + a Im w)^{-J}`.  The integral is *signed*:
the modulus bound is false (its size is `log(1/|Re w|)` if one takes absolute values), but the
antiderivative `log(i t - w)` keeps the two endpoints at a bounded ratio.

The main theorem is `Work.Asymptotics.tile_pole_integral_decay`; the specialisation `J = 0` gives
`Work.Asymptotics.tile_pole_integral_bound`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.not_integrableOn_of_simplePole

noncomputable section
open MeasureTheory Filter Topology Set
open scoped Topology

namespace Work.Asymptotics

/-! ## Real-variable helpers -/

lemma exp_self_le (u : ℝ) : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]

lemma pow_mul_exp_neg_half_le (J : ℕ) : ∀ x : ℝ, 0 ≤ x → x ^ J * Real.exp (-x / 2) ≤ (2 * J) ^ J := by
  intro x hx
  have hpowJ : (0:ℝ) ≤ (2*J)^J := by positivity
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ; simp only [Nat.cast_zero, mul_zero, pow_zero, one_mul]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · rcases le_or_gt x (2 * (J:ℝ)) with h | h
    · have h1 : x ^ J ≤ (2*(J:ℝ))^J := pow_le_pow_left₀ hx h J
      have h2 : Real.exp (-x/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc x^J * Real.exp (-x/2) ≤ (2*(J:ℝ))^J * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le hpowJ
        _ = (2*(J:ℝ))^J := by ring
    · have hJpos : (0:ℝ) < (2*(J:ℝ)) := by positivity
      set u : ℝ := x / (2*(J:ℝ)) with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hxu : x = 2*(J:ℝ)*u := by rw [hu]; field_simp
      have hule : u ≤ Real.exp u := exp_self_le u
      have hstep : u^J ≤ Real.exp ((J:ℝ)*u) := by
        have h1 : u^J ≤ (Real.exp u)^J := pow_le_pow_left₀ hu0 hule J
        rwa [← Real.exp_nat_mul] at h1
      have hpos : (0:ℝ) < Real.exp ((J:ℝ)*u) := Real.exp_pos _
      have hmain : u^J * Real.exp (-((J:ℝ)*u)) ≤ 1 := by
        rw [Real.exp_neg]
        calc u^J * (Real.exp ((J:ℝ)*u))⁻¹ ≤ Real.exp ((J:ℝ)*u) * (Real.exp ((J:ℝ)*u))⁻¹ :=
              mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr hpos.le)
          _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      have harg : -(2*(J:ℝ)*u) / 2 = -((J:ℝ)*u) := by ring
      have heq : x^J * Real.exp (-x/2) = (2*(J:ℝ))^J * (u^J * Real.exp (-((J:ℝ)*u))) := by
        rw [hxu, mul_pow, harg]
        ring
      rw [heq]
      calc (2*(J:ℝ))^J * (u^J * Real.exp (-((J:ℝ)*u))) ≤ (2*(J:ℝ))^J * 1 :=
            mul_le_mul_of_nonneg_left hmain hpowJ
        _ = (2*(J:ℝ))^J := by ring

lemma pow_mul_exp_neg_le' (M : ℕ) : ∀ x : ℝ, 0 ≤ x → x ^ M * Real.exp (-x) ≤ (M:ℝ) ^ M := by
  intro x hx
  have hpowM : (0:ℝ) ≤ (M:ℝ)^M := by positivity
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp only [Nat.cast_zero, pow_zero, one_mul]
    exact Real.exp_le_one_iff.mpr (by linarith)
  · rcases le_or_gt x (M:ℝ) with h | h
    · have h1 : x ^ M ≤ (M:ℝ)^M := pow_le_pow_left₀ hx h M
      have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      calc x^M * Real.exp (-x) ≤ (M:ℝ)^M * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le hpowM
        _ = (M:ℝ)^M := by ring
    · have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
      set u : ℝ := x / (M:ℝ) with hu
      have hu0 : 0 ≤ u := by rw [hu]; positivity
      have hxu : x = (M:ℝ)*u := by rw [hu]; field_simp
      have hule : u ≤ Real.exp u := exp_self_le u
      have hstep : u^M ≤ Real.exp ((M:ℝ)*u) := by
        have h1 : u^M ≤ (Real.exp u)^M := pow_le_pow_left₀ hu0 hule M
        rwa [← Real.exp_nat_mul] at h1
      have hpos : (0:ℝ) < Real.exp ((M:ℝ)*u) := Real.exp_pos _
      have hmain : u^M * Real.exp (-((M:ℝ)*u)) ≤ 1 := by
        rw [Real.exp_neg]
        calc u^M * (Real.exp ((M:ℝ)*u))⁻¹ ≤ Real.exp ((M:ℝ)*u) * (Real.exp ((M:ℝ)*u))⁻¹ :=
              mul_le_mul_of_nonneg_right hstep (inv_nonneg.mpr hpos.le)
          _ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
      have heq : x^M * Real.exp (-x) = (M:ℝ)^M * (u^M * Real.exp (-((M:ℝ)*u))) := by
        rw [hxu, mul_pow]
        ring
      rw [heq]
      calc (M:ℝ)^M * (u^M * Real.exp (-((M:ℝ)*u))) ≤ (M:ℝ)^M * 1 :=
            mul_le_mul_of_nonneg_left hmain hpowM
        _ = (M:ℝ)^M := by ring

lemma exp_neg_half_mul_pow_bdd (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (-x / 2) * (1 + x) ^ J ≤ C := by
  refine ⟨2 ^ J * (1 + (2 * J) ^ J), by positivity, fun x hx => ?_⟩
  have hbase : (0:ℝ) < 2^J := by positivity
  rcases le_or_gt x 1 with h | h
  · have h1 : (1+x)^J ≤ 2^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h2 : Real.exp (-x/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : Real.exp (-x/2) * (1+x)^J ≤ 2^J := by
      have := mul_le_mul h2 h1 (by positivity) (by norm_num)
      simpa using this
    have h5 : (0:ℝ) ≤ (2*J)^J := by positivity
    nlinarith [h3, h5, hbase]
  · have h1 : (1+x)^J ≤ (2*x)^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h3 : Real.exp (-x/2) * (2*x)^J = 2^J * (x^J * Real.exp (-x/2)) := by rw [mul_pow]; ring
    have h4 : Real.exp (-x/2) * (1+x)^J ≤ 2^J * (x^J * Real.exp (-x/2)) := by
      rw [← h3]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h5 : x^J * Real.exp (-x/2) ≤ (2*(J:ℝ))^J := pow_mul_exp_neg_half_le J x hx
    have h6 : 2^J * (x^J * Real.exp (-x/2)) ≤ 2^J * (2*(J:ℝ))^J := mul_le_mul_of_nonneg_left h5 hbase.le
    have h7 : (0:ℝ) ≤ (2*(J:ℝ))^J := by positivity
    nlinarith [h4, h6, h7, hbase]

lemma exp_neg_mul_pow_bdd (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → Real.exp (-x) * x * (1 + x) ^ J ≤ C := by
  refine ⟨2 ^ J * (1 + ((J+1:ℕ):ℝ) ^ (J+1)), by positivity, fun x hx => ?_⟩
  have hbase : (0:ℝ) < 2^J := by positivity
  rcases le_or_gt x 1 with h | h
  · have h1 : (1+x)^J ≤ 2^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : x * Real.exp (-x) ≤ 1 := by
      calc x * Real.exp (-x) ≤ 1 * 1 := mul_le_mul (by linarith) h2 (Real.exp_pos _).le (by norm_num)
        _ = 1 := by ring
    have h4 : Real.exp (-x) * x * (1+x)^J = (x * Real.exp (-x)) * (1+x)^J := by ring
    rw [h4]
    have h5 : (x * Real.exp (-x)) * (1+x)^J ≤ 2^J := by
      have := mul_le_mul h3 h1 (by positivity) (by norm_num)
      simpa using this
    have h7 : (0:ℝ) ≤ ((J+1:ℕ):ℝ)^(J+1) := by positivity
    nlinarith [h5, h7, hbase]
  · have h1 : (1+x)^J ≤ (2*x)^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h4 : Real.exp (-x) * x * (1+x)^J ≤ Real.exp (-x) * x * (2*x)^J :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : Real.exp (-x) * x * (2*x)^J = 2^J * (x^(J+1) * Real.exp (-x)) := by
      rw [mul_pow, pow_succ]; ring
    rw [h5] at h4
    have h6 : x^(J+1) * Real.exp (-x) ≤ ((J+1:ℕ):ℝ)^(J+1) := pow_mul_exp_neg_le' (J+1) x hx
    have h7 : 2^J * (x^(J+1) * Real.exp (-x)) ≤ 2^J * ((J+1:ℕ):ℝ)^(J+1) :=
      mul_le_mul_of_nonneg_left h6 hbase.le
    have h8 : (0:ℝ) ≤ ((J+1:ℕ):ℝ)^(J+1) := by positivity
    nlinarith [h4, h7, h8, hbase]

/-! ### The weighted exponential moment -/

lemma exp_neg_half_mul_mul_pow_bdd (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x * Real.exp (-x/2) * (1 + x)^J ≤ C := by
  refine ⟨2^J * (1 + (2*((J+1:ℕ):ℝ))^(J+1)), by positivity, fun x hx => ?_⟩
  have hbase : (0:ℝ) < 2^J := by positivity
  rcases le_or_gt x 1 with h | h
  · have h1 : (1+x)^J ≤ 2^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h2 : Real.exp (-x/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : x * Real.exp (-x/2) * (1+x)^J ≤ 2^J := by
      have h4 : x * Real.exp (-x/2) ≤ 1 := by
        calc x * Real.exp (-x/2) ≤ 1 * 1 := mul_le_mul (by linarith) h2 (Real.exp_pos _).le (by norm_num)
          _ = 1 := by ring
      have := mul_le_mul h4 h1 (by positivity) (by norm_num)
      simpa using this
    have h5 : (0:ℝ) ≤ (2*((J+1:ℕ):ℝ))^(J+1) := by positivity
    nlinarith [h3, h5, hbase]
  · have h1 : (1+x)^J ≤ (2*x)^J := pow_le_pow_left₀ (by linarith) (by linarith) J
    have h4 : x * Real.exp (-x/2) * (1+x)^J ≤ x * Real.exp (-x/2) * (2*x)^J :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h5 : x * Real.exp (-x/2) * (2*x)^J = 2^J * (x^(J+1) * Real.exp (-x/2)) := by
      rw [mul_pow, pow_succ]; ring
    rw [h5] at h4
    have h6 : x^(J+1) * Real.exp (-x/2) ≤ (2*((J+1:ℕ):ℝ))^(J+1) :=
      pow_mul_exp_neg_half_le (J+1) x hx
    have h7 : 2^J * (x^(J+1) * Real.exp (-x/2)) ≤ 2^J * (2*((J+1:ℕ):ℝ))^(J+1) :=
      mul_le_mul_of_nonneg_left h6 hbase.le
    have h8 : (0:ℝ) ≤ (2*((J+1:ℕ):ℝ))^(J+1) := by positivity
    nlinarith [h4, h7, h8, hbase]


/-! ### Pointwise bounds for the difference of the exponential moments -/

lemma abs_pow_sub_pow_le (j : ℕ) {t y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |t^j - y^j| ≤ (j:ℝ) * |t-y| := by
  have hconv : Convex ℝ (Set.Icc (0:ℝ) 1) := convex_Icc _ _
  have hd : ∀ x ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℝ (fun u : ℝ => u^j) x := by
    intro x _; fun_prop
  have hb : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖deriv (fun u : ℝ => u^j) x‖ ≤ (j:ℝ) := by
    intro x hx
    rw [deriv_pow_field (x := x) j, Real.norm_eq_abs, abs_mul]
    have hx1 : x ≤ 1 := hx.2
    have hx0 : 0 ≤ x := hx.1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ))]
    have habs : |x ^ (j-1)| ≤ 1 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [abs_of_nonneg (by positivity)]
        exact pow_le_one₀ hx0 hx1
    calc (j:ℝ) * |x ^ (j-1)| ≤ (j:ℝ) * 1 := mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (j:ℝ) := by ring
  have h := hconv.norm_image_sub_le_of_norm_deriv_le hd hb hy ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm] at h
  exact h

lemma abs_exp_neg_sub_le {a : ℝ} (ha : 0 ≤ a) {t y : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |Real.exp (-(a*t)) - Real.exp (-(a*y))| ≤ a * |t-y| := by
  have hconv : Convex ℝ (Set.Icc (0:ℝ) 1) := convex_Icc _ _
  have hderiv : ∀ x : ℝ, HasDerivAt (fun u : ℝ => Real.exp (-(a*u))) (-a * Real.exp (-(a*x))) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => -(a*u)) (-a) x := by
      have h0 : HasDerivAt (fun u : ℝ => a*u) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      have h2 : HasDerivAt (fun u : ℝ => -(a*u)) (-a) x := h0.neg
      exact h2
    have h3 : HasDerivAt (fun u : ℝ => Real.exp (-(a*u))) (Real.exp (-(a*x)) * (-a)) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(a*x))).comp x h1
    convert h3 using 1
    ring
  have hd : ∀ x ∈ Set.Icc (0:ℝ) 1, DifferentiableAt ℝ (fun u : ℝ => Real.exp (-(a*u))) x :=
    fun x _ => (hderiv x).differentiableAt
  have hb : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖deriv (fun u : ℝ => Real.exp (-(a*u))) x‖ ≤ a := by
    intro x hx
    rw [(hderiv x).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg ha,
      abs_of_nonneg (Real.exp_pos _).le]
    have hx0 : 0 ≤ x := hx.1
    have hexp : Real.exp (-(a*x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc a * Real.exp (-(a*x)) ≤ a * 1 := mul_le_mul_of_nonneg_left hexp ha
      _ = a := by ring
  have h := hconv.norm_image_sub_le_of_norm_deriv_le hd hb hy ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_sub_comm] at h
  exact h

/-- `‖t^j e^{-at} - y^j e^{-ay}‖ ≤ (j+a)|t-y|` on the window `[y/2, 1]`. -/
lemma norm_pow_mul_exp_sub_le (j : ℕ) {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hy1 : y ≤ 1/2) :
    ∀ t ∈ Set.Icc (y/2) 1,
      ‖(t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ)) - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ))‖
        ≤ ((j:ℝ)+a) * |t-y| := by
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1, hy]
  have ht1 : t ≤ 1 := ht.2
  have hy0 : 0 ≤ y := le_of_lt hy
  have hty : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0, ht1⟩
  have hyy : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy0, by linarith⟩
  have hE : ∀ s : ℝ, Complex.exp (-(a:ℂ)*(s:ℂ)) = ((Real.exp (-(a*s)) : ℝ) : ℂ) := by
    intro s
    have harg : -(a:ℂ)*(s:ℂ) = ((-(a*s) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_exp]
  have h1 : (t:ℂ)^j = ((t^j : ℝ) : ℂ) := (Complex.ofReal_pow t j).symm
  have h2 : (y:ℂ)^j = ((y^j : ℝ) : ℂ) := (Complex.ofReal_pow y j).symm
  rw [hE t, hE y, h1, h2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real]
  have hsplit : t^j * Real.exp (-(a*t)) - y^j * Real.exp (-(a*y))
      = t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))
        + (t^j - y^j) * Real.exp (-(a*y)) := by ring
  rw [hsplit]
  have hb1 : |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))| ≤ 1 * (a * |t-y|) := by
    rw [abs_mul]
    have hp : |t^j| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ ht0 ht1
    exact mul_le_mul hp (abs_exp_neg_sub_le ha hty hyy) (abs_nonneg _) (by norm_num)
  have hb2 : |(t^j - y^j) * Real.exp (-(a*y))| ≤ ((j:ℝ) * |t-y|) * 1 := by
    rw [abs_mul]
    have hp : |Real.exp (-(a*y))| ≤ 1 := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_mul (abs_pow_sub_pow_le j hty hyy) hp (abs_nonneg _) (by positivity)
  calc |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y))) + (t^j - y^j) * Real.exp (-(a*y))|
      ≤ |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))| + |(t^j - y^j) * Real.exp (-(a*y))| :=
        abs_add_le _ _
    _ ≤ 1 * (a * |t-y|) + ((j:ℝ) * |t-y|) * 1 := add_le_add hb1 hb2
    _ = ((j:ℝ)+a) * |t-y| := by ring

/-- The weighted version: the difference is `O(e^{-ay/2}|t-y|)`. -/
lemma norm_pow_mul_exp_sub_le_weighted (j : ℕ) {a y : ℝ} (ha : 0 ≤ a) (hy : 0 < y)
    (hy1 : y ≤ 1/2) :
    ∀ t ∈ Set.Icc (y/2) 1,
      ‖(t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ)) - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ))‖
        ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) * |t-y| := by
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1, hy]
  have ht1 : t ≤ 1 := ht.2
  have hty : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0, ht1⟩
  have hyy : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hy, by linarith [hy]⟩
  have hE : ∀ s : ℝ, Complex.exp (-(a:ℂ)*(s:ℂ)) = ((Real.exp (-(a*s)) : ℝ) : ℂ) := by
    intro s
    have harg : -(a:ℂ)*(s:ℂ) = ((-(a*s) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, ← Complex.ofReal_exp]
  have h1 : (t:ℂ)^j = ((t^j : ℝ) : ℂ) := (Complex.ofReal_pow t j).symm
  have h2 : (y:ℂ)^j = ((y^j : ℝ) : ℂ) := (Complex.ofReal_pow y j).symm
  rw [hE t, hE y, h1, h2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real]
  have htp : |t^j| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ ht0 ht1
  have h2' : |Real.exp (-(a*t)) - Real.exp (-(a*y))| ≤ a * Real.exp (-(a*y/2)) * |t-y| := by
    have hu : t - y/2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hy]⟩
    have hv : y/2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith [hy1]⟩
    have hraw := abs_exp_neg_sub_le ha hu hv
    have harg : (t - y/2) - y/2 = t - y := by ring
    rw [harg] at hraw
    have hfac : Real.exp (-(a*t)) - Real.exp (-(a*y))
        = Real.exp (-(a*y/2)) * (Real.exp (-(a*(t-y/2))) - Real.exp (-(a*(y/2)))) := by
      have hh1 : -(a*y/2) + -(a*(t-y/2)) = -(a*t) := by ring
      have hh2 : -(a*y/2) + -(a*(y/2)) = -(a*y) := by ring
      rw [mul_sub, ← Real.exp_add, ← Real.exp_add, hh1, hh2]
    rw [hfac, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(a*y/2)) * |Real.exp (-(a*(t-y/2))) - Real.exp (-(a*(y/2)))|
        ≤ Real.exp (-(a*y/2)) * (a * |t-y|) := mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
      _ = a * Real.exp (-(a*y/2)) * |t-y| := by ring
  have hsplit : t^j * Real.exp (-(a*t)) - y^j * Real.exp (-(a*y))
      = t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))
        + (t^j - y^j) * Real.exp (-(a*y)) := by ring
  rw [hsplit]
  have hb1 : |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))|
      ≤ 1 * (a * Real.exp (-(a*y/2)) * |t-y|) := by
    rw [abs_mul]
    exact mul_le_mul htp h2' (abs_nonneg _) (by norm_num)
  have hb2 : |(t^j - y^j) * Real.exp (-(a*y))| ≤ ((j:ℝ) * |t-y|) * Real.exp (-(a*y/2)) := by
    rw [abs_mul]
    have hp : |Real.exp (-(a*y))| ≤ Real.exp (-(a*y/2)) := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (by nlinarith [hy, ha])
    exact mul_le_mul (abs_pow_sub_pow_le j hty hyy) hp (abs_nonneg _) (by positivity)
  calc |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y))) + (t^j - y^j) * Real.exp (-(a*y))|
      ≤ |t^j * (Real.exp (-(a*t)) - Real.exp (-(a*y)))| + |(t^j - y^j) * Real.exp (-(a*y))| :=
        abs_add_le _ _
    _ ≤ 1 * (a * Real.exp (-(a*y/2)) * |t-y|) + ((j:ℝ) * |t-y|) * Real.exp (-(a*y/2)) :=
        add_le_add hb1 hb2
    _ ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) * |t-y| := by
        have hnn : (0:ℝ) ≤ |t-y| := abs_nonneg _
        have he : (0:ℝ) < Real.exp (-(a*y/2)) := Real.exp_pos _
        nlinarith

/-! ### The complex inversion identity -/

lemma inv_add_mul_I (a b : ℝ) :
    (1 : ℂ) / ((a : ℂ) + (b : ℂ) * Complex.I)
      = ((a : ℂ) - (b : ℂ) * Complex.I) / ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne ((a:ℂ) + (b:ℂ)*Complex.I) 0 with h | h
  · have ha : a = 0 := by
      have hh := congrArg Complex.re h; simpa using hh
    have hb : b = 0 := by
      have hh := congrArg Complex.im h; simpa using hh
    subst ha; subst hb; simp
  · have hD : ((a^2+b^2 : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0:ℝ) < a^2+b^2 := by
        rcases eq_or_ne a 0 with ha | ha
        · rcases eq_or_ne b 0 with hb | hb
          · exact absurd (by rw [ha, hb]; simp) h
          · nlinarith [sq_pos_of_ne_zero hb]
        · nlinarith [sq_pos_of_ne_zero ha]
      exact_mod_cast ne_of_gt hpos
    field_simp
    push_cast
    rw [show ((a:ℂ)+(b:ℂ)*Complex.I)*((a:ℂ)-(b:ℂ)*Complex.I)
        = (a:ℂ)^2 - ((b:ℂ)^2 * (Complex.I*Complex.I)) by ring]
    rw [Complex.I_mul_I]
    ring

/-! ### The `arctan` integral -/

lemma integral_abs_div_sq_le_pi {e y : ℝ} (hy : 0 < y) :
    ∫ t in (y/2)..1, |e| / (e^2 + (t-y)^2) ≤ Real.pi := by
  rcases eq_or_ne e 0 with he0 | hene
  · subst he0
    have hz : (fun t : ℝ => |(0:ℝ)| / ((0:ℝ)^2 + (t-y)^2)) = fun _ : ℝ => (0:ℝ) := by
      funext t; simp
    rw [hz, intervalIntegral.integral_zero]
    positivity
  · set F : ℝ → ℝ := fun t => (e/|e|) * Real.arctan ((t-y)/e) with hF
    have hderiv : ∀ t ∈ Set.uIcc (y/2) 1, HasDerivAt F (|e|/(e^2+(t-y)^2)) t := by
      intro t ht
      have h1 : HasDerivAt (fun s : ℝ => (s-y)/e) (1/e) t := by
        have h0 : HasDerivAt (fun s : ℝ => (s-y)/e) ((1:ℝ)/e) t := by
          have hh := ((hasDerivAt_id t).sub_const y).div_const e
          simpa using hh
        exact h0
      have h2 : HasDerivAt (fun s : ℝ => Real.arctan ((s-y)/e))
          (1/(1+((t-y)/e)^2) * (1/e)) t := HasDerivAt.arctan h1
      have h3 : HasDerivAt F ((e/|e|) * (1/(1+((t-y)/e)^2) * (1/e))) t := by
        rw [hF]
        exact h2.const_mul (e/|e|)
      convert h3 using 1
      have hq : (1:ℝ) + ((t-y)/e)^2 ≠ 0 := by positivity
      have hD : e^2 + (t-y)^2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hene]
      field_simp
      rw [sq_abs]
    have hint : IntervalIntegrable (fun t : ℝ => |e| / (e^2 + (t-y)^2)) volume (y/2) 1 := by
      refine Continuous.intervalIntegrable ?_ _ _
      refine Continuous.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · intro t; nlinarith [sq_pos_of_ne_zero hene]
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [hval]
    have hbound : ∀ t : ℝ, |F t| ≤ Real.pi / 2 := by
      intro t
      have h1 : |(e / |e|)| = 1 := by
        have hpos : (0:ℝ) < |e| := abs_pos.mpr hene
        rw [abs_div, abs_abs, div_self (ne_of_gt hpos)]
      have h2 : |Real.arctan ((t-y)/e)| ≤ Real.pi/2 := by
        rw [abs_le]
        exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _), le_of_lt (Real.arctan_lt_pi_div_two _)⟩
      rw [hF]
      simp only
      rw [abs_mul, h1, one_mul]
      exact h2
    have hfinal : F 1 - F (y/2) ≤ Real.pi := by
      have a1 := hbound 1
      have a2 := hbound (y/2)
      have h3 := abs_le.mp a1
      have h4 := abs_le.mp a2
      linarith
    exact hfinal

/-! ### The logarithmic ratio bound -/

lemma log_ratio_bound {e y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/2) (he : |e| < 1) :
    |(Real.log (e^2 + (1-y)^2) - Real.log (e^2 + (y/2-y)^2))/2|
      ≤ (Real.log 4 + Real.log (17/16) + 3) * (1 + 1/y) := by
  have hea := (abs_lt.mp he).1
  have heb := (abs_lt.mp he).2
  have he2 : e^2 < 1 := by nlinarith
  have hsqy : (1-y)^2 ≤ 1 := by nlinarith
  set P : ℝ := e^2 + (1-y)^2 with hP
  set Q : ℝ := e^2 + (y/2-y)^2 with hQ
  have hPpos : 0 < P := by rw [hP]; nlinarith [sq_nonneg e, sq_nonneg (1-y)]
  have hPlow : (1:ℝ)/4 ≤ P := by rw [hP]; nlinarith [sq_nonneg e]
  have hPhigh : P ≤ 2 := by rw [hP]; linarith
  have hQpos : 0 < Q := by rw [hQ]; nlinarith [sq_nonneg e, sq_nonneg (y/2-y)]
  have hQhigh : Q ≤ 17/16 := by rw [hQ]; nlinarith [sq_nonneg e, hy1]
  have hQlow : y^2/4 ≤ Q := by rw [hQ]; nlinarith [sq_nonneg e]
  have hlogP : |Real.log P| ≤ Real.log 4 := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h3 : Real.log ((1:ℝ)/4) ≤ Real.log P := Real.log_le_log (by norm_num) hPlow
      rw [one_div, Real.log_inv] at h3
      linarith
    · have h3 : Real.log P ≤ Real.log 2 := Real.log_le_log hPpos hPhigh
      have h4 : Real.log (2:ℝ) ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
  have hlogQ : |Real.log Q| ≤ Real.log (17/16) + Real.log (4/y^2) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h3 : Real.log (y^2/4) ≤ Real.log Q := Real.log_le_log (by positivity) hQlow
      have h4 : Real.log (4/y^2) = - Real.log (y^2/4) := by
        have hsq : (4:ℝ)/y^2 = (y^2/4)⁻¹ := by field_simp
        rw [hsq, Real.log_inv]
      have h16 : 0 ≤ Real.log (17/16) := Real.log_nonneg (by norm_num)
      linarith
    · have h3 : Real.log Q ≤ Real.log (17/16) := Real.log_le_log hQpos hQhigh
      have h4 : 0 ≤ Real.log (4/y^2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hy1, hy]
      linarith
  have hmain : |Real.log P - Real.log Q| / 2 ≤ (Real.log 4 + Real.log (17/16) + 3) * (1 + 1/y) := by
    have h1 : |Real.log P - Real.log Q| ≤ Real.log 4 + (Real.log (17/16) + Real.log (4/y^2)) := by
      calc |Real.log P - Real.log Q| ≤ |Real.log P| + |Real.log Q| := abs_sub _ _
        _ ≤ Real.log 4 + (Real.log (17/16) + Real.log (4/y^2)) := add_le_add hlogP hlogQ
    have h2 : Real.log (4/y^2) ≤ 4 * (1 + 1/y) := by
      have hsq : (4:ℝ)/y^2 = (2/y)^2 := by field_simp; norm_num
      rw [hsq, Real.log_pow]
      have h3 : Real.log (2/y) ≤ 2/y := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2/y by positivity)
        linarith
      have h4 : (2:ℝ) * (2/y) ≤ 4 * (1 + 1/y) := by
        have hyne : y ≠ 0 := ne_of_gt hy
        field_simp
        nlinarith [hy.le]
      have h5 : (2:ℝ) * Real.log (2/y) ≤ 2 * (2/y) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlog16nn : 0 ≤ Real.log (17/16) := Real.log_nonneg (by norm_num)
    have hone : 1 ≤ 1 + 1/y := by
      have : (0:ℝ) ≤ 1/y := by positivity
      linarith
    have h9 : Real.log 4 ≤ Real.log 4 * (1+1/y) := le_mul_of_one_le_right hlog4nn hone
    have h10 : Real.log (17/16) ≤ Real.log (17/16) * (1+1/y) := le_mul_of_one_le_right hlog16nn hone
    have h8 : Real.log 4 + (Real.log (17/16) + Real.log (4/y^2))
        ≤ (Real.log 4 + Real.log (17/16) + 3) * (1 + 1/y) * 2 := by
      nlinarith [h2, h9, h10, hlog4nn, hlog16nn, hone]
    linarith [h1, h8]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact hmain


/-! ### The FTC for the signed weight -/

lemma integral_div_sq_eq_log {e y : ℝ} (he : e ≠ 0) :
    ∫ t in (y/2)..1, (t-y)/(e^2+(t-y)^2)
      = (Real.log (e^2+(1-y)^2) - Real.log (e^2+(y/2-y)^2))/2 := by
  have hderiv : ∀ t ∈ Set.uIcc (y/2) 1,
      HasDerivAt (fun s : ℝ => Real.log (e^2+(s-y)^2)/2) ((t-y)/(e^2+(t-y)^2)) t := by
    intro t ht
    have hD : e^2 + (t-y)^2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero he]
    have h1 : HasDerivAt (fun s : ℝ => e^2 + (s-y)^2) (2*(t-y)) t := by
      have hb : HasDerivAt (fun s : ℝ => s-y) 1 t := (hasDerivAt_id t).sub_const y
      have h0 : HasDerivAt (fun s : ℝ => (s-y)^2) (2*(t-y)^(2-1)*1) t := hb.pow 2
      have h2 : HasDerivAt (fun s : ℝ => e^2 + (s-y)^2) (2*(t-y)^(2-1)*1) t :=
        h0.const_add (e^2)
      simpa using h2
    have h3 : HasDerivAt (fun s : ℝ => Real.log (e^2+(s-y)^2))
        ((2*(t-y))/(e^2+(t-y)^2)) t := h1.log hD
    have h4 : HasDerivAt (fun s : ℝ => Real.log (e^2+(s-y)^2)/2)
        (((2*(t-y))/(e^2+(t-y)^2))/2) t := h3.div_const 2
    convert h4 using 1
    ring
  have hint : IntervalIntegrable (fun t : ℝ => (t-y)/(e^2+(t-y)^2)) volume (y/2) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    refine Continuous.div (by fun_prop) ?_ ?_
    · fun_prop
    · intro t; nlinarith [sq_pos_of_ne_zero he]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  ring

/-! ### The two model integrals -/

lemma norm_integral_modelA (j : ℕ) {e y a : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/2) (ha : 0 ≤ a)
    (he : e ≠ 0) :
    ‖∫ t in (y/2)..1, (((-e)/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))‖
      ≤ Real.pi * Real.exp (-(a*y/2)) := by
  have hy2 : y/2 ≤ 1 := by linarith
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hy2) ?_
  have hD : ∀ t : ℝ, e^2 + (t-y)^2 ≠ 0 := fun t => by nlinarith [sq_pos_of_ne_zero he]
  have hcongr : ∫ t in (y/2)..1,
        ‖((( -e)/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))‖
      = ∫ t in (y/2)..1, |e|/(e^2+(t-y)^2) * (t^j * Real.exp (-(a*t))) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hy2] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1, hy]
    have hDnn : 0 ≤ e^2 + (t-y)^2 := by positivity
    rw [norm_mul, norm_mul]
    have h1 : ‖((( -e)/(e^2+(t-y)^2) : ℝ) : ℂ)‖ = |e|/(e^2+(t-y)^2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hDnn]
    have h2 : ‖(t:ℂ)^j‖ = t^j := by
      rw [Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have h3 : ‖Complex.exp (-(a:ℂ)*(t:ℂ))‖ = Real.exp (-(a*t)) := by
      rw [Complex.norm_exp]
      have harg : (-(a:ℂ)*(t:ℂ)).re = -(a*t) := by
        rw [show -(a:ℂ)*(t:ℂ) = ((-(a*t):ℝ):ℂ) by push_cast; ring, Complex.ofReal_re]
      rw [harg]
    rw [h1, h2, h3]
    ring
  rw [hcongr]
  have hstep : ∫ t in (y/2)..1, |e|/(e^2+(t-y)^2) * (t^j * Real.exp (-(a*t)))
      ≤ ∫ t in (y/2)..1, Real.exp (-(a*y/2)) * (|e|/(e^2+(t-y)^2)) := by
    refine intervalIntegral.integral_mono_on hy2 ?_ ?_ (fun t ht => ?_)
    · refine Continuous.intervalIntegrable ?_ _ _
      refine Continuous.mul (Continuous.div continuous_const (by fun_prop) (fun t => hD t)) ?_
      exact (continuous_id.pow j).mul (Real.continuous_exp.comp (by fun_prop))
    · refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul (Continuous.div continuous_const (by fun_prop) (fun t => hD t))
    · have ht0 : 0 ≤ t := by linarith [ht.1, hy]
      have ht1 : t ≤ 1 := ht.2
      have htj : t^j ≤ 1 := pow_le_one₀ ht0 ht1
      have hexp : Real.exp (-(a*t)) ≤ Real.exp (-(a*y/2)) := by
        apply Real.exp_le_exp.mpr; nlinarith [ht.1, ha]
      calc |e|/(e^2+(t-y)^2) * (t^j * Real.exp (-(a*t)))
          ≤ |e|/(e^2+(t-y)^2) * (1 * Real.exp (-(a*y/2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul htj hexp (Real.exp_pos _).le (by norm_num)
        _ = Real.exp (-(a*y/2)) * (|e|/(e^2+(t-y)^2)) := by ring
  calc ∫ t in (y/2)..1, |e|/(e^2+(t-y)^2) * (t^j * Real.exp (-(a*t)))
      ≤ ∫ t in (y/2)..1, Real.exp (-(a*y/2)) * (|e|/(e^2+(t-y)^2)) := hstep
    _ = Real.exp (-(a*y/2)) * ∫ t in (y/2)..1, |e|/(e^2+(t-y)^2) := by
          rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (-(a*y/2)) * Real.pi :=
          mul_le_mul_of_nonneg_left (integral_abs_div_sq_le_pi hy) (Real.exp_pos _).le
    _ = Real.pi * Real.exp (-(a*y/2)) := by ring

lemma norm_integral_modelB (j : ℕ) {e y a : ℝ} (hy : 0 < y) (hy1 : y ≤ 1/2) (ha : 0 ≤ a)
    (he : e ≠ 0) :
    ‖∫ t in (y/2)..1, (((-(t-y))/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))‖
      ≤ Real.exp (-(a*y/2)) * (1 + y^j * |(Real.log (e^2+(1-y)^2) - Real.log (e^2+(y/2-y)^2))/2|)
        * ((j:ℝ)+a+1) := by
  have hy2 : y/2 ≤ 1 := by linarith
  have hD : ∀ t : ℝ, e^2 + (t-y)^2 ≠ 0 := fun t => by nlinarith [sq_pos_of_ne_zero he]
  set W : ℝ → ℝ := fun t => (-(t-y))/(e^2+(t-y)^2) with hW
  set f : ℝ → ℂ := fun t => (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ)) with hf
  set fy : ℂ := (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)) with hfy
  have hWcont : Continuous W := by
    rw [hW]
    refine Continuous.div ?_ ?_ (fun t => hD t)
    · fun_prop
    · fun_prop
  have hfcont : Continuous f := by
    rw [hf]; fun_prop
  have hcont1 : Continuous fun t : ℝ => (((W t:ℝ):ℂ) * fy) :=
    (Complex.continuous_ofReal.comp hWcont).mul continuous_const
  have hcont2 : Continuous fun t : ℝ => (((W t:ℝ):ℂ) * (f t - fy)) :=
    (Complex.continuous_ofReal.comp hWcont).mul (hfcont.sub continuous_const)
  have hWint : ∫ t in (y/2)..1, W t
      = -(Real.log (e^2+(1-y)^2) - Real.log (e^2+(y/2-y)^2))/2 := by
    have h1 : (fun t : ℝ => W t) = fun t => (-(t-y))/(e^2+(t-y)^2) := rfl
    rw [h1, show (fun t : ℝ => (-(t-y))/(e^2+(t-y)^2))
        = fun t => -((t-y)/(e^2+(t-y)^2)) by funext t; ring,
      intervalIntegral.integral_neg, integral_div_sq_eq_log he]
    ring
  have hfy_norm : ‖fy‖ = y^j * Real.exp (-(a*y)) := by
    rw [hfy, norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hy), Complex.norm_exp]
    congr 1
    rw [show (-(a:ℂ)*(y:ℂ)) = ((-(a*y):ℝ):ℂ) by push_cast; ring, Complex.ofReal_re]
  -- split the integral
  have hcongr : ∫ t in (y/2)..1, (((-(t-y))/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j
        * Complex.exp (-(a:ℂ)*(t:ℂ))
      = ∫ t in (y/2)..1, (((W t:ℝ):ℂ) * f t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [hW, hf]; ring
  rw [hcongr]
  have hdecomp : ∫ t in (y/2)..1, (((W t:ℝ):ℂ) * f t)
      = (∫ t in (y/2)..1, (((W t:ℝ):ℂ) * fy)) + ∫ t in (y/2)..1, (((W t:ℝ):ℂ) * (f t - fy)) := by
    rw [← intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    ring
  rw [hdecomp]
  have hfirst : ∫ t in (y/2)..1, (((W t:ℝ):ℂ) * fy) = ((∫ t in (y/2)..1, W t : ℝ) : ℂ) * fy := by
    rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const]
  rw [hfirst]
  -- bound the two pieces
  have hb1 : ‖(((∫ t in (y/2)..1, W t : ℝ) : ℂ) * fy)‖
      ≤ Real.exp (-(a*y)) * (y^j * |(Real.log (e^2+(1-y)^2) - Real.log (e^2+(y/2-y)^2))/2|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hfy_norm, hWint, neg_div, abs_neg]
    exact le_of_eq (by ring_nf)
  have hle2 : ∀ t ∈ Set.Icc (y/2) 1, ‖(((W t:ℝ):ℂ) * (f t - fy))‖
      ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) := by
    intro t ht
    have hDnn : 0 ≤ e^2 + (t-y)^2 := by positivity
    have hWv : ‖(((W t:ℝ):ℂ))‖ = |t-y|/(e^2+(t-y)^2) := by
      rw [hW, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg hDnn]
    have hfv : f t - fy = (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))
        - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)) := by rw [hf, hfy]
    rw [norm_mul, hWv, hfv]
    have hdiff := norm_pow_mul_exp_sub_le_weighted j ha hy hy1 t ht
    calc |t-y|/(e^2+(t-y)^2) * ‖(t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))
            - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ))‖
        ≤ |t-y|/(e^2+(t-y)^2) * (((j:ℝ)+a) * Real.exp (-(a*y/2)) * |t-y|) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = ((j:ℝ)+a) * Real.exp (-(a*y/2)) * (|t-y|^2/(e^2+(t-y)^2)) := by ring
      _ ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]
          nlinarith [sq_nonneg e, sq_abs (t-y)]
      _ = ((j:ℝ)+a) * Real.exp (-(a*y/2)) := by ring
  have hb2 : ‖∫ t in (y/2)..1, (((W t:ℝ):ℂ) * (f t - fy))‖
      ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hy2) ?_
    have hc : ∫ t in (y/2)..1, ‖(((W t:ℝ):ℂ) * (f t - fy))‖
        ≤ ∫ t in (y/2)..1, (((j:ℝ)+a) * Real.exp (-(a*y/2))) := by
      refine intervalIntegral.integral_mono_on hy2 ?_ ?_ hle2
      · refine Continuous.intervalIntegrable ?_ _ _
        exact hcont2.norm
      · exact continuous_const.intervalIntegrable _ _
    have hcpos : (0:ℝ) ≤ (j:ℝ)+a := by positivity
    have hee : (0:ℝ) < Real.exp (-(a*y/2)) := Real.exp_pos _
    have hy2' : (0:ℝ) ≤ 1 - y/2 := by linarith
    have hy2'' : (1:ℝ) - y/2 ≤ 1 := by linarith
    refine le_trans hc ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hcc : (0:ℝ) ≤ ((j:ℝ)+a) * Real.exp (-(a*y/2)) := mul_nonneg hcpos hee.le
    calc (1 - y/2) * (((j:ℝ)+a) * Real.exp (-(a*y/2)))
        ≤ 1 * (((j:ℝ)+a) * Real.exp (-(a*y/2))) := mul_le_mul_of_nonneg_right hy2'' hcc
      _ = ((j:ℝ)+a) * Real.exp (-(a*y/2)) := by ring
  set Lv : ℝ := (Real.log (e^2+(1-y)^2) - Real.log (e^2+(y/2-y)^2))/2 with hLv
  have hLvnn : 0 ≤ y^j * |Lv| := by positivity
  have hjnn : (0:ℝ) ≤ (j:ℝ)+a := by positivity
  calc ‖(((∫ t in (y/2)..1, W t : ℝ) : ℂ) * fy)
        + (∫ t in (y/2)..1, (((W t:ℝ):ℂ) * (f t - fy)))‖
      ≤ ‖(((∫ t in (y/2)..1, W t : ℝ) : ℂ) * fy)‖
        + ‖∫ t in (y/2)..1, (((W t:ℝ):ℂ) * (f t - fy))‖ := norm_add_le _ _
    _ ≤ Real.exp (-(a*y)) * (y^j * |Lv|) + ((j:ℝ)+a) * Real.exp (-(a*y/2)) :=
        add_le_add hb1 hb2
    _ ≤ Real.exp (-(a*y/2)) * (1 + y^j * |Lv|) * ((j:ℝ)+a+1) := by
        have h1 : Real.exp (-(a*y)) ≤ Real.exp (-(a*y/2)) :=
          Real.exp_le_exp.mpr (by nlinarith [hy, ha])
        have he : (0:ℝ) < Real.exp (-(a*y/2)) := Real.exp_pos _
        have hstep : Real.exp (-(a*y)) * (y^j * |Lv|) ≤ Real.exp (-(a*y/2)) * (y^j * |Lv|) :=
          mul_le_mul_of_nonneg_right h1 hLvnn
        have h5 : (0:ℝ) ≤ 1 + y^j * |Lv| := by linarith
        have h6 : (y^j * |Lv|) + ((j:ℝ)+a)
            ≤ (1 + y^j * |Lv|) * ((j:ℝ)+a+1) := by nlinarith [hLvnn, hjnn]
        calc Real.exp (-(a*y)) * (y^j * |Lv|) + ((j:ℝ)+a) * Real.exp (-(a*y/2))
            ≤ Real.exp (-(a*y/2)) * (y^j * |Lv|) + ((j:ℝ)+a) * Real.exp (-(a*y/2)) := by
              linarith [hstep]
          _ = Real.exp (-(a*y/2)) * ((y^j * |Lv|) + ((j:ℝ)+a)) := by ring
          _ ≤ Real.exp (-(a*y/2)) * ((1 + y^j * |Lv|) * ((j:ℝ)+a+1)) :=
              mul_le_mul_of_nonneg_left h6 he.le
          _ = Real.exp (-(a*y/2)) * (1 + y^j * |Lv|) * ((j:ℝ)+a+1) := by ring


/-! ## The main theorem -/



/-- A function with a non-removable simple pole at an interior point `t₀` of `(a,b)` is not
integrable on `Ioc a b`. -/
lemma not_integrableOn_Ioc_of_simplePole {f g : ℝ → ℂ} {t₀ a b : ℝ}
    (ha : a < t₀) (hb : t₀ < b) {c : ℂ} (hc : c ≠ 0)
    (hg : ∃ M : ℝ, ∀ᶠ t in nhds t₀, ‖g t‖ ≤ M)
    (hf : ∀ᶠ t in nhds t₀, f t = c / ((t : ℂ) - t₀) + g t) :
    ¬ IntegrableOn f (Set.Ioc a b) := by
  intro hfint
  set δ : ℝ := min (t₀ - a) (b - t₀) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hsub : Set.uIoc (t₀ - δ) (t₀ + δ) ⊆ Set.Ioc a b := by
    rw [uIoc_of_le (by linarith)]
    intro x hx
    simp only [Set.mem_Ioc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2, min_le_left (t₀ - a) (b - t₀),
      min_le_right (t₀ - a) (b - t₀)]
  have hii : IntervalIntegrable f volume (t₀ - δ) (t₀ + δ) := by
    rw [intervalIntegrable_iff]
    exact hfint.mono_set hsub
  have hbigO : (fun x : ℝ => (x - t₀)⁻¹) =O[𝓝[≠] t₀] f := by
    obtain ⟨M, hMe⟩ := hg
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 / ‖c‖, ?_⟩
    have hcomb : ∀ᶠ t in 𝓝 t₀, ‖g t‖ ≤ M ∧ f t = c / ((t : ℂ) - t₀) + g t := hMe.and hf
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hcomb
    have hnormc : 0 < ‖c‖ := norm_pos_iff.mpr hc
    set N : ℝ := |M| + 1 with hNdef
    have hNpos : 0 < N := by positivity
    have hMN : M ≤ N := by have := le_abs_self M; linarith
    have hsub_norm : ∀ x : ℝ, ‖(x : ℂ) - (t₀ : ℂ)‖ = |x - t₀| := by
      intro x
      rw [← Complex.ofReal_sub, ← Real.sqrt_sq (norm_nonneg (((x - t₀ : ℝ) : ℂ))),
        ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
    have hηpos : 0 < min ε (‖c‖ / (2 * N)) :=
      lt_min hεpos (div_pos hnormc (by linarith))
    have hηleε : min ε (‖c‖ / (2 * N)) ≤ ε := min_le_left _ _
    have hηle : min ε (‖c‖ / (2 * N)) ≤ ‖c‖ / (2 * N) := min_le_right _ _
    have hball : ∀ᶠ x in 𝓝[≠] t₀, x ∈ Metric.ball t₀ (min ε (‖c‖ / (2 * N))) :=
      (show ∀ᶠ x in 𝓝 t₀, x ∈ Metric.ball t₀ (min ε (‖c‖ / (2 * N))) from
        Metric.ball_mem_nhds t₀ hηpos).filter_mono nhdsWithin_le_nhds
    filter_upwards [hball, self_mem_nhdsWithin] with x hxball hxne
    have hxne' : x ≠ t₀ := hxne
    have hxd : dist x t₀ < min ε (‖c‖ / (2 * N)) := hxball
    have hxε : x ∈ Metric.ball t₀ ε := Metric.ball_subset_ball hηleε hxball
    obtain ⟨hgx, hfx⟩ := hε hxε
    have habs : 0 < |x - t₀| := abs_pos.mpr (sub_ne_zero.mpr hxne')
    have hlow : ‖c‖ / |x - t₀| - M ≤ ‖f x‖ := by
      have hn : ‖c / ((x : ℂ) - (t₀ : ℂ))‖ = ‖c‖ / |x - t₀| := by
        rw [norm_div, hsub_norm x]
      calc ‖c‖ / |x - t₀| - M
          = ‖c / ((x : ℂ) - (t₀ : ℂ))‖ - M := by rw [hn]
        _ ≤ ‖c / ((x : ℂ) - (t₀ : ℂ))‖ - ‖g x‖ := by linarith
        _ ≤ ‖c / ((x : ℂ) - (t₀ : ℂ)) + g x‖ := by
              simpa using norm_sub_norm_le (c / ((x : ℂ) - (t₀ : ℂ))) (-(g x))
        _ = ‖f x‖ := by rw [← hfx]
    have hmiddle : ‖c‖ / (2 * |x - t₀|) ≤ ‖c‖ / |x - t₀| - M := by
      have hdist : |x - t₀| < ‖c‖ / (2 * N) :=
        lt_of_lt_of_le (by rw [← Real.dist_eq]; exact hxd) hηle
      have hpos2 : (0:ℝ) < 2 * |x - t₀| := by positivity
      have hpos3 : (0:ℝ) < 2 * N := by linarith
      have h3 : 2 * N * |x - t₀| < ‖c‖ := by
        have := (lt_div_iff₀ hpos3).mp hdist
        nlinarith [this]
      have h4 : N < ‖c‖ / (2 * |x - t₀|) := by
        rw [lt_div_iff₀ hpos2]
        nlinarith [h3]
      have h2 : M ≤ ‖c‖ / (2 * |x - t₀|) := by linarith
      have hid : ‖c‖ / |x - t₀| = 2 * (‖c‖ / (2 * |x - t₀|)) := by field_simp
      linarith [hid, h2]
    have hkey : ‖c‖ / (2 * |x - t₀|) ≤ ‖f x‖ := le_trans hmiddle hlow
    have hgoal : |x - t₀|⁻¹ ≤ (2 / ‖c‖) * ‖f x‖ := by
      have heq : (2 / ‖c‖) * (‖c‖ / (2 * |x - t₀|)) = |x - t₀|⁻¹ := by field_simp
      calc |x - t₀|⁻¹ = (2 / ‖c‖) * (‖c‖ / (2 * |x - t₀|)) := heq.symm
        _ ≤ (2 / ‖c‖) * ‖f x‖ := mul_le_mul_of_nonneg_left hkey (by positivity)
    rw [Real.norm_eq_abs, abs_inv]
    exact hgoal
  have hne : t₀ - δ ≠ t₀ + δ := by intro h; linarith [hδpos]
  have hmem : t₀ ∈ uIcc (t₀ - δ) (t₀ + δ) := by
    rw [Set.mem_uIcc]; left; exact ⟨by linarith [hδpos], by linarith [hδpos]⟩
  exact not_intervalIntegrable_of_sub_inv_isBigO_punctured hbigO hne hmem hii


theorem tile_pole_integral_decay (j J : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon →
      ∀ a : ℝ, 0 ≤ a →
        ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ j
            * Complex.exp (-(a : ℂ) * (t : ℂ))‖
          ≤ C * (Work.Kernels.scale w) ^ N * ((1 + a * w.im)⁻¹) ^ J := by
  obtain ⟨C1, hC1nn, hC1⟩ := exp_neg_half_mul_pow_bdd J
  obtain ⟨C3, hC3nn, hC3⟩ := exp_neg_half_mul_mul_pow_bdd J
  set CL : ℝ := Real.log 4 + Real.log (17/16) + 3 with hCL
  have hCLnn : 0 ≤ CL := by
    rw [hCL]
    have h1 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (17/16) := Real.log_nonneg (by norm_num)
    linarith
  refine ⟨Real.pi * C1 + (1 + 2 * CL) * (((j:ℝ) + 1) * C1 + C3), 2, by positivity, by norm_num, ?_⟩
  intro w hw a ha
  set y : ℝ := w.im with hy
  set e : ℝ := w.re with he
  set Lval : ℝ := (Real.log (e^2 + (1-y)^2) - Real.log (e^2 + (y/2-y)^2))/2 with hLval
  have hypos : 0 < y := w.im_pos
  have hyhalf : y ≤ 1/2 := tile_im_le_half hw
  have heabs : |e| < 1 := by
    have h := (mem_DomainD.mp hw.1)
    rw [abs_lt]
    exact ⟨by rw [he]; exact h.1, by rw [he]; exact h.2.1⟩
  have hscale : (1:ℝ) + 1/y ≤ Work.Kernels.scale w := by
    rw [one_div, Work.Kernels.scale, ← hy]
    have h1 : (0:ℝ) ≤ (w.im)⁻¹ := inv_nonneg.mpr w.im_pos.le
    have h2 : (0:ℝ) ≤ ‖(w:ℂ)‖ := norm_nonneg _
    linarith
  have hxy : (0:ℝ) ≤ a * y := mul_nonneg ha hypos.le
  have h1y : (1:ℝ) ≤ 1 + 1/y := by
    have : (0:ℝ) ≤ 1/y := by positivity
    linarith
  have hC1' : Real.exp (-(a*y/2)) ≤ C1 * ((1 + a*y)⁻¹)^J := by
    have h := hC1 (a*y) hxy
    rw [show -(a*y)/2 = -(a*y/2) by ring] at h
    have hpow : (0:ℝ) < (1 + a*y)^J := by positivity
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow]
    exact h
  have hC3' : a * Real.exp (-(a*y/2)) ≤ C3 * (1/y) * ((1 + a*y)⁻¹)^J := by
    have h := hC3 (a*y) hxy
    rw [show -(a*y)/2 = -(a*y/2) by ring] at h
    have hpow : (0:ℝ) < (1 + a*y)^J := by positivity
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have h2 : a * Real.exp (-(a*y/2)) * (1+a*y)^J
        = (a*y * Real.exp (-(a*y/2)) * (1+a*y)^J) / y := by
      field_simp
    rw [h2]
    calc (a*y * Real.exp (-(a*y/2)) * (1+a*y)^J) / y ≤ C3 / y :=
          div_le_div_of_nonneg_right h hypos.le
      _ = C3 * (1/y) := by ring
  have hLv : y^j * |Lval| ≤ 2 * CL * (1 + 1/y) := by
    have h := log_ratio_bound hypos hyhalf heabs
    rw [← hLval, ← hCL] at h
    have h1 : y^j * (1 + 1/y) ≤ 2 * (1 + 1/y) := by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp only [pow_zero, one_mul]; linarith [h1y]
      · have hy1 : y ≤ 1 := by linarith
        have hyj : y^j ≤ 1 := pow_le_one₀ hypos.le hy1
        have hyj1 : y^(j-1) ≤ 1 := pow_le_one₀ hypos.le hy1
        have hyne : y ≠ 0 := ne_of_gt hypos
        have hyinv : y * (1/y) = 1 := by field_simp
        have hjj : y^j * (1/y) = y^(j-1) := by
          have hj1 : j = (j-1) + 1 := by omega
          conv_lhs => rw [hj1, pow_succ]
          rw [mul_assoc, hyinv, mul_one]
        rw [show y^j * (1 + 1/y) = y^j + y^j * (1/y) by ring, hjj]
        linarith [hyj, hyj1, h1y]
    calc y^j * |Lval| ≤ y^j * (CL * (1 + 1/y)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = CL * (y^j * (1 + 1/y)) := by ring
      _ ≤ CL * (2 * (1 + 1/y)) := mul_le_mul_of_nonneg_left h1 hCLnn
      _ = 2 * CL * (1 + 1/y) := by ring
  have hQnn : (0:ℝ) ≤ ((1 + a*y)⁻¹)^J := by positivity
  have hHnn : (0:ℝ) ≤ 1 + 2*CL := by linarith
  have hKnn : (0:ℝ) ≤ (((j:ℝ)+1)*C1 + C3) := by positivity
  have harith : Real.pi * Real.exp (-(a*y/2))
        + Real.exp (-(a*y/2)) * (1 + y^j * |Lval|) * ((j:ℝ)+a+1)
      ≤ (Real.pi * C1 + (1 + 2 * CL) * (((j:ℝ) + 1) * C1 + C3))
        * (Work.Kernels.scale w)^2 * ((1 + a * y)⁻¹)^J := by
    have hterm : Real.exp (-(a*y/2)) * (1 + y^j * |Lval|) * ((j:ℝ)+a+1)
        ≤ (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3) * ((1 + a*y)⁻¹)^J := by
      have hkey : Real.exp (-(a*y/2)) * ((j:ℝ)+a+1)
          ≤ (((j:ℝ)+1)*C1 + C3*(1/y)) * ((1+a*y)⁻¹)^J := by
        have hsplit : Real.exp (-(a*y/2)) * ((j:ℝ)+a+1)
            = ((j:ℝ)+1) * Real.exp (-(a*y/2)) + a * Real.exp (-(a*y/2)) := by ring
        rw [hsplit]
        calc ((j:ℝ)+1) * Real.exp (-(a*y/2)) + a * Real.exp (-(a*y/2))
            ≤ ((j:ℝ)+1) * (C1 * ((1+a*y)⁻¹)^J) + C3 * (1/y) * ((1+a*y)⁻¹)^J :=
              add_le_add (mul_le_mul_of_nonneg_left hC1' (by positivity)) hC3'
          _ = (((j:ℝ)+1)*C1 + C3*(1/y)) * ((1+a*y)⁻¹)^J := by ring
      have hfac : (1 + y^j * |Lval|) ≤ (1 + 2*CL) * (1 + 1/y) := by linarith [hLv, h1y, hCLnn]
      have hRnn : (0:ℝ) ≤ (1 + 2*CL) * (1 + 1/y) := mul_nonneg hHnn (by linarith)
      have hstep : (1 + y^j * |Lval|) * (Real.exp (-(a*y/2)) * ((j:ℝ)+a+1))
          ≤ ((1 + 2*CL) * (1 + 1/y)) * ((((j:ℝ)+1)*C1 + C3*(1/y)) * ((1+a*y)⁻¹)^J) :=
            mul_le_mul hfac hkey (mul_nonneg (Real.exp_pos _).le (by positivity)) hRnn
      have h10 : (((j:ℝ)+1)*C1 + C3*(1/y)) ≤ (1 + 1/y) * ((((j:ℝ)+1)*C1) + C3) := by
        have hA : ((j:ℝ)+1)*C1 ≤ (1+1/y) * (((j:ℝ)+1)*C1) := by
          rw [mul_comm (1+1/y) (((j:ℝ)+1)*C1)]
          exact le_mul_of_one_le_right (by positivity) h1y
        have hB : C3 * (1/y) ≤ (1+1/y) * C3 := by
          have hh : (1+1/y) * C3 = C3 + (1/y)*C3 := by ring
          rw [hh]; nlinarith [hC3nn]
        nlinarith [hA, hB]
      have h11 : (1 + 1/y) * ((((j:ℝ)+1)*C1 + C3*(1/y)))
          ≤ (1 + 1/y)^2 * ((((j:ℝ)+1)*C1) + C3) := by
        have := mul_le_mul_of_nonneg_left h10 (show (0:ℝ) ≤ 1+1/y by linarith)
        calc (1 + 1/y) * ((((j:ℝ)+1)*C1 + C3*(1/y)))
            ≤ (1 + 1/y) * ((1 + 1/y) * ((((j:ℝ)+1)*C1) + C3)) := this
          _ = (1 + 1/y)^2 * ((((j:ℝ)+1)*C1) + C3) := by ring
      calc Real.exp (-(a*y/2)) * (1 + y^j * |Lval|) * ((j:ℝ)+a+1)
          = (1 + y^j * |Lval|) * (Real.exp (-(a*y/2)) * ((j:ℝ)+a+1)) := by ring
        _ ≤ ((1 + 2*CL) * (1 + 1/y)) * ((((j:ℝ)+1)*C1 + C3*(1/y)) * ((1+a*y)⁻¹)^J) := hstep
        _ = (1 + 2*CL) * ((1 + 1/y) * ((((j:ℝ)+1)*C1 + C3*(1/y))) * ((1+a*y)⁻¹)^J) := by ring
        _ ≤ (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3) * ((1 + a*y)⁻¹)^J := by
              calc (1 + 2*CL) * ((1 + 1/y) * ((((j:ℝ)+1)*C1 + C3*(1/y))) * ((1+a*y)⁻¹)^J)
                  = (1 + 2*CL) * ((1 + 1/y) * ((((j:ℝ)+1)*C1 + C3*(1/y)))) * ((1+a*y)⁻¹)^J := by ring
                _ ≤ (1 + 2*CL) * ((1 + 1/y)^2 * ((((j:ℝ)+1)*C1) + C3)) * ((1+a*y)⁻¹)^J :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h11 hHnn) hQnn
                _ = (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3) * ((1 + a*y)⁻¹)^J := by ring
    have hfirst : Real.pi * Real.exp (-(a*y/2)) ≤ Real.pi * C1 * ((1 + a*y)⁻¹)^J := by
      have := mul_le_mul_of_nonneg_left hC1' Real.pi_pos.le
      linarith [this]
    have hb1 : Real.pi * C1 * ((1 + a*y)⁻¹)^J
        ≤ Real.pi * C1 * (1+1/y)^2 * ((1 + a*y)⁻¹)^J := by
      have h2 : (1:ℝ) ≤ (1+1/y)^2 := one_le_pow₀ h1y (n := 2)
      have h3 : Real.pi * C1 ≤ Real.pi * C1 * (1+1/y)^2 :=
        le_mul_of_one_le_right (by positivity) h2
      exact mul_le_mul_of_nonneg_right h3 hQnn
    have hpos1 : (0:ℝ) ≤ Real.pi * C1 := by positivity
    have hscale1 : (1:ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hcomp : (1+1/y)^2 ≤ (Work.Kernels.scale w)^2 := pow_le_pow_left₀ (by linarith) hscale 2
    have hH2 : (0:ℝ) ≤ (1 + 2*CL) * (((j:ℝ)+1)*C1 + C3) := mul_nonneg hHnn hKnn
    calc Real.pi * Real.exp (-(a*y/2))
          + Real.exp (-(a*y/2)) * (1 + y^j * |Lval|) * ((j:ℝ)+a+1)
        ≤ Real.pi * C1 * ((1 + a*y)⁻¹)^J
          + (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3) * ((1 + a*y)⁻¹)^J :=
            add_le_add hfirst hterm
      _ ≤ (Real.pi * C1 * (1+1/y)^2 * ((1 + a*y)⁻¹)^J)
          + (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3) * ((1 + a*y)⁻¹)^J :=
            add_le_add hb1 le_rfl
      _ = ((Real.pi * C1) * (1+1/y)^2 + (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3)) * ((1 + a*y)⁻¹)^J := by ring
      _ ≤ ((Real.pi * C1) * (Work.Kernels.scale w)^2 + (1 + 2*CL) * (Work.Kernels.scale w)^2 * (((j:ℝ)+1)*C1 + C3)) * ((1 + a*y)⁻¹)^J := by
            have h5 : (Real.pi * C1) * (1+1/y)^2 ≤ (Real.pi * C1) * (Work.Kernels.scale w)^2 :=
              mul_le_mul_of_nonneg_left hcomp hpos1
            have h6 : (1 + 2*CL) * (1 + 1/y)^2 * (((j:ℝ)+1)*C1 + C3)
                ≤ (1 + 2*CL) * (Work.Kernels.scale w)^2 * (((j:ℝ)+1)*C1 + C3) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp hHnn) hKnn
            exact mul_le_mul_of_nonneg_right (add_le_add h5 h6) hQnn
      _ = (Real.pi * C1 + (1 + 2 * CL) * (((j:ℝ) + 1) * C1 + C3))
            * (Work.Kernels.scale w)^2 * ((1 + a * y)⁻¹)^J := by ring
  rcases eq_or_ne e 0 with he0 | hene
  · have hwcoe : (w:ℂ) = (y:ℂ) * Complex.I := by
      have h := Complex.re_add_im (w:ℂ)
      rw [show (w:ℂ).re = w.re from rfl, show (w:ℂ).im = w.im from rfl, hy.symm, he.symm] at h
      rw [he0] at h
      simpa using h.symm
    set c : ℂ := (1/Complex.I) * (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
      · exact div_ne_zero one_ne_zero Complex.I_ne_zero
      · exact pow_ne_zero _ (by exact_mod_cast ne_of_gt hypos)
    have hgbdd : ∃ M : ℝ, ∀ᶠ t : ℝ in nhds y, ‖(1/Complex.I) * (((t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))
        - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)))/((t:ℂ)-(y:ℂ)))‖ ≤ M := by
      refine ⟨(j:ℝ)+a, ?_⟩
      have hball : ∀ᶠ t in nhds y, t ∈ Metric.ball y (y/2) :=
        Metric.ball_mem_nhds y (by linarith)
      filter_upwards [hball] with t ht
      have htd : |t - y| < y/2 := by rw [← Real.dist_eq]; exact ht
      have htmem : t ∈ Set.Icc (y/2) 1 := by
        constructor <;> [linarith [abs_lt.mp htd]; linarith [abs_lt.mp htd, hyhalf]]
      have hdiv : ‖(((t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ)) - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)))
          / ((t:ℂ)-(y:ℂ)))‖ ≤ (j:ℝ)+a := by
        rw [norm_div]
        have hz : ‖(t:ℂ)-(y:ℂ)‖ = |t-y| := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [hz]
        rcases eq_or_ne (t-y) 0 with h | h
        · rw [h, abs_zero, div_zero]; positivity
        · have habs : 0 < |t-y| := abs_pos.mpr h
          rw [div_le_iff₀ habs]
          have hmvt := norm_pow_mul_exp_sub_le j ha hypos hyhalf t htmem
          convert hmvt using 2
      rw [norm_mul]
      have h1 : ‖(1:ℂ)/Complex.I‖ = 1 := by rw [norm_div, norm_one, Complex.norm_I, div_one]
      rw [h1, one_mul]
      exact hdiv
    have hf : ∀ᶠ t : ℝ in nhds y,
        (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ j * Complex.exp (-(a : ℂ) * (t : ℂ))
          = c / ((t : ℂ) - (y:ℂ)) + (1/Complex.I) * (((t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))
              - (y:ℂ)^j * Complex.exp (-(a:ℂ)*(y:ℂ)))/((t:ℂ)-(y:ℂ))) := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      rw [hwcoe, hc]
      have h1 : (t:ℂ)*Complex.I - (y:ℂ)*Complex.I = ((t:ℂ)-(y:ℂ))*Complex.I := by ring
      rw [h1]
      have h2 : (1:ℂ)/(((t:ℂ)-(y:ℂ))*Complex.I)
          = (1/Complex.I) * (1/((t:ℂ)-(y:ℂ))) := by field_simp
      rw [h2]
      rcases eq_or_ne ((t:ℂ)-(y:ℂ)) 0 with h3 | h3
      · rw [h3]; simp
      · field_simp
        ring
    have hnotint : ¬ IntegrableOn (fun t : ℝ => (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ))
        * (t : ℂ) ^ j * Complex.exp (-(a : ℂ) * (t : ℂ))) (Set.Ioc (y/2) 1) :=
      not_integrableOn_Ioc_of_simplePole (a := y/2) (b := 1) (t₀ := y)
        (by linarith) (by linarith) hcne hgbdd hf
    have hzero : ∫ t in (y/2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ j
        * Complex.exp (-(a : ℂ) * (t : ℂ)) = 0 := by
      rw [intervalIntegral.integral_undef]
      rw [intervalIntegrable_iff, uIoc_of_le (by linarith : y/2 ≤ 1)]
      exact hnotint
    rw [hzero]
    simp only [norm_zero]
    refine le_trans ?_ (le_trans harith ?_)
    · positivity
    · rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  · have hwcoe : (w:ℂ) = (e:ℂ) + (y:ℂ)*Complex.I := by
      have h := Complex.re_add_im (w:ℂ)
      rw [show (w:ℂ).re = w.re from rfl, show (w:ℂ).im = w.im from rfl, hy.symm, he.symm] at h
      exact h.symm
    set A : ℝ → ℂ := fun t => (((-e)/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j
      * Complex.exp (-(a:ℂ)*(t:ℂ)) with hA
    set B : ℝ → ℂ := fun t => (((-(t-y))/(e^2+(t-y)^2) : ℝ) : ℂ) * (t:ℂ)^j
      * Complex.exp (-(a:ℂ)*(t:ℂ)) with hB
    have hDne : ∀ t : ℝ, e^2 + (t-y)^2 ≠ 0 := fun t => by nlinarith [sq_pos_of_ne_zero hene]
    have hsplit : ∀ t : ℝ, (1 : ℂ) / ((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^j * Complex.exp (-(a:ℂ)*(t:ℂ))
        = A t + Complex.I * B t := by
      intro t
      rw [hA, hB]
      have harg : (t:ℂ)*Complex.I - (w:ℂ)
          = (((-e : ℝ)) : ℂ) + (((t-y : ℝ)) : ℂ)*Complex.I := by
        rw [hwcoe]; push_cast; ring
      rw [harg, inv_add_mul_I (-e) (t-y)]
      have hsq : ((-e:ℝ)^2 + (t-y)^2 : ℝ) = e^2 + (t-y)^2 := by ring
      rw [hsq]
      push_cast
      ring
    have hAcont : Continuous A := by rw [hA]; fun_prop
    have hBcont : Continuous B := by rw [hB]; fun_prop
    have hAint : IntervalIntegrable A volume (y/2) 1 := hAcont.intervalIntegrable _ _
    have hBint : IntervalIntegrable B volume (y/2) 1 := hBcont.intervalIntegrable _ _
    have hId : (∫ t in (y/2)..1, (1 : ℂ) / ((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^j
          * Complex.exp (-(a:ℂ)*(t:ℂ)))
        = (∫ t in (y/2)..1, A t) + Complex.I * (∫ t in (y/2)..1, B t) := by
      have hF : (fun t : ℝ => (1 : ℂ) / ((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^j
          * Complex.exp (-(a:ℂ)*(t:ℂ))) = fun t => A t + Complex.I * B t := by
        funext t; exact hsplit t
      rw [hF, intervalIntegral.integral_add hAint (hBint.const_mul Complex.I),
        intervalIntegral.integral_const_mul]
    have hbound : ‖∫ t in (y/2)..1, (1 : ℂ) / ((t:ℂ)*Complex.I - (w:ℂ)) * (t:ℂ)^j
          * Complex.exp (-(a:ℂ)*(t:ℂ))‖
        ≤ Real.pi * Real.exp (-(a*y/2))
          + Real.exp (-(a*y/2)) * (1 + y^j * |Lval|) * ((j:ℝ)+a+1) := by
      rw [hId]
      refine le_trans (norm_add_le (∫ t in (y/2)..1, A t)
        (Complex.I * (∫ t in (y/2)..1, B t))) ?_
      rw [norm_mul, Complex.norm_I, one_mul]
      refine add_le_add ?_ ?_
      · simpa [hA] using norm_integral_modelA j hypos hyhalf ha hene
      · simpa [hB, ← hLval] using norm_integral_modelB j hypos hyhalf ha hene
    refine le_trans hbound (le_trans harith ?_)
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

theorem tile_pole_integral_bound (j : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon →
      ∀ a : ℝ, 0 ≤ a →
        ‖∫ t in (w.im / 2)..1, (1 : ℂ) / ((t : ℂ) * Complex.I - (w : ℂ)) * (t : ℂ) ^ j
            * Complex.exp (-(a : ℂ) * (t : ℂ))‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := tile_pole_integral_decay j 0
  refine ⟨C, N, hC, hN, fun w hw a ha => ?_⟩
  have h := hb w hw a ha
  simpa using h

end Work.Asymptotics
