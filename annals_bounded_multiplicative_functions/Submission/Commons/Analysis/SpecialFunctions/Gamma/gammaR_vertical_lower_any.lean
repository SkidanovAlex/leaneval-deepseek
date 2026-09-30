import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real BigOperators

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

lemma grvla_sinh_le_mul_exp (x : ℝ) (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  have h2 : Real.exp (2 * x) * (1 - 2 * x) ≤ 1 := by
    by_cases hxhalf : 1 / 2 ≤ x
    · have hnonpos : 1 - 2 * x ≤ 0 := by linarith
      have hprod : Real.exp (2 * x) * (1 - 2 * x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (2 * x)).le hnonpos
      linarith
    · have hy0 : 0 ≤ 2 * x := by linarith
      have hy1 : 2 * x < 1 := by linarith
      have hb : 0 < 1 - 2 * x := by linarith
      have hexp := Real.exp_bound_div_one_sub_of_interval hy0 hy1
      exact (le_div_iff₀ hb).mp hexp
  have hm : Real.exp (2 * x) - 1 ≤ 2 * x * Real.exp (2 * x) := by
    nlinarith [h2]
  have hmul := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-x)).le
  have hL : Real.exp (-x) * (Real.exp (2 * x) - 1) = Real.exp x - Real.exp (-x) := by
    rw [mul_sub]
    have h1 : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h1]
    ring
  have hR : Real.exp (-x) * (2 * x * Real.exp (2 * x)) = 2 * x * Real.exp x := by
    calc
      Real.exp (-x) * (2 * x * Real.exp (2 * x))
          = 2 * x * (Real.exp (-x) * Real.exp (2 * x)) := by ring
      _ = 2 * x * Real.exp x := by
        have h1 : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [h1]
  have hA : Real.exp x - Real.exp (-x) ≤ 2 * x * Real.exp x := by
    calc
      Real.exp x - Real.exp (-x) = Real.exp (-x) * (Real.exp (2 * x) - 1) := hL.symm
      _ ≤ Real.exp (-x) * (2 * x * Real.exp (2 * x)) := hmul
      _ = 2 * x * Real.exp x := hR
  have hdiv := div_le_div_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 2)
  calc
    (Real.exp x - Real.exp (-x)) / 2 ≤ (2 * x * Real.exp x) / 2 := hdiv
    _ = x * Real.exp x := by ring

lemma grvla_norm_sin_I_mul_ofReal (y : ℝ) :
    ‖Complex.sin (I * (y : ℂ))‖ = |Real.sinh y| := by
  rw [mul_comm I, Complex.sin_mul_I]
  rw [norm_mul, Complex.norm_I, mul_one]
  rw [← Complex.ofReal_sinh]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs]

lemma grvla_gamma_one_vertical_lower (t : ℝ) :
    Real.exp (-(Real.pi / 2) * |t|) ≤ ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * (t : ℂ))‖ := by
  have hmain (u : ℝ) (hu0 : 0 < u) :
      Real.exp (-(Real.pi / 2) * u) ≤ ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * (u : ℂ))‖ := by
    let z : ℂ := I * (u : ℂ)
    have hz_ne : z ≠ 0 := by
      intro hz0
      have him : z.im = u := by simp [z]
      have : z.im = 0 := congrArg Complex.im hz0
      linarith
    have hnormz : ‖z‖ = u := by
      dsimp [z]
      rw [norm_mul, Complex.norm_I, Complex.norm_real]
      simp [abs_of_pos hu0]
    have hG_rec : ‖Complex.Gamma (1 + z)‖ = u * ‖Complex.Gamma z‖ := by
      have h := Complex.Gamma_add_one z hz_ne
      have hz1 : 1 + z = z + 1 := by ring
      calc
        ‖Complex.Gamma (1 + z)‖ = ‖Complex.Gamma (z + 1)‖ := by rw [hz1]
        _ = ‖z * Complex.Gamma z‖ := by rw [h]
        _ = ‖z‖ * ‖Complex.Gamma z‖ := by rw [norm_mul]
        _ = u * ‖Complex.Gamma z‖ := by rw [hnormz]
    have hrefl := Gamma_mul_Gamma_one_sub_norm z
    have hcs : ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma (1 + z)‖ := by
      have hconjarg : (starRingEnd ℂ) (1 + z) = 1 - z := by
        dsimp [z]
        rw [map_add, map_one, map_mul]
        simp
        ring_nf
      calc
        ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma ((starRingEnd ℂ) (1 + z))‖ := by rw [hconjarg]
        _ = ‖(starRingEnd ℂ) (Complex.Gamma (1 + z))‖ := by rw [Complex.Gamma_conj]
        _ = ‖Complex.Gamma (1 + z)‖ := Complex.norm_conj _
    have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
      exact sin_ne_zero_of_im_ne_zero (by
        have him : ((Real.pi : ℂ) * z).im = Real.pi * u := by simp [z]
        rw [him]
        exact mul_ne_zero (ne_of_gt Real.pi_pos) (ne_of_gt hu0))
    have hprod : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 + z)‖ =
        Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      calc
        ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 + z)‖
            = ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by rw [hcs]
        _ = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := hrefl
    have hsq : ‖Complex.Gamma (1 + z)‖ ^ 2 =
        (Real.pi * u) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      rw [sq]
      calc
        ‖Complex.Gamma (1 + z)‖ * ‖Complex.Gamma (1 + z)‖
            = (u * ‖Complex.Gamma z‖) * ‖Complex.Gamma (1 + z)‖ := by rw [hG_rec]
        _ = u * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1 + z)‖) := by ring
        _ = u * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖) := by rw [hprod]
        _ = (Real.pi * u) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
          rw [mul_div_assoc]
          ring
    have hsin_val : ‖Complex.sin ((Real.pi : ℂ) * z)‖ = Real.sinh (Real.pi * u) := by
      have harg : (Real.pi : ℂ) * z = I * ((Real.pi * u : ℝ) : ℂ) := by
        dsimp [z]
        calc (Real.pi : ℂ) * (I * (u : ℂ)) = I * ((Real.pi : ℂ) * (u : ℂ)) := by ring
        _ = I * ((Real.pi * u : ℝ) : ℂ) := by rw [← Complex.ofReal_mul]
      rw [harg]
      rw [grvla_norm_sin_I_mul_ofReal (Real.pi * u)]
      rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hu0)))]
    have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤
        (Real.pi * u) * Real.exp (Real.pi * u) := by
      rw [hsin_val]
      exact grvla_sinh_le_mul_exp (Real.pi * u) (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hu0))
    have hbig : Real.exp (-(Real.pi * u)) ≤ ‖Complex.Gamma (1 + z)‖ ^ 2 := by
      have hden : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := norm_pos_iff.mpr hsin_ne
      have hpiu : 0 < Real.pi * u := mul_pos Real.pi_pos hu0
      have heq : Real.exp (-(Real.pi * u)) =
          (Real.pi * u) / ((Real.pi * u) * Real.exp (Real.pi * u)) := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt (Real.exp_pos (Real.pi * u)), ne_of_gt hpiu]
      calc
        Real.exp (-(Real.pi * u)) = (Real.pi * u) / ((Real.pi * u) * Real.exp (Real.pi * u)) := heq
        _ ≤ (Real.pi * u) / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
          exact div_le_div_of_nonneg_left hpiu.le hden hsin_le
        _ = ‖Complex.Gamma (1 + z)‖ ^ 2 := hsq.symm
    have hpowle : (Real.exp (-(Real.pi / 2) * u)) ^ 2 ≤ ‖Complex.Gamma (1 + z)‖ ^ 2 := by
      have he2 : (Real.exp (-(Real.pi / 2) * u)) ^ 2 = Real.exp (-(Real.pi * u)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [he2]
      exact hbig
    have hsqle := sq_le_sq.mp hpowle
    have hpos : 0 < Real.exp (-(Real.pi / 2) * u) := Real.exp_pos _
    have hzdef : 1 + z = ((1 : ℝ) : ℂ) + I * (u : ℂ) := by simp [z]
    calc
      Real.exp (-(Real.pi / 2) * u) ≤ ‖Complex.Gamma (1 + z)‖ := by
        have h' : |Real.exp (-(Real.pi / 2) * u)| = Real.exp (-(Real.pi / 2) * u) :=
          abs_of_pos hpos
        have hnormabs : |‖Complex.Gamma (1 + z)‖| = ‖Complex.Gamma (1 + z)‖ :=
          abs_of_nonneg (norm_nonneg _)
        rw [hnormabs] at hsqle
        rw [← h']
        exact hsqle
      _ = ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * (u : ℂ))‖ := by rw [hzdef]
  by_cases ht0 : t = 0
  · simp [ht0]
  · by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      exact hmain t (lt_of_le_of_ne ht (Ne.symm ht0))
    · let s : ℂ := ((1 : ℝ) : ℂ) + I * (t : ℂ)
      let sp : ℂ := ((1 : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ)
      have hu0 : 0 < -t := by linarith
      have hconjarg : (starRingEnd ℂ) s = sp := by
        dsimp [s, sp]
        apply Complex.ext <;> simp
      have hcs : ‖Complex.Gamma sp‖ = ‖Complex.Gamma s‖ := by
        calc
          ‖Complex.Gamma sp‖ = ‖Complex.Gamma ((starRingEnd ℂ) s)‖ := by rw [hconjarg]
          _ = ‖(starRingEnd ℂ) (Complex.Gamma s)‖ := by rw [Complex.Gamma_conj]
          _ = ‖Complex.Gamma s‖ := Complex.norm_conj _
      calc
        Real.exp (-(Real.pi / 2) * |t|) = Real.exp (-(Real.pi / 2) * (-t)) := by
          rw [abs_of_neg (by linarith : t < 0)]
        _ ≤ ‖Complex.Gamma sp‖ := by simpa [sp] using hmain (-t) hu0
        _ = ‖Complex.Gamma s‖ := hcs
        _ = ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * (t : ℂ))‖ := by simp [s]

/-- closed interval (0,1] vertical lower bound -/
theorem grvla_gamma_vertical_exp_decay_lower_unit (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|) ≤
        ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by
  by_cases hlt : σ < 1
  · exact gamma_vertical_exp_decay_lower σ hσ0 hlt
  · have hσ1' : σ = 1 := le_antisymm hσ1 (le_of_not_gt hlt)
    subst σ
    refine ⟨1, by norm_num, ?_⟩
    intro t
    have hpow : (1 + |t|) ^ ((1 : ℝ) - 1) = 1 := by
      rw [sub_self, Real.rpow_zero]
    calc
      1 * (1 + |t|) ^ ((1 : ℝ) - 1) * Real.exp (-(Real.pi / 2) * |t|)
          = Real.exp (-(Real.pi / 2) * |t|) := by rw [hpow]; ring
      _ ≤ ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * (t : ℂ))‖ := grvla_gamma_one_vertical_lower t

/-- functional equation shift -/
theorem grvla_gamma_nat_shift_norm (σ : ℝ) (hσ0 : 0 < σ) (t : ℝ) (n : ℕ) :
    ‖Complex.Gamma (((σ + n : ℝ) : ℂ) + I * (t : ℂ))‖ =
      ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ *
        ∏ j ∈ Finset.range n, ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let s : ℂ := (((σ + (n : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)
      have hs_ne : s ≠ 0 := by
        intro hs0
        have hre : s.re = σ + (n : ℝ) := by simp [s]
        have : s.re = 0 := congrArg Complex.re hs0
        linarith
      have harg1 : (((σ + (n + 1 : ℕ) : ℝ) : ℂ) + I * (t : ℂ)) = s + 1 := by
        dsimp [s]
        push_cast
        ring
      have hstep : ‖Complex.Gamma (((σ + (n + 1 : ℕ) : ℝ) : ℂ) + I * (t : ℂ))‖ =
          ‖Complex.Gamma s‖ * ‖s‖ := by
        calc
          ‖Complex.Gamma (((σ + (n + 1 : ℕ) : ℝ) : ℂ) + I * (t : ℂ))‖
              = ‖Complex.Gamma (s + 1)‖ := by rw [harg1]
          _ = ‖s * Complex.Gamma s‖ := by rw [Complex.Gamma_add_one s hs_ne]
          _ = ‖Complex.Gamma s‖ * ‖s‖ := by
                rw [norm_mul]
                ring
      have hprod_succ : ∏ j ∈ Finset.range (n + 1), ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ =
          (∏ j ∈ Finset.range n, ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖) *
            ‖(((σ + (n : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
        rw [Finset.prod_range_succ]
      have hsn : ‖s‖ = ‖(((σ + (n : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
        dsimp [s]
      calc
        ‖Complex.Gamma (((σ + (n + 1 : ℕ) : ℝ) : ℂ) + I * (t : ℂ))‖
            = ‖Complex.Gamma s‖ * ‖s‖ := hstep
        _ = (‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ *
              ∏ j ∈ Finset.range n, ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖) * ‖s‖ := by
              rw [ih]
        _ = ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ *
              ((∏ j ∈ Finset.range n, ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖) * ‖s‖) := by
              ring
        _ = ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ *
              ∏ j ∈ Finset.range (n + 1), ‖(((σ + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
              rw [hprod_succ, ← hsn]


-- Γℝ norm identity
lemma grvla_gammaR_norm_eq (a T : ℝ) :
    ‖Complex.Gammaℝ (((a : ℝ) : ℂ) + I * (T : ℂ))‖
      = Real.pi ^ (-(a / 2)) *
          ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := by
  let s : ℂ := ((a : ℝ) : ℂ) + I * (T : ℂ)
  have hs_re : s.re = a := by simp [s]
  have hs_im : s.im = T := by simp [s]
  have hre_div : (s / 2).re = a / 2 := by
    rw [Complex.div_re]
    simp [hs_re, hs_im]
    ring
  have hre_neg : (-s / 2).re = -(a / 2) := by
    have hswap : -s / 2 = -(s / 2) := by ring
    rw [hswap, Complex.neg_re, hre_div]
  have hnorm_pow : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-(a / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [hre_neg]
  have hhalf : s / 2 = ((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre_div]
      simp
    · have him_div : (s / 2).im = T / 2 := by
        rw [Complex.div_im]
        simp [hs_re, hs_im]
        ring
      rw [him_div]
      simp
  calc
    ‖Complex.Gammaℝ (((a : ℝ) : ℂ) + I * (T : ℂ))‖
        = ‖Complex.Gammaℝ s‖ := by simp [s]
    _ = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
          rw [Complex.Gammaℝ_def, norm_mul]
    _ = Real.pi ^ (-(a / 2)) * ‖Complex.Gamma (s / 2)‖ := by rw [hnorm_pow]
    _ = Real.pi ^ (-(a / 2)) * ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := by
          rw [hhalf]

-- intermediate: for every σ > 0 the vertical lower bound with sharp rate and p ≤ 0
theorem grvla_gamma_vertical_lower_any_helper (σ : ℝ) (hσ : 0 < σ) :
    ∃ c p : ℝ, 0 < c ∧ p ≤ 0 ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ p * Real.exp (-(Real.pi / 2) * |t|) ≤
        ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by
  let m : ℕ := Nat.ceil σ
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact Nat.ceil_pos.mpr hσ
  let k : ℕ := m - 1
  let σ0 : ℝ := σ - (k : ℝ)
  have hkcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  have hle : σ ≤ (m : ℝ) := by
    dsimp [m]
    exact (Nat.ceil_le.mp (le_refl m))
  have hlt : (m : ℝ) < σ + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hσ.le
  have hσ0pos : 0 < σ0 := by
    dsimp [σ0, k]
    -- σ0 = σ - (m-1) = σ + 1 - m > 0 since m < σ+1
    have : σ + 1 - (m : ℝ) > 0 := by linarith
    linarith
  have hσ0le : σ0 ≤ 1 := by
    dsimp [σ0, k]
    have h1 : σ - ((m : ℝ) - 1) ≤ 1 := by linarith
    simpa [hkcast] using h1
  have hσ0_add : σ0 + (k : ℝ) = σ := by
    dsimp [σ0, k]
    rw [hkcast]
    ring
  obtain ⟨c0, hc0pos, hc0⟩ := grvla_gamma_vertical_exp_decay_lower_unit σ0 hσ0pos hσ0le
  let P : ℝ := ∏ j ∈ Finset.range k, (σ0 + (j : ℝ))
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (by
      intro j hj
      have : 0 < σ0 + (j : ℝ) := by
        have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
        linarith
      exact this)
  let c : ℝ := c0 * P
  let p : ℝ := σ0 - 1
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos hc0pos hPpos
  have hple : p ≤ 0 := by
    dsimp [p]
    linarith
  refine ⟨c, p, hcpos, hple, ?_⟩
  intro t
  have hbase := hc0 t
  -- base bound: c0 * (1+|t|)^(σ0-1) * exp ≤ ‖Γ(σ0 + it)‖
  let X : ℝ := (1 + |t|) ^ (σ0 - 1) * Real.exp (-(Real.pi / 2) * |t|)
  have hfac (j : ℕ) (hj : j ∈ Finset.range k) :
      σ0 + (j : ℝ) ≤ ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
    let z : ℂ := (((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)
    have hz_re : z.re = σ0 + (j : ℝ) := by simp [z]
    have hz0 : 0 ≤ σ0 + (j : ℝ) := by
      have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
      linarith
    have hle := Complex.abs_re_le_norm z
    rw [hz_re] at hle
    have habs : |σ0 + (j : ℝ)| = σ0 + (j : ℝ) := abs_of_nonneg hz0
    rw [habs] at hle
    exact hle
  have hfac0 : ∀ j ∈ Finset.range k, 0 ≤ σ0 + (j : ℝ) := by
    intro j hj
    have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
    linarith
  
  have hPnorm : ∏ j ∈ Finset.range k,
      ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ = ∏ j ∈ Finset.range k,
      ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := rfl
  have hPle : P ≤ ∏ j ∈ Finset.range k,
      ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
    dsimp [P]
    exact Finset.prod_le_prod₀ hfac0 hfac
  have hshift := grvla_gamma_nat_shift_norm σ0 hσ0pos t k
  have hArg : (((σ0 + (k : ℕ) : ℝ) : ℂ) + I * (t : ℂ)) = (σ : ℂ) + I * (t : ℂ) := by
    have h' : (((σ0 + (k : ℕ) : ℝ) : ℂ)) = (σ : ℂ) := by
      rw [hσ0_add]
    rw [h']
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + |t|) _) (Real.exp_nonneg _)
  have hmul1 : c0 * X * P ≤ ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ * P := by
    have hb : c0 * X ≤ ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ := by
      simpa [X, mul_assoc] using hbase
    exact mul_le_mul_of_nonneg_right hb hPpos.le
  have hmul2 : ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ * P ≤
      ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ * ∏ j ∈ Finset.range k,
        ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
    exact mul_le_mul_of_nonneg_left hPle (norm_nonneg _)
  have hmain : c * X ≤ ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by
    calc
      c * X = c0 * X * P := by
        dsimp [c]
        ring
      _ ≤ ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ * P := hmul1
      _ ≤ ‖Complex.Gamma ((σ0 : ℂ) + I * (t : ℂ))‖ * ∏ j ∈ Finset.range k,
            ‖(((σ0 + (j : ℝ)) : ℝ) : ℂ) + I * (t : ℂ)‖ := hmul2
      _ = ‖Complex.Gamma (((σ0 + (k : ℕ) : ℝ) : ℂ) + I * (t : ℂ))‖ := by
            exact hshift.symm
      _ = ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by rw [hArg]
  dsimp [p, X] at hmain
  convert hmain using 1; ring


-- auxiliary: antitone rpow for exponent ≤ 0: 0 < x ≤ y and p ≤ 0 → y^p ≤ x^p
lemma grvla_rpow_le_of_le_and_nonpos {x y p : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hp : p ≤ 0) :
    y ^ p ≤ x ^ p := by
  let q : ℝ := -p
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hqle : x ^ q ≤ y ^ q := Real.rpow_le_rpow hx.le hxy hq0
  have hp_eq : p = -q := by dsimp [q]; ring
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [hp_eq, Real.rpow_neg hy.le q, Real.rpow_neg hx.le q]
  simpa [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx q) hqle

theorem gammaR_vertical_lower_any (a : ℝ) (ha : 0 < a) :
    ∃ c p : ℝ, 0 < c ∧ p ≤ 0 ∧ ∀ T : ℝ,
      c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by
  let σ : ℝ := a / 2
  have hσ : 0 < σ := by
    dsimp [σ]
    linarith
  obtain ⟨cΓ, p, hcΓ, hple, hΓ⟩ := grvla_gamma_vertical_lower_any_helper σ hσ
  let c : ℝ := Real.pi ^ (-(a / 2)) * cΓ
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) hcΓ
  refine ⟨c, p, hcpos, hple, ?_⟩
  intro T
  have hnorm := grvla_gammaR_norm_eq a T
  have ht' := hΓ (T / 2)
  have harg : ((σ : ℂ) + I * ((T / 2 : ℝ) : ℂ)) =
      ((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ) := by
    dsimp [σ]
  have hE : Real.exp (-(Real.pi / 2) * |T / 2|) = Real.exp (-(Real.pi / 4) * |T|) := by
    congr 1
    have ha2 : |T / 2| = |T| / 2 := by
      rw [abs_div]
      norm_num
    rw [ha2]
    ring
  have hΓT : cΓ * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
      ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := by
    calc
      cΓ * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|)
          = cΓ * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 2) * |T / 2|) := by rw [hE]
      _ ≤ ‖Complex.Gamma ((σ : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := ht'
      _ = ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := by rw [harg]
  have hpi0 : 0 ≤ Real.pi ^ (-(a / 2)) := (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hΓT hpi0
  have hmul' : c * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
      Real.pi ^ (-(a / 2)) * ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((T / 2 : ℝ) : ℂ))‖ := by
    simpa [c, mul_assoc] using hmul
  have htarget : c * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
      ‖Complex.Gammaℝ (((a : ℝ) : ℂ) + I * (T : ℂ))‖ := by
    rw [hnorm]
    exact hmul'
  have hhalf : |T / 2| ≤ |T| := by
    calc
      |T / 2| = |(1 / 2 : ℝ) * T| := by congr 1; ring
      _ = |(1 / 2 : ℝ)| * |T| := by rw [abs_mul]
      _ = (1 / 2 : ℝ) * |T| := by norm_num
      _ ≤ |T| := by
        have hT0 : 0 ≤ |T| := abs_nonneg T
        nlinarith
  have hxpos : 0 < 1 + |T / 2| := by positivity
  have hxy : 1 + |T / 2| ≤ 1 + |T| := by linarith
  have hpoly : (1 + |T|) ^ p ≤ (1 + |T / 2|) ^ p :=
    grvla_rpow_le_of_le_and_nonpos hxpos hxy hple
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have he0 : 0 ≤ Real.exp (-(Real.pi / 4) * |T|) := Real.exp_nonneg _
  have hfin : c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
      c * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|) := by
    calc
      c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|)
          = c * Real.exp (-(Real.pi / 4) * |T|) * (1 + |T|) ^ p := by ring
      _ ≤ c * Real.exp (-(Real.pi / 4) * |T|) * (1 + |T / 2|) ^ p := by
          exact mul_le_mul_of_nonneg_left hpoly (mul_nonneg hc0 he0)
      _ = c * (1 + |T / 2|) ^ p * Real.exp (-(Real.pi / 4) * |T|) := by ring
  exact le_trans hfin htarget

end Commons.Analysis.SpecialFunctions.Gamma
