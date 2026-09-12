import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 8000000

namespace Commons.Analysis.SpecialFunctions

/-- `x ≤ exp x` for every real `x`. -/
lemma self_le_exp (x : ℝ) : x ≤ Real.exp x := by
  have h := Real.add_one_le_exp x
  linarith

/-- For `1 ≤ x`, `⌈x⌉₊ ≤ 2 x` (as reals). -/
lemma ceil_le_two_mul {x : ℝ} (hx : 1 ≤ x) : ((Nat.ceil x : ℕ) : ℝ) ≤ 2 * x := by
  have h0 : 0 ≤ x := le_trans zero_le_one hx
  have hlt : ((Nat.ceil x : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one h0
  linarith

/-- `7 ^ y = exp (log 7 * y)` for real `y`. -/
lemma seven_rpow (y : ℝ) : (7 : ℝ) ^ y = Real.exp (Real.log 7 * y) :=
  Real.rpow_def_of_pos (by norm_num) y

theorem exists_model_count_bound (Q₁ : ℝ) (hQ₁ : 0 < Q₁) :
    ∃ Q > 0, ∀ n ≥ Q, ∀ H ≥ 1,
      ((Nat.ceil (Q₁ * Real.log n) + 1 : ℕ) : ℝ) ^ 2
        * (((2 * Nat.ceil (((n : ℝ) * (H : ℝ) ^ ((n : ℝ))⁻¹) ^ (Q₁ * Real.log n)) + 3 : ℕ)) : ℝ)
            ^ (Nat.ceil (Q₁ * Real.log n) * Nat.ceil (Q₁ * (n : ℝ) * Real.log n))
        * ((Nat.ceil (Q₁ * Real.log n) : ℕ) : ℝ) ^ (Nat.ceil (Q₁ * Real.log n))
        ≤ (n : ℝ) ^ (Q * (n : ℝ) * (Real.log n) ^ 3) * (H : ℝ) ^ (Q * (Real.log n) ^ 3) := by
  set T : ℝ := max (1 / Q₁) (13 * Q₁ ^ 2 + 4 * Q₁ ^ 2 * Real.log 7 + 1) with hTdef
  set Q : ℝ := max (Real.exp T) (4 * Q₁ ^ 3 + 2) with hQdef
  refine ⟨Q, ?_, ?_⟩
  · -- Q > 0
    have : (0 : ℝ) < Real.exp T := Real.exp_pos T
    rw [hQdef]
    exact lt_max_of_lt_left this
  · intro n hn H hH
    have hQexp : Real.exp T ≤ Q := by rw [hQdef]; exact le_max_left _ _
    have hQbig : 4 * Q₁ ^ 3 + 2 ≤ Q := by rw [hQdef]; exact le_max_right _ _
    have hexpT_le_n : Real.exp T ≤ n := le_trans hQexp hn
    have hnpos : 0 < n := lt_of_lt_of_le (Real.exp_pos T) hexpT_le_n
    have hlog7_nonneg : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
    have hTpos : 0 < T := by
      rw [hTdef]
      have : (0:ℝ) < 13 * Q₁ ^ 2 + 4 * Q₁ ^ 2 * Real.log 7 + 1 := by
        nlinarith [sq_nonneg Q₁]
      exact lt_max_of_lt_right this
    have hn_ge_one : 1 ≤ n := by
      have : 1 ≤ Real.exp T := Real.one_le_exp hTpos.le
      linarith
    -- t := log n
    set t : ℝ := Real.log n with ht
    have ht_ge_T : T ≤ t := by
      rw [ht]
      simpa using Real.log_le_log (Real.exp_pos T) hexpT_le_n
    have ht_ge_inv : (1 : ℝ) / Q₁ ≤ t := by
      refine le_trans ?_ ht_ge_T
      rw [hTdef]; exact le_max_left _ _
    have ht_ge_big : 13 * Q₁ ^ 2 + 4 * Q₁ ^ 2 * Real.log 7 + 1 ≤ t := by
      refine le_trans ?_ ht_ge_T
      rw [hTdef]; exact le_max_right _ _
    have ht_ge_one : 1 ≤ t := by nlinarith [ht_ge_big, hlog7_nonneg, sq_nonneg Q₁]
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht_ge_one
    have ht_sq_ge : 13 * Q₁ ^ 2 + 4 * Q₁ ^ 2 * Real.log 7 ≤ t ^ 2 := by
      nlinarith [ht_ge_big, ht_ge_one, sq_nonneg (t - 1), hlog7_nonneg, sq_nonneg Q₁]
    -- c := Q₁ * t
    set c : ℝ := Q₁ * t with hc
    have hc_ge_one : 1 ≤ c := by
      rw [hc]
      have h1 : Q₁ * (1 / Q₁) = 1 := by field_simp
      have hmul : Q₁ * (1 / Q₁) ≤ Q₁ * t := mul_le_mul_of_nonneg_left ht_ge_inv hQ₁.le
      linarith
    have hc_pos : 0 < c := lt_of_lt_of_le one_pos hc_ge_one
    set a : ℕ := Nat.ceil c with ha
    set b : ℕ := Nat.ceil (Q₁ * n * t) with hb
    set u : ℝ := (n * H ^ n⁻¹) ^ c with hu
    -- basic bounds
    have ha_le : ((a : ℕ) : ℝ) ≤ 2 * c := by
      rw [ha]; exact ceil_le_two_mul hc_ge_one
    have hb_arg_ge_one : 1 ≤ Q₁ * n * t := by
      have hre : Q₁ * n * t = (Q₁ * t) * n := by ring
      rw [hre]
      have hprod : 1 * 1 ≤ (Q₁ * t) * n :=
        mul_le_mul hc_ge_one hn_ge_one (by norm_num) (by positivity)
      simpa using hprod
    have hb_le : ((b : ℕ) : ℝ) ≤ 2 * (Q₁ * n * t) := by
      rw [hb]; exact ceil_le_two_mul hb_arg_ge_one
    have hQint_nonneg : 0 ≤ Q₁ * n * t := le_trans zero_le_one hb_arg_ge_one
    have hab_le : ((a * b : ℕ) : ℝ) ≤ 4 * Q₁ ^ 2 * n * t ^ 2 := by
      rw [Nat.cast_mul]
      calc (a : ℝ) * (b : ℝ) ≤ (2 * c) * (2 * (Q₁ * n * t)) := by
              exact mul_le_mul ha_le hb_le (Nat.cast_nonneg b) (by positivity)
        _ = 4 * Q₁ ^ 2 * n * t ^ 2 := by rw [hc]; ring
    -- u ≥ 1
    have hHn_ge_one : 1 ≤ H ^ n⁻¹ := Real.one_le_rpow hH (inv_nonneg.mpr hnpos.le)
    have hbase_ge_one : 1 ≤ n * H ^ n⁻¹ := by
      have hprod : 1 * 1 ≤ n * H ^ n⁻¹ :=
        mul_le_mul hn_ge_one hHn_ge_one (by norm_num) (by linarith)
      simpa using hprod
    have hbase_nonneg : 0 ≤ n * H ^ n⁻¹ := by positivity
    have hu_ge_one : 1 ≤ u := by
      rw [hu]
      exact Real.one_le_rpow hbase_ge_one hc_pos.le
    -- ceil u ≤ 2u
    have hceil_u : ((Nat.ceil u : ℕ) : ℝ) ≤ 2 * u := ceil_le_two_mul hu_ge_one
    have hu_nonneg : 0 ≤ u := le_trans zero_le_one hu_ge_one
    have hceil2u : ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ≤ 7 * u := by
      have hcast : ((2 * Nat.ceil u + 3 : ℕ) : ℝ) = 2 * ((Nat.ceil u : ℕ) : ℝ) + 3 := by
        push_cast; ring
      rw [hcast]
      nlinarith [hceil_u, hu_ge_one]
    -- abbreviations
    set En : ℝ := 4 * Q₁ ^ 3 * n * t ^ 3 with hEn
    set EH : ℝ := 4 * Q₁ ^ 3 * t ^ 3 with hEH
    set G : ℝ := n ^ En * H ^ EH with hG
    have hG_nonneg : 0 ≤ G := by rw [hG]; positivity
    set extra : ℝ := 9 * c ^ 2 * (7:ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) * Real.exp (4 * c ^ 2) with hextra
    -- (1) bound T1
    have hT1 : ((a + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * c ^ 2 := by
      have hle : ((a + 1 : ℕ) : ℝ) ≤ 3 * c := by
        rw [Nat.cast_add, Nat.cast_one]
        linarith [ha_le, hc_ge_one]
      calc ((a + 1 : ℕ) : ℝ) ^ 2 ≤ (3 * c) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
        _ = 9 * c ^ 2 := by ring
    -- (2) bound u^(a*b)
    have hu_bound : u ^ (a * b) ≤ G := by
      rw [← Real.rpow_natCast u (a * b), hu]
      rw [← Real.rpow_mul hbase_nonneg c ((a * b : ℕ) : ℝ)]
      have he_le : c * ((a * b : ℕ) : ℝ) ≤ En := by
        have hmul : c * ((a * b : ℕ) : ℝ) ≤ c * (4 * Q₁ ^ 2 * n * t ^ 2) :=
          mul_le_mul_of_nonneg_left hab_le hc_pos.le
        rw [hc] at hmul
        rw [hEn]
        nlinarith [hmul]
      calc (n * H ^ n⁻¹) ^ (c * ((a * b : ℕ) : ℝ))
          ≤ (n * H ^ n⁻¹) ^ En := Real.rpow_le_rpow_of_exponent_le hbase_ge_one he_le
        _ = n ^ En * (H ^ n⁻¹) ^ En := by
              rw [Real.mul_rpow (show (0:ℝ) ≤ n by positivity) (show (0:ℝ) ≤ H ^ n⁻¹ by positivity)]
        _ = n ^ En * H ^ (n⁻¹ * En) := by rw [Real.rpow_mul (by positivity : (0:ℝ) ≤ H)]
        _ = G := by
            rw [hG, hEH]
            congr 1
            rw [hEn, show (4:ℝ) * Q₁ ^ 3 * n * t ^ 3 = n * (4 * Q₁ ^ 3 * t ^ 3) by ring,
                inv_mul_cancel_left₀ (ne_of_gt hnpos)]
    -- (3) bound 7^(a*b)
    have h7_bound : (7 : ℝ) ^ (a * b) ≤ (7 : ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) := by
      rw [← Real.rpow_natCast 7 (a * b)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hab_le
    -- (4) bound whole T2
    have hT2 : ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ^ (a * b)
        ≤ (7 : ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) * G := by
      calc ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ^ (a * b)
          ≤ (7 * u) ^ (a * b) := pow_le_pow_left₀ (by positivity) hceil2u (a * b)
        _ = (7 : ℝ) ^ (a * b) * u ^ (a * b) := by rw [mul_pow]
        _ ≤ (7 : ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) * G :=
            mul_le_mul h7_bound hu_bound (by positivity) (by positivity)
    -- (5) bound T3
    have hT3 : ((a : ℕ) : ℝ) ^ a ≤ Real.exp (4 * c ^ 2) := by
      rw [← Real.rpow_natCast (a : ℝ) a]
      have h2c_ge_one : 1 ≤ 2 * c := by linarith
      calc (a : ℝ) ^ (((a : ℕ)) : ℝ)
          ≤ (2 * c) ^ (((a : ℕ)) : ℝ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg a) ha_le (Nat.cast_nonneg a)
        _ ≤ (2 * c) ^ (2 * c) := Real.rpow_le_rpow_of_exponent_le h2c_ge_one ha_le
        _ ≤ Real.exp (4 * c ^ 2) := by
              rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < 2 * c), Real.exp_le_exp]
              have hlog : Real.log (2 * c) ≤ 2 * c := Real.log_le_self (by linarith)
              have hmul := mul_le_mul_of_nonneg_right hlog (by linarith : (0:ℝ) ≤ 2 * c)
              nlinarith [hmul]
    -- (6) assemble LHS ≤ extra * G
    have hLHS_le : ((a + 1 : ℕ) : ℝ) ^ 2 * ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ^ (a * b)
          * ((a : ℕ) : ℝ) ^ a ≤ extra * G := by
      have h1 : ((a + 1 : ℕ) : ℝ) ^ 2 * ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ^ (a * b)
          ≤ 9 * c ^ 2 * ((7 : ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) * G) :=
        mul_le_mul hT1 hT2 (by positivity) (by positivity)
      have h2 : ((a + 1 : ℕ) : ℝ) ^ 2 * ((2 * Nat.ceil u + 3 : ℕ) : ℝ) ^ (a * b)
            * ((a : ℕ) : ℝ) ^ a
          ≤ (9 * c ^ 2 * ((7 : ℝ) ^ (4 * Q₁ ^ 2 * n * t ^ 2) * G)) * Real.exp (4 * c ^ 2) :=
        mul_le_mul h1 hT3 (by positivity) (by positivity)
      rw [hextra]
      refine le_trans h2 (le_of_eq ?_)
      ring
    -- (7) absorption
    have hA : 13 * Q₁ ^ 2 * t ^ 2 ≤ n * t ^ 4 := by
      have h1 : 13 * Q₁ ^ 2 ≤ n * t ^ 2 := by
        nlinarith [ht_sq_ge, hn_ge_one, sq_nonneg Q₁, hlog7_nonneg]
      have := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
      nlinarith [this]
    have hB : Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2) ≤ n * t ^ 4 := by
      have h2 : 4 * Q₁ ^ 2 * Real.log 7 ≤ t ^ 2 := by nlinarith [ht_sq_ge]
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ n * t ^ 2)
      nlinarith [this]
    have harg : 9 * c ^ 2 + Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2) + 4 * c ^ 2 ≤ 2 * n * t ^ 4 := by
      rw [hc]
      nlinarith [hA, hB]
    have hextra_bound : extra ≤ n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3) := by
      rw [hextra, seven_rpow]
      have h9 : 9 * c ^ 2 ≤ Real.exp (9 * c ^ 2) := self_le_exp _
      have h1 : 9 * c ^ 2 * Real.exp (Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2)) * Real.exp (4 * c ^ 2)
          ≤ Real.exp (9 * c ^ 2) * Real.exp (Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2))
              * Real.exp (4 * c ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right h9 (by positivity)
        · positivity
      have hEE : Real.exp (9 * c ^ 2) * Real.exp (Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2))
            * Real.exp (4 * c ^ 2)
          = Real.exp (9 * c ^ 2 + Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2) + 4 * c ^ 2) := by
        rw [Real.exp_add, Real.exp_add]
      have h2 : Real.exp (9 * c ^ 2 + Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2) + 4 * c ^ 2)
          ≤ Real.exp (2 * n * t ^ 4) := Real.exp_le_exp.mpr harg
      have h3 : Real.exp (2 * n * t ^ 4) = n ^ (2 * n * t ^ 3) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        rw [← ht]
        ring
      have hH1 : 1 ≤ H ^ (2 * t ^ 3) := Real.one_le_rpow hH (by positivity)
      have h4 : n ^ (2 * n * t ^ 3) ≤ n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3) := by
        have hpos : 0 < n ^ (2 * n * t ^ 3) := Real.rpow_pos_of_pos hnpos _
        have := mul_le_mul_of_nonneg_left hH1 hpos.le
        simpa using this
      calc 9 * c ^ 2 * Real.exp (Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2)) * Real.exp (4 * c ^ 2)
          ≤ Real.exp (9 * c ^ 2) * Real.exp (Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2))
              * Real.exp (4 * c ^ 2) := h1
        _ = Real.exp (9 * c ^ 2 + Real.log 7 * (4 * Q₁ ^ 2 * n * t ^ 2) + 4 * c ^ 2) := hEE
        _ ≤ Real.exp (2 * n * t ^ 4) := h2
        _ = n ^ (2 * n * t ^ 3) := h3
        _ ≤ n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3) := h4
    -- (8) final assembly
    have hfinal : extra * G ≤ n ^ (Q * n * t ^ 3) * H ^ (Q * t ^ 3) := by
      have hstep : extra * G ≤ (n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3)) * (n ^ En * H ^ EH) :=
        mul_le_mul hextra_bound le_rfl hG_nonneg (by positivity)
      have hHpos : (0:ℝ) < H := by linarith
      have hmid : (n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3)) * (n ^ En * H ^ EH)
          = n ^ (2 * n * t ^ 3 + En) * H ^ (2 * t ^ 3 + EH) := by
        rw [Real.rpow_add hnpos, Real.rpow_add hHpos]
        ring
      have e1 : 2 * n * t ^ 3 + En = (4 * Q₁ ^ 3 + 2) * n * t ^ 3 := by rw [hEn]; ring
      have e2 : 2 * t ^ 3 + EH = (4 * Q₁ ^ 3 + 2) * t ^ 3 := by rw [hEH]; ring
      have hnnt : 0 ≤ n * t ^ 3 := mul_nonneg hnpos.le (pow_nonneg ht_pos.le 3)
      have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht_pos.le 3
      have hexp1 : (4 * Q₁ ^ 3 + 2) * n * t ^ 3 ≤ Q * n * t ^ 3 := by
        rw [show (4 * Q₁ ^ 3 + 2) * n * t ^ 3 = (4 * Q₁ ^ 3 + 2) * (n * t ^ 3) by ring,
            show Q * n * t ^ 3 = Q * (n * t ^ 3) by ring]
        exact mul_le_mul_of_nonneg_right hQbig hnnt
      have hexp2 : (4 * Q₁ ^ 3 + 2) * t ^ 3 ≤ Q * t ^ 3 :=
        mul_le_mul_of_nonneg_right hQbig ht3
      have hEq : n ^ ((4 * Q₁ ^ 3 + 2) * n * t ^ 3) * H ^ ((4 * Q₁ ^ 3 + 2) * t ^ 3)
          ≤ n ^ (Q * n * t ^ 3) * H ^ (Q * t ^ 3) := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow_of_exponent_le hn_ge_one hexp1
        · exact Real.rpow_le_rpow_of_exponent_le hH hexp2
        · exact Real.rpow_nonneg (le_of_lt hHpos) _
        · exact Real.rpow_nonneg hnpos.le _
      calc extra * G
          ≤ (n ^ (2 * n * t ^ 3) * H ^ (2 * t ^ 3)) * (n ^ En * H ^ EH) := hstep
        _ = n ^ (2 * n * t ^ 3 + En) * H ^ (2 * t ^ 3 + EH) := hmid
        _ = n ^ ((4 * Q₁ ^ 3 + 2) * n * t ^ 3) * H ^ ((4 * Q₁ ^ 3 + 2) * t ^ 3) := by
              rw [e1, e2]
        _ ≤ n ^ (Q * n * t ^ 3) * H ^ (Q * t ^ 3) := hEq
    exact le_trans hLHS_le hfinal

end Commons.Analysis.SpecialFunctions