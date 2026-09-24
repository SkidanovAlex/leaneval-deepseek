import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The `λ₂` partial sum twisted by a Dirichlet character, truncated at `T`. -/
noncomputable def lambda2CharSum (T y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
    * (χ (n : ZMod q) : ℂ)

/-- The supremum over `y ≤ x` of the norm of the twisted `λ₂` partial sum. -/
noncomputable def lambda2CharSup (x T q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup ((fun y : ℕ => ‖lambda2CharSum T y q χ‖) '' Set.Icc 1 x)

/-- The `q`-th term of the totient-weighted average over primitive characters. -/
noncomputable def lambda2Term (x T q : ℕ) : ℝ :=
  ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
            (Classical.decPred _) Finset.univ),
      lambda2CharSup x T q χ

/-- **The `λ₂`-sum factorises.**  Using `d | n` to write `n = d·(n/d)`, the Dirichlet sum over
`λ₂` splits into a Möbius-twisted `d`-sum and a log-weighted character sum. -/
lemma lambda2_mul_char_eq_sum (q T y : ℕ) (χ : DirichletCharacter ℂ q) :
    lambda2CharSum T y q χ
      = ∑ d ∈ Finset.Icc 1 T,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (χ (d : ZMod q) : ℂ)
            * (∑ h ∈ Finset.Icc 1 (y / d),
                ((Real.log (h : ℝ) : ℂ)) * (χ (h : ZMod q) : ℂ)) := by
  have key : lambda2CharSum T y q χ
      = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((Real.log (((n / d : ℕ) : ℝ)) : ℂ))
            * (χ ((d * (n / d) : ℕ) : ZMod q) : ℂ) := by
    rw [lambda2CharSum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdn : d * (n / d) = n := Nat.mul_div_cancel' hdvd
    have hcast : ((d : ZMod q) * ((n / d : ℕ) : ZMod q)) = ((n : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, hdn]
    rw [hcast]
  rw [key, Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap y T
        (fun d h => ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((Real.log (h : ℝ) : ℂ))
            * (χ ((d * h : ℕ) : ZMod q) : ℂ))]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Nat.cast_mul, map_mul]
  ring

/-- `log (2n+2) ≥ 0`. -/
lemma log_two_mul_add_two_nonneg (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ) + 2) :=
  Real.log_nonneg (by have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)

/-- The Moebius factor has norm at most one. -/
lemma norm_moebius_cast_le_one (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

/-- A sum over primitive characters is bounded by the number of such characters times a
uniform pointwise bound. -/
lemma prim_char_sum_le_card_mul {q : ℕ} (f : DirichletCharacter ℂ q → ℝ) (B : ℝ)
    (h : ∀ χ, χ.IsPrimitive → f χ ≤ B) (hB : 0 ≤ B) :
    (∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ), f χ)
      ≤ (((@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ).card : ℕ) : ℝ) * B := by
  rw [@Finset.sum_filter (DirichletCharacter ℂ q) ℝ Finset.univ _
      (fun χ => χ.IsPrimitive) (Classical.decPred _) f]
  rw [← nsmul_eq_mul, ← Finset.sum_const,
      @Finset.sum_filter (DirichletCharacter ℂ q) ℝ Finset.univ _
      (fun χ => χ.IsPrimitive) (Classical.decPred _) (fun _ => B)]
  refine Finset.sum_le_sum (fun χ _ => ?_)
  by_cases hc : χ.IsPrimitive
  · rw [if_pos hc, if_pos hc]; exact h χ hc
  · rw [if_neg hc, if_neg hc]

/-- The number of primitive characters mod `q` is at most `φ(q)`. -/
lemma card_primitive_le_totient (q : ℕ) [NeZero q] :
    ((@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ).card : ℕ) ≤ q.totient := by
  calc _ ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
        @Finset.card_filter_le (DirichletCharacter ℂ q) (Finset.univ)
          (fun χ => χ.IsPrimitive) (Classical.decPred _)
    _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
    _ = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- The principal-character (`q = 1`) contribution: the plain partial sums of `λ₂`. -/
lemma lambda2_charSum_level_one_le (T y : ℕ) (χ : DirichletCharacter ℂ 1) :
    ‖lambda2CharSum T y 1 χ‖ ≤ (y : ℝ) * Real.log y * (1 + Real.log T) := by
  have hchar : ∀ n : ℕ, (χ (n : ZMod 1) : ℂ) = 1 := fun n => by
    rw [Subsingleton.elim (n : ZMod 1) (1 : ZMod 1), MulChar.map_one]
  rw [lambda2CharSum]
  have hsum : (∑ n ∈ Finset.Icc 1 y,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
          * (χ (n : ZMod 1) : ℂ))
      = ((∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))) : ℝ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hchar n, mul_one]
  have hnorm : ‖∑ n ∈ Finset.Icc 1 y,
        (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
          * (χ (n : ZMod 1) : ℂ)‖
      = |∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))| := by
    rw [hsum]
    exact RCLike.norm_ofReal _
  rw [hnorm]
  have hlogy : 0 ≤ Real.log (y : ℝ) := by
    rcases Nat.eq_zero_or_pos y with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hlognd : ∀ n ∈ Finset.Icc 1 y, ∀ d ∈ n.divisors.filter (fun d => d ≤ T),
      0 ≤ Real.log (((n / d : ℕ) : ℝ)) := by
    intro n hn d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by have := (Finset.mem_Icc.mp hn).1; omega)
    have hnd1 : 1 ≤ n / d :=
      (Nat.one_le_div_iff (by omega)).mpr (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hn).1; omega) hdvd)
    exact Real.log_nonneg (by exact_mod_cast hnd1)
  have habs : ∀ d : ℕ, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := fun d => by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  have hle : ∀ d : ℕ, (∑ h ∈ Finset.Icc 1 (y / d), Real.log (h : ℝ))
      ≤ ((y / d : ℕ) : ℝ) * Real.log y := by
    intro d
    calc (∑ h ∈ Finset.Icc 1 (y / d), Real.log (h : ℝ))
        ≤ ∑ h ∈ Finset.Icc 1 (y / d), Real.log (y : ℝ) := by
          refine Finset.sum_le_sum (fun h hh => ?_)
          have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
          have hy : (h : ℝ) ≤ (y : ℝ) := by
            have : h ≤ y := le_trans (Finset.mem_Icc.mp hh).2 (Nat.div_le_self y d)
            exact_mod_cast this
          exact Real.log_le_log (by exact_mod_cast hh1) hy
      _ = ((y / d : ℕ) : ℝ) * Real.log y := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  calc |∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))|
      ≤ ∑ n ∈ Finset.Icc 1 y, |∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          |((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))| := by
        refine Finset.sum_le_sum (fun n _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * Real.log (((n / d : ℕ) : ℝ)) := by
        refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun d hd => ?_))
        rw [abs_mul, abs_of_nonneg (hlognd n hn d hd)]
    _ ≤ ∑ n ∈ Finset.Icc 1 y, ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
          Real.log (((n / d : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun d hd => ?_))
        exact mul_le_of_le_one_left (hlognd n hn d hd) (habs d)
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ h ∈ Finset.Icc 1 (y / d), Real.log (h : ℝ) :=
        Commons.NumberTheory.ArithmeticFunction.sum_Icc_divisors_filter_swap (M := ℝ) y T
          (fun _ h => Real.log (h : ℝ))
    _ ≤ ∑ d ∈ Finset.Icc 1 T, ((y / d : ℕ) : ℝ) * Real.log y := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact hle d
    _ ≤ ∑ d ∈ Finset.Icc 1 T, ((y : ℝ) / (d : ℝ)) * Real.log y := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact mul_le_mul_of_nonneg_right Nat.cast_div_le hlogy
    _ = (∑ d ∈ Finset.Icc 1 T, (y : ℝ) / (d : ℝ)) * Real.log y := by
        rw [Finset.sum_mul]
    _ ≤ ((y : ℝ) * (1 + Real.log T)) * Real.log y := by
        refine mul_le_mul_of_nonneg_right ?_ hlogy
        have hsplit : (∑ d ∈ Finset.Icc 1 T, (y : ℝ) / (d : ℝ))
            = (y : ℝ) * ∑ d ∈ Finset.Icc 1 T, 1 / (d : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left
          (Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log T) (by positivity)
    _ = (y : ℝ) * Real.log y * (1 + Real.log T) := by ring

/-- Type I bound for a non-principal character: with `C` the Polya--Vinogradov constant, the
`λ₂`-sum truncated at `y ≤ x` is at most `C·T·√q·log(2q+2)·log(2x+2)`. -/
lemma lambda2_charSum_bound_of_ne_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (x T y q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → 1 ≤ y → y ≤ x →
      ‖lambda2CharSum T y q χ‖
      ≤ C * (T : ℝ) * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (x : ℝ) + 2) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.charSum_logWeighted_range_le_polyaVinogradov
  refine ⟨C, hCpos, ?_⟩
  intro x T y q _ χ hχ hy hyx
  rw [lambda2_mul_char_eq_sum]
  have hBnn : 0 ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) := by
    have h1 := log_two_mul_add_two_nonneg q
    have h2 := log_two_mul_add_two_nonneg x
    positivity
  have hinner : ∀ d ∈ Finset.Icc 1 T,
      ‖∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * (χ (h : ZMod q) : ℂ)‖
        ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2) := by
    intro d _
    rcases Nat.eq_zero_or_pos (y / d) with h0 | hpos
    · rw [h0]
      simp only [show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty, norm_zero]
      exact hBnn
    · have h1 : 1 ≤ y / d := hpos
      have hpv := hC q χ hχ 1 (y / d) h1
      have hle : 2 * ((y / d : ℕ) : ℝ) + 2 ≤ 2 * (x : ℝ) + 2 := by
        have h2 : (y / d : ℕ) ≤ x := le_trans (Nat.div_le_self y d) hyx
        have h3 : ((y / d : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h2
        linarith
      have hlog : Real.log (2 * ((y / d : ℕ) : ℝ) + 2) ≤ Real.log (2 * (x : ℝ) + 2) :=
        Real.log_le_log (by positivity) hle
      have hcoef : 0 ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
        have h1 := log_two_mul_add_two_nonneg q
        positivity
      exact hpv.trans (mul_le_mul_of_nonneg_left hlog hcoef)
  calc ‖∑ d ∈ Finset.Icc 1 T,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (χ (d : ZMod q) : ℂ)
          * (∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * (χ (h : ZMod q) : ℂ))‖
      ≤ ∑ d ∈ Finset.Icc 1 T,
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * (χ (d : ZMod q) : ℂ)
            * (∑ h ∈ Finset.Icc 1 (y / d), ((Real.log (h : ℝ) : ℂ)) * (χ (h : ZMod q) : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 T,
          1 * 1 * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) * Real.log (2 * (x : ℝ) + 2)) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [norm_mul, norm_mul]
        have h1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 :=
          norm_moebius_cast_le_one d
        have h2 : ‖(χ (d : ZMod q) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h3 := hinner d hd
        have hab : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ * ‖(χ (d : ZMod q) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        exact mul_le_mul hab h3 (norm_nonneg _) (by positivity)
    _ = (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (x : ℝ) + 2)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        ring
    _ = C * (T : ℝ) * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)
          * Real.log (2 * (x : ℝ) + 2) := by ring

theorem vaughan_type1_lambda2_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
              * (χ (n : ZMod q) : ℂ)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 3 := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := lambda2_charSum_bound_of_ne_one
  refine ⟨max 2 C₂, lt_of_lt_of_le (by norm_num) (le_max_left (2:ℝ) C₂), ?_⟩
  intro x Q T hx hQ hT hTx
  have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hQ2 : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  set L : ℝ := Real.log ((x:ℝ)*(Q:ℝ)+2) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h4 : (4:ℝ) ≤ (x:ℝ)*(Q:ℝ) := by
      have h := mul_le_mul hx2 hQ2 (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg x)
      linarith
    have h6 : (6:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by linarith
    have he : Real.exp 1 ≤ 6 := by linarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 6 := Real.log_le_log (Real.exp_pos 1) he
      _ ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) := Real.log_le_log (by norm_num) h6
  have hLnn : 0 ≤ L := le_trans (by norm_num) hL1
  have hlogxL : Real.log (x:ℝ) ≤ L := by
    rw [hL]
    refine Real.log_le_log (by linarith : (0:ℝ) < (x:ℝ)) ?_
    have h := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (Q:ℝ) by linarith)
      (show (0:ℝ) ≤ (x:ℝ) by positivity)
    linarith
  have hlogTx : Real.log (T:ℝ) ≤ Real.log (x:ℝ) := by
    refine Real.log_le_log ?_ ?_
    · exact_mod_cast hT
    · exact_mod_cast hTx
  have hlogTL : Real.log (T:ℝ) ≤ L := hlogTx.trans hlogxL
  have hlogQ2L : Real.log (2*(Q:ℝ)+2) ≤ L := by
    rw [hL]
    refine Real.log_le_log (by positivity) ?_
    have h := mul_le_mul_of_nonneg_right hx2 (show (0:ℝ) ≤ (Q:ℝ) by positivity)
    linarith
  have hlogx2L : Real.log (2*(x:ℝ)+2) ≤ L := by
    rw [hL]
    refine Real.log_le_log (by positivity) ?_
    have h := mul_le_mul_of_nonneg_left hQ2 (show (0:ℝ) ≤ (x:ℝ) by positivity)
    linarith
  change (∑ q ∈ Finset.Icc 1 Q, lambda2Term x T q)
      ≤ max 2 C₂ * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ)) * L^3
  have hsplitIcc : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : (1:ℕ) ∉ Finset.Icc 2 Q := by simp [Finset.mem_Icc]
  -- the `q = 1` term
  have hF1 : lambda2Term x T 1 ≤ 2 * (x:ℝ) * L^2 := by
    rw [lambda2Term]
    have hcoef : (((1:ℕ) : ℝ) / ((1:ℕ).totient : ℝ)) = 1 := by
      rw [Nat.totient_one]; norm_num
    rw [hcoef, one_mul]
    have hterm : ∀ χ : DirichletCharacter ℂ 1, χ.IsPrimitive → lambda2CharSup x T 1 χ ≤ 2 * (x:ℝ) * L^2 := by
      intro χ _
      rw [lambda2CharSup]
      refine Real.sSup_le (fun z hz => ?_) (by positivity)
      obtain ⟨y, hy, rfl⟩ := hz
      have hb : ‖∑ n ∈ Finset.Icc 1 y,
            (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
              * (χ (n : ZMod 1) : ℂ)‖
          ≤ (y:ℝ) * Real.log y * (1 + Real.log T) := lambda2_charSum_level_one_le T y χ
      have hb2 : (y:ℝ) * Real.log y * (1 + Real.log T) ≤ 2 * (x:ℝ) * L^2 := by
        have hypos : (0:ℝ) < (y:ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy.1)
        have hyxr : (y:ℝ) ≤ (x:ℝ) := by exact_mod_cast hy.2
        have hlogy : Real.log (y:ℝ) ≤ L := (Real.log_le_log hypos hyxr).trans hlogxL
        have hlogy_nn : 0 ≤ Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast hy.1)
        have hlogT_nn : 0 ≤ Real.log (T:ℝ) := Real.log_nonneg (by exact_mod_cast hT)
        have hfac : (1 + Real.log (T:ℝ)) ≤ 2 * L := by linarith
        have hxL_nn : (0:ℝ) ≤ (x:ℝ) * L := by positivity
        calc (y:ℝ) * Real.log y * (1 + Real.log T)
            ≤ (x:ℝ) * L * (2 * L) := by
              refine mul_le_mul (mul_le_mul hyxr hlogy hlogy_nn (Nat.cast_nonneg x)) hfac
                (by linarith) ?_
              positivity
          _ = 2 * (x:ℝ) * L^2 := by ring
      exact le_trans hb hb2
    have hcard1 : (((@Finset.filter (DirichletCharacter ℂ 1) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ).card : ℕ) : ℝ) ≤ 1 := by
      have h2 := card_primitive_le_totient 1
      rw [Nat.totient_one] at h2
      exact_mod_cast h2
    calc (∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ 1) (fun χ => χ.IsPrimitive)
            (Classical.decPred _) Finset.univ), lambda2CharSup x T 1 χ)
        ≤ (((@Finset.filter (DirichletCharacter ℂ 1) (fun χ => χ.IsPrimitive)
            (Classical.decPred _) Finset.univ).card : ℕ) : ℝ) * (2 * (x:ℝ) * L^2) :=
          prim_char_sum_le_card_mul _ _ hterm (by positivity)
      _ ≤ 1 * (2 * (x:ℝ) * L^2) := mul_le_mul_of_nonneg_right hcard1 (by positivity)
      _ = 2 * (x:ℝ) * L^2 := by ring
  -- the `q ≥ 2` terms
  set Λ : ℝ := C₂ * (T:ℝ) * ((Q:ℝ) * Real.sqrt Q) * L^2 with hΛ
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]
    have h1 : (0:ℝ) ≤ (Q:ℝ) * Real.sqrt Q := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₂pos) (Nat.cast_nonneg T)) h1)
      (by positivity)
  have hFq : ∀ q ∈ Finset.Icc 2 Q, lambda2Term x T q ≤ Λ := by
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
    haveI hneq : NeZero q := ⟨by omega⟩
    rw [lambda2Term]
    have hBnn : 0 ≤ C₂ * (T:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2) := by
      have h1 := log_two_mul_add_two_nonneg q
      have h2 := log_two_mul_add_two_nonneg x
      positivity
    have hterm : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        lambda2CharSup x T q χ
          ≤ C₂ * (T:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2) := by
      intro χ hprim
      have hχne : χ ≠ 1 := by
        intro h1
        rw [h1] at hprim
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hprim
        omega
      rw [lambda2CharSup]
      refine Real.sSup_le (fun z hz => ?_) hBnn
      obtain ⟨y, hy, rfl⟩ := hz
      exact hC₂ x T y q χ hχne hy.1 hy.2
    have hcard : (((@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ).card : ℕ) : ℝ) ≤ (q.totient : ℝ) := by
      exact_mod_cast card_primitive_le_totient q
    have hsum_le : (∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
            (Classical.decPred _) Finset.univ), lambda2CharSup x T q χ)
        ≤ (q.totient : ℝ) * (C₂ * (T:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2)
            * Real.log (2*(x:ℝ)+2)) := by
      refine (prim_char_sum_le_card_mul _ _ hterm hBnn).trans ?_
      exact mul_le_mul_of_nonneg_right hcard hBnn
    have hcoef_nn : 0 ≤ (q:ℝ) / (q.totient : ℝ) := by positivity
    refine (mul_le_mul_of_nonneg_left hsum_le hcoef_nn).trans ?_
    have hφ : (q.totient : ℝ) ≠ 0 := by
      have hpos := Nat.totient_pos.mpr (by omega : 0 < q)
      exact_mod_cast hpos.ne'
    have heq : ((q:ℝ) / (q.totient:ℝ)) * ((q.totient:ℝ) * (C₂ * (T:ℝ) * Real.sqrt q
          * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2)))
        = (q:ℝ) * (C₂ * (T:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2)
          * Real.log (2*(x:ℝ)+2)) := by
      field_simp
    rw [heq]
    have h1 : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
    have h2 : Real.sqrt q ≤ Real.sqrt Q := Real.sqrt_le_sqrt h1
    have h3 : Real.log (2*(q:ℝ)+2) ≤ L := by
      have h31 : Real.log (2*(q:ℝ)+2) ≤ Real.log (2*(Q:ℝ)+2) := by
        refine Real.log_le_log (by positivity) ?_
        have : (q:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hqQ
        linarith
      exact h31.trans hlogQ2L
    have h4 : Real.log (2*(x:ℝ)+2) ≤ L := hlogx2L
    have h5 : (q:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2)
        ≤ (Q:ℝ) * Real.sqrt Q * L * L := by
      have hQQ : 0 ≤ (Q:ℝ) * Real.sqrt Q := by positivity
      have hstep1 : (q:ℝ) * Real.sqrt q ≤ (Q:ℝ) * Real.sqrt Q :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg q) (by positivity)
      have hstep2 : (q:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2)
          ≤ (Q:ℝ) * Real.sqrt Q * L :=
        mul_le_mul hstep1 h3 (log_two_mul_add_two_nonneg q) hQQ
      exact mul_le_mul hstep2 h4 (log_two_mul_add_two_nonneg x) (by positivity)
    calc (q:ℝ) * (C₂ * (T:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2))
        = ((q:ℝ) * Real.sqrt q * Real.log (2*(q:ℝ)+2) * Real.log (2*(x:ℝ)+2))
            * (C₂ * (T:ℝ)) := by ring
      _ ≤ ((Q:ℝ) * Real.sqrt Q * L * L) * (C₂ * (T:ℝ)) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = Λ := by rw [hΛ]; ring
  have hcard2 : (((Finset.Icc 2 Q).card : ℕ) : ℝ) ≤ (Q:ℝ) := by
    rw [Nat.card_Icc]
    have : Q + 1 - 2 ≤ Q := by omega
    exact_mod_cast this
  have hsum2 : ∑ q ∈ Finset.Icc 2 Q, lambda2Term x T q ≤ (Q:ℝ) * Λ := by
    refine (Finset.sum_le_card_nsmul _ _ Λ hFq).trans ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard2 hΛnn
  have hQ5 : (Q:ℝ)^(5/2:ℝ) = (Q:ℝ) * ((Q:ℝ) * Real.sqrt Q) := by
    have h3 : (Q:ℝ)^(3/2:ℝ) = (Q:ℝ) * Real.sqrt Q := by
      rw [Real.sqrt_eq_rpow]
      calc (Q:ℝ)^(3/2:ℝ) = (Q:ℝ)^((1:ℝ) + 1/2) := by norm_num
        _ = (Q:ℝ)^(1:ℝ) * (Q:ℝ)^(1/2:ℝ) := Real.rpow_add (by linarith) 1 (1/2)
        _ = (Q:ℝ) * (Q:ℝ)^(1/2:ℝ) := by rw [Real.rpow_one]
    calc (Q:ℝ)^(5/2:ℝ) = (Q:ℝ)^((1:ℝ) + 3/2) := by norm_num
      _ = (Q:ℝ)^(1:ℝ) * (Q:ℝ)^(3/2:ℝ) := Real.rpow_add (by linarith) 1 (3/2)
      _ = (Q:ℝ) * ((Q:ℝ) * Real.sqrt Q) := by rw [Real.rpow_one, h3]
  have hΛeq : (Q:ℝ) * Λ = C₂ * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2 := by
    rw [hΛ, hQ5]
    ring
  have hsum2' : ∑ q ∈ Finset.Icc 2 Q, lambda2Term x T q
      ≤ C₂ * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2 := by
    refine hsum2.trans ?_
    rw [hΛeq]
  have htot : lambda2Term x T 1 + ∑ q ∈ Finset.Icc 2 Q, lambda2Term x T q
      ≤ max 2 C₂ * ((x:ℝ) + (T:ℝ) * (Q:ℝ)^(5/2:ℝ)) * L^3 := by
    have hA : lambda2Term x T 1 + ∑ q ∈ Finset.Icc 2 Q, lambda2Term x T q
        ≤ 2 * (x:ℝ) * L^2 + C₂ * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2 := by linarith
    refine hA.trans ?_
    have hL23 : L^2 ≤ L^3 := by
      have h := mul_le_mul_of_nonneg_left hL1 (show (0:ℝ) ≤ L^2 by positivity)
      have he : L^3 = L^2 * L := by ring
      calc L^2 = L^2 * 1 := by ring
        _ ≤ L^2 * L := h
        _ = L^3 := he.symm
    have hK2 : (2:ℝ) ≤ max 2 C₂ := le_max_left _ _
    have hKC : C₂ ≤ max 2 C₂ := le_max_right _ _
    have hxnn : (0:ℝ) ≤ (x:ℝ) := by positivity
    have h2' : C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ)) ≤ max 2 C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ)) :=
      mul_le_mul_of_nonneg_right hKC (by positivity)
    have h1' : 2 * (x:ℝ) ≤ max 2 C₂ * (x:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hK2 hxnn
      linarith
    have hsum' : 2 * (x:ℝ) + C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))
        ≤ max 2 C₂ * (x:ℝ) + max 2 C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ)) := by linarith
    have hstep1 : (2 * (x:ℝ) + C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))) * L^2
        ≤ (max 2 C₂ * (x:ℝ) + max 2 C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))) * L^2 :=
      mul_le_mul_of_nonneg_right hsum' (by positivity)
    have heq1 : (max 2 C₂ * (x:ℝ) + max 2 C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))) * L^2
        = max 2 C₂ * ((x:ℝ) + (T:ℝ) * (Q:ℝ)^(5/2:ℝ)) * L^2 := by ring
    have hstep2 : (max 2 C₂ * (x:ℝ) + max 2 C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))) * L^2
        ≤ max 2 C₂ * ((x:ℝ) + (T:ℝ) * (Q:ℝ)^(5/2:ℝ)) * L^3 := by
      rw [heq1]
      have hXnn : (0:ℝ) ≤ (x:ℝ) + (T:ℝ) * (Q:ℝ)^(5/2:ℝ) := by positivity
      have hKnn : (0:ℝ) ≤ max 2 C₂ := by positivity
      exact mul_le_mul_of_nonneg_left hL23 (mul_nonneg hKnn hXnn)
    have hstart : 2 * (x:ℝ) * L^2 + C₂ * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2
        = (2 * (x:ℝ) + C₂ * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ))) * L^2 := by ring
    rw [hstart]
    exact hstep1.trans hstep2
  rw [hsplitIcc, Finset.sum_insert hnotmem]
  exact htot

end Commons.NumberTheory.BombieriVinogradov
