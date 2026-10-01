import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
import Submission.Work.LinnikAreas.Density4.prime_log_sum_repr

/-!
# Partial summation over primes, with square-log error

`Σ_{y < p ≤ x} log p · log(p/y) = x·log(x/y) + O(x)`, uniformly for `1 ≤ y ≤ x`.

Ingredients (all proved in this workspace):

* `Work.LinnikAreas.Density4.prime_log_sum_repr` (Abel summation over primes): the sum equals
  `θ(⌊x⌋)·log(x/y) − ∫_y^x θ(t)/t dt`.
* PNT for `θ` with log-power error,
  `Commons.NumberTheory.Zeta.psi_sub_id_powLog_real` together with
  `Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le` (see
  `theta_sub_id_powlog_aux` below; the same statement is available as the public
  `Work.LinnikAreas.Density4.theta_sub_id_powlog`).

Then `|θ(⌊x⌋) − x|·log(x/y) = O(x)` (take exponent `2`; `θ(⌊x⌋) = θ x`), while
`|∫_y^x θ(t)/t| ≤ (log 4 + 4)(x − y) = O(x)` by Chebyshev's elementary bound
`θ(t) ≤ (log 4 + 4)·t`.  Small `x` are handled crudely; the existential constant absorbs the
bounded range.
-/

namespace Work.LinnikAreas.Density4

open MeasureTheory intervalIntegral Finset


/-- PNT for `θ` with log-power error, derived from PNT for `ψ` with log-power error
(`psi_sub_id_powLog_real`) together with the classical estimate `ψ − θ ≤ 1.099 √·`
(`psi_sub_theta_eventually_le`).  This is a private copy of
`Work.LinnikAreas.Density4.theta_sub_id_powlog`, kept here so that the main result is
self-contained. -/
private lemma theta_sub_id_powlog_aux (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ t : ℝ, x₀ ≤ t →
      |Chebyshev.theta t - t| ≤ t / (Real.log t) ^ A := by
  obtain ⟨x₁, hx₁⟩ :=
    Commons.NumberTheory.Zeta.psi_sub_id_powLog_real (A + 1) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le
  have hlittle : (fun t : ℝ => Real.log t ^ A) =o[Filter.atTop]
      (fun t : ℝ => t ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) A (by norm_num)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    (Asymptotics.isLittleO_iff.mp hlittle (by norm_num : (0 : ℝ) < 1 / 2.199))
  refine ⟨max (max x₁ (max (Real.exp 4) T)) ((N : ℝ) + 1), ?_, ?_⟩
  · have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    have h1 : Real.exp 4 ≤ max (max x₁ (max (Real.exp 4) T)) ((N : ℝ) + 1) :=
      le_trans (le_trans (le_max_left (Real.exp 4) T) (le_max_right x₁ _)) (le_max_left _ _)
    linarith
  · intro t ht
    have hx₁t : x₁ ≤ t := le_trans (le_trans (le_max_left x₁ _) (le_max_left _ _)) ht
    have hexp4t : Real.exp 4 ≤ t :=
      le_trans (le_trans (le_trans (le_max_left (Real.exp 4) T) (le_max_right x₁ _))
        (le_max_left _ _)) ht
    have hTt : T ≤ t :=
      le_trans (le_trans (le_trans (le_max_right (Real.exp 4) T) (le_max_right x₁ _))
        (le_max_left _ _)) ht
    have ht1 : 1 ≤ t := by
      have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith
    have htpos : 0 < t := by linarith
    have hlog4 : 4 ≤ Real.log t := by
      rw [← Real.log_exp 4]
      exact Real.log_le_log (Real.exp_pos 4) hexp4t
    have hlogpos : 0 < Real.log t := by linarith
    have hlogApos : 0 < (Real.log t) ^ A := Real.rpow_pos_of_pos hlogpos A
    have hψ := hx₁ t hx₁t
    have htN : (N : ℝ) + 1 ≤ t := le_trans (le_max_right _ _) ht
    have hfl : N ≤ ⌊t⌋₊ := Nat.le_floor (by linarith : (N : ℝ) ≤ t)
    have hsub : Chebyshev.psi t - Chebyshev.theta t ≤ 1.099 * Real.sqrt t := by
      rw [Chebyshev.psi_eq_psi_coe_floor t, Chebyshev.theta_eq_theta_coe_floor t]
      refine (hN ⌊t⌋₊ hfl).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast Nat.floor_le (le_of_lt htpos))) (by norm_num)
    have hsqrt : (Real.log t) ^ A ≤ (1 / 2.199) * Real.sqrt t := by
      have h := hT t hTt
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hlogpos) A),
        Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt htpos) (1 / 2 : ℝ))] at h
      rwa [Real.sqrt_eq_rpow]
    have hkey : 2.198 * Real.sqrt t ≤ t / (Real.log t) ^ A := by
      rw [le_div_iff₀ hlogApos]
      have haux : 2.198 * (Real.log t) ^ A ≤ Real.sqrt t := by nlinarith [hsqrt]
      nlinarith [haux, Real.sq_sqrt (le_of_lt htpos), Real.sqrt_nonneg t, hlogApos]
    have hsqrtle : 1.099 * Real.sqrt t ≤ (1 / 2) * (t / (Real.log t) ^ A) := by linarith
    have hψterm : t / (Real.log t) ^ (A + 1) ≤ (1 / 2) * (t / (Real.log t) ^ A) := by
      rw [Real.rpow_add hlogpos A 1, Real.rpow_one]
      have hdiv : 1 / Real.log t ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith)
      calc t / ((Real.log t) ^ A * Real.log t)
          = (t / (Real.log t) ^ A) * (1 / Real.log t) := by field_simp
        _ ≤ (t / (Real.log t) ^ A) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = (1 / 2) * (t / (Real.log t) ^ A) := by ring
    have hsplit : |Chebyshev.theta t - t|
        ≤ (Chebyshev.psi t - Chebyshev.theta t) + |Chebyshev.psi t - t| := by
      have hθψ : Chebyshev.theta t ≤ Chebyshev.psi t := Chebyshev.theta_le_psi t
      have hid : Chebyshev.theta t - t
          = (Chebyshev.theta t - Chebyshev.psi t) + (Chebyshev.psi t - t) := by ring
      rw [hid]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_of_nonpos (by linarith)]
      ring
    calc |Chebyshev.theta t - t|
        ≤ (Chebyshev.psi t - Chebyshev.theta t) + |Chebyshev.psi t - t| := hsplit
      _ ≤ (1 / 2) * (t / (Real.log t) ^ A) + (1 / 2) * (t / (Real.log t) ^ A) := by
          linarith [hsub, hsqrtle, hψ, hψterm]
      _ = t / (Real.log t) ^ A := by ring


theorem prime_log_gap_sum : ∃ C : ℝ, 0 < C ∧ ∀ (y x : ℝ), 1 ≤ y → y ≤ x →
    |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
        Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) - x * Real.log (x / y)| ≤ C * x := by
  obtain ⟨x₀, hx₀1, hθbd⟩ := theta_sub_id_powlog_aux 2 (by norm_num)
  set N : ℕ := ⌈max x₀ (Real.exp 4)⌉₊ with hNdef
  set X : ℝ := (N : ℝ) + 1 with hXdef
  have hNge : max x₀ (Real.exp 4) ≤ (N : ℝ) := by
    rw [hNdef]; exact Nat.le_ceil _
  have hx₀X : x₀ ≤ X := by
    have h1 : x₀ ≤ max x₀ (Real.exp 4) := le_max_left _ _
    rw [hXdef]; linarith
  have hexpX : Real.exp 4 ≤ X := by
    have h1 : Real.exp 4 ≤ max x₀ (Real.exp 4) := le_max_right _ _
    rw [hXdef]; linarith
  have hX1 : 1 ≤ X := by
    have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hXpos : 0 < X := by linarith
  have hlogX : 4 ≤ Real.log X := by
    have hpos : 0 < Real.exp 4 := Real.exp_pos 4
    calc (4 : ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
      _ ≤ Real.log X := Real.log_le_log hpos hexpX
  have hlogXpos : 0 < Real.log X := by linarith
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4le3 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    linarith
  have hlog4le7 : Real.log 4 + 4 ≤ 7 := by linarith
  set C₀ : ℝ := max 10 ((Real.log 4 + 4 + 1) * Real.log (X + 1)) with hC₀def
  refine ⟨C₀, ?_, ?_⟩
  · rw [hC₀def]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 10) (le_max_left _ _)
  · intro y x hy hyx
    have hxpos : 0 < x := by linarith
    have hypos : 0 < y := by linarith
    have hlogxy : 0 ≤ Real.log (x / y) :=
      Real.log_nonneg (by rw [le_div_iff₀ hypos]; linarith)
    have hlogxy_le_x : Real.log (x / y) ≤ Real.log x := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hypos]
      exact le_mul_of_one_le_right (le_of_lt hxpos) hy
    have hC₀x : C₀ * x = max 10 ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x := by rw [hC₀def]
    rw [hC₀x]
    by_cases hbig : X + 1 ≤ x
    · -- ============ Case 1: X + 1 ≤ x
      have hxX : X ≤ x := by linarith
      have hlogx4 : 4 ≤ Real.log x := le_trans hlogX (Real.log_le_log hXpos hxX)
      have hlogxpos : 0 < Real.log x := by linarith
      have hθx : Chebyshev.theta (⌊x⌋₊) = Chebyshev.theta x :=
        (Chebyshev.theta_eq_theta_coe_floor x).symm
      have hθbdx : |Chebyshev.theta (⌊x⌋₊) - x| ≤ x / (Real.log x) ^ (2 : ℝ) := by
        rw [hθx]; exact hθbd x (le_trans hx₀X hxX)
      have hint : |∫ t in y..x, Chebyshev.theta t / t| ≤ (Real.log 4 + 4) * (x - y) := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
          (C := Real.log 4 + 4) (f := fun t : ℝ => Chebyshev.theta t / t) ?_
        · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)] at h
          exact h
        · intro t ht
          have htmem : t ∈ Set.Ioc y x := by
            have h' := ht
            rw [Set.uIoc_of_le hyx] at h'
            exact h'
          have htpos : 0 < t := by linarith [htmem.1]
          rw [Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (Chebyshev.theta_nonneg t) (le_of_lt htpos)),
            div_le_iff₀ htpos]
          exact (Chebyshev.theta_le_psi t).trans
            (Chebyshev.psi_le_const_mul_self (le_of_lt htpos))
      rw [prime_log_sum_repr hy hyx]
      have hring : Chebyshev.theta ⌊x⌋₊ * Real.log (x / y)
            - (∫ t in y..x, Chebyshev.theta t / t) - x * Real.log (x / y)
          = (Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y)
            - ∫ t in y..x, Chebyshev.theta t / t := by ring
      rw [hring]
      have hsplit : |(Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y)
            - ∫ t in y..x, Chebyshev.theta t / t|
          ≤ |(Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y)|
            + |∫ t in y..x, Chebyshev.theta t / t| := by
        have h := abs_add_le ((Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y))
          (-(∫ t in y..x, Chebyshev.theta t / t))
        simpa [sub_eq_add_neg, abs_neg] using h
      have hterm1 : |Chebyshev.theta ⌊x⌋₊ - x| * Real.log (x / y) ≤ x := by
        have h1 : |Chebyshev.theta ⌊x⌋₊ - x| * Real.log (x / y)
            ≤ (x / (Real.log x) ^ (2 : ℝ)) * Real.log x := by
          refine mul_le_mul hθbdx hlogxy_le_x hlogxy ?_
          positivity
        refine h1.trans ?_
        rw [Real.rpow_two, div_mul_eq_mul_div,
          div_le_iff₀ (by positivity : (0:ℝ) < (Real.log x) ^ 2)]
        have hsq : Real.log x ≤ (Real.log x) ^ 2 := by nlinarith [hlogx4]
        exact mul_le_mul_of_nonneg_left hsq (le_of_lt hxpos)
      have hterm2 : |∫ t in y..x, Chebyshev.theta t / t| ≤ (Real.log 4 + 4) * x := by
        refine hint.trans ?_
        have hLnn : 0 ≤ Real.log 4 + 4 := by linarith
        exact mul_le_mul_of_nonneg_left (by linarith) hLnn
      have hsum2 : x + (Real.log 4 + 4) * x
          ≤ max 10 ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x := by
        have h1 : x + (Real.log 4 + 4) * x = (1 + (Real.log 4 + 4)) * x := by ring
        rw [h1]
        have h2 : (1 + (Real.log 4 + 4)) ≤ 10 := by linarith
        exact mul_le_mul_of_nonneg_right h2 (le_of_lt hxpos) |>.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hxpos))
      calc |(Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y)
            - ∫ t in y..x, Chebyshev.theta t / t|
          ≤ |(Chebyshev.theta ⌊x⌋₊ - x) * Real.log (x / y)|
            + |∫ t in y..x, Chebyshev.theta t / t| := hsplit
        _ = |Chebyshev.theta ⌊x⌋₊ - x| * Real.log (x / y)
            + |∫ t in y..x, Chebyshev.theta t / t| := by
              rw [abs_mul, abs_of_nonneg hlogxy]
        _ ≤ x + (Real.log 4 + 4) * x := add_le_add hterm1 hterm2
        _ ≤ max 10 ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x := hsum2
    · -- ============ Case 2: x < X + 1
      have hxX1 : x < X + 1 := not_le.mp hbig
      have hlogx_le : Real.log x ≤ Real.log (X + 1) := Real.log_le_log hxpos (by linarith)
      have hlogX1nn : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
      have hMle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
      have hθM : Chebyshev.theta (⌊x⌋₊) ≤ (Real.log 4 + 4) * x := by
        have h1 : Chebyshev.theta (⌊x⌋₊) ≤ (Real.log 4 + 4) * (⌊x⌋₊ : ℝ) :=
          (Chebyshev.theta_le_psi _).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))
        exact h1.trans (mul_le_mul_of_nonneg_left hMle (by linarith))
      have hsub : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)))
          ⊆ (⌊x⌋₊).primesLE := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp
        exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2.1⟩
      have hsum_le :
          (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
            Real.log (p : ℝ)) ≤ Chebyshev.theta (⌊x⌋₊) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log]
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i hi _
        exact Real.log_nonneg (by
          have h2 : 2 ≤ i := (Nat.mem_primesLE.mp hi).2.two_le
          exact_mod_cast (by omega : 1 ≤ i))
      have hSle :
          (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
            Real.log (p : ℝ) * Real.log ((p : ℝ) / y))
            ≤ Real.log (x / y) * Chebyshev.theta (⌊x⌋₊) := by
        calc (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / y))
            ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
                Real.log (p : ℝ) * Real.log (x / y) := by
              refine Finset.sum_le_sum ?_
              intro p hp
              simp only [Finset.mem_filter, Finset.mem_Icc] at hp
              have hp_le : (p : ℝ) ≤ x := le_trans (by exact_mod_cast hp.1.2) hMle
              have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
                have h2 : 2 ≤ p := hp.2.1.two_le
                exact_mod_cast (by omega : 1 ≤ p))
              have hle : Real.log ((p : ℝ) / y) ≤ Real.log (x / y) :=
                Real.log_le_log (div_pos (by exact_mod_cast hp.2.1.pos) hypos)
                  (div_le_div_of_nonneg_right hp_le (le_of_lt hypos))
              exact mul_le_mul_of_nonneg_left hle hlogp
          _ = Real.log (x / y) * (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
                (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)), Real.log (p : ℝ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun p _ => by ring)
          _ ≤ Real.log (x / y) * Chebyshev.theta (⌊x⌋₊) :=
              mul_le_mul_of_nonneg_left hsum_le hlogxy
      have hSnn : 0 ≤ (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
            Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) := by
        refine Finset.sum_nonneg ?_
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp
        refine mul_nonneg (Real.log_nonneg (by
          have h2 : 2 ≤ p := hp.2.1.two_le
          exact_mod_cast (by omega : 1 ≤ p))) ?_
        refine Real.log_nonneg ?_
        rw [le_div_iff₀ hypos]
        simpa using le_of_lt hp.2.2
      have h1 : |(∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) - x * Real.log (x / y)|
            ≤ (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
              (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) + x * Real.log (x / y) := by
        have h := abs_add_le (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter
            (fun p => Nat.Prime p ∧ (y : ℝ) < (p : ℝ)),
            Real.log (p : ℝ) * Real.log ((p : ℝ) / y)) (-(x * Real.log (x / y)))
        simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg hSnn,
          abs_of_nonneg (mul_nonneg (le_of_lt hxpos) hlogxy)] using h
      have h2 : Real.log (x / y) * Chebyshev.theta (⌊x⌋₊) + x * Real.log (x / y)
            ≤ ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x := by
        have hlogxy_le_X : Real.log (x / y) ≤ Real.log (X + 1) := le_trans hlogxy_le_x hlogx_le
        have ha : Real.log (x / y) * Chebyshev.theta (⌊x⌋₊)
            ≤ Real.log (X + 1) * ((Real.log 4 + 4) * x) := by
          refine mul_le_mul hlogxy_le_X hθM (Chebyshev.theta_nonneg _) hlogX1nn
        have hb : x * Real.log (x / y) ≤ x * Real.log (X + 1) :=
          mul_le_mul_of_nonneg_left hlogxy_le_X (le_of_lt hxpos)
        have key : Real.log (X + 1) * ((Real.log 4 + 4) * x) + x * Real.log (X + 1)
            = ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x := by ring
        linarith [ha, hb, key.le, key.ge]
      have h3 : ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x
            ≤ max 10 ((Real.log 4 + 4 + 1) * Real.log (X + 1)) * x :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hxpos)
      linarith [h1, hSle, h2, h3]



end Work.LinnikAreas.Density4
