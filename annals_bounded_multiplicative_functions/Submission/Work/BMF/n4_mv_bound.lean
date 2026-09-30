import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.tuple_setup
import Submission.Work.BMF.n4_defs
import Submission.Work.BMF.n4_mv_defs
import Submission.Work.BMF.n4_sum_normSq_mvCoeff_le
import Submission.Work.BMF.n4_log_term_bound
import Submission.Work.BMF.n4_card_tup_le_pi0
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_mean_value

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N4: the mean-value bound for the `(2ℓ-2)`-th moment of the prime–character sum

We prove `Work.BMF.n4_mv_bound`.  For `m = ℓ - 1 ≥ 1` the `m`-th power of the prime–character
sum expands, by `sum_tup_char_cpow` (`n4_defs.lean`) and the fibre decomposition
`n4_sum_mvCoeff_eq_tup_sum`, into the Dirichlet polynomial `Σ_{n ≤ ⌊(2P)^m⌋} a_n n^{it}` with
grouped coefficients `a_n = mvCoeff P q χ m n`.  Hence
`‖Σ_{p ∈ admP} χ(p) p^{it}‖^{2m} = ‖Σ_{n ≤ N} a_n n^{it}‖²` pointwise and the mean value
theorem `dirichlet_mean_value` plus the fibre bound `fiber_card_le` (for the `ℓ²` mass of the
coefficients) and `primesIn_card_le_pi0` (for the number of admissible primes) give the claim.
-/

namespace Work.BMF

open Finset Real Complex
open scoped BigOperators

/-! ## A one-dimensional interval-integral monotonicity lemma -/

theorem n4_intervalIntegral_mono_of_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ t, 0 ≤ f t) :
    ∀ T : ℝ, 0 ≤ T → T ≤ 1 → ∫ t in (-T)..T, f t ≤ ∫ t in (-1)..1, f t := by
  intro T hT hT1
  have hInt : IntervalIntegrable f MeasureTheory.volume (-1) 1 := hf.intervalIntegrable (-1) 1
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hT1
    (Filter.Eventually.of_forall (fun x => h0 x)) hInt

/-! ## Continuity of the prime–character sum -/

lemma continuous_cpow_I_mul_nat {n : ℕ} (hn : 1 ≤ n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (Complex.I * t) := by
  have h : (fun t : ℝ => (n : ℂ) ^ (Complex.I * t))
      = fun t : ℝ => Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I) := by
    funext t
    rw [Complex.cpow_def_of_ne_zero (by norm_cast; omega), ← Complex.natCast_log]
    congr 1
    push_cast
    ring
  rw [h]
  fun_prop

lemma continuous_psum (P : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ => psum P q χ t := by
  unfold psum
  refine continuous_finsetSum _ (fun p hp => ?_)
  have hprime : p.Prime := by
    have h1 : p ∈ (primesIn P (2*P)).filter (fun p => ¬ p ∣ q) := by simpa [admP] using hp
    have h2 : p ∈ primesIn P (2*P) := (Finset.mem_filter.mp h1).1
    have h3 : p ∈ (natIcc P (2*P)).filter Nat.Prime := by simpa [primesIn] using h2
    exact (Finset.mem_filter.mp h3).2
  exact continuous_const.mul (continuous_cpow_I_mul_nat hprime.one_le)

/-! ## The two algebraic identities -/

/-- The `m`-th power of the prime–character sum, expanded over `m`-tuples. -/
lemma n4_pow_eq_tup_sum {P : ℝ} (hP : 0 ≤ P) (q m : ℕ)
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    psum P q χ t ^ m
      = ∑ v ∈ tup P q m,
          (∏ i, χ ((v i : ℕ) : ZMod q)) * ((tprod v : ℕ) : ℂ) ^ (Complex.I * t) := by
  rw [← sum_tup_char_cpow P q m hP χ t]
  exact Finset.sum_congr rfl (fun v _ => by rw [tprod, Nat.cast_prod, map_prod])

/-- The fibre decomposition: the grouped coefficients form the same Dirichlet polynomial. -/
lemma n4_sum_mvCoeff_eq_tup_sum {P : ℝ} {q m N : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hN : ∀ v ∈ tup P q m, tprod v ≤ N) :
    ∑ n ∈ Finset.range (N + 1), mvCoeff P q χ m n * ((n : ℂ) ^ (Complex.I * t))
      = ∑ v ∈ tup P q m,
          (∏ i, χ ((v i : ℕ) : ZMod q)) * ((tprod v : ℕ) : ℂ) ^ (Complex.I * t) := by
  classical
  have hmaps : ∀ v ∈ tup P q m, tprod v ∈ Finset.range (N + 1) := fun v hv =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hN v hv))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun v => (∏ i, χ ((v i : ℕ) : ZMod q)) * ((tprod v : ℕ) : ℂ) ^ (Complex.I * t))]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [mvCoeff_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [(Finset.mem_filter.mp hv).2]

/-! ## The mean-value bound -/

theorem n4_mv_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P : ℝ), P₀ ≤ P → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (T : ℝ),
      0 ≤ T →
      ∫ t in (-T)..T, ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2 * ℓ - 2)
        ≤ C * (T + P ^ (ℓ - 1) * Real.log P) * pi0 P ^ (ℓ - 1) := by
  rcases eq_or_lt_of_le hℓ with h1 | h2
  · -- `ℓ = 1`: the integrand is identically `1` and the claim reads `2T ≤ C (T + log P)`.
    obtain rfl : ℓ = 1 := h1.symm
    refine ⟨2, 1, by norm_num, ?_⟩
    intro P hP q χ T hT
    have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
    have hfun : (fun t : ℝ =>
          ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2 * 1 - 2))
        = fun _ : ℝ => (1 : ℝ) := by
      funext t
      rw [show (2 * 1 - 2 : ℕ) = 0 from rfl]
      simp
    have hP0 : P ^ (1 - 1 : ℕ) = 1 := by
      rw [show (1 - 1 : ℕ) = 0 from rfl]; simp
    have hpi0 : pi0 P ^ (1 - 1 : ℕ) = 1 := by
      rw [show (1 - 1 : ℕ) = 0 from rfl]; simp
    rw [hfun, intervalIntegral.integral_const, hP0, hpi0]
    simp only [smul_eq_mul, mul_one, one_mul]
    nlinarith [hlog, hT]
  · -- `ℓ ≥ 2`: expand the `m = ℓ - 1`-st power and apply the mean value theorem.
    set m : ℕ := ℓ - 1 with hm_def
    have hm1 : 1 ≤ m := by omega
    have hexp : 2 * ℓ - 2 = 2 * m := by omega
    obtain ⟨C₂, hC₂pos, hmean⟩ := Commons.NumberTheory.DirichletPolynomial.dirichlet_mean_value
    obtain ⟨Cc, Pc, hCcpos, _hPc1, hcard⟩ := n4_card_tup_le_pi0
    obtain ⟨Cd, Pd, hCdpos, _hPd1, hlogb⟩ := n4_log_term_bound m
    refine ⟨C₂ * ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * (1 + Cd),
            max (max Pc Pd) (max ((2:ℝ)^m) (Real.exp 1)), ?_, ?_⟩
    · have hK : (0:ℝ) < ((((m+1)^m : ℕ)) : ℝ) := by
        have h : (0:ℕ) < (m+1)^m := pow_pos (Nat.succ_pos m) m
        exact_mod_cast h
      have hCc : (0:ℝ) < Cc ^ m := pow_pos hCcpos m
      have hCd : (0:ℝ) < 1 + Cd := by linarith
      exact mul_pos (mul_pos (mul_pos hC₂pos hK) hCc) hCd
    · intro P hP q χ T hT
      have hPc : Pc ≤ P := le_trans (le_trans (le_max_left Pc Pd)
        (le_max_left (max Pc Pd) (max ((2:ℝ)^m) (Real.exp 1)))) hP
      have hPd : Pd ≤ P := le_trans (le_trans (le_max_right Pc Pd)
        (le_max_left (max Pc Pd) (max ((2:ℝ)^m) (Real.exp 1)))) hP
      have hP2m : (2:ℝ)^m ≤ P := le_trans (le_trans (le_max_left ((2:ℝ)^m) (Real.exp 1))
        (le_max_right (max Pc Pd) (max ((2:ℝ)^m) (Real.exp 1)))) hP
      have hPe : Real.exp 1 ≤ P := le_trans (le_trans (le_max_right ((2:ℝ)^m) (Real.exp 1))
        (le_max_right (max Pc Pd) (max ((2:ℝ)^m) (Real.exp 1)))) hP
      have hP2 : (2:ℝ) ≤ P := le_trans (le_of_lt Real.exp_one_gt_two) hPe
      have hP1 : (1:ℝ) ≤ P := by linarith
      have hPpos : (0:ℝ) < P := by linarith
      have hlog1 : 1 ≤ Real.log P := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) hPe
      have hlog0 : 0 ≤ Real.log P := le_trans zero_le_one hlog1
      set N : ℕ := ⌊(2*P)^m⌋₊ with hN_def
      have hNval : ((N : ℕ) : ℝ) = ((⌊(2*P)^m⌋₊ : ℕ) : ℝ) := by rw [hN_def]
      have htv : ∀ v ∈ tup P q m, tprod v ≤ N := by
        intro v hv
        rw [hN_def]
        exact Nat.le_floor (tprod_le (le_of_lt hPpos) hv)
      set a : ℕ → ℂ := mvCoeff P q χ m with ha_def
      set S : ℝ := ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2 with hS_def
      have hS0 : 0 ≤ S := by
        rw [hS_def]
        exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
      have hSbound : S ≤ ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * pi0 P ^ m := by
        have h1 := n4_sum_normSq_mvCoeff_le hP1 hm1 hP2m χ htv
        have h2 := hcard P hPc q m
        have hK : (0:ℝ) ≤ ((((m+1)^m : ℕ)) : ℝ) := by positivity
        rw [hS_def]
        calc ∑ n ∈ Finset.range (N + 1), ‖a n‖ ^ 2
            ≤ ((((m+1)^m : ℕ)) : ℝ) * ((tup P q m).card : ℝ) := h1
          _ ≤ ((((m+1)^m : ℕ)) : ℝ) * (Cc ^ m * pi0 P ^ m) :=
              mul_le_mul_of_nonneg_left h2 hK
          _ = ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * pi0 P ^ m := by ring
      have hX0 : 0 ≤ P ^ m * Real.log P := by
        have h := pow_nonneg (le_of_lt hPpos) m
        positivity
      have hX1 : 1 ≤ P ^ m * Real.log P := by
        have h1m : (1:ℝ) ≤ P ^ m := one_le_pow₀ hP1
        nlinarith
      have hNlog : (N : ℝ) * Real.log (2 + (N : ℝ)) ≤ Cd * (P ^ m * Real.log P) := by
        calc (N : ℝ) * Real.log (2 + (N : ℝ))
            = ((⌊(2*P)^m⌋₊ : ℕ) : ℝ) * Real.log (2 + ((⌊(2*P)^m⌋₊ : ℕ) : ℝ)) := by rw [hNval]
          _ ≤ Cd * P ^ m * Real.log P := hlogb P hPd
          _ = Cd * (P ^ m * Real.log P) := by ring
      have hfinish : C₂ * (max T 1 + (N : ℝ) * Real.log (2 + (N : ℝ))) * S
          ≤ (C₂ * ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * (1 + Cd))
              * (T + P ^ m * Real.log P) * pi0 P ^ m := by
        have hmax : max T 1 ≤ T + P ^ m * Real.log P :=
          max_le (le_add_of_nonneg_right hX0)
            (le_trans hX1 (le_add_of_nonneg_left hT))
        have hstep : max T 1 + (N : ℝ) * Real.log (2 + (N : ℝ))
            ≤ (1 + Cd) * (T + P ^ m * Real.log P) := by
          have h1 : Cd * (P ^ m * Real.log P) ≤ Cd * (T + P ^ m * Real.log P) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hT) (le_of_lt hCdpos)
          calc max T 1 + (N : ℝ) * Real.log (2 + (N : ℝ))
              ≤ (T + P ^ m * Real.log P) + Cd * (P ^ m * Real.log P) := add_le_add hmax hNlog
            _ ≤ (T + P ^ m * Real.log P) + Cd * (T + P ^ m * Real.log P) := add_le_add le_rfl h1
            _ = (1 + Cd) * (T + P ^ m * Real.log P) := by ring
        have h3 : C₂ * (max T 1 + (N : ℝ) * Real.log (2 + (N : ℝ)))
            ≤ C₂ * ((1 + Cd) * (T + P ^ m * Real.log P)) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hC₂pos)
        have hfac : (0:ℝ) ≤ C₂ * ((1 + Cd) * (T + P ^ m * Real.log P)) :=
          mul_nonneg (le_of_lt hC₂pos) (mul_nonneg (by linarith) (by linarith))
        calc C₂ * (max T 1 + (N : ℝ) * Real.log (2 + (N : ℝ))) * S
            ≤ (C₂ * ((1 + Cd) * (T + P ^ m * Real.log P)))
                * (((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * pi0 P ^ m) :=
              mul_le_mul h3 hSbound hS0 hfac
          _ = (C₂ * ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * (1 + Cd))
                * (T + P ^ m * Real.log P) * pi0 P ^ m := by ring
      have hpt : ∀ t : ℝ,
          ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2 * m)
          = ‖∑ n ∈ Finset.range (N + 1), a n * ((n : ℂ) ^ (Complex.I * t))‖ ^ 2 := by
        intro t
        change ‖psum P q χ t‖ ^ (2 * m)
          = ‖∑ n ∈ Finset.range (N + 1), a n * ((n : ℂ) ^ (Complex.I * t))‖ ^ 2
        rw [show 2 * m = m * 2 from by ring, pow_mul, ← norm_pow,
            n4_pow_eq_tup_sum (le_of_lt hPpos) q m χ t,
            (n4_sum_mvCoeff_eq_tup_sum χ t htv).symm]
      have hcont : Continuous fun t : ℝ =>
          ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2 * m) := by
        change Continuous fun t : ℝ => ‖psum P q χ t‖ ^ (2 * m)
        exact ((continuous_psum P q χ).norm).pow (2 * m)
      rw [hexp]
      by_cases hT1 : 1 ≤ T
      · have hmeanT := hmean N T a hT1
        rw [← hS_def] at hmeanT
        have hcast : (∫ t in (-T)..T,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m))
            = ∫ t in (-T)..T, ‖∑ n ∈ Finset.range (N+1), a n * ((n:ℂ)^(Complex.I*t))‖^2 :=
          intervalIntegral.integral_congr (fun t _ => hpt t)
        have hTm : max T 1 = T := le_antisymm (max_le le_rfl hT1) (le_max_left T 1)
        calc (∫ t in (-T)..T,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m))
            = ∫ t in (-T)..T, ‖∑ n ∈ Finset.range (N+1), a n * ((n:ℂ)^(Complex.I*t))‖^2 :=
              hcast
          _ ≤ C₂ * (T + (N:ℝ) * Real.log (2 + (N:ℝ))) * S := hmeanT
          _ = C₂ * (max T 1 + (N:ℝ) * Real.log (2 + (N:ℝ))) * S := by rw [hTm]
          _ ≤ (C₂ * ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * (1 + Cd))
                * (T + P ^ m * Real.log P) * pi0 P ^ m := hfinish
      · rw [not_le] at hT1
        have hpiece : (∫ t in (-T)..T,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m))
            ≤ ∫ t in (-1)..1,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m) :=
          n4_intervalIntegral_mono_of_nonneg hcont (fun t => by positivity) T hT (le_of_lt hT1)
        have hcast : (∫ t in (-1)..1,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m))
            = ∫ t in (-1)..1, ‖∑ n ∈ Finset.range (N+1), a n * ((n:ℂ)^(Complex.I*t))‖^2 :=
          intervalIntegral.integral_congr (fun t _ => hpt t)
        have hmean1 := hmean N 1 a le_rfl
        rw [← hS_def] at hmean1
        have hTm : max T 1 = 1 := le_antisymm (max_le (le_of_lt hT1) le_rfl) (le_max_right T 1)
        calc (∫ t in (-T)..T,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m))
            ≤ ∫ t in (-1)..1,
              ‖∑ p ∈ admP P q, χ (p : ZMod q) * (p : ℂ) ^ (Complex.I * t)‖ ^ (2*m) := hpiece
          _ = ∫ t in (-1)..1, ‖∑ n ∈ Finset.range (N+1), a n * ((n:ℂ)^(Complex.I*t))‖^2 :=
              hcast
          _ ≤ C₂ * (1 + (N:ℝ) * Real.log (2 + (N:ℝ))) * S := hmean1
          _ = C₂ * (max T 1 + (N:ℝ) * Real.log (2 + (N:ℝ))) * S := by rw [hTm]
          _ ≤ (C₂ * ((((m+1)^m : ℕ)) : ℝ) * Cc ^ m * (1 + Cd))
                * (T + P ^ m * Real.log P) * pi0 P ^ m := hfinish

end Work.BMF
