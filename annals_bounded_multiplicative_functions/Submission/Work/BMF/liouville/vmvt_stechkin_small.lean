import Mathlib
import Submission.Work.BMF.liouville.vmvt_stechkin_defs
import Submission.Work.BMF.liouville.stechF_step_core
import Submission.Work.BMF.liouville.vmvt_step_ineq_sharp
import Submission.Work.BMF.liouville.vJ_le_pow_mul_vJ
import Submission.Work.BMF.recursion_step
import Submission.Work.BMF.vmvt_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Stechkin's bound for the Vinogradov mean value theorem, with an explicit constant

`J_{s,k}(X) ≤ exp(C·min(⌊s/k⌋,k)·k²·log k) · X^{2s − k(k+1)/2 + (k²/2)(1−1/k)^{⌊s/k⌋}}`
for `2 ≤ k ≤ s`, `X ≥ 1` (see the citation of Stechkin's theorem in Ford, *Vinogradov's integral
and bounds for the Riemann zeta function*, Proc. LMS **85** (2002), (1.6)).

The proof is the classical Vinogradov–Linnik iteration of `Work.BMF.vmvt_uniform`, but with the
sharp constant `stechF k r = exp(stechK·k·r·(k+r)·(1+log k))` (`Work.BMF.liouville.vmvt_stechkin_defs`)
in place of `Ac C₀ k r`: the per-step arithmetic is `stechF_step_core` and the step itself
`vmvt_step_ineq_sharp`.  Non-multiples of `k` are handled by `vJ_le_pow_mul_vJ`, and for
`⌊s/k⌋ ≥ k` the estimate is reduced to `s' = k²`, so that `min(⌊s/k⌋,k)` is exactly the number of
steps paid for.
-/

open scoped BigOperators

namespace Work.BMF.liouville

open Work.BMF
open LeanEval.NumberTheory.VinogradovMeanValue

set_option maxHeartbeats 2000000

/-- The constant comparison: for `r ≤ k`, `stechF k r ≤ exp(stechC·r·k²·log k)`. -/
lemma stechF_le_exp_small (k r : ℕ) (hk : 2 ≤ k) (hrk : r ≤ k) :
    stechF k r ≤ Real.exp (stechC * (r : ℝ) * (k : ℝ) ^ 2 * Real.log (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogk0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hlogk_half : (1 / 2 : ℝ) ≤ Real.log (k : ℝ) := by
    have h1 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h
      linarith
    exact le_trans h1 (Real.log_le_log (by norm_num) hk2)
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    simp [stechF]
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
    have hrR : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
    have hKpos : 0 < stechK := lt_of_lt_of_le (by norm_num) eight_le_stechK
    have hb : ((k : ℝ) + (r : ℝ)) * (1 + Real.log (k : ℝ)) ≤ 8 * (k : ℝ) * Real.log (k : ℝ) := by
      have h1 : (1 : ℝ) + Real.log (k : ℝ) ≤ 4 * Real.log (k : ℝ) := by
        linarith only [hlogk_half]
      have h2 : (k : ℝ) + (r : ℝ) ≤ 2 * (k : ℝ) := by linarith only [hrR]
      have h3 : (0 : ℝ) ≤ 1 + Real.log (k : ℝ) := by linarith only [hlogk0]
      have h5 : (2 * (k : ℝ)) * (4 * Real.log (k : ℝ)) = 8 * (k : ℝ) * Real.log (k : ℝ) := by ring
      have h4 := mul_le_mul h2 h1 h3 (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ))
      linarith only [h4, h5]
    rw [stechF, stechC]
    apply Real.exp_le_exp.mpr
    have h6 : stechK * (k : ℝ) * (r : ℝ) * ((k : ℝ) + (r : ℝ)) * (1 + Real.log (k : ℝ))
        ≤ stechK * (k : ℝ) * (r : ℝ) * (8 * (k : ℝ) * Real.log (k : ℝ)) := by
      have hc0 : (0 : ℝ) ≤ stechK * (k : ℝ) * (r : ℝ) := by positivity
      calc stechK * (k : ℝ) * (r : ℝ) * ((k : ℝ) + (r : ℝ)) * (1 + Real.log (k : ℝ))
          = (stechK * (k : ℝ) * (r : ℝ)) * (((k : ℝ) + (r : ℝ)) * (1 + Real.log (k : ℝ))) := by
            ring
        _ ≤ (stechK * (k : ℝ) * (r : ℝ)) * (8 * (k : ℝ) * Real.log (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hb hc0
        _ = stechK * (k : ℝ) * (r : ℝ) * (8 * (k : ℝ) * Real.log (k : ℝ)) := by ring
    have h7 : stechK * (k : ℝ) * (r : ℝ) * (8 * (k : ℝ) * Real.log (k : ℝ))
        = 8 * stechK * (r : ℝ) * (k : ℝ) ^ 2 * Real.log (k : ℝ) := by ring
    linarith only [h6, h7]

/-- The base case of the sharp iteration: `k! ≤ stechF k 1`. -/
lemma stechF_factorial_le (k : ℕ) (hk : 2 ≤ k) : ((k.factorial : ℕ) : ℝ) ≤ stechF k 1 := by
  have hk1 : 1 ≤ k := by omega
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1'
  have hfact0 : (0 : ℝ) < ((k.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h1 : Real.log ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
    have h2 : ((k.factorial : ℕ) : ℝ) ≤ (k : ℝ) ^ k := by
      calc ((k.factorial : ℕ) : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by
            exact_mod_cast Nat.factorial_le_pow k
        _ = (k : ℝ) ^ k := by push_cast; ring
    calc Real.log ((k.factorial : ℕ) : ℝ) ≤ Real.log ((k : ℝ) ^ k) :=
          Real.log_le_log hfact0 h2
      _ = (k : ℝ) * Real.log (k : ℝ) := Real.log_pow _ _
  have hK1 : (1 : ℝ) ≤ stechK := le_trans (by norm_num) eight_le_stechK
  have h2 : (k : ℝ) * Real.log (k : ℝ)
      ≤ stechK * (k : ℝ) * ((1 : ℕ) : ℝ) * ((k : ℝ) + ((1 : ℕ) : ℝ)) * (1 + Real.log (k : ℝ)) := by
    have hone : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hone]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := le_trans zero_le_one hk1'
    have h3 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith only [hk1']
    have h4 : (1 : ℝ) ≤ 1 + Real.log (k : ℝ) := by linarith only [hlogk]
    have hL : Real.log (k : ℝ) ≤ ((k : ℝ) + 1) * (1 + Real.log (k : ℝ)) := by
      nlinarith only [hk1', hlogk, h3, h4]
    have h5 : (k : ℝ) * Real.log (k : ℝ)
        ≤ (k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hL hk0
    have h6 : (0 : ℝ) ≤ (k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ))) := by positivity
    have h7 : (k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ)))
        ≤ stechK * ((k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ)))) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1 h6
    calc (k : ℝ) * Real.log (k : ℝ)
        ≤ (k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ))) := h5
      _ ≤ stechK * ((k : ℝ) * (((k : ℝ) + 1) * (1 + Real.log (k : ℝ)))) := h7
      _ = stechK * (k : ℝ) * 1 * ((k : ℝ) + 1) * (1 + Real.log (k : ℝ)) := by ring
  calc ((k.factorial : ℕ) : ℝ) = Real.exp (Real.log ((k.factorial : ℕ) : ℝ)) :=
        (Real.exp_log hfact0).symm
    _ ≤ Real.exp (stechK * (k : ℝ) * ((1 : ℕ) : ℝ) * ((k : ℝ) + ((1 : ℕ) : ℝ))
          * (1 + Real.log (k : ℝ))) := Real.exp_le_exp.mpr (le_trans h1 h2)
    _ = stechF k 1 := by rw [stechF]

/-- **The sharp Vinogradov–Linnik induction**: for `k ≥ 2`, `r ≥ 1` and `Q ≥ 1`,
`J_{kr,k}(Q) ≤ stechF k r · Q^{th k r}`. -/
theorem main_sharp (k : ℕ) (hk : 2 ≤ k) :
    ∀ r ≥ 1, ∀ Q ≥ 1, J (k * r) k Q ≤ stechF k r * (Q : ℝ) ^ (th k r) := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
      intro Q hQ
      have hth : th k 1 = (k : ℝ) := th_one_aux k (by omega)
      have hk1 : k * 1 = k := Nat.mul_one k
      rw [hk1, hth, Real.rpow_natCast]
      have hfac : ((k.factorial : ℕ) : ℝ) ≤ stechF k 1 := stechF_factorial_le k hk
      calc J k k Q ≤ ((k.factorial : ℕ) : ℝ) * (Q : ℝ) ^ k := J_kk_le k Q
        _ ≤ stechF k 1 * (Q : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_right hfac (by positivity)
  | succ r hr ih =>
      intro Q hQ
      set M : ℕ := max k (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ + 1) with hMdef
      set Y : ℕ := max (2*M) ⌈pC * (k:ℝ)^3 * Real.log k⌉₊ with hYdef
      have hk1 : 1 ≤ k := by omega
      have hM1 : 1 ≤ M := le_trans (by omega : 1 ≤ k) (le_max_left _ _)
      obtain ⟨P, hPp, hPlb, hPub, hPcard⟩ := exists_prime_set k M hk hM1
      have hMk : k ≤ M := le_max_left _ _
      have hMgt : (Q:ℝ)^(1/(k:ℝ)) < (M:ℝ) := by
        have hceil : (Q:ℝ)^(1/(k:ℝ)) ≤ ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        have hlt : ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) < (M:ℝ) := by
          have h2 : (⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) + 1 ≤ M := by
            simp only [hMdef]
            exact le_max_right _ _
          have h3 : ((⌈(Q:ℝ)^(1/(k:ℝ))⌉₊ : ℕ) : ℝ) + 1 ≤ (M:ℝ) := by exact_mod_cast h2
          linarith
        exact lt_of_le_of_lt hceil hlt
      have hMQ : (Q:ℝ) < (M:ℝ)^k := by
        have hq0 : (0:ℝ) ≤ Q := by positivity
        have hk0 : (0:ℝ) < k := by positivity
        have hrpow : ((Q:ℝ)^(1/(k:ℝ)))^k = (Q:ℝ) := by
          rw [← Real.rpow_natCast ((Q:ℝ)^(1/(k:ℝ))) k, ← Real.rpow_mul hq0]
          have hexp : (1/(k:ℝ)) * (k:ℝ) = 1 := by field_simp
          rw [hexp, Real.rpow_one]
        calc (Q:ℝ) = ((Q:ℝ)^(1/(k:ℝ)))^k := hrpow.symm
          _ < (M:ℝ)^k := pow_lt_pow_left₀ hMgt (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ Q) _) (by omega : k ≠ 0)
      have hSk : k ≤ k*(r+1) := by nlinarith [hr]
      have hrec := recursion_step k (k*(r+1)) Q M Y hk hSk hQ hMk hMQ P hPp hPlb hPub hPcard.ge
      have hsub : k*(r+1) - k = k*r := by rw [Nat.mul_succ]; omega
      rw [hsub] at hrec
      have hP6 : (P.card:ℝ)^2 ≤ (k:ℝ)^6 := by
        have h1 : P.card ≤ k^3 := by
          rw [hPcard]
          refine Nat.ceil_le.mpr ?_
          push_cast
          nlinarith [show (0:ℝ) ≤ (k:ℝ)^3 by positivity]
        have h2 : ((P.card:ℕ):ℝ) ≤ ((k^3:ℕ):ℝ) := by exact_mod_cast h1
        push_cast at h2
        have h3 : ((P.card:ℕ):ℝ)^2 ≤ ((k:ℝ)^3)^2 :=
          pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (P.card:ℝ)) h2 2
        calc ((P.card:ℕ):ℝ)^2 ≤ ((k:ℝ)^3)^2 := h3
          _ = (k:ℝ)^6 := by ring
      have hIH := ih (1 + Q / M) (Nat.le_add_right 1 (Q/M))
      have hcast : (((1 + Q / M : ℕ) : ℝ)) ≤ 1 + (Q:ℝ)/(M:ℝ) := by
        have h1 : ((Q / M : ℕ) : ℝ) * (M:ℝ) ≤ (Q:ℝ) := by
          have := Nat.div_mul_le_self Q M
          exact_mod_cast this
        have hMpos : (0:ℝ) < M := by positivity
        have h2 : ((Q / M : ℕ) : ℝ) ≤ (Q:ℝ)/(M:ℝ) := by
          rw [le_div_iff₀ hMpos]
          exact h1
        push_cast
        linarith
      have hAcpos : 0 < stechF k r := stechF_pos k r
      have hIH' : J (k*r) k (1 + Q / M) ≤ stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r) := by
        refine hIH.trans ?_
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hAcpos)
        exact Real.rpow_le_rpow (by positivity) hcast (th_nonneg k r hk1 hr)
      calc J (k*(r+1)) k Q
          ≤ (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*
              ((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M) := hrec
        _ ≤ (4*(k:ℝ)^4)^(k*(r+1)) + 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*
              ((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*
              (stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by
            have hprod : (P.card:ℝ)^2 * J (k*r) k (1 + Q / M) ≤
                (k:ℝ)^6 * (stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) :=
              mul_le_mul hP6 hIH' (by
                unfold LeanEval.NumberTheory.VinogradovMeanValue.J; positivity) (by positivity)
            have h2 := mul_le_mul_of_nonneg_left hprod
              (show (0:ℝ) ≤ 4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k by positivity)
            have hprod2 : 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M)
                ≤ 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*(stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by
              calc 4*((k.factorial:ℕ):ℝ)*(P.card:ℝ)^2*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*J (k*r) k (1 + Q / M)
                  = (4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k)*((P.card:ℝ)^2*J (k*r) k (1 + Q / M)) := by ring
                _ ≤ (4*((k.factorial:ℕ):ℝ)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k)*((k:ℝ)^6*(stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r))) := h2
                _ = 4*((k.factorial:ℕ):ℝ)*((k:ℝ)^6)*((Y:ℕ):ℝ)^(2*(k*r)+k*(k-1)/2)*(Q:ℝ)^k*(stechF k r * (1 + (Q:ℝ)/(M:ℝ))^(th k r)) := by ring
            exact add_le_add (le_refl _) hprod2
        _ ≤ stechF k (r+1) * (Q:ℝ)^(th k (r+1)) := by
            have hstep := vmvt_step_ineq_sharp k r Q hk hr hQ
            simp only [hMdef, hYdef]
            rw [show 2*(k*r)+k*(k-1)/2 = 2*k*r+k*(k-1)/2 from by ring]
            exact hstep



/-- **Stechkin's bound in the range `2s ≤ k(k+1)`** (equivalently `⌊s/k⌋ ≤ k`), with the exact
exponents and the sharp constant.  This is the range reached by the sharp Vinogradov–Linnik
iteration; the complementary range `s ≥ k(k+1)/2 + 1` requires the sharp (ε-free) Vinogradov mean
value bound above the critical index (see `Work.BMF.liouville.sharp_vmvt_above_critical`). -/
theorem vmvt_stechkin_small : ∃ C : ℝ, 0 < C ∧ ∀ (s k X : ℕ),
    2 ≤ k → k ≤ s → 2 * s ≤ k * (k + 1) → 1 ≤ X →
    Work.BMF.vJ s k X ≤
      Real.exp (C * ((min (s / k) k : ℕ) : ℝ) * (k : ℝ) ^ 2 * Real.log (k : ℝ)) *
        (X : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
          + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k)) := by
  refine ⟨stechC, stechC_pos, ?_⟩
  intro s k X hk hks hs hX
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hr1 : 1 ≤ s / k := by
    have h : 0 < s / k := Nat.div_pos hks (by omega : 0 < k)
    omega
  set r : ℕ := s / k with hrdef
  have hr1' : 1 ≤ r := by rw [hrdef]; exact hr1
  have hrk : r ≤ k := by
    rw [hrdef]
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < k)]
    have hsR : (s : ℝ) * 2 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
      have h : ((2 * s : ℕ) : ℝ) ≤ ((k * (k + 1) : ℕ) : ℝ) := by exact_mod_cast hs
      push_cast at h
      linarith only [h]
    have hpos : (0 : ℝ) < (k : ℝ) * ((k : ℝ) + 1) := by positivity
    have h4 : (s : ℝ) < ((k : ℝ) + 1) * (k : ℝ) := by nlinarith only [hsR, hpos]
    exact_mod_cast h4
  have hkr : k * r ≤ s := by rw [hrdef]; exact Nat.mul_div_le s k
  have hmin : min (s / k) k = r := by rw [← hrdef]; exact min_eq_left hrk
  rw [hmin]
  have hconst := stechF_le_exp_small k r hk hrk
  have h1 : Work.BMF.vJ s k X ≤ (X : ℝ) ^ (2 * (s - k * r)) * Work.BMF.vJ (k * r) k X :=
    vJ_le_pow_mul_vJ s (k * r) k X hkr
  have h2 : Work.BMF.vJ (k * r) k X ≤ stechF k r * (X : ℝ) ^ (th k r) :=
    main_sharp k hk r hr1' X hX
  have hexp : (((2 * (s - k * r) : ℕ)) : ℝ) + th k r
      = 2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
        + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k) := by
    have hc0 : (((2 * (s - k * r) : ℕ)) : ℝ) = 2 * ((s - k * r : ℕ) : ℝ) := by push_cast; ring
    have hc1 : ((s - k * r : ℕ) : ℝ) = (s : ℝ) - ((k * r : ℕ) : ℝ) := Nat.cast_sub hkr
    have hc2 : ((k * r : ℕ) : ℝ) = (k : ℝ) * (r : ℝ) := by push_cast; ring
    rw [hc0, hc1, hc2, th, ← hrdef]
    ring
  have step : Work.BMF.vJ s k X
      ≤ stechF k r * (X : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
          + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k)) := by
    calc Work.BMF.vJ s k X
        ≤ (X : ℝ) ^ (2 * (s - k * r)) * (stechF k r * (X : ℝ) ^ (th k r)) :=
          le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = stechF k r * ((X : ℝ) ^ (2 * (s - k * r)) * (X : ℝ) ^ (th k r)) := by ring
      _ = stechF k r * (X : ℝ) ^ ((((2 * (s - k * r) : ℕ)) : ℝ) + th k r) := by
          rw [← Real.rpow_natCast (X : ℝ) (2 * (s - k * r)), ← Real.rpow_add hXpos]
      _ = stechF k r * (X : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
            + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k)) := by rw [hexp]
  calc Work.BMF.vJ s k X
      ≤ stechF k r * (X : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
          + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k)) := step
    _ ≤ Real.exp (stechC * (r : ℝ) * (k : ℝ) ^ 2 * Real.log (k : ℝ))
          * (X : ℝ) ^ (2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2
            + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ (s / k)) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (le_of_lt hXpos) _)

end Work.BMF.liouville
