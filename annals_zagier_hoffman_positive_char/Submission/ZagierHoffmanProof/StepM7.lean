import Submission.ZagierHoffmanProof.StepM6
import Submission.ZagierHoffmanProof.StepM8
import Submission.ZagierHoffmanProof.StepB7
import Submission.Commons.Data.Nat.choose_odd_iff
import Submission.Commons.Data.Nat.choose_add_odd_iff
import Submission.Commons.Data.Nat.step_iter_ge
import Submission.Commons.Data.Nat.step_iter_two_pow_mul
import Submission.Commons.Data.Nat.land_pred_iff
import Submission.Commons.Data.Nat.step_R_pres

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero
open Commons.Data.Nat

/-!
# Step M7: Thakur's recursion `s_{d+1}(k) = s_d(s_1(k)) + s_1(k)` for `q = 2`

Combining the truncated level recursion of Step M5 with the `q = 2` dominance analysis
(Thakur, *Power sums ...*, §8.1) we obtain the exact valuation of every power sum over `F₂`:

  `v (P_d k) = exp (−∑_{i=1}^{d} T^i(k))`,   `T k = k + 2 ^ v_2(k)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section CardTwo

/-- A field with `Nat.card F = 2` has characteristic `2`. -/
lemma charP_two_of_card_two (h2 : Nat.card F = 2) : CharP F 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpchar, n, hprime, hcard⟩ := FiniteField.card' F
  have hpn : p ^ (n : ℕ) = 2 := by rw [← hcard, Fintype.card_eq_nat_card, h2]
  have hn0 : (n : ℕ) ≠ 0 := n.pos.ne'
  have hp2 : p = 2 := by
    have hpdvd : p ∣ 2 := by rw [← hpn]; exact dvd_pow_self p hn0
    rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd with h | h
    · exact absurd h hprime.ne_one
    · exact h
  rw [← hp2]; exact hpchar

/-- In a field with `Nat.card F = 2`, a natural number cast vanishes exactly on the evens. -/
lemma natCast_eq_zero_iff_of_card_two (h2 : Nat.card F = 2) (n : ℕ) :
    ((n : ℕ) : F) = 0 ↔ Even n := by
  haveI := charP_two_of_card_two F h2
  rw [CharP.cast_eq_zero_iff F 2 n]
  exact even_iff_two_dvd.symm

/-- For `Nat.card F = 2`: `binF F k j ≠ 0 ↔ (k + j - 1).choose j` is odd. -/
lemma binF_ne_zero_iff_odd (h2 : Nat.card F = 2) (k j : ℕ) :
    binF F k j ≠ 0 ↔ Odd ((k + j - 1).choose j) := by
  have hc := natCast_eq_zero_iff_of_card_two F h2 ((k + j - 1).choose j)
  have h2' : ((↑((k + j - 1).choose j) : F)) ≠ 0 ↔ ¬ Even ((k + j - 1).choose j) :=
    not_congr hc
  rw [binF, mul_ne_zero_iff, ← Nat.not_even_iff_odd]
  constructor
  · rintro ⟨-, h⟩; rwa [h2'] at h
  · intro h; exact ⟨pow_ne_zero _ (by norm_num), by rwa [h2']⟩

end CardTwo

section Lowbit

lemma land_self (n : ℕ) : n &&& n = n := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_land]
  cases n.testBit i <;> simp

/-- For odd `m`, clearing the lowest set bit does nothing: `m &&& (m-1) = m-1`. -/
lemma land_pred_self_of_odd {m : ℕ} (hm : Odd m) : m &&& (m - 1) = m - 1 := by
  obtain ⟨c, rfl⟩ := hm
  rw [Nat.add_sub_cancel, StepR.land_odd_two, land_self]

/-- The lowbit `k - (k &&& (k-1))` is the largest power of two dividing `k`. -/
lemma lowbit_eq_two_pow_factorization (k : ℕ) (hk : k ≠ 0) :
    k - (k &&& (k - 1)) = 2 ^ k.factorization 2 := by
  set a := k.factorization 2 with ha
  have h2a_dvd : 2 ^ a ∣ k := (Nat.prime_two.pow_dvd_iff_le_factorization hk).mpr (by rw [ha])
  have hk_eq : k = 2 ^ a * (k / 2 ^ a) := (Nat.mul_div_cancel' h2a_dvd).symm
  have hle : 2 ^ a ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h2a_dvd
  have hm_odd : Odd (k / 2 ^ a) := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c, hc⟩
    have h2 : 2 ^ (a + 1) ∣ k := by
      rw [hk_eq, hc, pow_succ]
      exact ⟨c, by ring⟩
    have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization hk).mp h2
    rw [ha] at h3
    omega
  have hpred : k - 1 = 2 ^ a * (k / 2 ^ a - 1) + (2 ^ a - 1) := by
    have h1 : 2 ^ a * (k / 2 ^ a - 1) = k - 2 ^ a := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_div_cancel' h2a_dvd]
    rw [h1, ← Nat.add_sub_assoc (Nat.one_le_two_pow (n := a)), Nat.sub_add_cancel hle]
  have hmod : (k - 1) % 2 ^ a = 2 ^ a - 1 := by
    rw [hpred, Nat.mul_add_mod_self_left,
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one)]
  have hdiv : (k - 1) / 2 ^ a = k / 2 ^ a - 1 := by
    rw [hpred, Nat.mul_add_div (Nat.two_pow_pos a),
      Nat.div_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos a) Nat.zero_lt_one), Nat.add_zero]
  have e1 : (k &&& (k - 1)) % 2 ^ a = k % 2 ^ a := by
    rw [Nat.and_mod_two_pow, hmod,
      Nat.and_two_pow_sub_one_of_lt_two_pow (Nat.mod_lt k (Nat.two_pow_pos a))]
  have e2 : (k &&& (k - 1)) / 2 ^ a = (k / 2 ^ a) &&& (k / 2 ^ a - 1) := by
    rw [Nat.and_div_two_pow, hdiv]
  have hself : (k / 2 ^ a) &&& (k / 2 ^ a - 1) = k / 2 ^ a - 1 := land_pred_self_of_odd hm_odd
  have hkmod : k % 2 ^ a = 0 := Nat.dvd_iff_mod_eq_zero.mp h2a_dvd
  have hd : 2 ^ a * ((k &&& (k - 1)) / 2 ^ a) + (k &&& (k - 1)) % 2 ^ a = k &&& (k - 1) :=
    Nat.div_add_mod _ _
  rw [e2, hself, e1, hkmod, Nat.add_zero] at hd
  have hthis : 2 ^ a * (k / 2 ^ a - 1) = k - 2 ^ a := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_div_cancel' h2a_dvd]
  rw [← hd, hthis, Nat.sub_sub_self hle]

end Lowbit

section StepForm

/-- `Tmap` keeps nonzero numbers nonzero. -/
lemma Tmap_ne_zero (k : ℕ) : Tmap k ≠ 0 := Nat.pos_iff_ne_zero.mp (Tmap_pos k)

lemma Tmap_iter_ne_zero (k : ℕ) (hk : k ≠ 0) (i : ℕ) : Nat.iterate Tmap i k ≠ 0 := by
  induction i with
  | zero => simpa using hk
  | succ n _ => rw [Function.iterate_succ_apply']; exact Tmap_ne_zero _

/-- `Tmap` in the "lowbit" form used by the commons bitwise API. -/
lemma Tmap_eq_step {k : ℕ} (hk : k ≠ 0) : Tmap k = k + (k - (k &&& (k - 1))) := by
  rw [Tmap_def, lowbit_eq_two_pow_factorization k hk]

/-- The `Tmap`-orbit and the lowbit-orbit of a nonzero number agree. -/
lemma Tmap_iter_eq_step_iter (k : ℕ) (hk : k ≠ 0) (i : ℕ) :
    Nat.iterate Tmap i k
      = Nat.iterate (fun n : ℕ => n + (n - (n &&& (n - 1)))) i k := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact Tmap_eq_step (Tmap_iter_ne_zero k hk n)

end StepForm

section JMinTwo

/-- Admissibility at `q = 2` is exactly the "no carry" condition on `k - 1`. -/
lemma binF_psumF_ne_zero_iff_land (h2 : Nat.card F = 2) (k : ℕ+) (j : ℕ) :
    binF F k j * psumF F j ≠ 0 ↔ 1 ≤ j ∧ j &&& ((k : ℕ) - 1) = 0 := by
  rw [mul_binF_psumF_ne_zero_iff]
  unfold IsGoodJ
  rw [h2]
  constructor
  · rintro ⟨h1, -, hbin⟩
    refine ⟨h1, ?_⟩
    rw [binF_ne_zero_iff_odd F h2] at hbin
    rw [show (k : ℕ) + j - 1 = j + ((k : ℕ) - 1) by have := k.pos; omega] at hbin
    exact (choose_add_odd_iff j ((k : ℕ) - 1)).mp hbin
  · rintro ⟨h1, hland⟩
    refine ⟨h1, by simp, ?_⟩
    rw [binF_ne_zero_iff_odd F h2,
      show (k : ℕ) + j - 1 = j + ((k : ℕ) - 1) by have := k.pos; omega]
    exact (choose_add_odd_iff j ((k : ℕ) - 1)).mpr hland

/-- The least admissible shift at `q = 2` is the lowbit of `k`. -/
theorem jMin_card_two (h2 : Nat.card F = 2) (k : ℕ+) :
    jMin F k = 2 ^ (k : ℕ).factorization 2 := by
  classical
  have hne : (k : ℕ) ≠ 0 := k.pos.ne'
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  set a := (k : ℕ).factorization 2 with ha
  have h2a_dvd : 2 ^ a ∣ (k : ℕ) :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hne).mpr (by rw [ha])
  have hcoe : (k : ℕ) = 2 ^ a * ((k : ℕ) / 2 ^ a) := (Nat.mul_div_cancel' h2a_dvd).symm
  have hm_odd : Odd ((k : ℕ) / 2 ^ a) := by
    rw [← Nat.not_even_iff_odd]
    rintro ⟨c, hc⟩
    have h2 : 2 ^ (a + 1) ∣ (k : ℕ) := by
      refine ⟨c, ?_⟩
      have hkk : (k : ℕ) = 2 ^ a * (c + c) := by rw [hcoe, hc]
      rw [hkk, pow_succ]; ring
    have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp h2
    exact Nat.not_succ_le_self a (ha ▸ h3)
  have hkey : (2 ^ (k : ℕ).factorization 2) &&& ((k : ℕ) - 1) = 0 := by
    rw [← ha]
    refine (land_pred_iff (k : ℕ) (2 ^ a) hk1
      (Nat.one_le_pow _ _ (by norm_num))).mpr ⟨dvd_rfl, ?_⟩
    rw [Nat.div_self (pow_pos (by norm_num) _), Nat.one_and_eq_mod_two]
    obtain ⟨c, hc⟩ := hm_odd
    rw [hc]
    omega
  refine le_antisymm ?_ ?_
  · refine jMin_le F (show IsGoodJ F (k : ℕ) (2 ^ (k : ℕ).factorization 2) from ?_)
    refine ⟨Nat.one_le_pow _ _ (by norm_num), by rw [h2]; exact one_dvd _, ?_⟩
    rw [binF_ne_zero_iff_odd F h2,
      show (k : ℕ) + 2 ^ (k : ℕ).factorization 2 - 1
        = 2 ^ (k : ℕ).factorization 2 + ((k : ℕ) - 1) by
        have := Nat.one_le_two_pow (n := (k : ℕ).factorization 2); omega]
    exact (choose_add_odd_iff (2 ^ (k : ℕ).factorization 2) ((k : ℕ) - 1)).mpr hkey
  · have hland := (binF_psumF_ne_zero_iff_land F h2 k (jMin F k)).mp
      ((mul_binF_psumF_ne_zero_iff F (k : ℕ) (jMin F k)).mpr (jMin_spec F k))
    exact Nat.le_of_dvd (jMin_pos F k)
      ((land_pred_iff (k : ℕ) (jMin F k) hk1 (jMin_pos F k)).mp hland.2).1

end JMinTwo

section Dominance

/-- Monotonicity of `sExp` in the argument from monotonicity of the iterates. -/
lemma sExp_le_of_iter_le (d : ℕ) {x y : ℕ}
    (h : ∀ i : ℕ, Nat.iterate Tmap i x ≤ Nat.iterate Tmap i y) : sExp d x ≤ sExp d y := by
  unfold sExp
  refine Finset.sum_le_sum fun i _ => ?_
  exact_mod_cast h (i + 1)

/-- **The dominance estimate** (Thakur §8.1) for `q = 2`: away from the least admissible
shift, the exponent `(k+j) + s_d(k+j)` is strictly larger. -/
theorem jMin_dominates (h2 : Nat.card F = 2) (d : ℕ) (k : ℕ+) (j : ℕ) (hj : 1 ≤ j)
    (hadm : binF F k j * psumF F j ≠ 0) (hjne : j ≠ jMin F k) :
    ((k : ℤ) + jMin F k) + sExp d ((k : ℕ) + jMin F k)
      < ((k : ℤ) + j) + sExp d ((k : ℕ) + j) := by
  classical
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  have hjmin : jMin F k = 2 ^ (k : ℕ).factorization 2 := jMin_card_two F h2 k
  obtain ⟨-, hbin⟩ := (binF_psumF_ne_zero_iff_land F h2 k j).mp hadm
  obtain ⟨hdvd, hdisj⟩ :=
    (land_pred_iff (k : ℕ) j hk1 hj).mp hbin
  set a := (k : ℕ).factorization 2 with ha
  set m := (k : ℕ) / 2 ^ a with hm
  set u := j / 2 ^ a with hu
  have hj_eq : j = 2 ^ a * u := by rw [hu, Nat.mul_div_cancel' hdvd]
  have hle_j : 2 ^ a ≤ j := Nat.le_of_dvd hj hdvd
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact Nat.div_pos hle_j (pow_pos (by norm_num) _)
  have h2a_dvd : 2 ^ a ∣ (k : ℕ) := (Nat.prime_two.pow_dvd_iff_le_factorization k.pos.ne').mpr
    (by rw [ha])
  have hk_eq : (k : ℕ) = 2 ^ a * m := by
    rw [hm]; exact (Nat.mul_div_cancel' h2a_dvd).symm
  have hm_odd : Odd m := by
    rw [hm, ← Nat.not_even_iff_odd]
    rintro ⟨c, hc⟩
    have h2 : 2 ^ (a + 1) ∣ (k : ℕ) := by
      refine ⟨c, ?_⟩
      have hkk : (k : ℕ) = 2 ^ a * (c + c) := by rw [hk_eq, hm, hc]
      rw [hkk, pow_succ]; ring
    have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization k.pos.ne').mp h2
    exact Nat.not_succ_le_self a (ha ▸ h3)
  have hdisj' : (m - 1) &&& u = 0 := by rw [Nat.land_comm]; exact hdisj
  have hiter : ∀ i : ℕ, stepf^[i] (m + 1) ≤ stepf^[i] (m + u) :=
    fun i => step_iter_ge_odd' m u hm_odd hu1 hdisj' i
  have hscale : ∀ i : ℕ, Nat.iterate Tmap i ((k : ℕ) + jMin F k)
      ≤ Nat.iterate Tmap i ((k : ℕ) + j) := by
    intro i
    have h1 : (k : ℕ) + jMin F k = 2 ^ a * (m + 1) := by rw [hjmin, hk_eq]; ring
    have h2' : (k : ℕ) + j = 2 ^ a * (m + u) := by rw [hj_eq, hk_eq]; ring
    rw [h1, h2', Tmap_iter_eq_step_iter _ (by positivity) i,
      Tmap_iter_eq_step_iter _ (by positivity) i]
    rw [step_iter_two_pow_mul, step_iter_two_pow_mul]
    exact Nat.mul_le_mul_left _ (hiter i)
  have hmono := sExp_le_of_iter_le d hscale
  have hjmin_lt : jMin F k < j := by
    refine lt_of_le_of_ne ?_ (Ne.symm hjne)
    rw [hjmin]; exact hle_j
  have : (jMin F k : ℤ) < (j : ℤ) := by exact_mod_cast hjmin_lt
  linarith

end Dominance

section Main

/-- The summand of the truncated level recursion (Step M5). -/
noncomputable def expTerm (d : ℕ) (k : ℕ+) (j : ℕ) : RatFunc.CompletionAtInfty F :=
  cst F (binF F k j * psumF F j) *
    (((((Polynomial.X : F[X]) : RatFunc F)) : RatFunc.CompletionAtInfty F) ^
      ((k : ℕ) + j))⁻¹ *
    P F d ⟨(k : ℕ) + j, Nat.add_pos_left k.pos j⟩

/-- The truncated level recursion, restated with `expTerm`. -/
theorem P_succ_expansion' (d N : ℕ) (k : ℕ+) :
    ∃ E : RatFunc.CompletionAtInfty F,
      P F (d + 1) k = (∑ j ∈ Finset.range (N + 1), expTerm F d k j) + E ∧
      Valued.v E ≤ exp (-(((d : ℤ) + 1) * ((k : ℤ) + N + 1))) := by
  simpa only [expTerm] using P_succ_expansion F d N k

/-- The valuation of a summand with nonzero coefficient. -/
lemma expTerm_val (d : ℕ) (k : ℕ+) (j : ℕ)
    (hP : ∀ m : ℕ+, Valued.v (P F d m) = exp (-(sExp d (m : ℕ))))
    (hc : binF F k j * psumF F j ≠ 0) :
    Valued.v (expTerm F d k j) = exp (-(((k : ℤ) + j) + sExp d ((k : ℕ) + j))) :=
  v_P_expansion_term F d k j (sExp d ((k : ℕ) + j)) (hP _) hc

lemma expTerm_eq_zero (d : ℕ) (k : ℕ+) (j : ℕ) (hc : binF F k j * psumF F j = 0) :
    expTerm F d k j = 0 := by
  unfold expTerm
  rw [hc, cst_zero, zero_mul, zero_mul]

/-- **Thakur's recursion for `q = 2`**: the exact valuation of every power sum over `F₂`,
`v (P_d k) = exp (−∑_{i=1}^{d} T^i(k))` with `T k = k + 2 ^ v_2(k)`. -/
theorem val_P_iter (h2 : Nat.card F = 2) (d : ℕ) (k : ℕ+) :
    Valued.v (P F d k) = exp (-(sExp d (k : ℕ))) := by
  induction d generalizing k with
  | zero =>
      rw [P_zero_eq_one F k, sExp_zero]
      simp
  | succ d ih =>
      set S : ℤ := sExp d ((k : ℕ) + jMin F k) with hS
      have hSnn : 0 ≤ S := sExp_nonneg d _
      set N : ℕ := (k : ℕ) + jMin F k + S.toNat with hN
      obtain ⟨E, hE, hvE⟩ := P_succ_expansion' F d N k
      have hjc : binF F k (jMin F k) * psumF F (jMin F k) ≠ 0 :=
        (mul_binF_psumF_ne_zero_iff F (k : ℕ) (jMin F k)).mpr (jMin_spec F k)
      have hvalj := expTerm_val F d k (jMin F k) ih hjc
      have hdom : ∀ j ∈ Finset.range (N + 1), j ≠ jMin F k →
          Valued.v (expTerm F d k j) < Valued.v (expTerm F d k (jMin F k)) := by
        intro j _ hjne
        by_cases hc : binF F k j * psumF F j = 0
        · rw [expTerm_eq_zero F d k j hc, map_zero, hvalj]
          exact lt_of_lt_of_le (zero_lt_iff.mpr WithZero.exp_ne_zero) le_rfl
        · rw [expTerm_val F d k j ih hc, hvalj]
          refine WithZero.exp_lt_exp.mpr ?_
          have hj1 : 1 ≤ j := ((binF_psumF_ne_zero_iff_land F h2 k j).mp hc).1
          have := jMin_dominates F h2 d k j hj1 hc hjne
          linarith
      have hjmin_mem : jMin F k ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range, hN]
        have := jMin_pos F k
        omega
      have hsum := Valuation.map_sum_eq_of_lt (v := Valued.v) hjmin_mem (by
        intro i hi
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
        exact hdom i hi.1 hi.2)
      have hElt : Valued.v E < Valued.v (expTerm F d k (jMin F k)) := by
        rw [hvalj]
        refine lt_of_le_of_lt hvE (WithZero.exp_lt_exp.mpr ?_)
        have hSc : ((S.toNat : ℕ) : ℤ) = S := Int.toNat_of_nonneg hSnn
        have hNc : ((N : ℕ) : ℤ) = (k : ℤ) + jMin F k + S := by
          rw [hN]; push_cast [hSc]; ring
        have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast k.pos
        have hj0 : (0 : ℤ) ≤ (jMin F k : ℤ) := by exact_mod_cast (Nat.zero_le _)
        have hd1 : (1 : ℤ) ≤ (d : ℤ) + 1 := by omega
        have hkn : (1 : ℤ) ≤ (k : ℤ) + (N : ℤ) + 1 := by
          have : (0 : ℤ) ≤ (N : ℤ) := Nat.cast_nonneg N; linarith
        rw [hNc]
        nlinarith [hd1, hk1, hj0, hkn]
      rw [hE, Valuation.map_add_eq_of_lt_left (v := Valued.v) (by rw [hsum]; exact hElt),
        hsum, hvalj, sExp_succ]
      congr 1
      have : Tmap (k : ℕ) = (k : ℕ) + jMin F k := by
        rw [Tmap_def, jMin_card_two F h2 k]
      rw [this]
      push_cast
      ring

end Main

end ZagierHoffmanPositiveChar
