import Submission.ZagierHoffmanProof.ThakurDeg2
import Submission.Commons.Algebra.CharP.choose_add_mul_pow_eq_one

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# Step M3: Thakur's degree formula for the depth-one power sums

This file assembles the truncated expansion of Step M2 into Thakur's theorem
("Power sums with applications to multizeta values and zeta zero distribution for
`F_q[t]`, Theorem 3.1"): for `k ≥ 1` and `q = |F|`,

  `deg S_1(k) = −(k + j_min(k))`,  `j_min(k) = min {j ≥ 1 : (q−1) ∣ j, C(k+j−1, j) ≠ 0 in F}`,

i.e. `v (P_1(k)) = exp (−(k + j_min(k)))` in the completion at infinity.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section JMin

/-- `j` is a *good shift* for the depth-one summand at `k`: positive, divisible by `q − 1`,
and with non-vanishing binomial coefficient `C(−k, j) = (−1)^j C(k + j − 1, j)`. -/
def IsGoodJ (k j : ℕ) : Prop :=
  1 ≤ j ∧ (Nat.card F - 1) ∣ j ∧ binF F k j ≠ 0

lemma exists_goodJ (k : ℕ+) : ∃ j, IsGoodJ F (k : ℕ) j := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpchar, n, hprime, hcard⟩ := FiniteField.card' F
  haveI : CharP F p := hpchar
  haveI : Fact p.Prime := ⟨hprime⟩
  have hq2 : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card, hcard]
    exact Nat.succ_le_of_lt (one_lt_pow₀ hprime.one_lt (Nat.pos_iff_ne_zero.mp n.pos))
  have hp1 : 1 ≤ p ^ (k : ℕ) := one_le_pow₀ hprime.one_le
  refine ⟨(Nat.card F - 1) * p ^ (k : ℕ), ⟨?_, Nat.dvd_mul_right _ _, ?_⟩⟩
  · exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (lt_of_lt_of_le zero_lt_one hp1))
  · rw [binF_ne_zero_iff]
    have hidx2 : (Nat.card F - 1) * p ^ (k : ℕ) = p ^ (k : ℕ) * (Nat.card F - 1) := by ring
    have hidx : (k : ℕ) + (Nat.card F - 1) * p ^ (k : ℕ) - 1
        = ((k : ℕ) - 1) + p ^ (k : ℕ) * (Nat.card F - 1) := by
      rw [hidx2]
      generalize p ^ (k : ℕ) * (Nat.card F - 1) = M
      have hk1 : 1 ≤ (k : ℕ) := k.pos
      omega
    rw [hidx, hidx2,
      Commons.Algebra.CharP.choose_add_mul_pow_eq_one (R := F) (p := p) (e := (k : ℕ))
        (a := (k : ℕ) - 1) (N := Nat.card F - 1) ?_]
    · exact one_ne_zero
    · have h1 : (k : ℕ) < 2 ^ (k : ℕ) := Nat.lt_two_pow_self
      have h2 : 2 ^ (k : ℕ) ≤ p ^ (k : ℕ) := Nat.pow_le_pow_left hprime.two_le (k : ℕ)
      omega

/-- The least good shift at `k`. -/
noncomputable def jMin (k : ℕ+) : ℕ := by
  classical
  exact Nat.find (exists_goodJ F k)

lemma jMin_spec (k : ℕ+) : IsGoodJ F (k : ℕ) (jMin F k) := by
  classical
  exact Nat.find_spec (exists_goodJ F k)
lemma jMin_pos (k : ℕ+) : 1 ≤ jMin F k := (jMin_spec F k).1
lemma jMin_dvd (k : ℕ+) : (Nat.card F - 1) ∣ jMin F k := (jMin_spec F k).2.1
lemma jMin_binF_ne (k : ℕ+) : binF F (k : ℕ) (jMin F k) ≠ 0 := (jMin_spec F k).2.2
lemma jMin_min {k : ℕ+} {j : ℕ} (h : j < jMin F k) : ¬ IsGoodJ F (k : ℕ) j := by
  classical
  exact Nat.find_min (exists_goodJ F k) h
lemma jMin_le {k : ℕ+} {j : ℕ} (h : IsGoodJ F (k : ℕ) j) : jMin F k ≤ j := by
  classical
  exact Nat.find_min' (exists_goodJ F k) h

end JMin

section Bounds

/-- `v (cst a) = 1` for `a ≠ 0`. -/
lemma v_cst_eq_one (a : F) (ha : a ≠ 0) : Valued.v (cst F a) = 1 := by
  rw [cst, cstHom, RingHom.comp_apply, toK, v_toK F _ (by simpa using ha)]
  have h3 : (algebraMap F (RatFunc F) a).intDegree = 0 := by
    rw [RatFunc.algebraMap_eq_C, RatFunc.intDegree_C]
  rw [h3, WithZero.exp_zero]

/-- `psumF j ≠ 0` exactly for `j ≥ 1` divisible by `q − 1`. -/
lemma psumF_ne_zero_iff (j : ℕ) : psumF F j ≠ 0 ↔ 1 ≤ j ∧ (Nat.card F - 1) ∣ j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [psumF_zero]
    simp
  · rw [psumF_eq F j h]
    by_cases hjc : (Nat.card F - 1) ∣ j
    · rw [if_pos hjc]
      exact ⟨fun _ => ⟨h, hjc⟩, fun _ => neg_ne_zero.mpr one_ne_zero⟩
    · rw [if_neg hjc]
      exact ⟨fun hne => absurd rfl hne, fun hj => absurd hj.2 hjc⟩

lemma mul_binF_psumF_ne_zero_iff (k j : ℕ) :
    binF F k j * psumF F j ≠ 0 ↔ IsGoodJ F k j := by
  rw [mul_ne_zero_iff, IsGoodJ, binF_ne_zero_iff, psumF_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h3, h1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h3, h1, h2⟩

/-- The valuation of a single summand of `trExp`. -/
lemma trExp_term_val (k j : ℕ) (z : RatFunc.CompletionAtInfty F) (m : ℤ)
    (hz : z ≠ 0) (hzv : Valued.v z = WithZero.exp m) (ha : binF F k j * psumF F j ≠ 0) :
    Valued.v (cst F (binF F k j * psumF F j) * (z ^ (k + j))⁻¹)
      = WithZero.exp (-(m * ((k : ℤ) + j))) := by
  rw [Valuation.map_mul, v_cst_eq_one F _ ha, Valuation.map_inv, Valuation.map_pow, hzv,
    exp_pow, ← WithZero.exp_neg, one_mul]
  congr 1

/-- ★ The valuation of the truncated exponential sum `trExp`: the smallest good shift
`jMin` dominates. -/
lemma v_trExp (k : ℕ+) (N : ℕ) (z : RatFunc.CompletionAtInfty F) (m : ℤ)
    (hz : z ≠ 0) (hzv : Valued.v z = WithZero.exp m) (hm : 0 < m) (hN : jMin F k ≤ N) :
    Valued.v (trExp F (k : ℕ) N z) = WithZero.exp (-(m * ((k : ℤ) + jMin F k))) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hJm := jMin_spec F k
  have hJm' : binF F (k : ℕ) (jMin F k) * psumF F (jMin F k) ≠ 0 :=
    (mul_binF_psumF_ne_zero_iff F (k : ℕ) (jMin F k)).mpr hJm
  have hterm := trExp_term_val F (k : ℕ) (jMin F k) z m hz hzv hJm'
  have hmem : jMin F k ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]
    have := jMin_pos F k
    omega
  have hmain : Valued.v (∑ j ∈ Finset.range (N + 1),
        cst F (binF F (k : ℕ) j * psumF F j) * (z ^ ((k : ℕ) + j))⁻¹)
      = Valued.v (cst F (binF F (k : ℕ) (jMin F k) * psumF F (jMin F k))
          * (z ^ ((k : ℕ) + jMin F k))⁻¹) := by
    refine Valuation.map_sum_eq_of_lt
      (v := (Valued.v : Valuation (RatFunc.CompletionAtInfty F) ℤᵐ⁰)) hmem ?_
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hjm, hne⟩ := hj
    rw [Finset.mem_range] at hjm
    by_cases hz0 : binF F (k : ℕ) j * psumF F j = 0
    · rw [hz0, cst_zero, zero_mul, Valuation.map_zero]
      refine lt_of_lt_of_le (zero_lt_iff.mpr ?_) le_rfl
      exact hterm.symm ▸ WithZero.exp_ne_zero
    · have hj' : IsGoodJ F (k : ℕ) j := (mul_binF_psumF_ne_zero_iff F (k : ℕ) j).mp hz0
      have hlt : jMin F k < j := by
        rcases lt_trichotomy j (jMin F k) with h | h | h
        · exact absurd hj' (jMin_min F h)
        · exact absurd h hne
        · exact h
      rw [trExp_term_val F (k : ℕ) j z m hz hzv hz0, hterm]
      refine WithZero.exp_lt_exp.mpr ?_
      have hkk : (0 : ℤ) < (k : ℤ) := by exact_mod_cast k.pos
      nlinarith
  rw [trExp, hmain, hterm]

end Bounds

section Main

/-- ★ The valuation of `zetaSum F k z` for `z` with `v z = exp m`, `m > 0`, and all
translates `z + c`. -/
theorem v_zetaSum (k : ℕ+) (z : RatFunc.CompletionAtInfty F) (m : ℤ)
    (hz : z ≠ 0) (hzv : Valued.v z = WithZero.exp m) (hm : 0 < m)
    (hzc : ∀ c : F, Valued.v (z + cst F c) = Valued.v z) :
    Valued.v (zetaSum F (k : ℕ) z) = WithZero.exp (-(m * ((k : ℤ) + jMin F k))) := by
  obtain ⟨W, h1, h2⟩ := trunc_expansion F (k : ℕ) (jMin F k) k.pos z m hz hzv hm.le hzc
  have htr : Valued.v (trExp F (k : ℕ) (jMin F k) z)
      = WithZero.exp (-(m * ((k : ℤ) + jMin F k))) :=
    v_trExp F k (jMin F k) z m hz hzv hm le_rfl
  have hlt : Valued.v W < Valued.v (trExp F (k : ℕ) (jMin F k) z) := by
    rw [htr]
    refine lt_of_le_of_lt h2 ?_
    rw [WithZero.exp_lt_exp]
    have hkk : (0 : ℤ) < (k : ℤ) := by exact_mod_cast k.pos
    nlinarith
  rw [h1, Valuation.map_add_eq_of_lt_left (v := Valued.v) hlt, htr]

/-- `X` as an element of the completion at infinity. -/
noncomputable def XK : RatFunc.CompletionAtInfty F := toK F RatFunc.X

lemma v_XK : Valued.v (XK F) = WithZero.exp (1 : ℤ) := v_toK_X F

lemma XK_ne_zero : XK F ≠ 0 := by
  intro h
  have h1 : Valued.v (XK F) = 0 := by rw [h, map_zero]
  rw [v_XK F] at h1
  exact WithZero.exp_ne_zero h1

lemma coe_X_add_C (c : F) :
    (((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F)
      = XK F + cst F c := by
  have h1 : (((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F))
      = RatFunc.X + algebraMap F (RatFunc F) c := by
    rw [show ((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)
        = algebraMap F[X] (RatFunc F) (Polynomial.X + Polynomial.C c) from rfl, map_add]
    congr 1
  rw [h1]
  show toK F (RatFunc.X + algebraMap F (RatFunc F) c) = XK F + cst F c
  rw [map_add]
  rfl

lemma X_add_C_ne_zero (c : F) : (Polynomial.X + Polynomial.C c : F[X]) ≠ 0 := by
  intro h
  have := Polynomial.natDegree_X_add_C c
  rw [h, Polynomial.natDegree_zero] at this
  exact absurd this (by norm_num)

lemma intDegree_X_add_C (c : F) :
    (((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)).intDegree = 1 := by
  rw [show ((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)
      = algebraMap F[X] (RatFunc F) (Polynomial.X + Polynomial.C c) from rfl,
    RatFunc.intDegree_polynomial, Polynomial.natDegree_X_add_C]
  norm_num

lemma coe_X_add_C_ne_zero (c : F) :
    (((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F)) ≠ 0 := by
  intro h
  have h1 := intDegree_X_add_C F c
  rw [h, RatFunc.intDegree_zero] at h1
  norm_num at h1

lemma v_XK_add_cst (c : F) : Valued.v (XK F + cst F c) = Valued.v (XK F) := by
  rw [← coe_X_add_C F c]
  change Valued.v (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)
      (((Polynomial.X + Polynomial.C c : F[X]) : RatFunc F))) = Valued.v (XK F)
  rw [v_toK F _ (coe_X_add_C_ne_zero F c), intDegree_X_add_C F c, v_XK F]

/-- ★★ **Thakur's theorem 3.1 for the depth-one power sum**: the degree at infinity of
`S_1(k) = ∑_{c : F} (X + c)^{-k}` is `−(k + j_min(k))`; equivalently the power sum has
valuation `exp (−(k + j_min(k)))` in the completion. -/
theorem val_P_one (k : ℕ+) :
    Valued.v (P F 1 k) = WithZero.exp (-((k : ℤ) + jMin F k)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hP : P F 1 k = zetaSum F (k : ℕ) (XK F) := by
    rw [P_one_eq_sum_translate F k, zetaSum]
    apply Finset.sum_congr rfl
    intro c _
    rw [coe_X_add_C F c]
  rw [hP]
  have h := v_zetaSum F k (XK F) 1 (XK_ne_zero F) (v_XK F) one_pos (v_XK_add_cst F)
  simpa using h

end Main

end ZagierHoffmanPositiveChar
