import Mathlib.FieldTheory.Finite.Basic
import Submission.ZagierHoffmanProof.StepA3
import Submission.Commons.Algebra.Binomial.trunc_inv_add_one
import Submission.Commons.FieldTheory.Finite.sum_units_inv_pow
import Submission.Commons.FieldTheory.Finite.sum_erase_zero_eq_units
import Submission.Commons.FieldTheory.Polynomial.unit_inv_cong

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The level-one shuffle identity `(P1)` and its divisibility core `(S4)`

`(P1)` is the polynomial avatar of `(2.1)` at `d = 1` (Thakur's product identity,
Chen's explicit coefficients):

    A_a · A_b  =  A_{a+b}  +  Σ_{0<i<a+b} Δ^i_{a,b} · [1]^i · A_{a+b-i}        in F[X]

with `A_n = Σ_c Q_c^n`, `Q_c = ∏_{b≠c}(X + C b)`, `[1] = X^q - X`.
The difference polynomial is `thakurP1Q`.

Strategy (validated numerically in /tmp/val_modY.py):
  (S1) `Q` is translation invariant (`Q(X + θ) = Q(X)`),
  (S2) `natDegree Q ≤ (a+b)·q − 1 < q·(a+b) = natDegree [1]^{a+b}`,
  (S3) `X^{a+b} | Q` (the core, `S4`) forces `Q = 0`:
       by (S1) `(X + θ)^{a+b} | Q` for all `θ`, so `[1]^{a+b} | Q`
       (pairwise coprime linear factors), and the degree bound kills `Q`.
  (S4) `X^{a+b} | Q` is proved by expanding each `A_n` modulo `X^{a+b}`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `(P1)`-difference polynomial:
`A_a·A_b − A_{a+b} − Σ_{0<i<a+b} Δ^i [1]^i A_{a+b-i}`. -/
noncomputable def thakurP1Q (a b : ℕ) : F[X] :=
  A F a * A F b - A F (a + b) -
    ∑ i ∈ Finset.Icc 1 (a + b - 1),
      Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)

-- basic degree facts ------------------------------------------------

lemma carlitzOne_monic : (carlitzOne F).Monic := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [carlitzOne_eq_prod_X_add_C F]
  change (∏ c ∈ (Finset.univ : Finset F), (X + C c)).Monic
  exact Polynomial.monic_prod_of_monic (s := (Finset.univ : Finset F))
    (f := fun c : F => X + C c) (by
      intro c hc
      exact Polynomial.monic_X_add_C c)

lemma carlitzOne_natDegree_pow (n : ℕ) : ((carlitzOne F) ^ n).natDegree = n * Nat.card F := by
  rw [(carlitzOne_monic F).natDegree_pow n, carlitzOne_natDegree F]

/-- Multiplying by a constant does not increase the natural degree. -/
lemma natDegree_C_mul_le (c : F) (p : F[X]) :
    (Polynomial.C c * p).natDegree ≤ p.natDegree := by
  calc
    (Polynomial.C c * p).natDegree ≤ (Polynomial.C c).natDegree + p.natDegree :=
      Polynomial.natDegree_mul_le
    _ = p.natDegree := by rw [Polynomial.natDegree_C]; simp

-- small arithmetic lemmas over `ℕ` --------------------------------

/-- `i·q + (a+b−i)·(q−1) = (a+b)·(q−1) + i` for `1 ≤ i ≤ a+b−1`, `2 ≤ q`. -/
lemma arith_split (a b i q : ℕ) (hq : 2 ≤ q) (hi1 : 1 ≤ i) (hi2 : i ≤ a + b - 1) :
    i * q + (a + b - i) * (q - 1) = (a + b) * (q - 1) + i := by
  have hiab : i ≤ a + b := by omega
  have hsub : (a + b - i) + i = a + b := Nat.sub_add_cancel hiab
  have hqsplit : (q - 1) + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
  nlinarith

/-- `(a+b)·(q−1) + (a+b−1) = (a+b)·q − 1` for `2 ≤ q`, `2 ≤ a+b`. -/
lemma arith_combine (a b q : ℕ) (hq : 2 ≤ q) (hab : 2 ≤ a + b) :
    (a + b) * (q - 1) + (a + b - 1) = (a + b) * q - 1 := by
  have hle : a + b ≤ (a + b) * q := Nat.le_mul_of_pos_right (a + b) (by omega : 0 < q)
  calc
    (a + b) * (q - 1) + (a + b - 1)
        = ((a + b) * q - (a + b) * 1) + (a + b - 1) := by
            rw [Nat.mul_sub_left_distrib]
      _ = ((a + b) * q - (a + b)) + (a + b - 1) := by rw [mul_one]
      _ = (a + b) * q - 1 := by omega

/-- `(a+b)·(q−1) ≤ (a+b)·q − 1` for `1 ≤ a+b`, `2 ≤ q`. -/
lemma arith_loose (a b q : ℕ) (hq : 2 ≤ q) (hab : 1 ≤ a + b) :
    (a + b) * (q - 1) ≤ (a + b) * q - 1 := by
  have hq1 : 1 ≤ q := by omega
  calc
    (a + b) * (q - 1) = (a + b) * q - (a + b) * 1 := by rw [Nat.mul_sub_left_distrib]
    _ = (a + b) * q - (a + b) := by rw [mul_one]
    _ ≤ (a + b) * q - 1 := by omega

-- ============================================================
-- (S1) translation invariance
-- ============================================================

/-- Each summand `Δ^i·[1]^i·A_{a+b-i}` is translation invariant. -/
lemma P1_summand_comp_add (a b i : ℕ) (θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (((Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).comp (X + C θ))) =
      Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  calc
    ((C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).comp (X + C θ))
        = (C (ChenDeltaZ F a b i : F)).comp (X + C θ) *
            ((carlitzOne F) ^ i).comp (X + C θ) *
            (A F (a + b - i)).comp (X + C θ) := by
          rw [Polynomial.mul_comp, Polynomial.mul_comp]
    _ = C (ChenDeltaZ F a b i : F) *
            ((carlitzOne F) ^ i).comp (X + C θ) *
            (A F (a + b - i)).comp (X + C θ) := by
          rw [Polynomial.C_comp]
    _ = C (ChenDeltaZ F a b i : F) * ((carlitzOne F) ^ i) * (A F (a + b - i)) := by
          rw [Polynomial.pow_comp, carlitzOne_comp_add F θ, A_comp_add F (a + b - i) θ]

/-- (S1): the `(P1)`-difference is translation invariant. -/
lemma thakurP1Q_comp_add (a b : ℕ) (θ : F) :
    letI : Fintype F := Fintype.ofFinite F
    (thakurP1Q F a b).comp (X + C θ) = thakurP1Q F a b := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  unfold thakurP1Q
  calc
    ((A F a * A F b - A F (a + b) - (∑ i ∈ Finset.Icc 1 (a + b - 1),
        Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))).comp (X + C θ))
        = ((A F a * A F b - A F (a + b)).comp (X + C θ)) -
            ((∑ i ∈ Finset.Icc 1 (a + b - 1),
              Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).comp (X + C θ)) := by
          rw [Polynomial.sub_comp]
    _ = ((A F a * A F b).comp (X + C θ) - (A F (a + b)).comp (X + C θ)) -
            ((∑ i ∈ Finset.Icc 1 (a + b - 1),
              Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).comp (X + C θ)) := by
          rw [Polynomial.sub_comp]
    _ = (A F a * A F b - A F (a + b)) -
            (∑ i ∈ Finset.Icc 1 (a + b - 1),
              (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).comp (X + C θ)) := by
          rw [Polynomial.mul_comp, A_comp_add F a θ, A_comp_add F b θ, A_comp_add F (a + b) θ]
          rw [Polynomial.sum_comp]
    _ = A F a * A F b - A F (a + b) -
          (∑ i ∈ Finset.Icc 1 (a + b - 1),
            Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact P1_summand_comp_add F a b i θ

-- ============================================================
-- (S2) degree bound
-- ============================================================

/-- Bound for a single summand `C Δ · [1]^i · A_{a+b-i}`, `1 ≤ i ≤ a+b−1`,
`1 ≤ a`, `1 ≤ b`. -/
lemma P1_summand_natDegree_le (a b i : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hi1 : 1 ≤ i) (hi2 : i ≤ a + b - 1) :
    letI : Fintype F := Fintype.ofFinite F
    ((Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).natDegree) ≤
      (a + b) * Nat.card F - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  calc
    ((C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).natDegree)
        ≤ (C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i).natDegree
            + (A F (a + b - i)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ ((carlitzOne F) ^ i).natDegree + (A F (a + b - i)).natDegree := by
        exact Nat.add_le_add_right
          (natDegree_C_mul_le F (ChenDeltaZ F a b i : F) ((carlitzOne F) ^ i)) _
    _ ≤ ((carlitzOne F) ^ i).natDegree + (a + b - i) * (Nat.card F - 1) := by
        exact Nat.add_le_add_left (A_natDegree_le F (a + b - i)) _
    _ = i * Nat.card F + (a + b - i) * (Nat.card F - 1) := by
        rw [carlitzOne_natDegree_pow F i]
    _ ≤ (a + b) * Nat.card F - 1 := by
        calc
          i * Nat.card F + (a + b - i) * (Nat.card F - 1)
              = (a + b) * (Nat.card F - 1) + i := arith_split a b i (Nat.card F) hq hi1 hi2
          _ ≤ (a + b) * (Nat.card F - 1) + (a + b - 1) :=
              Nat.add_le_add_left hi2 ((a + b) * (Nat.card F - 1))
          _ = (a + b) * Nat.card F - 1 := arith_combine a b (Nat.card F) hq (by omega)

/-- (S2): natural degree of the `(P1)`-difference is `≤ (a+b)·q − 1`. -/
lemma thakurP1Q_natDegree_le (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    (thakurP1Q F a b).natDegree ≤ (a + b) * Nat.card F - 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let B : ℕ := (a + b) * Nat.card F - 1
  have hq : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  have hab : 1 ≤ a + b := by omega
  have hprod : (A F a * A F b).natDegree ≤ B := by
    calc
      (A F a * A F b).natDegree ≤ (A F a).natDegree + (A F b).natDegree := Polynomial.natDegree_mul_le
      _ ≤ a * (Nat.card F - 1) + b * (Nat.card F - 1) := by
          exact Nat.add_le_add (A_natDegree_le F a) (A_natDegree_le F b)
      _ = (a + b) * (Nat.card F - 1) := by rw [Nat.add_mul]
      _ ≤ B := by
          dsimp [B]
          exact arith_loose a b (Nat.card F) hq hab
  have hAab : (A F (a + b)).natDegree ≤ B := by
    calc
      (A F (a + b)).natDegree ≤ (a + b) * (Nat.card F - 1) := A_natDegree_le F (a + b)
      _ ≤ B := by
          dsimp [B]
          exact arith_loose a b (Nat.card F) hq hab
  have hsum : ((∑ i ∈ Finset.Icc 1 (a + b - 1),
        Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).natDegree) ≤ B := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hmem : i ∈ Finset.Icc 1 (a + b - 1) := hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hmem).1
    have hi2 : i ≤ a + b - 1 := (Finset.mem_Icc.mp hmem).2
    have hbnd := P1_summand_natDegree_le F a b i ha hb hi1 hi2
    dsimp [B] at hbnd ⊢
    exact hbnd
  -- assemble
  calc
    (thakurP1Q F a b).natDegree
        = ((A F a * A F b - A F (a + b)) -
            (∑ i ∈ Finset.Icc 1 (a + b - 1),
              Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))).natDegree := by
            rfl
    _ ≤ max (A F a * A F b - A F (a + b)).natDegree
          ((∑ i ∈ Finset.Icc 1 (a + b - 1),
            Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)).natDegree) :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ B := by
        apply max_le
        · calc
            (A F a * A F b - A F (a + b)).natDegree
                ≤ max (A F a * A F b).natDegree (A F (a + b)).natDegree :=
                  Polynomial.natDegree_sub_le _ _
            _ ≤ B := by
                apply max_le
                · exact hprod
                · exact hAab
        · dsimp [B]
          exact hsum

-- ============================================================
-- (S3) divisibility forces zero
-- ============================================================

/-- If `X^(a+b) | Q` and `Q` is translation invariant with `natDegree Q < (a+b)·q`,
then `Q = 0`. -/
lemma thakurP1Q_eq_zero_of_X_pow_dvd (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hdvd : X ^ (a + b) ∣ thakurP1Q F a b) :
    letI : Fintype F := Fintype.ofFinite F
    thakurP1Q F a b = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  by_contra hQ
  have hq : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  -- from translation invariance and X^(a+b) | Q get (X + C c)^(a+b) | Q for all c
  have hall : ∀ c : F, (X + C c) ^ (a + b) ∣ thakurP1Q F a b := by
    intro c
    exact shift_dvd_of_dvd_comp F (thakurP1Q F a b) (a + b) c (thakurP1Q_comp_add F a b c) hdvd
  have hcar : (carlitzOne F) ^ (a + b) ∣ thakurP1Q F a b :=
    carlitzOne_pow_dvd_of_shift_dvd F (thakurP1Q F a b) (a + b) hall
  have hdegQ : (thakurP1Q F a b).natDegree < ((carlitzOne F) ^ (a + b)).natDegree := by
    calc
      (thakurP1Q F a b).natDegree ≤ (a + b) * Nat.card F - 1 := thakurP1Q_natDegree_le F a b ha hb
      _ < ((carlitzOne F) ^ (a + b)).natDegree := by
          rw [carlitzOne_natDegree_pow F (a + b)]
          have hpos : 0 < (a + b) * Nat.card F := by
            exact mul_pos (by omega : 0 < a + b) (by omega : 0 < Nat.card F)
          exact Nat.sub_lt hpos (by norm_num)
  have hle := Polynomial.natDegree_le_of_dvd hcar hQ
  omega

-- ============================================================
-- (S4) machinery, part I: congruences modulo X^N and truncated series
-- ============================================================

/-- `p ≡ q (mod X^n)`, i.e. `X^n | p - q`. -/
def Cong (n : ℕ) (p q : F[X]) : Prop := X ^ n ∣ p - q
attribute [irreducible] Cong

namespace Cong

lemma refl (n : ℕ) (p : F[X]) : Cong F n p p := by
  unfold Cong
  simp

lemma symm {n : ℕ} {p q : F[X]} (h : Cong F n p q) : Cong F n q p := by
  unfold Cong at h ⊢
  rw [← neg_sub]
  exact dvd_neg.mpr h

lemma trans {n : ℕ} {p q r : F[X]} (hpq : Cong F n p q) (hqr : Cong F n q r) :
    Cong F n p r := by
  unfold Cong at hpq hqr ⊢
  have : X ^ n ∣ (p - q) + (q - r) := dvd_add hpq hqr
  convert this using 1
  ring

lemma congr_right {n : ℕ} {p q r : F[X]} (h : Cong F n p q) (hq : q = r) :
    Cong F n p r := by
  simpa [hq] using h

lemma congr_left {n : ℕ} {p q r : F[X]} (h : Cong F n q r) (hp : p = q) :
    Cong F n p r := by
  simpa [hp] using h

lemma add {n : ℕ} {p p' q q' : F[X]} (hp : Cong F n p p') (hq : Cong F n q q') :
    Cong F n (p + q) (p' + q') := by
  unfold Cong at hp hq ⊢
  have : X ^ n ∣ (p - p') + (q - q') := dvd_add hp hq
  convert this using 1
  ring

lemma sub {n : ℕ} {p p' q q' : F[X]} (hp : Cong F n p p') (hq : Cong F n q q') :
    Cong F n (p - q) (p' - q') := by
  unfold Cong at hp hq ⊢
  have : X ^ n ∣ (p - p') - (q - q') := dvd_sub hp hq
  convert this using 1
  ring

lemma mul {n : ℕ} {p p' q q' : F[X]} (hp : Cong F n p p') (hq : Cong F n q q') :
    Cong F n (p * q) (p' * q') := by
  unfold Cong at hp hq ⊢
  have h1 : X ^ n ∣ p * q - p' * q := by
    have h1' : X ^ n ∣ q * (p - p') := dvd_mul_of_dvd_right hp q
    convert h1' using 1
    ring
  have h2 : X ^ n ∣ p' * q - p' * q' := by
    have h2' : X ^ n ∣ (q - q') * p' := dvd_mul_of_dvd_left hq p'
    convert h2' using 1
    ring
  have : X ^ n ∣ (p * q - p' * q) + (p' * q - p' * q') := dvd_add h1 h2
  convert this using 1
  ring

lemma mul_left {n : ℕ} {p q : F[X]} (r : F[X]) (h : Cong F n p q) : Cong F n (r * p) (r * q) := by
  simpa using mul F (refl F n r) h

lemma mul_right {n : ℕ} {p q : F[X]} (r : F[X]) (h : Cong F n p q) : Cong F n (p * r) (q * r) := by
  simpa [mul_comm] using mul F h (refl F n r)

lemma neg {n : ℕ} {p q : F[X]} (h : Cong F n p q) : Cong F n (-p) (-q) := by
  simpa using sub F (refl F n 0) h

lemma pow {n k : ℕ} {p q : F[X]} (h : Cong F n p q) : Cong F n (p ^ k) (q ^ k) := by
  induction k with
  | zero => simpa using refl F n (1 : F[X])
  | succ k ih =>
      simpa [pow_succ] using mul F ih h

lemma zero_right {n : ℕ} (p : F[X]) : Cong F n p p := refl F n p

/-- From `X^n | p` get `Cong n p 0`. -/
lemma of_dvd_zero {n : ℕ} {p : F[X]} (h : X ^ n ∣ p) : Cong F n p 0 := by
  unfold Cong
  simpa using h

/-- From `Cong n p 0` get `X^n | p`. -/
lemma dvd_zero {n : ℕ} {p : F[X]} (h : Cong F n p 0) : X ^ n ∣ p := by
  unfold Cong at h
  simpa using h

lemma symm_zero {n : ℕ} {p : F[X]} (h : Cong F n 0 p) : X ^ n ∣ p := by
  unfold Cong at h
  rw [zero_sub, dvd_neg] at h
  simpa using h

lemma of_dvd_zero' {n : ℕ} {p : F[X]} (h : X ^ n ∣ p) : Cong F n 0 p := by
  unfold Cong
  rw [zero_sub]
  exact dvd_neg.mpr h

end Cong


/-- The power sum over `F*` of the `m`-th inverse powers (as an `F`-valued scalar):
`Σ_{c ∈ F, c ≠ 0} (c : F)⁻¹ ^ m`. -/
noncomputable def FstarSum (m : ℕ) : F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  exact ∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (c : F)⁻¹ ^ m

/-- Truncated inverse of `X + c` (`c ≠ 0`) at degree `< N`:
`Σ_{k<N} (-1)^k C(n+k-1,k) c^{-(n+k)} X^k`. -/
noncomputable def invTrunc (c : F) (n N : ℕ) : F[X] :=
  ∑ k ∈ Finset.range N,
    Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : F) * (c)⁻¹ ^ (n + k)) * X ^ k

/-- The coefficient series `Σ_{k<N} (-1)^k C(n+k-1,k) Σ_{u} u^{-(n+k)} X^k`; this is
`Σ_{u : Fˣ} invTrunc (u : F) n N` (see `units_invTrunc_sum`). -/
noncomputable def Vser (n N : ℕ) : F[X] :=
  ∑ k ∈ Finset.range N,
    Polynomial.C ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : F) * FstarSum F (n + k)) * X ^ k

/-- coefficient of `X^k` in `Vser` for `k < N`. -/
lemma Vser_coeff (n N k : ℕ) (hk : k < N) :
    (Vser F n N).coeff k =
      ((((-1 : ℤ) ^ k * (Nat.choose (n + k - 1) k : ℤ)) : F) * FstarSum F (n + k)) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  unfold Vser
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h; exact hbk h.symm
  · intro hk'
    exfalso
    exact hk' (Finset.mem_range.mpr hk)

/-- coefficient of `X^k` in `Vser` for `N ≤ k` is zero. -/
lemma Vser_coeff_ge (n N k : ℕ) (hk : N ≤ k) :
    (Vser F n N).coeff k = 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  unfold Vser
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Polynomial.coeff_C_mul_X_pow]
  have hbk : b ≠ k := by
    intro hbk
    have : b < k := lt_of_lt_of_le (Finset.mem_range.mp hb) hk
    exact (Nat.ne_of_lt this) hbk
  rw [if_neg (Ne.symm hbk)]

-- ============================================================
-- (S4) machinery, part II: Chen's coefficient identity
-- ============================================================

/-- `(-1)^(a-1) = -(-1)^(e-a)` over `ℤ`, for `1 ≤ a ≤ e` and `e` even. -/
lemma int_negOne_pow_sub (a e : ℕ) (ha : 1 ≤ a) (he1 : 1 ≤ e) (hae : a ≤ e) (he : Even e) :
    ((-1 : ℤ) ^ (a - 1)) = -((-1 : ℤ) ^ (e - a)) := by
  have hprod : ((-1 : ℤ) ^ (a - 1)) * ((-1 : ℤ) ^ (e - a)) = -1 := by
    rw [← pow_add]
    have hsum : (a - 1) + (e - a) = e - 1 := by omega
    rw [hsum]
    have hodd : Odd (e - 1) := by
      rcases he with ⟨r, hr⟩
      use r - 1
      omega
    rw [hodd.neg_one_pow]
  have hsq : ((-1 : ℤ) ^ (e - a)) ^ 2 = 1 := by
    rw [← pow_mul]
    have heven : Even (2 * (e - a)) := ⟨e - a, by ring⟩
    simpa using heven.neg_one_pow (α := ℤ)
  calc
    (-1 : ℤ) ^ (a - 1) = ((-1 : ℤ) ^ (a - 1)) * 1 := by ring
    _ = ((-1 : ℤ) ^ (a - 1)) * ((-1 : ℤ) ^ (e - a)) ^ 2 := by rw [hsq]
    _ = (((-1 : ℤ) ^ (a - 1)) * ((-1 : ℤ) ^ (e - a))) * ((-1 : ℤ) ^ (e - a)) := by ring
    _ = -1 * ((-1 : ℤ) ^ (e - a)) := by rw [hprod]
    _ = -((-1 : ℤ) ^ (e - a)) := by ring

/-- Same identity in the coefficient field `F` (holds in every ring, since only
`(-1)^2 = 1` and `-(-1) = 1` are used). -/
lemma negOne_pow_sub (a e : ℕ) (ha : 1 ≤ a) (he1 : 1 ≤ e) (hae : a ≤ e) (he : Even e) :
    (-1 : F) ^ (a - 1) = -((-1 : F) ^ (e - a)) := by
  have hz := int_negOne_pow_sub a e ha he1 hae he
  apply_fun (fun z : ℤ => (z : F)) at hz
  simpa [Int.cast_pow, Int.cast_neg] using hz

/-- If `q - 1 | e` and `e` is odd then `F` has characteristic `2`. -/
lemma char_two_of_dvd_odd (e : ℕ) (hdiv : (Nat.card F - 1) ∣ e) (hodd : ¬ Even e) :
    letI : Fintype F := Fintype.ofFinite F
    ringChar F = 2 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  have hqnot : ¬ (2 ∣ Nat.card F - 1) := by
    intro h2
    have : 2 ∣ e := dvd_trans h2 hdiv
    exact hodd (even_iff_two_dvd.mpr this)
  have hqnotE : ¬ Even (Nat.card F - 1) := fun h => hqnot (even_iff_two_dvd.mp h)
  have hoddq : Odd (Nat.card F - 1) := Nat.not_even_iff_odd.mp hqnotE
  have hqeven : Even (Nat.card F) := by
    rcases hoddq with ⟨k, hk⟩
    use k + 1
    omega
  have hqev : 2 ∣ Nat.card F := even_iff_two_dvd.mp hqeven
  have hdiv2 : 2 ∣ Fintype.card F := by
    rw [Fintype.card_eq_nat_card]
    exact hqev
  have hmod : Fintype.card F % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv2
  exact (FiniteField.even_card_iff_char_two (F := F)).mpr hmod

/-- Per-term sign identity with the binomial coefficient (the case `(q-1) | e`). -/
lemma chen_coeff_term (a e : ℕ) (ha : 1 ≤ a) (he1 : 1 ≤ e)
    (hdiv : (Nat.card F - 1) ∣ e) :
    ((-1 : F) ^ (a - 1)) * (Nat.choose (e - 1) (a - 1) : F)
      = -(((-1 : F) ^ (e - a)) * (Nat.choose (e - 1) (a - 1) : F)) := by
  by_cases hC : Nat.choose (e - 1) (a - 1) = 0
  · rw [hC]
    simp
  · have hpos : 0 < Nat.choose (e - 1) (a - 1) := Nat.pos_of_ne_zero hC
    have hae : a ≤ e := by
      have hlt : ¬ (e - 1) < (a - 1) := by
        intro hl
        exact hC ((Nat.choose_eq_zero_iff).2 hl)
      omega
    by_cases he : Even e
    · have hs := negOne_pow_sub F a e ha he1 hae he
      calc
        (-1 : F) ^ (a - 1) * (Nat.choose (e - 1) (a - 1) : F)
            = (-((-1 : F) ^ (e - a))) * (Nat.choose (e - 1) (a - 1) : F) := by rw [hs]
        _ = -(((-1 : F) ^ (e - a)) * (Nat.choose (e - 1) (a - 1) : F)) := by ring
    · have hch : ringChar F = 2 := by
        simpa using char_two_of_dvd_odd F e hdiv he
      have hchar : CharP F 2 := ringChar.of_eq hch
      have hneg : (-1 : F) = 1 := by
        simpa using (CharTwo.neg_eq (R := F) (1 : F))
      have hm : -(Nat.choose (e - 1) (a - 1) : F) = (Nat.choose (e - 1) (a - 1) : F) :=
        CharTwo.neg_eq (R := F) (Nat.choose (e - 1) (a - 1) : F)
      calc
        (-1 : F) ^ (a - 1) * (Nat.choose (e - 1) (a - 1) : F)
            = (1 : F) ^ (a - 1) * (Nat.choose (e - 1) (a - 1) : F) := by rw [hneg]
        _ = (Nat.choose (e - 1) (a - 1) : F) := by simp
        _ = -((1 : F) ^ (e - a) * (Nat.choose (e - 1) (a - 1) : F)) := by
            simp
            exact hm.symm
        _ = -(((-1 : F) ^ (e - a)) * (Nat.choose (e - 1) (a - 1) : F)) := by rw [hneg]

/-- Casting `(if Even n then (1 : ℤ) else -1)` into `F` gives `(-1 : F) ^ n`. -/
lemma cast_even_sign (n : ℕ) : ((if Even n then (1 : ℤ) else -1) : F) = (-1 : F) ^ n := by
  by_cases h : Even n
  · rw [if_pos h]
    rw [h.neg_one_pow]
    norm_num
  · have hodd : Odd n := Nat.not_even_iff_odd.mp h
    rw [if_neg h]
    rw [hodd.neg_one_pow]

/-- Chen's delta (divisibility case) as powers of `-1`. -/
lemma chen_delta_neg_pow (a b e : ℕ) (hdiv : (Nat.card F - 1) ∣ e) :
    (ChenDeltaZ F a b e : F) =
      ((-1 : F) ^ (a - 1)) * (Nat.choose (e - 1) (a - 1) : F) +
        ((-1 : F) ^ (b - 1)) * (Nat.choose (e - 1) (b - 1) : F) := by
  unfold ChenDeltaZ
  rw [if_pos hdiv]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [← cast_even_sign F (a - 1), ← cast_even_sign F (b - 1)]
  simp

/-- Chen's coefficient identity (S4-CC): for `1 ≤ e < a+b`,
`Δ^e_{a,b}` equals the `X^e`-coefficient of the truncated product expansion. -/
lemma chen_coeff_eq (a b e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (he1 : 1 ≤ e) (helt : e < a + b) :
    (ChenDeltaZ F a b e : F) =
      - (if (Nat.card F - 1) ∣ e then (1 : F) else 0) *
        (((-1 : F) ^ (e - a)) * (Nat.choose (e - 1) (a - 1) : F) +
          ((-1 : F) ^ (e - b)) * (Nat.choose (e - 1) (b - 1) : F)) := by
  classical
  by_cases hdiv : (Nat.card F - 1) ∣ e
  · have h1 := chen_coeff_term F a e ha he1 hdiv
    have h2 := chen_coeff_term F b e hb he1 hdiv
    have hd := chen_delta_neg_pow F a b e hdiv
    rw [hd]
    rw [h1, h2]
    simp [hdiv]
    ring
  · unfold ChenDeltaZ
    simp [hdiv]

-- ============================================================
-- (S4) machinery, part III: the coefficient of the truncated series
-- ============================================================

/-- The `F*`-power sum: `Σ_{u : Fˣ} (u:F)⁻¹ ^ m` equals `-1` if `(q-1) | m`, else `0`
(`0 < m`). -/
lemma FstarSum_eq (m : ℕ) (hm : 0 < m) :
    FstarSum F m = if (Nat.card F - 1) ∣ m then (-1 : F) else 0 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Nat.card F := Fintype.card_eq_nat_card
  unfold FstarSum
  rw [Commons.FieldTheory.Finite.sum_erase_zero_eq_units (K := F) (fun c : F => (c : F)⁻¹ ^ m)]
  have h := Commons.FieldTheory.Finite.sum_units_inv_pow (K := F) m hm
  rwa [hcard] at h

/-- The coefficient of `X^e` in `X^n·Vser(n,N)` (`e < N`, `n,e ≥ 1`):
`-[(q-1)|e]·(-1)^(e-n)·C(e-1,n-1)`. -/
lemma coeff_X_pow_Vser (n e N : ℕ) (hn : 1 ≤ n) (he1 : 1 ≤ e) (helt : e < N) :
    (X ^ n * Vser F n N).coeff e =
      - (if (Nat.card F - 1) ∣ e then (1 : F) else 0) *
        ((-1 : F) ^ (e - n)) * (Nat.choose (e - 1) (n - 1) : F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  by_cases hd : (Nat.card F - 1) ∣ e
  · by_cases hne : n ≤ e
    · have hel' : e - n < N := by omega
      rw [Polynomial.coeff_X_pow_mul', if_pos hne]
      rw [Vser_coeff F n N (e - n) hel']
      have hesum : n + (e - n) = e := by omega
      rw [hesum]
      rw [FstarSum_eq F e (by omega : 1 ≤ e), if_pos hd]
      rw [if_pos hd]
      have hni : (↑(-1 : ℤ) : F) = (-1 : F) := by norm_num
      rw [Int.cast_natCast]
      rw [hni]
      have hCsym : (Nat.choose (e - 1) (e - n) : F) = (Nat.choose (e - 1) (n - 1) : F) := by
        congr 1
        have h1 : e - n ≤ e - 1 := by omega
        have hs := Nat.choose_symm (n := e - 1) (k := e - n) h1
        have : (e - 1) - (e - n) = n - 1 := by omega
        rw [this] at hs
        exact hs.symm
      rw [hCsym]
      ring
    · rw [Polynomial.coeff_X_pow_mul', if_neg hne]
      have hC : Nat.choose (e - 1) (n - 1) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      rw [hC]
      simp
  · by_cases hne : n ≤ e
    · have hel' : e - n < N := by omega
      rw [Polynomial.coeff_X_pow_mul', if_pos hne]
      rw [Vser_coeff F n N (e - n) hel']
      have hesum : n + (e - n) = e := by omega
      rw [hesum]
      rw [FstarSum_eq F e (by omega : 1 ≤ e), if_neg hd]
      rw [if_neg hd]
      simp
    · rw [Polynomial.coeff_X_pow_mul', if_neg hne]
      rw [if_neg hd]
      simp

/-- The coefficient contribution of the two `Vser` terms equals Chen's `Δ^e`. -/
lemma W_coeff (a b e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (he1 : 1 ≤ e) (helt : e < a + b) :
    (X ^ a * Vser F a (a + b)).coeff e + (X ^ b * Vser F b (a + b)).coeff e =
      (ChenDeltaZ F a b e : F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hce := chen_coeff_eq F a b e ha hb he1 helt
  rw [hce]
  rw [coeff_X_pow_Vser F a e (a + b) ha he1 helt]
  rw [coeff_X_pow_Vser F b e (a + b) hb he1 helt]
  ring

/-- The truncated combination `W := X^a V_a + X^b V_b − Σ Δ_i X^i` is divisible by
`X^(a+b)`. -/
lemma W_dvd (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    X ^ (a + b) ∣
      (X ^ a * Vser F a (a + b) + X ^ b * Vser F b (a + b) -
        ∑ i ∈ Finset.Icc 1 (a + b - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [Polynomial.X_pow_dvd_iff]
  intro e he
  by_cases he0 : e = 0
  · subst e
    have ha0 : ¬ a ≤ 0 := by omega
    have hb0 : ¬ b ≤ 0 := by omega
    have hS : (∑ i ∈ Finset.Icc 1 (a + b - 1),
        Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i).coeff 0 = 0 := by
      rw [finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Polynomial.coeff_C_mul_X_pow]
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hne : (0 : ℕ) ≠ i := by omega
      rw [if_neg hne]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add]
    rw [Polynomial.coeff_X_pow_mul', if_neg ha0]
    rw [Polynomial.coeff_X_pow_mul', if_neg hb0]
    rw [hS]
    simp
  · have he1 : 1 ≤ e := Nat.succ_le_of_lt (Nat.pos_of_ne_zero he0)
    have helt : e < a + b := he
    calc
      ((X ^ a * Vser F a (a + b) + X ^ b * Vser F b (a + b) -
          ∑ i ∈ Finset.Icc 1 (a + b - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i).coeff e)
          = (X ^ a * Vser F a (a + b)).coeff e + (X ^ b * Vser F b (a + b)).coeff e
              - (∑ i ∈ Finset.Icc 1 (a + b - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i).coeff e := by
            rw [coeff_sub, coeff_add]
      _ = (X ^ a * Vser F a (a + b)).coeff e + (X ^ b * Vser F b (a + b)).coeff e
              - (ChenDeltaZ F a b e : F) := by
            congr 1
            rw [finsetSum_coeff]
            rw [Finset.sum_eq_single e]
            · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
            · intro b' hb' hb'e
              rw [Polynomial.coeff_C_mul_X_pow, if_neg]
              intro h; exact hb'e h.symm
            · intro he'
              exfalso
              exact he' (by
                simp only [Finset.mem_Icc]
                exact ⟨he1, by omega⟩)
      _ = 0 := by
            rw [W_coeff F a b e ha hb he1 helt]
            simp

-- ============================================================
-- (S4) machinery, part IV: expansion of A_n modulo X^N
-- ============================================================

/-- `X` and `X + C c` are coprime for `c ≠ 0`. -/
lemma coprime_XpC_X (c : F) (hc : c ≠ 0) : IsCoprime (X + C c : F[X]) (X : F[X]) := by
  refine ⟨C (c⁻¹), -C (c⁻¹), ?_⟩
  calc
    C (c⁻¹) * (X + C c) + (-C (c⁻¹)) * X = C (c⁻¹) * C c := by ring
    _ = C (c⁻¹ * c) := by rw [← C_mul]
    _ = 1 := by simp [inv_mul_cancel₀ hc]

/-- If `X^N | (X + C c)^n · p` with `c ≠ 0`, then `X^N | p`. -/
lemma dvd_of_dvd_mul_XpC (c : F) (hc : c ≠ 0) (n N : ℕ) {p : F[X]}
    (h : X ^ N ∣ (X + C c) ^ n * p) : X ^ N ∣ p := by
  have h1 : IsCoprime ((X + C c) ^ n) (X ^ N) := by
    exact (IsCoprime.pow_left (m := n) (coprime_XpC_X F c hc)).pow_right (n := N)
  exact h1.symm.dvd_of_dvd_mul_left h

/-- `[1] = X · (X^(q-1) - 1)`: `carlitzOne = X · qPoly 0`. -/
lemma carlitzOne_eq_X_mul_qPoly0 :
    carlitzOne F = X * qPoly F (0 : F) := by
  have h := carlitzOne_eq_mul_qPoly F (0 : F)
  simpa using h

/-- Per-term expansion for a nonzero root `c`: modulo `X^N`,
`Q_c^n ≡ X^n · Q_0^n · invTrunc(c,n,N)`. -/
lemma Q_cong (c : F) (hc : c ≠ 0) (n N : ℕ) (hn : 1 ≤ n) :
    X ^ N ∣ (qPoly F c) ^ n - (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  apply dvd_of_dvd_mul_XpC F c hc n N
  have hprod : (qPoly F c) ^ n * (X + C c) ^ n = (X ^ n) * (qPoly F 0) ^ n := by
    calc
      (qPoly F c) ^ n * (X + C c) ^ n = ((qPoly F c) * (X + C c)) ^ n := by rw [← mul_pow]
      _ = ((X + C c) * qPoly F c) ^ n := by rw [mul_comm]
      _ = carlitzOne F ^ n := by rw [← carlitzOne_eq_mul_qPoly F c]
      _ = (X * qPoly F (0 : F)) ^ n := by rw [carlitzOne_eq_X_mul_qPoly0 F]
      _ = (X ^ n) * (qPoly F (0 : F)) ^ n := by rw [mul_pow]
  have hUi : X ^ N ∣ (X + C c) ^ n * invTrunc F c n N - 1 := by
    exact Commons.FieldTheory.Polynomial.unit_inv_cong (K := F) (u := Units.mk0 c hc) n N hn
  have hneg : X ^ N ∣ (1 - (X + C c) ^ n * invTrunc F c n N) := by
    have h4 : X ^ N ∣ -((X + C c) ^ n * invTrunc F c n N - 1) := dvd_neg.mpr hUi
    convert h4 using 1
    ring
  have h2 : X ^ N ∣ (X ^ n) * (qPoly F 0) ^ n * (1 - (X + C c) ^ n * invTrunc F c n N) := by
    exact dvd_mul_of_dvd_right hneg ((X ^ n) * (qPoly F 0) ^ n)
  have hmain : (X + C c) ^ n * ((qPoly F c) ^ n - (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N)
      = (X ^ n) * (qPoly F 0) ^ n * (1 - (X + C c) ^ n * invTrunc F c n N) := by
    calc
      (X + C c) ^ n * ((qPoly F c) ^ n - (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N)
          = (X + C c) ^ n * (qPoly F c) ^ n
              - (X + C c) ^ n * ((X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N) := by ring
      _ = (X ^ n) * (qPoly F 0) ^ n
              - (X + C c) ^ n * ((X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N) := by
            rw [mul_comm ((X + C c) ^ n) ((qPoly F c) ^ n), hprod]
      _ = (X ^ n) * (qPoly F 0) ^ n
              - (X ^ n) * (qPoly F 0) ^ n * ((X + C c) ^ n * invTrunc F c n N) := by ring
      _ = (X ^ n) * (qPoly F 0) ^ n * (1 - (X + C c) ^ n * invTrunc F c n N) := by ring
  rw [hmain]
  exact h2

/-- The truncated series sum over nonzero `c` equals `Vser`:
`Σ_{c∈F, c≠0} invTrunc(c,n,N) = Vser(n,N)`. -/
lemma erase_invTrunc_sum (n N : ℕ) :
    letI : Fintype F := Fintype.ofFinite F
    letI : DecidableEq F := Classical.decEq F
    (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), invTrunc F c n N) = Vser F n N := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  ext j
  by_cases hj : j < N
  · calc
      (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), invTrunc F c n N).coeff j
          = ∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (invTrunc F c n N).coeff j := by
              rw [finsetSum_coeff]
      _ = ∑ c ∈ (Finset.univ : Finset F).erase (0 : F),
            ((((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) : F) * c⁻¹ ^ (n + j)) := by
              apply Finset.sum_congr rfl
              intro c hc
              unfold invTrunc
              rw [finsetSum_coeff]
              rw [Finset.sum_eq_single j]
              · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
              · intro b hb hbj
                rw [Polynomial.coeff_C_mul_X_pow, if_neg]
                intro h; exact hbj h.symm
              · intro h'
                exfalso
                exact h' (Finset.mem_range.mpr hj)
      _ = (((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) : F) *
            (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), c⁻¹ ^ (n + j)) := by
              rw [Finset.mul_sum]
      _ = (((-1 : ℤ) ^ j * (Nat.choose (n + j - 1) j : ℤ)) : F) * FstarSum F (n + j) := by
              unfold FstarSum
              rfl
      _ = (Vser F n N).coeff j := by
              unfold Vser
              rw [finsetSum_coeff]
              rw [Finset.sum_eq_single j]
              · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
              · intro b hb hbj
                rw [Polynomial.coeff_C_mul_X_pow, if_neg]
                intro h; exact hbj h.symm
              · intro h'
                exfalso
                exact h' (Finset.mem_range.mpr hj)
  · rw [Vser_coeff_ge F n N j (by omega)]
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro c hc
    unfold invTrunc
    rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro hjk
    have : k < N := Finset.mem_range.mp hk
    omega

/-- `A F n ≡ Q_0^n · (1 + X^n · Vser(n,N))  (mod X^N)`. -/
lemma A_cong (n N : ℕ) (hn : 1 ≤ n) :
    letI : Fintype F := Fintype.ofFinite F
    X ^ N ∣ A F n - (qPoly F 0) ^ n * (1 + (X ^ n) * Vser F n N) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hA : A F n = (qPoly F 0) ^ n + ∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n := by
    unfold A
    change (∑ c : F, (qPoly F c) ^ n) =
      (qPoly F 0) ^ n + ∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n
    rw [← Finset.add_sum_erase (s := (Finset.univ : Finset F))
      (f := fun c : F => (qPoly F c) ^ n) (Finset.mem_univ 0)]
  have hper : ∀ c ∈ (Finset.univ : Finset F).erase (0 : F),
      X ^ N ∣ (qPoly F c) ^ n - (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N := by
    intro c hc
    exact Q_cong F c (by exact (Finset.mem_erase.mp hc).1) n N hn
  have hsum : X ^ N ∣
      (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n) -
        ∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.dvd_sum hper
  -- the second sum is X^n·Q_0^n · Σ erase invTrunc = X^n·Q_0^n·Vser
  have hdist : (∑ c ∈ (Finset.univ : Finset F).erase (0 : F),
        (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N)
      = (X ^ n) * (qPoly F 0) ^ n * Vser F n N := by
    calc
      (∑ c ∈ (Finset.univ : Finset F).erase (0 : F),
          (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N)
          = (X ^ n) * (qPoly F 0) ^ n * (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), invTrunc F c n N) := by
            rw [Finset.mul_sum]
      _ = (X ^ n) * (qPoly F 0) ^ n * Vser F n N := by rw [erase_invTrunc_sum F n N]
  have hdist2 : X ^ N ∣ (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n) -
      (X ^ n) * (qPoly F 0) ^ n * Vser F n N := by
    have hz : (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n) -
          (X ^ n) * (qPoly F 0) ^ n * Vser F n N
        = ((∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n) -
            ∑ c ∈ (Finset.univ : Finset F).erase (0 : F),
              (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N)
          + ((∑ c ∈ (Finset.univ : Finset F).erase (0 : F),
              (X ^ n) * (qPoly F 0) ^ n * invTrunc F c n N) -
              (X ^ n) * (qPoly F 0) ^ n * Vser F n N) := by ring
    rw [hz]
    exact dvd_add hsum (by rw [hdist]; simp)
  rw [hA]
  have hz2 : (qPoly F 0) ^ n + (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n)
        - (qPoly F 0) ^ n * (1 + (X ^ n) * Vser F n N)
      = (∑ c ∈ (Finset.univ : Finset F).erase (0 : F), (qPoly F c) ^ n)
          - (X ^ n) * (qPoly F 0) ^ n * Vser F n N := by ring
  rw [hz2]
  exact hdist2

-- ============================================================
-- (S4) machinery, part V: assembly — X^(a+b) divides Q — and (P1)
-- ============================================================

namespace Cong

/-- Sums preserve congruence (over a Finset with membership binder). -/
lemma sum {n : ℕ} {ι : Type*} (s : Finset ι) {f g : ι → F[X]}
    (h : ∀ i ∈ s, Cong F n (f i) (g i)) : Cong F n (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  unfold Cong at h ⊢
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum h

/-- `p + q ≡ p` when `X^n | q`. -/
lemma add_right_of_dvd {n : ℕ} {p q : F[X]} (hq : X ^ n ∣ q) : Cong F n (p + q) p := by
  unfold Cong
  rw [show (p + q) - p = q by ring]
  exact hq

end Cong

set_option maxHeartbeats 16000000 in
/-- The `(P1)` difference is divisible by `X^(a+b)`: the core `S4`. -/
lemma thakurP1Q_X_pow_dvd (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    letI : Fintype F := Fintype.ofFinite F
    X ^ (a + b) ∣ thakurP1Q F a b := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let N : ℕ := a + b
  let g : F[X] := qPoly F 0
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hNmi_helper : ∀ i ∈ Finset.Icc 1 (N - 1), 1 ≤ N - i := by
    intro i hi
    have hi2 : i ≤ N - 1 := (Finset.mem_Icc.mp hi).2
    omega
  -- cong for each of a, b
  have hAa : Cong F N (A F a) (g ^ a * (1 + X ^ a * Vser F a N)) := by
    unfold Cong
    dsimp [g, N]
    exact (A_cong F a (a + b) ha)
  have hAb : Cong F N (A F b) (g ^ b * (1 + X ^ b * Vser F b N)) := by
    unfold Cong
    dsimp [g, N]
    exact (A_cong F b (a + b) hb)
  -- A_N ≡ g^N
  have hAN : Cong F N (A F N) (g ^ N) := by
    have hA0 : Cong F N (A F N) (g ^ N * (1 + X ^ N * Vser F N N)) := by
      unfold Cong
      dsimp [g, N]
      exact (A_cong F N N hN1)
    have hd : X ^ N ∣ g ^ N * (X ^ N * Vser F N N) := by
      refine ⟨g ^ N * Vser F N N, ?_⟩
      ring
    have hc : Cong F N (g ^ N * (1 + X ^ N * Vser F N N)) (g ^ N) := by
      have hEq : g ^ N * (1 + X ^ N * Vser F N N) = g ^ N + g ^ N * (X ^ N * Vser F N N) := by ring
      rw [hEq]
      exact Cong.add_right_of_dvd F hd
    exact Cong.trans F hA0 hc
  -- product A_a · A_b ≡ g^N (1 + X^a V_a + X^b V_b)
  have hAA : Cong F N (A F a * A F b)
      (g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N)) := by
    have hP := Cong.mul F hAa hAb
    have hEq : (g ^ a * (1 + X ^ a * Vser F a N)) * (g ^ b * (1 + X ^ b * Vser F b N))
        = g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N)
          + X ^ N * (g ^ N * Vser F a N * Vser F b N) := by
      have hX : (X : F[X]) ^ a * (X : F[X]) ^ b = (X : F[X]) ^ N := by
        rw [← pow_add]
      have hIn : (1 + X ^ a * Vser F a N) * (1 + X ^ b * Vser F b N)
          = 1 + X ^ a * Vser F a N + X ^ b * Vser F b N + X ^ N * (Vser F a N * Vser F b N) := by
        have hExp : (1 + X ^ a * Vser F a N) * (1 + X ^ b * Vser F b N)
            = 1 + X ^ a * Vser F a N + X ^ b * Vser F b N
              + (X ^ a * X ^ b) * (Vser F a N * Vser F b N) := by ring
        rw [hExp, hX]
      calc
        (g ^ a * (1 + X ^ a * Vser F a N)) * (g ^ b * (1 + X ^ b * Vser F b N))
            = (g ^ a * g ^ b) * ((1 + X ^ a * Vser F a N) * (1 + X ^ b * Vser F b N)) := by ring
        _ = g ^ (a + b) * ((1 + X ^ a * Vser F a N) * (1 + X ^ b * Vser F b N)) := by rw [← pow_add]
        _ = g ^ N * ((1 + X ^ a * Vser F a N) * (1 + X ^ b * Vser F b N)) := by dsimp [N]
        _ = g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N + X ^ N * (Vser F a N * Vser F b N)) := by rw [hIn]
        _ = g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N)
              + X ^ N * (g ^ N * Vser F a N * Vser F b N) := by ring
    have hT : Cong F N ((g ^ a * (1 + X ^ a * Vser F a N)) * (g ^ b * (1 + X ^ b * Vser F b N)))
        (g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N)) := by
      rw [hEq]
      exact Cong.add_right_of_dvd F (by exact ⟨g ^ N * Vser F a N * Vser F b N, by ring⟩)
    exact Cong.trans F hP hT
  -- each summand [1]^i · A_{N-i} ≡ C(Δ_i)·X^i·g^N
  have hterm : ∀ i ∈ Finset.Icc 1 (N - 1),
      Cong F N (Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (N - i))
        (Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi2 : i ≤ N - 1 := (Finset.mem_Icc.mp hi).2
    have hNmi : 1 ≤ N - i := hNmi_helper i hi
    have hAi : Cong F N (A F (N - i)) (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N)) := by
      unfold Cong
      dsimp [g, N]
      exact (A_cong F (N - i) N hNmi)
    have h1 : Cong F N ((carlitzOne F) ^ i * A F (N - i))
        ((carlitzOne F) ^ i * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N))) :=
      Cong.mul_left F ((carlitzOne F) ^ i) hAi
    have hcar : carlitzOne F = X * g := by dsimp [g]; exact carlitzOne_eq_X_mul_qPoly0 F
    have hPow : (carlitzOne F) ^ i * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N))
        = X ^ i * g ^ N + X ^ N * (g ^ N * Vser F (N - i) N) := by
      have hg : g ^ i * g ^ (N - i) = g ^ N := by
        rw [← pow_add]
        congr 1
        omega
      have hX : (X : F[X]) ^ i * (X : F[X]) ^ (N - i) = (X : F[X]) ^ N := by
        rw [← pow_add]
        congr 1
        omega
      calc
        (carlitzOne F) ^ i * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N))
            = (X * g) ^ i * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N)) := by rw [hcar]
        _ = (X ^ i * g ^ i) * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N)) := by rw [mul_pow]
        _ = (X ^ i * (g ^ i * g ^ (N - i))) * (1 + X ^ (N - i) * Vser F (N - i) N) := by ring
        _ = (X ^ i * g ^ N) * (1 + X ^ (N - i) * Vser F (N - i) N) := by rw [hg]
        _ = X ^ i * g ^ N * (1 + X ^ (N - i) * Vser F (N - i) N) := by ring
        _ = X ^ i * g ^ N + X ^ i * g ^ N * (X ^ (N - i) * Vser F (N - i) N) := by ring
        _ = X ^ i * g ^ N + X ^ N * (g ^ N * Vser F (N - i) N) := by
              congr 1
              calc
                X ^ i * g ^ N * (X ^ (N - i) * Vser F (N - i) N)
                    = (X ^ i * X ^ (N - i)) * (g ^ N * Vser F (N - i) N) := by ring
                _ = X ^ N * (g ^ N * Vser F (N - i) N) := by rw [hX]
    have h2 : Cong F N ((carlitzOne F) ^ i * (g ^ (N - i) * (1 + X ^ (N - i) * Vser F (N - i) N)))
        (X ^ i * g ^ N) := by
      rw [hPow]
      exact Cong.add_right_of_dvd F (by exact ⟨g ^ N * Vser F (N - i) N, by ring⟩)
    have h3 : Cong F N ((carlitzOne F) ^ i * A F (N - i)) (X ^ i * g ^ N) := Cong.trans F h1 h2
    have h4 : Cong F N (Polynomial.C (ChenDeltaZ F a b i : F) * ((carlitzOne F) ^ i * A F (N - i)))
        (Polynomial.C (ChenDeltaZ F a b i : F) * (X ^ i * g ^ N)) :=
      Cong.mul_left F (Polynomial.C (ChenDeltaZ F a b i : F)) h3
    have hpL : Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (N - i)
        = Polynomial.C (ChenDeltaZ F a b i : F) * ((carlitzOne F) ^ i * A F (N - i)) := by ring
    have hR : Polynomial.C (ChenDeltaZ F a b i : F) * (X ^ i * g ^ N)
        = Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N := by ring
    exact Cong.congr_right F (Cong.congr_left F h4 hpL) hR
  have hS : Cong F N (∑ i ∈ Finset.Icc 1 (N - 1),
      Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (N - i))
    (∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N) :=
    Cong.sum F (Finset.Icc 1 (N - 1)) hterm
  -- assemble: Q ≡ g^N·W, where W is the truncated combination
  let W : F[X] := X ^ a * Vser F a N + X ^ b * Vser F b N -
      ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i
  have hQ1 : Cong F N (A F a * A F b - A F N)
      (g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N) - g ^ N) := by
    exact Cong.sub F hAA hAN
  have hQ2 : Cong F N ((A F a * A F b - A F N) -
        ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (N - i))
      ((g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N) - g ^ N) -
        ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N) := by
    exact Cong.sub F hQ1 hS
  have hQ3 : Cong F N (thakurP1Q F a b)
      (g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N) - g ^ N -
        ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N) := by
    -- thakurP1Q unfolds to the expression on the left (N = a+b)
    unfold thakurP1Q
    dsimp [N]
    exact hQ2
  have hQ4 : g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N) - g ^ N -
        ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N
      = g ^ N * W := by
    dsimp [W]
    calc
      g ^ N * (1 + X ^ a * Vser F a N + X ^ b * Vser F b N) - g ^ N
            - ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N
          = g ^ N * (X ^ a * Vser F a N + X ^ b * Vser F b N)
            - ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i * g ^ N := by ring
      _ = g ^ N * (X ^ a * Vser F a N + X ^ b * Vser F b N)
            - g ^ N * (∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = g ^ N * (X ^ a * Vser F a N + X ^ b * Vser F b N
            - ∑ i ∈ Finset.Icc 1 (N - 1), Polynomial.C (ChenDeltaZ F a b i : F) * X ^ i) := by ring
  have hQ5 : Cong F N (thakurP1Q F a b) (g ^ N * W) := by
    have := Cong.congr_right F hQ3 hQ4
    -- hQ3 : Cong thakurP1Q LHSbig; hQ4 : LHSbig = g^N W: congr_right gives Cong thakurP1Q (g^N W)
    simpa using this
  have hW : X ^ N ∣ W := by
    dsimp [W, N]
    exact W_dvd F a b ha hb
  have hW0 : Cong F N W 0 := by
    unfold Cong
    simpa using hW
  have hgW0 : Cong F N (g ^ N * W) 0 := by
    have h1 := Cong.mul_left F (g ^ N) hW0
    have h2 : Cong F N (g ^ N * 0) 0 := by
      unfold Cong
      simp
    exact Cong.trans F h1 h2
  have hfin : Cong F N (thakurP1Q F a b) 0 :=
    Cong.trans F hQ5 hgW0
  unfold Cong at hfin
  simpa using hfin

/-- The level-one shuffle identity `(P1)` (Thakur product identity, d = 1,
Chen's explicit coefficients): `A_a·A_b = A_{a+b} + Σ_{0<i<a+b} Δ^i [1]^i A_{a+b-i}`. -/
theorem thakurP1 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    A F a * A F b =
      A F (a + b) +
        ∑ i ∈ Finset.Icc 1 (a + b - 1),
          Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hQ : thakurP1Q F a b = 0 :=
    thakurP1Q_eq_zero_of_X_pow_dvd F a b ha hb (thakurP1Q_X_pow_dvd F a b ha hb)
  unfold thakurP1Q at hQ
  calc
    A F a * A F b
        = (A F a * A F b - A F (a + b) -
              ∑ i ∈ Finset.Icc 1 (a + b - 1),
                Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i))
          + (A F (a + b) +
              ∑ i ∈ Finset.Icc 1 (a + b - 1),
                Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i)) := by ring
    _ = A F (a + b) +
          ∑ i ∈ Finset.Icc 1 (a + b - 1),
            Polynomial.C (ChenDeltaZ F a b i : F) * (carlitzOne F) ^ i * A F (a + b - i) := by
          rw [hQ]
          ring

end ZagierHoffmanPositiveChar
