import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
open MvPolynomial

namespace Commons.Algebra.MvPolynomial

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

private lemma natCast_eq_C (n : ℕ) (k : ℕ) : (k : P n) = MvPolynomial.C (k : ℝ) := by
  exact (map_natCast MvPolynomial.C k).symm

private lemma pderiv_natCast {n : ℕ} (i : Fin n) (k : ℕ) :
    MvPolynomial.pderiv i (k : P n) = 0 := by
  rw [natCast_eq_C n k, MvPolynomial.pderiv_C]

private lemma coef_id_ge2 (n j : ℕ) (hn : 1 ≤ n) (hj : 2 ≤ j) :
    ((((n - 1 : ℕ) : ℝ) * (((2 * j : ℕ) : ℝ))) + (((2 * j : ℕ) : ℝ) * (((2 * (j - 1)) : ℕ) : ℝ)))
      = (((2 * j * (n + 2 * j - 3)) : ℕ) : ℝ) := by
  have hid : (n + 2 * j - 3 : ℕ) = (n - 1) + 2 * (j - 1) := by omega
  calc
    ((((n - 1 : ℕ) : ℝ) * (((2 * j : ℕ) : ℝ))) + (((2 * j : ℕ) : ℝ) * (((2 * (j - 1)) : ℕ) : ℝ)))
        = ((((2 * j : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + (((2 * (j - 1)) : ℕ) : ℝ)))) := by ring
    _ = ((((2 * j : ℕ) : ℝ) * ((((n - 1) + 2 * (j - 1)) : ℕ) : ℝ))) := by rw [← Nat.cast_add]
    _ = ((((2 * j : ℕ) : ℝ) * (((n + 2 * j - 3) : ℕ) : ℝ))) := by rw [← hid]
    _ = (((2 * j * (n + 2 * j - 3)) : ℕ) : ℝ) := by rw [← Nat.cast_mul]

noncomputable section
variable {n : ℕ} [NeZero n]

private def x0 : P n := MvPolynomial.X (0 : Fin n)
private def TT : P n := ∑ i0 : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i0 : Fin n) : P n)^2

private lemma card_ne_zero : Fintype.card {i : Fin n // i ≠ 0} = n - 1 := by
  classical
  have hsing : Fintype.card {x : Fin n // x = 0} = 1 := by
    haveI : Subsingleton {x : Fin n // x = 0} := ⟨by
      intro a b
      apply Subtype.ext
      exact a.2.trans b.2.symm⟩
    exact Fintype.card_ofSubsingleton ⟨0, rfl⟩
  rw [Fintype.card_subtype_compl (p := fun x : Fin n => x = 0)]
  rw [Fintype.card_fin]
  rw [hsing]

private lemma coef_sum (j : ℕ) (hj : 2 ≤ j) :
    ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n))
        + (((n - 1 : ℕ) : P n) * ((2 * j : ℕ) : P n)))
      = (((2 * j * (n + 2 * j - 3)) : ℕ) : P n) := by
  have hn1 : 1 ≤ n := by have h0 := NeZero.ne n; omega
  rw [natCast_eq_C n (2 * j), natCast_eq_C n (2 * (j - 1)),
      natCast_eq_C n (n - 1), natCast_eq_C n (2 * j * (n + 2 * j - 3))]
  rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
  rw [← MvPolynomial.C_add]
  congr 1
  rw [← coef_id_ge2 n j hn1 hj]
  ring

private lemma pderiv_x0_pow (a : ℕ) :
    MvPolynomial.pderiv (0 : Fin n) (x0 ^ a) = (a : P n) * x0 ^ (a - 1) := by
  rw [MvPolynomial.pderiv_pow]
  simp [x0]

private lemma pderiv_x0_of_ne {i : Fin n} (hi : i ≠ 0) :
    MvPolynomial.pderiv i x0 = 0 := by
  unfold x0
  exact MvPolynomial.pderiv_X_of_ne hi.symm

private lemma pderiv_x0_pow_of_ne {i : Fin n} (hi : i ≠ 0) (a : ℕ) :
    MvPolynomial.pderiv i (x0 ^ a) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  rw [pderiv_x0_of_ne hi]
  simp

private lemma ppderiv_x0_pow (a : ℕ) :
    MvPolynomial.pderiv (0 : Fin n) (MvPolynomial.pderiv (0 : Fin n) (x0 ^ a)) =
      (((a * (a - 1)) : ℕ) : P n) * x0 ^ (a - 2) := by
  calc
    pderiv (0 : Fin n) (pderiv (0 : Fin n) (x0 ^ a))
        = pderiv (0 : Fin n) ((a : P n) * x0 ^ (a - 1)) := by rw [pderiv_x0_pow]
    _ = (a : P n) * pderiv (0 : Fin n) (x0 ^ (a - 1)) := by
        rw [MvPolynomial.pderiv_mul]
        rw [pderiv_natCast]
        simp
    _ = (a : P n) * (((a - 1 : ℕ) : P n) * x0 ^ ((a - 1) - 1)) := by rw [pderiv_x0_pow]
    _ = ((a : P n) * ((a - 1 : ℕ) : P n)) * x0 ^ ((a - 1) - 1) := by rw [← mul_assoc]
    _ = ((a : P n) * ((a - 1 : ℕ) : P n)) * x0 ^ (a - 2) := by
        have he : (a - 1) - 1 = a - 2 := by omega
        rw [he]
    _ = (((a * (a - 1)) : ℕ) : P n) * x0 ^ (a - 2) := by
        have h := (Nat.cast_mul (α := P n) a (a - 1 : ℕ)).symm
        rw [h]

private lemma pderiv_TT (i : Fin n) (hi : i ≠ 0) :
    MvPolynomial.pderiv i (TT) = ((2 : ℕ) : P n) * (MvPolynomial.X i : P n) := by
  classical
  unfold TT
  rw [map_sum]
  rw [Finset.sum_eq_single (a := (⟨i, hi⟩ : {i : Fin n // i ≠ 0}))]
  · rw [pow_two, MvPolynomial.pderiv_mul]
    simp
    ring
  · intro b hb hbne
    have hbnei : (b : Fin n) ≠ i := by
      intro hbi
      apply hbne
      exact Subtype.ext hbi
    rw [pow_two, MvPolynomial.pderiv_mul]
    simp [MvPolynomial.pderiv_X_of_ne (i := i) (j := (b : Fin n)) hbnei]
  · intro hmem
    simp at hmem

private lemma pderiv_TT_zero : MvPolynomial.pderiv (0 : Fin n) (TT) = 0 := by
  classical
  unfold TT
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i0 hi0
  rw [pow_two, MvPolynomial.pderiv_mul]
  simp [MvPolynomial.pderiv_X_of_ne (i := (0 : Fin n)) (j := (i0 : Fin n)) i0.2]

private lemma pderiv_TT_pow {i : Fin n} (hi : i ≠ 0) (j : ℕ) :
    MvPolynomial.pderiv i (TT ^ j) =
      ((2 * j : ℕ) : P n) * (MvPolynomial.X i : P n) * TT ^ (j - 1) := by
  rw [MvPolynomial.pderiv_pow]
  rw [pderiv_TT i hi]
  calc
    (j : P n) * TT ^ (j - 1) * (((2 : ℕ) : P n) * MvPolynomial.X i)
        = ((j : P n) * ((2 : ℕ) : P n)) * (TT ^ (j - 1) * MvPolynomial.X i) := by ring
    _ = ((2 * j : ℕ) : P n) * (TT ^ (j - 1) * MvPolynomial.X i) := by
        have hcoef : (j : P n) * ((2 : ℕ) : P n) = ((2 * j : ℕ) : P n) := by
          rw [mul_comm]
          rw [← Nat.cast_mul 2 j]
        rw [hcoef]
    _ = ((2 * j : ℕ) : P n) * MvPolynomial.X i * TT ^ (j - 1) := by ring

private lemma ppderiv_TT_pow {i : Fin n} (hi : i ≠ 0) (j : ℕ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (TT ^ j)) =
      ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (MvPolynomial.X i : P n)^2) * TT ^ (j - 2)
        + ((2 * j : ℕ) : P n) * TT ^ (j - 1) := by
  rw [pderiv_TT_pow hi j]
  rw [natCast_eq_C n (2 * j)]
  rw [mul_assoc]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_mul]
  rw [pderiv_TT_pow hi (j - 1)]
  rw [← natCast_eq_C n (2 * j)]
  simp
  have he : (j - 1) - 1 = j - 2 := by omega
  rw [he]
  ring

private lemma lap_TT_pow (j : ℕ) :
    (∑ i0 : {i : Fin n // i ≠ 0},
        MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j)))
      = (((2 * j * (n + 2 * j - 3)) : ℕ) : P n) * (TT : P n) ^ (j - 1) := by
  classical
  by_cases hge2 : 2 ≤ j
  · have hn1 : 1 ≤ n := by have h0 := NeZero.ne n; omega
    have hTpow : (TT : P n) * (TT : P n) ^ (j - 2) = (TT : P n) ^ (j - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hsummand : ∀ i0 : {i : Fin n // i ≠ 0},
        MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j)) =
          (((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (MvPolynomial.X (i0 : Fin n) : P n)^2) * (TT : P n) ^ (j - 2))
            + ((2 * j : ℕ) : P n) * (TT : P n) ^ (j - 1) := by
            intro i0
            exact ppderiv_TT_pow (i := i0.1) i0.2 j
    calc
      (∑ i0 : {i : Fin n // i ≠ 0},
          MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j)))
          = (∑ i0 : {i : Fin n // i ≠ 0},
                ((((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (MvPolynomial.X (i0 : Fin n) : P n)^2) * (TT : P n) ^ (j - 2))
                  + ((2 * j : ℕ) : P n) * (TT : P n) ^ (j - 1))) := by
              apply Finset.sum_congr rfl
              intro i0 hi0
              exact hsummand i0
      _ = (∑ i0 : {i : Fin n // i ≠ 0},
                ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (MvPolynomial.X (i0 : Fin n) : P n)^2) * (TT : P n) ^ (j - 2))
            + (∑ i0 : {i : Fin n // i ≠ 0}, ((2 * j : ℕ) : P n) * (TT : P n) ^ (j - 1)) := by
              rw [Finset.sum_add_distrib]
      _ = (((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (TT : P n)) * (TT : P n) ^ (j - 2))
            + (∑ i0 : {i : Fin n // i ≠ 0}, ((2 * j : ℕ) : P n) * (TT : P n) ^ (j - 1)) := by
              rw [← Finset.sum_mul]
              rw [← Finset.mul_sum]
              simp [TT]
      _ = ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (TT : P n) ^ (j - 1))
            + (∑ i0 : {i : Fin n // i ≠ 0}, ((2 * j : ℕ) : P n) * (TT : P n) ^ (j - 1)) := by
              rw [mul_assoc]
              rw [hTpow]
      _ = ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n)) * (TT : P n) ^ (j - 1))
            + ((((n - 1 : ℕ) : P n) * ((2 * j : ℕ) : P n)) * (TT : P n) ^ (j - 1)) := by
              rw [Finset.sum_const, Finset.card_univ, card_ne_zero, nsmul_eq_mul]
              rw [← mul_assoc]
      _ = ((((2 * j : ℕ) : P n) * ((2 * (j - 1) : ℕ) : P n))
            + (((n - 1 : ℕ) : P n) * ((2 * j : ℕ) : P n))) * (TT : P n) ^ (j - 1) := by
              rw [← add_mul]
      _ = (((2 * j * (n + 2 * j - 3)) : ℕ) : P n) * (TT : P n) ^ (j - 1) := by
              rw [coef_sum j hge2]
  · have hle : j ≤ 1 := by omega
    interval_cases j
    · simp
    · calc
        (∑ i0 : {i : Fin n // i ≠ 0},
            MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ 1)))
            = (∑ i0 : {i : Fin n // i ≠ 0},
                MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) (TT : P n))) := by
                simp
        _ = (∑ i0 : {i : Fin n // i ≠ 0}, ((2 : ℕ) : P n)) := by
                apply Finset.sum_congr rfl
                intro i0 hi0
                rw [pderiv_TT i0.1 i0.2]
                rw [natCast_eq_C n 2]
                rw [MvPolynomial.pderiv_C_mul]
                simp
        _ = (((n - 1 : ℕ) : P n) * ((2 : ℕ) : P n)) := by
                rw [Finset.sum_const, Finset.card_univ, card_ne_zero, nsmul_eq_mul]
        _ = (((2 * 1 * (n + 2 * 1 - 3)) : ℕ) : P n) * (TT : P n) ^ (1 - 1) := by
                have hnat : 2 * (n - 1) = 2 * 1 * (n + 2 * 1 - 3) := by omega
                rw [mul_comm, ← Nat.cast_mul 2 (n - 1)]
                rw [hnat]
                simp


omit [NeZero n] in
private lemma pderiv2_mul (i : Fin n) (f g : P n) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (f * g)) =
      (MvPolynomial.pderiv i (MvPolynomial.pderiv i f)) * g
        + (2 : ℝ) • ((MvPolynomial.pderiv i f) * (MvPolynomial.pderiv i g))
        + f * MvPolynomial.pderiv i (MvPolynomial.pderiv i g) := by
  rw [MvPolynomial.pderiv_mul]
  rw [map_add]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
  rw [two_smul ℝ ((MvPolynomial.pderiv i f) * (MvPolynomial.pderiv i g))]
  ring

private lemma pderiv_TT_pow_zero (j : ℕ) :
    MvPolynomial.pderiv (0 : Fin n) ((TT : P n) ^ j) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  rw [pderiv_TT_zero]
  simp

private lemma lap_index_zero (a j : ℕ) :
    MvPolynomial.pderiv (0 : Fin n) (MvPolynomial.pderiv (0 : Fin n)
      ((x0 : P n) ^ a * (TT : P n) ^ j)) =
      (((a * (a - 1)) : ℕ) : P n) * (x0 : P n) ^ (a - 2) * (TT : P n) ^ j := by
  rw [pderiv2_mul]
  rw [ppderiv_x0_pow a]
  rw [pderiv_TT_pow_zero j]
  simp

private lemma lap_index_ne {i : Fin n} (hi : i ≠ 0) (a j : ℕ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i
      ((x0 : P n) ^ a * (TT : P n) ^ j)) =
      (x0 : P n) ^ a * (MvPolynomial.pderiv i (MvPolynomial.pderiv i ((TT : P n) ^ j))) := by
  rw [pderiv2_mul]
  rw [pderiv_x0_pow_of_ne hi a]
  simp

private lemma sum_split (F : Fin n → P n) :
    (∑ i : Fin n, F i) = F (0 : Fin n) + ∑ i0 : {i : Fin n // i ≠ 0}, F (i0 : Fin n) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i ≠ 0)
  have huniv : Finset.univ = insert (0 : Fin n) s := by
    ext x
    by_cases h : x = 0
    · simp [s, h]
    · simp [s, h]
  calc
    (∑ i : Fin n, F i) = ∑ i ∈ Finset.univ, F i := by rfl
    _ = ∑ i ∈ insert (0 : Fin n) s, F i := by rw [huniv]
    _ = F 0 + ∑ i ∈ s, F i := by
        rw [Finset.sum_insert]
        simp [s]
    _ = F (0 : Fin n) + ∑ i0 : {i : Fin n // i ≠ 0}, F (i0 : Fin n) := by
        congr 1
        rw [Finset.sum_subtype (p := fun i : Fin n => i ≠ 0) s (by intro x; simp [s]) (fun i => F i)]

theorem lap_zterm
    {n : ℕ} [NeZero n] (a j : ℕ) :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ a *
          (∑ i0 : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i0 : Fin n) : MvPolynomial (Fin n) ℝ)^2) ^ j)))
      = (MvPolynomial.C (((a * (a - 1)) : ℕ) : ℝ) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (a - 2) *
          (∑ i0 : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i0 : Fin n) : MvPolynomial (Fin n) ℝ)^2) ^ j) +
        (MvPolynomial.C (((2 * j * (n + 2*j - 3)) : ℕ) : ℝ) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ a *
          (∑ i0 : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i0 : Fin n) : MvPolynomial (Fin n) ℝ)^2) ^ (j - 1)) := by
  change (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        ((x0 : P n) ^ a * (TT : P n) ^ j)))
      = (MvPolynomial.C (((a * (a - 1)) : ℕ) : ℝ) *
          (x0 : P n) ^ (a - 2) * (TT : P n) ^ j) +
        (MvPolynomial.C (((2 * j * (n + 2 * j - 3)) : ℕ) : ℝ) *
          (x0 : P n) ^ a * (TT : P n) ^ (j - 1))
  calc
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i ((x0 : P n) ^ a * (TT : P n) ^ j)))
        = MvPolynomial.pderiv (0 : Fin n) (MvPolynomial.pderiv (0 : Fin n) ((x0 : P n) ^ a * (TT : P n) ^ j))
          + (∑ i0 : {i : Fin n // i ≠ 0}, MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((x0 : P n) ^ a * (TT : P n) ^ j))) := by
            simpa using (sum_split (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i ((x0 : P n) ^ a * (TT : P n) ^ j))))
    _ = (((a * (a - 1)) : ℕ) : P n) * (x0 : P n) ^ (a - 2) * (TT : P n) ^ j
          + (x0 : P n) ^ a * (∑ i0 : {i : Fin n // i ≠ 0}, MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j))) := by
            rw [lap_index_zero a j]
            have h : (∑ i0 : {i : Fin n // i ≠ 0}, MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((x0 : P n) ^ a * (TT : P n) ^ j)))
                = (x0 : P n) ^ a * (∑ i0 : {i : Fin n // i ≠ 0}, MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j))) := by
                have hh : (∑ i0 : {i : Fin n // i ≠ 0}, MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((x0 : P n) ^ a * (TT : P n) ^ j)))
                    = (∑ i0 : {i : Fin n // i ≠ 0}, (x0 : P n) ^ a * MvPolynomial.pderiv (i0 : Fin n) (MvPolynomial.pderiv (i0 : Fin n) ((TT : P n) ^ j))) := by
                    apply Finset.sum_congr rfl
                    intro i0 hi0
                    exact lap_index_ne i0.2 a j
                rw [hh]
                rw [← Finset.mul_sum]
            rw [h]
    _ = (((a * (a - 1)) : ℕ) : P n) * (x0 : P n) ^ (a - 2) * (TT : P n) ^ j
          + (x0 : P n) ^ a * ((((2 * j * (n + 2 * j - 3)) : ℕ) : P n) * (TT : P n) ^ (j - 1)) := by
            rw [lap_TT_pow j]
    _ = (MvPolynomial.C (((a * (a - 1)) : ℕ) : ℝ) * (x0 : P n) ^ (a - 2) * (TT : P n) ^ j)
          + (MvPolynomial.C (((2 * j * (n + 2 * j - 3)) : ℕ) : ℝ) * (x0 : P n) ^ a * (TT : P n) ^ (j - 1)) := by
            rw [natCast_eq_C n (a * (a - 1))]
            rw [natCast_eq_C n (2 * j * (n + 2 * j - 3))]
            ring

end
end Commons.Algebra.MvPolynomial