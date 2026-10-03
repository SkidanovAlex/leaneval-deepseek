/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the natural extension, at an arbitrary universe

`Work.ORHughesFree.NaturalExtension.naturalExtension_exists` proves the existence of the natural
extension of a `τ`-compatible Sylvester rank function `rk` on a von Neumann regular ring, but its
statement is pinned to the universe `0` (`{U : Type}`).  This file proves the same statement for
`R : Type u` at an arbitrary universe.

The construction is the ultralimit of the truncated ranks: for a matrix `A` over `R[t^{±1};τ]`
and `i : ℕ`, the truncation `trunc i A` is a matrix over `R` (see `Defs.lean`), and

`rkE A = lim_ω (rk (trunc i A) / i)`

along an ultrafilter `ω` containing all cofinite sets is a Sylvester rank function on
`R[t^{±1};τ]` (the truncations are rank functions up to an error of rank `O(1)`, see
`rk_trunc_mul_sub_le`), which extends `rk` (`trunc i (skewLaurentConst A) = i • A`) and sends
`I + A t` to `n` (`trunc i (onePlusAt n A) = i • n`).

The five truncation lemmas used here are proved at an arbitrary universe in the modules
`Submission.Work.ORHughesFree.NaturalExtensionGen.*` and are restated below as `…_univ`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_exists
import Submission.Work.ORHughesFree.NaturalExtensionGen.Trunc
import Submission.Work.ORHughesFree.NaturalExtensionGen.BlockDiag
import Submission.Work.ORHughesFree.NaturalExtensionGen.BlockUpper
import Submission.Work.ORHughesFree.NaturalExtensionGen.SkewConst
import Submission.Work.ORHughesFree.NaturalExtensionGen.OnePlusAt

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Filter

/-! ## The truncation lemmas at an arbitrary universe -/

theorem rk_trunc_mul_sub_le_univ {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R) {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL R)) (B : Matrix (Fin m) (Fin k) (SkewL R)) (i : ℕ) :
    rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤
      (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ) :=
  NaturalExtensionGen.Trunc.rk_trunc_mul_sub_le rk A B i

theorem rk_trunc_blockDiagFin2_univ {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R) {n m p q : ℕ} (i : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL R)) (B : Matrix (Fin p) (Fin q) (SkewL R)) :
    rk.rk ((n + p) * i) ((m + q) * i) (trunc i (blockDiagFin A B)) =
      rk.rk (n * i) (m * i) (trunc i A) + rk.rk (p * i) (q * i) (trunc i B) :=
  NaturalExtensionGen.BlockDiag.rk_trunc_blockDiagFin2 rk i A B

theorem rk_trunc_blockUpperFin2_univ {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R) {n m p q : ℕ} (i : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL R)) (B : Matrix (Fin p) (Fin q) (SkewL R))
    (C : Matrix (Fin n) (Fin q) (SkewL R)) :
    rk.rk (n * i) (m * i) (trunc i A) + rk.rk (p * i) (q * i) (trunc i B) ≤
      rk.rk ((n + p) * i) ((m + q) * i) (trunc i (blockUpperFin A B C)) :=
  NaturalExtensionGen.BlockUpper.rk_trunc_blockUpperFin2 rk i A B C

theorem rk_trunc_skewLaurentConst_univ {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (i : ℕ) :
    rk.rk (n * i) (m * i) (trunc i (skewLaurentConst n m A)) = (i : ℝ) * rk.rk n m A :=
  NaturalExtensionGen.SkewConst.rk_trunc_skewLaurentConst rk hτ A i

theorem rk_trunc_onePlusAt_univ {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (rk : SylvesterRank R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i : ℕ) :
    rk.rk (n * i) (n * i) (trunc i (onePlusAt n A)) = (i : ℝ) * n :=
  NaturalExtensionGen.OnePlusAt.rk_trunc_onePlusAt rk A i

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The rank of the `i`-th truncation of `A`, normalized by `i`. -/
noncomputable def rankSeq_univ (rk : SylvesterRank R) (ω : Ultrafilter ℕ) (n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (SkewL R)) : ℕ → ℝ :=
  fun i => rk.rk (n * i) (m * i) (trunc i A) / (i : ℝ)

theorem rankSeq_nonneg_univ (rk : SylvesterRank R) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL R)) (i : ℕ) : 0 ≤ rankSeq_univ rk ω n m A i :=
  div_nonneg (rk.rk_nonneg _ _ _) (Nat.cast_nonneg i)

theorem abs_rankSeq_le_univ (rk : SylvesterRank R) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL R)) :
    ∀ i, |rankSeq_univ rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) := by
  intro i
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp [rankSeq_univ]
  · rw [abs_of_nonneg (rankSeq_nonneg_univ rk ω A i)]
    have hpos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
    have hA : rk.rk (n * i) (m * i) (trunc i A) ≤ (n : ℝ) * (i : ℝ) := by
      have hle := RankAPI.rk_le_left rk (trunc i A)
      rw [Nat.cast_mul] at hle
      exact hle
    have hmax : (n : ℝ) * (i : ℝ) ≤ max (n : ℝ) (m : ℝ) * (i : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg i)
    rw [rankSeq_univ, div_le_iff₀ hpos]
    exact le_trans hA hmax

theorem abs_rankSeq_le_of_le_univ (rk : SylvesterRank R) (ω : Ultrafilter ℕ) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL R)) {N M : ℕ} (hn : n ≤ N) (hm : m ≤ M) :
    ∀ i, |rankSeq_univ rk ω n m A i| ≤ max (N : ℝ) (M : ℝ) :=
  fun i => le_trans (abs_rankSeq_le_univ rk ω A i)
    (max_le_max (Nat.cast_le.mpr hn) (Nat.cast_le.mpr hm))

theorem rankSeq_zero_univ (rk : SylvesterRank R) (ω : Ultrafilter ℕ) (n m : ℕ) :
    rankSeq_univ rk ω n m (0 : Matrix (Fin n) (Fin m) (SkewL R)) = fun _ => 0 := by
  funext i
  simp [rankSeq_univ, trunc_zero, rk.rk_zero]

/-! ## The main theorem -/

theorem natExt_exists_universe {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R) (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A) : ∃ rkE : SylvesterRank (SkewL R), IsNaturalExtension rk rkE := by
  classical
  obtain ⟨ω, hω⟩ := exists_ultrafilter_le_atTop
  have hbdd : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL R)) (i : ℕ),
      |rankSeq_univ rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) :=
    fun n m A => abs_rankSeq_le_univ rk ω A
  refine ⟨{ rk := fun n m A => blim ω (rankSeq_univ rk ω n m A),
            rk_nonneg := ?_,
            rk_zero := ?_,
            rk_one := ?_,
            rk_mul_le_left := ?_,
            rk_mul_le_right := ?_,
            rk_blockDiag := ?_,
            rk_blockUpper := ?_ }, ?_⟩
  · intro n m A
    exact blim_nonneg ω (hbdd n m A) (fun i => rankSeq_nonneg_univ rk ω A i)
  · intro n m
    rw [rankSeq_zero_univ rk ω n m]
    exact blim_const ω 0
  · have hmat : (1 : Matrix (Fin 1) (Fin 1) (SkewL R)) =
        onePlusAt 1 (0 : Matrix (Fin 1) (Fin 1) R) := by
      simp [onePlusAt]
    rw [hmat]
    have hev : ∀ᶠ i in Filter.atTop,
        rankSeq_univ rk ω 1 1 (onePlusAt 1 (0 : Matrix (Fin 1) (Fin 1) R)) i = 1 := by
      filter_upwards [eventually_ge_atTop 1] with i hi
      rw [rankSeq_univ, rk_trunc_onePlusAt_univ rk 0 i, Nat.cast_one, mul_one]
      have hi' : (i : ℝ) ≠ 0 := by positivity
      exact div_self hi'
    rw [blim_congr ω hω hev, blim_const ω 1]
  · intro n m k A B
    let C : ℝ := (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
    have hCnn : 0 ≤ C := by
      show 0 ≤ (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
      positivity
    have hpt : ∀ i : ℕ, rankSeq_univ rk ω n k (A * B) i ≤ rankSeq_univ rk ω n m A i + C / (i : ℝ) := by
      intro i
      have hsplit : trunc i (A * B) =
          trunc i A * trunc i B + (trunc i (A * B) - trunc i A * trunc i B) := by
        abel
      have h4 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
          rk.rk (n * i) (m * i) (trunc i A) + C := by
        have h1 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
            rk.rk (n * i) (k * i) (trunc i A * trunc i B) +
              rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) := by
          have hraw := RankAPI.rk_add_le rk (trunc i A * trunc i B)
            (trunc i (A * B) - trunc i A * trunc i B)
          have hsum : trunc i A * trunc i B +
              (trunc i (A * B) - trunc i A * trunc i B) = trunc i (A * B) := by abel
          rw [hsum] at hraw
          exact hraw
        have h2 : rk.rk (n * i) (k * i) (trunc i A * trunc i B) ≤
            rk.rk (n * i) (m * i) (trunc i A) :=
          rk.rk_mul_le_left (trunc i A) (trunc i B)
        have h3 : rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤ C :=
          rk_trunc_mul_sub_le_univ rk A B i
        linarith
      calc rankSeq_univ rk ω n k (A * B) i
          = rk.rk (n * i) (k * i) (trunc i (A * B)) / (i : ℝ) := rfl
        _ ≤ (rk.rk (n * i) (m * i) (trunc i A) + C) / (i : ℝ) :=
            div_le_div_of_nonneg_right h4 (Nat.cast_nonneg i)
        _ = rk.rk (n * i) (m * i) (trunc i A) / (i : ℝ) + C / (i : ℝ) := add_div _ _ _
        _ = rankSeq_univ rk ω n m A i + C / (i : ℝ) := rfl
    have hbndC : ∀ i : ℕ, |C / (i : ℝ)| ≤ C := by
      intro i
      rw [abs_of_nonneg (div_nonneg hCnn (Nat.cast_nonneg i))]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simpa using hCnn
      · rw [div_le_iff₀ (by exact_mod_cast hi)]
        have h1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
        nlinarith
    have hbndC' : ∀ i : ℕ, |C / (i : ℝ)| ≤ max (n : ℝ) (m : ℝ) + C :=
      fun i => le_trans (hbndC i)
        (le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ max (n : ℝ) (m : ℝ)))
    have hbndA' : ∀ i : ℕ, |rankSeq_univ rk ω n m A i| ≤ max (n : ℝ) (m : ℝ) + C :=
      fun i => le_trans (hbdd n m A i) (le_add_of_nonneg_right hCnn)
    have hsum : blim ω (fun i => rankSeq_univ rk ω n m A i + C / (i : ℝ)) =
        blim ω (rankSeq_univ rk ω n m A) + blim ω (fun i => C / (i : ℝ)) :=
      blim_add ω hbndA' hbndC'
    have htend : blim ω (fun i => C / (i : ℝ)) = 0 :=
      blim_of_tendsto ω hω hbndC (tendsto_const_div_atTop_nhds_zero_nat C)
    have hmono : blim ω (rankSeq_univ rk ω n k (A * B)) ≤
        blim ω (fun i => rankSeq_univ rk ω n m A i + C / (i : ℝ)) := by
      refine blim_mono ω (hbdd n k (A * B))
        (M' := max (n : ℝ) (m : ℝ) + C) (fun i => ?_) hpt
      calc |rankSeq_univ rk ω n m A i + C / (i : ℝ)|
          ≤ |rankSeq_univ rk ω n m A i| + |C / (i : ℝ)| := abs_add_le _ _
        _ ≤ max (n : ℝ) (m : ℝ) + C := add_le_add (hbdd n m A i) (hbndC i)
    calc blim ω (rankSeq_univ rk ω n k (A * B)) ≤
          blim ω (fun i => rankSeq_univ rk ω n m A i + C / (i : ℝ)) := hmono
      _ = blim ω (rankSeq_univ rk ω n m A) + blim ω (fun i => C / (i : ℝ)) := hsum
      _ = blim ω (rankSeq_univ rk ω n m A) := by rw [htend, add_zero]
  · intro n m k A B
    let C : ℝ := (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
    have hCnn : 0 ≤ C := by
      show 0 ≤ (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ)
      positivity
    have hpt : ∀ i : ℕ, rankSeq_univ rk ω n k (A * B) i ≤ rankSeq_univ rk ω m k B i + C / (i : ℝ) := by
      intro i
      have hsplit : trunc i (A * B) =
          trunc i A * trunc i B + (trunc i (A * B) - trunc i A * trunc i B) := by
        abel
      have h4 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
          rk.rk (m * i) (k * i) (trunc i B) + C := by
        have h1 : rk.rk (n * i) (k * i) (trunc i (A * B)) ≤
            rk.rk (n * i) (k * i) (trunc i A * trunc i B) +
              rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) := by
          have hraw := RankAPI.rk_add_le rk (trunc i A * trunc i B)
            (trunc i (A * B) - trunc i A * trunc i B)
          have hsum : trunc i A * trunc i B +
              (trunc i (A * B) - trunc i A * trunc i B) = trunc i (A * B) := by abel
          rw [hsum] at hraw
          exact hraw
        have h2 : rk.rk (n * i) (k * i) (trunc i A * trunc i B) ≤
            rk.rk (m * i) (k * i) (trunc i B) :=
          rk.rk_mul_le_right (trunc i A) (trunc i B)
        have h3 : rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤ C :=
          rk_trunc_mul_sub_le_univ rk A B i
        linarith
      calc rankSeq_univ rk ω n k (A * B) i
          = rk.rk (n * i) (k * i) (trunc i (A * B)) / (i : ℝ) := rfl
        _ ≤ (rk.rk (m * i) (k * i) (trunc i B) + C) / (i : ℝ) :=
            div_le_div_of_nonneg_right h4 (Nat.cast_nonneg i)
        _ = rk.rk (m * i) (k * i) (trunc i B) / (i : ℝ) + C / (i : ℝ) := add_div _ _ _
        _ = rankSeq_univ rk ω m k B i + C / (i : ℝ) := rfl
    have hbndC : ∀ i : ℕ, |C / (i : ℝ)| ≤ C := by
      intro i
      rw [abs_of_nonneg (div_nonneg hCnn (Nat.cast_nonneg i))]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simpa using hCnn
      · rw [div_le_iff₀ (by exact_mod_cast hi)]
        have h1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
        nlinarith
    have hbndC' : ∀ i : ℕ, |C / (i : ℝ)| ≤ max (m : ℝ) (k : ℝ) + C :=
      fun i => le_trans (hbndC i)
        (le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ max (m : ℝ) (k : ℝ)))
    have hbndB' : ∀ i : ℕ, |rankSeq_univ rk ω m k B i| ≤ max (m : ℝ) (k : ℝ) + C :=
      fun i => le_trans (hbdd m k B i) (le_add_of_nonneg_right hCnn)
    have hsum : blim ω (fun i => rankSeq_univ rk ω m k B i + C / (i : ℝ)) =
        blim ω (rankSeq_univ rk ω m k B) + blim ω (fun i => C / (i : ℝ)) :=
      blim_add ω hbndB' hbndC'
    have htend : blim ω (fun i => C / (i : ℝ)) = 0 :=
      blim_of_tendsto ω hω hbndC (tendsto_const_div_atTop_nhds_zero_nat C)
    have hmono : blim ω (rankSeq_univ rk ω n k (A * B)) ≤
        blim ω (fun i => rankSeq_univ rk ω m k B i + C / (i : ℝ)) := by
      refine blim_mono ω (hbdd n k (A * B))
        (M' := max (m : ℝ) (k : ℝ) + C) (fun i => ?_) hpt
      calc |rankSeq_univ rk ω m k B i + C / (i : ℝ)|
          ≤ |rankSeq_univ rk ω m k B i| + |C / (i : ℝ)| := abs_add_le _ _
        _ ≤ max (m : ℝ) (k : ℝ) + C := add_le_add (hbdd m k B i) (hbndC i)
    calc blim ω (rankSeq_univ rk ω n k (A * B)) ≤
          blim ω (fun i => rankSeq_univ rk ω m k B i + C / (i : ℝ)) := hmono
      _ = blim ω (rankSeq_univ rk ω m k B) + blim ω (fun i => C / (i : ℝ)) := hsum
      _ = blim ω (rankSeq_univ rk ω m k B) := by rw [htend, add_zero]
  · intro n m p q A B
    have hpt : ∀ i : ℕ, rankSeq_univ rk ω (n + p) (m + q) (blockDiagFin A B) i =
        rankSeq_univ rk ω n m A i + rankSeq_univ rk ω p q B i := by
      intro i
      simp only [rankSeq_univ]
      rw [rk_trunc_blockDiagFin2_univ rk i A B, add_div]
    rw [funext hpt]
    exact blim_add ω (abs_rankSeq_le_of_le_univ rk ω A (Nat.le_add_right n p) (Nat.le_add_right m q))
      (abs_rankSeq_le_of_le_univ rk ω B (Nat.le_add_left p n) (Nat.le_add_left q m))
  · intro n m p q A B C
    have hpt : ∀ i : ℕ, rankSeq_univ rk ω n m A i + rankSeq_univ rk ω p q B i ≤
        rankSeq_univ rk ω (n + p) (m + q) (blockUpperFin A B C) i := by
      intro i
      have h := rk_trunc_blockUpperFin2_univ rk i A B C
      simp only [rankSeq_univ]
      rw [← add_div]
      exact div_le_div_of_nonneg_right h (Nat.cast_nonneg i)
    calc blim ω (rankSeq_univ rk ω n m A) + blim ω (rankSeq_univ rk ω p q B)
        = blim ω (rankSeq_univ rk ω n m A + rankSeq_univ rk ω p q B) :=
          (blim_add ω (abs_rankSeq_le_of_le_univ rk ω A (Nat.le_add_right n p) (Nat.le_add_right m q))
            (abs_rankSeq_le_of_le_univ rk ω B (Nat.le_add_left p n) (Nat.le_add_left q m))).symm
      _ ≤ blim ω (rankSeq_univ rk ω (n + p) (m + q) (blockUpperFin A B C)) :=
          blim_mono ω (M' := max (n : ℝ) (m : ℝ) + max (p : ℝ) (q : ℝ)) (fun i => by
              calc |rankSeq_univ rk ω n m A i + rankSeq_univ rk ω p q B i|
                  ≤ |rankSeq_univ rk ω n m A i| + |rankSeq_univ rk ω p q B i| := abs_add_le _ _
                _ ≤ max (n : ℝ) (m : ℝ) + max (p : ℝ) (q : ℝ) :=
                    add_le_add (hbdd n m A i) (hbdd p q B i))
            (fun i => by
              refine le_trans (abs_rankSeq_le_univ rk ω (blockUpperFin A B C) i) ?_
              push_cast
              exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
                (add_le_add (le_max_right _ _) (le_max_right _ _))) hpt
  · constructor
    · intro n m A
      change blim ω (rankSeq_univ rk ω n m (skewLaurentConst n m A)) = rk.rk n m A
      have hev : ∀ᶠ i in Filter.atTop,
          rankSeq_univ rk ω n m (skewLaurentConst n m A) i = rk.rk n m A := by
        filter_upwards [eventually_ge_atTop 1] with i hi
        rw [rankSeq_univ, rk_trunc_skewLaurentConst_univ rk hτ A i]
        have hi' : (i : ℝ) ≠ 0 := by positivity
        exact mul_div_cancel_left₀ (rk.rk n m A) hi'
      rw [blim_congr ω hω hev, blim_const ω (rk.rk n m A)]
    · intro n A
      change blim ω (rankSeq_univ rk ω n n (onePlusAt n A)) = (n : ℝ)
      have hev : ∀ᶠ i in Filter.atTop, rankSeq_univ rk ω n n (onePlusAt n A) i = (n : ℝ) := by
        filter_upwards [eventually_ge_atTop 1] with i hi
        rw [rankSeq_univ, rk_trunc_onePlusAt_univ rk A i]
        have hi' : (i : ℝ) ≠ 0 := by positivity
        exact mul_div_cancel_left₀ (n : ℝ) hi'
      rw [blim_congr ω hω hev, blim_const ω (n : ℝ)]

end Work.ORHughesFree.NaturalExtension
