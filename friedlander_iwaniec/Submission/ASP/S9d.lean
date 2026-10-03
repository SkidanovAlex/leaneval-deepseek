/-
  Companion paper, §9: the `E₂` estimate (9.12).
-/
import Mathlib
import Submission.ASP.S9a
import Submission.ASP.S9c

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The key counting step: squarefree divisors of a prescribed `lcm` -/

/-- The number of squarefree `d ∈ [1,D]` with `lcm(ν²,d) ∣ n` is at most `τ(n)`: the map
`d ↦ d` is an injection into `n.divisors` (as `lcm(ν²,d) ∣ n` forces `d ∣ n`). -/
lemma card_sqfree_lcm_dvd_le_tau {ν D n : ℕ} (hn : 1 ≤ n) :
    (((Finset.Icc 1 D).filter Squarefree).filter (fun d => Nat.lcm (ν ^ 2) d ∣ n)).card
      ≤ n.divisors.card := by
  refine Finset.card_le_card (fun d hd => ?_)
  rw [Nat.mem_divisors]
  exact ⟨dvd_trans (Nat.dvd_lcm_right _ _) (Finset.mem_filter.mp hd).2, by omega⟩

/-- The `lcm`-weighted congruence sums over squarefree `d ≤ D`: exchanging the two sums
bounds them by the `τ`-weighted square-divisor sum over the `n ≤ t` divisible by `ν²`. -/
lemma sum_sqfree_Ad_lcm_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ν D t : ℕ) (ht : 1 ≤ t) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, Ad a (Nat.lcm (ν ^ 2) d) t)
      ≤ ∑ n ∈ (Finset.Icc 1 t).filter (fun n => ν ^ 2 ∣ n),
          a n * (n.divisors.card : ℝ) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 D).filter Squarefree with hS
  have h1 : (∑ d ∈ S, Ad a (Nat.lcm (ν ^ 2) d) t)
      = ∑ d ∈ S, ∑ n ∈ Finset.Icc 1 t,
          (if Nat.lcm (ν ^ 2) d ∣ n then a n else 0) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Ad, Nat.floor_natCast, Finset.sum_filter]
  have h2 : (∑ d ∈ S, ∑ n ∈ Finset.Icc 1 t,
        (if Nat.lcm (ν ^ 2) d ∣ n then a n else 0))
      = ∑ n ∈ Finset.Icc 1 t, a n * ((S.filter (fun d => Nat.lcm (ν ^ 2) d ∣ n)).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h1, h2]
  have h3 : (∑ n ∈ Finset.Icc 1 t, a n * ((S.filter (fun d => Nat.lcm (ν ^ 2) d ∣ n)).card : ℝ))
      = ∑ n ∈ (Finset.Icc 1 t).filter (fun n => ν ^ 2 ∣ n),
          a n * ((S.filter (fun d => Nat.lcm (ν ^ 2) d ∣ n)).card : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : ν ^ 2 ∣ n
    · rw [if_pos h]
    · rw [if_neg h]
      have hemp : S.filter (fun d => Nat.lcm (ν ^ 2) d ∣ n) = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr (fun d hd => ?_)
        rw [Finset.mem_filter] at hd
        exact h (dvd_trans (Nat.dvd_lcm_left _ _) hd.2)
      rw [hemp]
      simp
  rw [h3]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hc : (((S.filter (fun d => Nat.lcm (ν ^ 2) d ∣ n)).card : ℝ)) ≤ (n.divisors.card : ℝ) := by
    have h := card_sqfree_lcm_dvd_le_tau (ν := ν) (D := D) hn1
    rw [hS]
    exact_mod_cast h
  exact mul_le_mul_of_nonneg_left hc (ha n)

/-! ### The two halves of the `ν`-range -/

/-- The `A`-part of `Etwo`: `∑♭_{ν ∈ [νlo,νhi]} ∑♭_{d ≤ D} A_{[ν²,d]}(t)`. -/
def EtwoA (a : ℕ → ℝ) (t D : ℕ) (νlo νhi : ℕ) : ℝ :=
  ∑ ν ∈ ((Finset.Icc νlo νhi).filter Squarefree),
    ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, Ad a (Nat.lcm (ν ^ 2) d) t

/-- The `g`-part of `Etwo`: `A(t)·∑♭_{ν ∈ [νlo,νhi]} ∑♭_{d ≤ D} g([ν²,d])`. -/
def EtwoG (a g : ℕ → ℝ) (t D : ℕ) (νlo νhi : ℕ) : ℝ :=
  ∑ ν ∈ ((Finset.Icc νlo νhi).filter Squarefree),
    ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, g (Nat.lcm (ν ^ 2) d) * Acount a t

/-- `#{ν ∈ [a,b] : ν squarefree, ν² ∣ n}`. -/
def sqdvCount (n a b : ℕ) : ℕ :=
  (((Finset.Icc a b).filter Squarefree).filter (fun ν => ν ^ 2 ∣ n)).card

/-- The count rewritten with the predicate conjoined. -/
lemma sqdvCount_eq (n a b : ℕ) :
    sqdvCount n a b = ((Finset.Icc a b).filter (fun ν => Squarefree ν ∧ ν ^ 2 ∣ n)).card := by
  rw [sqdvCount, Finset.filter_filter]

/-- Every `ν` counted by `sqdvCount` gives a divisor `ν` of `n`, so the count is at most `τ(n)`. -/
lemma sqdvCount_le_tau {n a b : ℕ} (hn : 1 ≤ n) : sqdvCount n a b ≤ n.divisors.card := by
  rw [sqdvCount, Finset.filter_filter]
  refine Finset.card_le_card (fun ν hν => ?_)
  rw [Nat.mem_divisors]
  refine ⟨?_, by omega⟩
  exact dvd_trans (by exact ⟨ν, by ring⟩) (Finset.mem_filter.mp hν).2.2

/-- The `ν`-`n` exchange for a sum over squarefree `ν` with `ν² ∣ n`. -/
lemma sum_sqfree_sq_dvd_swap (Sν : Finset ℕ) (B : ℕ → ℝ) (t : ℕ) :
    (∑ ν ∈ Sν, ∑ n ∈ (Finset.Icc 1 t).filter (fun n => ν ^ 2 ∣ n), B n)
      = ∑ n ∈ Finset.Icc 1 t, B n * ((Sν.filter (fun ν => ν ^ 2 ∣ n)).card : ℝ) := by
  have h1 : (∑ ν ∈ Sν, ∑ n ∈ (Finset.Icc 1 t).filter (fun n => ν ^ 2 ∣ n), B n)
      = ∑ ν ∈ Sν, ∑ n ∈ Finset.Icc 1 t, (if ν ^ 2 ∣ n then B n else 0) :=
    Finset.sum_congr rfl (fun ν _ => Finset.sum_filter _ _)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Weighted Cauchy–Schwarz: `(∑ x y)² ≤ (∑ x)(∑ x y²)` for nonnegative `x`, `y`. -/
lemma sq_sum_mul_le_sum_mul_sum_mul_sq {ι : Type*} {s : Finset ι} {x y : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, x i * y i) ^ 2 ≤ (∑ i ∈ s, x i) * ∑ i ∈ s, x i * y i ^ 2 := by
  have hmain := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (x i))
    (fun i => Real.sqrt (x i) * y i)
  have h1 : (∑ i ∈ s, Real.sqrt (x i) * (Real.sqrt (x i) * y i))
      = ∑ i ∈ s, x i * y i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hs : Real.sqrt (x i) * Real.sqrt (x i) = x i := by
      rw [← pow_two, Real.sq_sqrt (hx i hi)]
    rw [← mul_assoc, hs]
  have h2 : (∑ i ∈ s, Real.sqrt (x i) ^ 2) = ∑ i ∈ s, x i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Real.sq_sqrt (hx i hi)]
  have h3 : (∑ i ∈ s, (Real.sqrt (x i) * y i) ^ 2) = ∑ i ∈ s, x i * y i ^ 2 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mul_pow, Real.sq_sqrt (hx i hi)]
  rw [h1, h2, h3] at hmain
  exact hmain

/-! ### The estimate (9.12): the half `ν > Y` -/

/-- **Companion §9, (9.12), the half `ν > Y`** (this is `E₂₁`, with `Y = L√D`):
Cauchy–Schwarz with (9.2) and the `τ³`-weighted square-divisor count. -/
theorem EtwoA_gt_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (t D Y : ℕ) (ht : 1 ≤ t) {X : ℝ}
    (hX : (∑ n ∈ Finset.Icc 1 t, (n.divisors.card : ℝ) ^ 3 * (sqdvCount n (Y + 1) t : ℝ)) ≤ X) :
    EtwoA a t D (Y + 1) t
      ≤ Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * Real.sqrt X := by
  classical
  have h1 : EtwoA a t D (Y + 1) t
      ≤ ∑ n ∈ Finset.Icc 1 t,
          (a n * (n.divisors.card : ℝ)) * (sqdvCount n (Y + 1) t : ℝ) := by
    rw [EtwoA]
    refine (Finset.sum_le_sum (fun ν _ => sum_sqfree_Ad_lcm_le a ha ν D t ht)).trans ?_
    rw [sum_sqfree_sq_dvd_swap ((Finset.Icc (Y + 1) t).filter Squarefree)
      (fun n => a n * (n.divisors.card : ℝ)) t]
    rfl
  refine le_trans h1 ?_
  set F : ℕ → ℝ := fun n => (a n * (n.divisors.card : ℝ)) * (sqdvCount n (Y + 1) t : ℝ)
    with hF
  set G : ℕ → ℝ := fun n => (n.divisors.card : ℝ) * (sqdvCount n (Y + 1) t : ℝ) with hG
  have hFG : ∀ n, F n = a n * G n := fun n => mul_assoc _ _ _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 t) (fun n => a n) G
  rw [show (∑ n ∈ Finset.Icc 1 t, a n * G n) = ∑ n ∈ Finset.Icc 1 t, F n from
    Finset.sum_congr rfl (fun n _ => (hFG n).symm)] at hcs
  have hbound : (∑ n ∈ Finset.Icc 1 t, G n ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 t, (n.divisors.card : ℝ) ^ 3 * (sqdvCount n (Y + 1) t : ℝ) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcard : ((sqdvCount n (Y + 1) t : ℕ) : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast sqdvCount_le_tau (a := Y + 1) (b := t) hn1
    have hG2 : G n = (n.divisors.card : ℝ) * (sqdvCount n (Y + 1) t : ℝ) := rfl
    rw [hG2]
    have hτ : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
    have hN : 0 ≤ ((sqdvCount n (Y + 1) t : ℕ) : ℝ) := Nat.cast_nonneg _
    have hN2 : ((sqdvCount n (Y + 1) t : ℕ) : ℝ) * ((sqdvCount n (Y + 1) t : ℕ) : ℝ)
        ≤ ((sqdvCount n (Y + 1) t : ℕ) : ℝ) * (n.divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard hN
    calc ((n.divisors.card : ℝ) * (sqdvCount n (Y + 1) t : ℝ)) ^ 2
        = (n.divisors.card : ℝ) ^ 2 *
            (((sqdvCount n (Y + 1) t : ℕ) : ℝ) * ((sqdvCount n (Y + 1) t : ℕ) : ℝ)) := by ring
      _ ≤ (n.divisors.card : ℝ) ^ 2 *
            (((sqdvCount n (Y + 1) t : ℕ) : ℝ) * (n.divisors.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hN2 (by positivity)
      _ = (n.divisors.card : ℝ) ^ 3 * (sqdvCount n (Y + 1) t : ℝ) := by ring
  have hnn : 0 ≤ ∑ n ∈ Finset.Icc 1 t, F n := by
    rw [hF]
    exact Finset.sum_nonneg (fun n _ => mul_nonneg (mul_nonneg (ha n) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
  have hnn2 : 0 ≤ ∑ n ∈ Finset.Icc 1 t, a n ^ 2 :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hXnn : 0 ≤ X := by
    refine le_trans (Finset.sum_nonneg (fun n _ => ?_)) hX
    exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
  have hsq : (∑ n ∈ Finset.Icc 1 t, F n) ^ 2 ≤ (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * X :=
    le_trans hcs (mul_le_mul_of_nonneg_left (le_trans hbound hX) hnn2)
  calc (∑ n ∈ Finset.Icc 1 t, F n)
      ≤ Real.sqrt ((∑ n ∈ Finset.Icc 1 t, a n ^ 2) * X) :=
        (Real.le_sqrt hnn (mul_nonneg hnn2 hXnn)).mpr hsq
    _ = Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * Real.sqrt X := Real.sqrt_mul hnn2 X


/-! ### The estimate (9.12): the half `L < ν ≤ Y` -/

/-- Splitting the `ν`-range at `Y`. -/
lemma EtwoA_eq_split (a : ℕ → ℝ) (t D L Y : ℕ) (hLY : L < Y) (hYt : Y ≤ t) :
    EtwoA a t D (L + 1) t = EtwoA a t D (L + 1) Y + EtwoA a t D (Y + 1) t := by
  unfold EtwoA
  have hset : Finset.Icc (L + 1) t = Finset.Icc (L + 1) Y ∪ Finset.Icc (Y + 1) t := by
    ext ν
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (L + 1) Y) (Finset.Icc (Y + 1) t) := by
    rw [Finset.disjoint_left]
    intro ν h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hset, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]

/-- **Companion §9, (9.12), the half `L < ν ≤ Y`** (this is `E₂₂`, with `Y = L√D`):
Cauchy–Schwarz with `S₁ = ∑♭_{L < ν ≤ Y} A_{ν²}(t)` and `S₂ = ∑_{n ≤ t} a_n τ(n)³`. -/
theorem EtwoA_le_le (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (t D L Y : ℕ) (ht : 1 ≤ t) :
    EtwoA a t D (L + 1) Y
      ≤ Real.sqrt (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t)
        * Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) := by
  classical
  have h1 : EtwoA a t D (L + 1) Y
      ≤ ∑ n ∈ Finset.Icc 1 t,
          (a n * (n.divisors.card : ℝ)) * (sqdvCount n (L + 1) Y : ℝ) := by
    rw [EtwoA]
    refine (Finset.sum_le_sum (fun ν _ => sum_sqfree_Ad_lcm_le a ha ν D t ht)).trans ?_
    rw [sum_sqfree_sq_dvd_swap ((Finset.Icc (L + 1) Y).filter Squarefree)
      (fun n => a n * (n.divisors.card : ℝ)) t]
    rfl
  have h1' : (∑ n ∈ Finset.Icc 1 t,
        (a n * (n.divisors.card : ℝ)) * (sqdvCount n (L + 1) Y : ℝ))
      = ∑ n ∈ Finset.Icc 1 t,
          (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ) :=
    Finset.sum_congr rfl (fun n _ => by ring)
  have hS1 : (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t)
      = ∑ n ∈ Finset.Icc 1 t, a n * (sqdvCount n (L + 1) Y : ℝ) := by
    have h : ∀ ν, Ad a (ν ^ 2) t
        = ∑ n ∈ (Finset.Icc 1 t).filter (fun n => ν ^ 2 ∣ n), a n := by
      intro ν
      rw [Ad, Nat.floor_natCast]
    rw [Finset.sum_congr rfl (fun ν _ => h ν)]
    rw [sum_sqfree_sq_dvd_swap ((Finset.Icc (L + 1) Y).filter Squarefree) (fun n => a n) t]
    rfl
  have h2 : (∑ n ∈ Finset.Icc 1 t,
        (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ) ^ 2)
      ≤ ∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3 := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcard : ((sqdvCount n (L + 1) Y : ℕ) : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast sqdvCount_le_tau (a := L + 1) (b := Y) hn1
    have hτ : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
    have hN : 0 ≤ ((sqdvCount n (L + 1) Y : ℕ) : ℝ) := Nat.cast_nonneg _
    have hkey : ((sqdvCount n (L + 1) Y : ℝ) * (n.divisors.card : ℝ) ^ 2)
        ≤ (n.divisors.card : ℝ) ^ 3 := by nlinarith [hcard, hτ, hN]
    calc (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ) ^ 2
        = a n * ((sqdvCount n (L + 1) Y : ℝ) * (n.divisors.card : ℝ) ^ 2) := by ring
      _ ≤ a n * (n.divisors.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hkey (ha n)
  have hnn1 : 0 ≤ ∑ n ∈ Finset.Icc 1 t, a n * (sqdvCount n (L + 1) Y : ℝ) :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (ha n) (Nat.cast_nonneg _))
  have hnn2 : 0 ≤ ∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3 :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (ha n) (by positivity))
  have hXnn : 0 ≤ ∑ n ∈ Finset.Icc 1 t,
      (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ) :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (mul_nonneg (ha n) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _))
  have hcs := sq_sum_mul_le_sum_mul_sum_mul_sq (s := Finset.Icc 1 t)
    (x := fun n => a n * (sqdvCount n (L + 1) Y : ℝ))
    (y := fun n => (n.divisors.card : ℝ))
    (fun n _ => mul_nonneg (ha n) (Nat.cast_nonneg _)) (fun n _ => Nat.cast_nonneg _)
  have hX : (∑ n ∈ Finset.Icc 1 t,
        (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ)) ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 t, a n * (sqdvCount n (L + 1) Y : ℝ))
        * (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) :=
    le_trans hcs (mul_le_mul_of_nonneg_left h2 hnn1)
  refine le_trans (le_trans h1 (le_of_eq h1')) ?_
  calc (∑ n ∈ Finset.Icc 1 t,
        (a n * (sqdvCount n (L + 1) Y : ℝ)) * (n.divisors.card : ℝ))
      ≤ Real.sqrt ((∑ n ∈ Finset.Icc 1 t, a n * (sqdvCount n (L + 1) Y : ℝ))
          * (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3)) :=
        (Real.le_sqrt hXnn (mul_nonneg hnn1 hnn2)).mpr hX
    _ = Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n * (sqdvCount n (L + 1) Y : ℝ))
          * Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) :=
        Real.sqrt_mul hnn1 _
    _ = Real.sqrt (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) := by
        rw [hS1]


/-! ### The assembly of (9.12) -/

/-- `Etwo` splits into its `A`-part and its `g`-part. -/
theorem Etwo_eq_A_add_G (a g : ℕ → ℝ) (t D L : ℕ) :
    Etwo a g t D L = EtwoA a t D (L + 1) t + EtwoG a g t D (L + 1) t := by
  rw [Etwo, EtwoA, EtwoG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [← Finset.sum_add_distrib]

/-- **Companion §9, (9.12)**: the estimate `E₂` in terms of the three explicit inputs
(9.2) (`hA2`), the τ³-weighted square-divisor count (`hX`), Lemma 2 with `k = 3` (`hS2`),
(1.8)+(9.1)+(R₃) (`hS1`) and the `g`-part (`hG`). -/
theorem Etwo_le (a g : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (t D L Y : ℕ) (ht : 1 ≤ t) (hLY : L < Y)
    (hYt : Y ≤ t) {X S1 S2 Gsum : ℝ}
    (hX : (∑ n ∈ Finset.Icc 1 t, (n.divisors.card : ℝ) ^ 3
        * (sqdvCount n (Y + 1) t : ℝ)) ≤ X)
    (hS1 : (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t) ≤ S1)
    (hS2 : (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) ≤ S2)
    (hG : EtwoG a g t D (L + 1) t ≤ Gsum) :
    Etwo a g t D L
      ≤ Real.sqrt S1 * Real.sqrt S2 + Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * Real.sqrt X
        + Gsum := by
  rw [Etwo_eq_A_add_G, EtwoA_eq_split a t D L Y hLY hYt]
  refine add_le_add (add_le_add ?_ ?_) hG
  · refine le_trans (EtwoA_le_le a ha t D L Y ht) ?_
    have h1 : Real.sqrt (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t)
        ≤ Real.sqrt S1 := Real.sqrt_le_sqrt hS1
    have h2 : Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3)
        ≤ Real.sqrt S2 := Real.sqrt_le_sqrt hS2
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact EtwoA_gt_le a ha t D Y ht hX

end

end Submission.ASP
