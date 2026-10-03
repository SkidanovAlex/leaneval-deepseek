import Mathlib
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.exists_dvd_ProdP_between

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Sums over unions

The Rankin step reindexes the `b₁`-tail of the `Π`-removal by a covering family of
divisor sets.  Two elementary facts about sums of **nonnegative** functions are needed:
the sum over a union is at most the sum of the sums, and the sum over a `biUnion` is at
most the double sum. -/

/-- For `F ≥ 0`, the sum over a union of two finsets is at most the sum of the sums. -/
lemma sum_union_le_of_nonneg (u v : Finset ℕ) (F : ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ x ∈ u ∪ v, F x ≤ ∑ x ∈ u, F x + ∑ x ∈ v, F x := by
  classical
  have hdisj : Disjoint u (v \ u) := Finset.disjoint_sdiff
  have heq : u ∪ (v \ u) = u ∪ v := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  calc ∑ x ∈ u ∪ v, F x = ∑ x ∈ u ∪ (v \ u), F x := by rw [heq]
    _ = ∑ x ∈ u, F x + ∑ x ∈ v \ u, F x := Finset.sum_union hdisj
    _ ≤ ∑ x ∈ u, F x + ∑ x ∈ v, F x :=
        add_le_add_right (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun x _ _ => hF x)) _

/-- For `F ≥ 0`, the sum over a `biUnion` is at most the iterated sum. -/
lemma sum_biUnion_le_of_nonneg (s : Finset ℕ) (g : ℕ → Finset ℕ) (F : ℕ → ℝ)
    (hF : ∀ x, 0 ≤ F x) :
    ∑ x ∈ s.biUnion g, F x ≤ ∑ a ∈ s, ∑ x ∈ g a, F x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (sum_union_le_of_nonneg (g a) (s.biUnion g) F hF).trans (add_le_add_right ih _)

/-- An injection `e` of a finite set into a union `⋃_{d ∈ D} g d`, with a nonnegative
weight `F`, gives `∑_{p ∈ s} F (e p) ≤ ∑_{d ∈ D} ∑_{x ∈ g d} F x`. -/
lemma sum_le_sum_of_injOn_biUnion (s : Finset (ℕ × ℕ)) (e : ℕ × ℕ → ℕ)
    (hinj : Set.InjOn e (↑s : Set (ℕ × ℕ))) (D : Finset ℕ) (g : ℕ → Finset ℕ) (F : ℕ → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hcover : ∀ p ∈ s, ∃ d ∈ D, e p ∈ g d) :
    ∑ p ∈ s, F (e p) ≤ ∑ d ∈ D, ∑ x ∈ g d, F x := by
  classical
  have himg : s.image e ⊆ D.biUnion g := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d, hd, hdg⟩ := hcover p hp
    exact Finset.mem_biUnion.mpr ⟨d, hd, hdg⟩
  calc ∑ p ∈ s, F (e p) = ∑ x ∈ s.image e, F x := (Finset.sum_image (f := F) hinj).symm
    _ ≤ ∑ x ∈ D.biUnion g, F x :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun x _ _ => hF x)
    _ ≤ ∑ d ∈ D, ∑ x ∈ g d, F x := sum_biUnion_le_of_nonneg D g F hF

/-! ## The pointwise (fixed `m`) Rankin reindexing

Every `b₁ ∣ Π(Pz)` with `b₁ > D` has a divisor `d` with `D < d ≤ D·Pz`
(`exists_dvd_ProdP_between`), and `(b₁, n) ↦ b₁ n` is injective because `b₁` is the
`Π`-part of `b₁ n` (`mul_inj_ProdP`).  Hence the `b₁`-tail inner sum is at most the
sum over all `N ≤ x` divisible by *some* such `d`. -/
lemma tail_inner_le (x Pz D m : ℕ) (hPz : 2 ≤ Pz) (hD : 1 ≤ D) (hm : 1 ≤ m) :
    (∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
        ∑ n ∈ (Finset.Icc 1 x).filter
            (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
          Work.FIChain.atilc (m * b₁ * n))
      ≤ ∑ d ∈ Work.FIChain.Dsp Pz D,
          ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
            Work.FIChain.atilc (m * N) := by
  classical
  have hL : (∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
        ∑ n ∈ (Finset.Icc 1 x).filter
            (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
          Work.FIChain.atilc (m * b₁ * n))
      = ∑ p ∈ ((((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁)) ×ˢ
              (Finset.Icc 1 x)).filter
              (fun p : ℕ × ℕ => Work.FITop4.PiCond Pz p.2 ∧ m * p.1 * p.2 ≤ x),
          Work.FIChain.atilc (m * (p.1 * p.2)) := by
    simp only [Finset.sum_filter, Finset.sum_product, mul_assoc]
  rw [hL]
  refine sum_le_sum_of_injOn_biUnion _ (fun p : ℕ × ℕ => p.1 * p.2) ?_ (Work.FIChain.Dsp Pz D)
      (fun d => (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x))
      (fun N => Work.FIChain.atilc (m * N)) (fun N => Work.FITop.atilFIa_nonneg _) ?_
  · intro p hp p' hp' heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
    obtain ⟨⟨hb1, _⟩, hcond⟩ := hp
    obtain ⟨⟨hb1', _⟩, hcond'⟩ := hp'
    have hdvdP : p.1 ∣ Work.FIChain.ProdP Pz :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hb1).1).1
    have hdvdP' : p'.1 ∣ Work.FIChain.ProdP Pz :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hb1').1).1
    obtain ⟨h1, h2⟩ := Work.FIChain.mul_inj_ProdP hdvdP hdvdP' hcond.1 hcond'.1 heq
    exact Prod.ext h1 h2
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hb1, hn1⟩, hcond⟩ := hp
    obtain ⟨hdvdB, hDb⟩ := Finset.mem_filter.mp hb1
    have hdvdP : p.1 ∣ Work.FIChain.ProdP Pz := (Nat.mem_divisors.mp hdvdB).1
    obtain ⟨d, hdP, hdb, hDd, hdle⟩ := Work.FIChain.exists_dvd_ProdP_between hPz hD hdvdP hDb
    refine ⟨d, Work.FIChain.mem_Dsp.mpr ⟨hdP, hDd, hdle⟩, ?_⟩
    have hp1 : 1 ≤ p.1 := by omega
    have hp2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hn1).1
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hdb.trans (dvd_mul_right p.1 p.2), ?_⟩
    · simpa using Nat.mul_le_mul hp1 hp2
    · calc p.1 * p.2 ≤ m * (p.1 * p.2) := by
            nth_rewrite 1 [← one_mul (p.1 * p.2)]
            exact Nat.mul_le_mul_right _ hm
        _ = m * p.1 * p.2 := by rw [mul_assoc]
        _ ≤ x := hcond.2
    · rw [show m * (p.1 * p.2) = m * p.1 * p.2 by rw [mul_assoc]]
      exact hcond.2

theorem tail_arith_step1 (x Pz D : ℕ) (hPz : 2 ≤ Pz) (hD : 1 ≤ D) :
    (∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
        ∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
          ∑ n ∈ (Finset.Icc 1 x).filter
              (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
            Work.FIChain.atilc (m * b₁ * n))
      ≤ ∑ d ∈ Work.FIChain.Dsp Pz D,
          ∑ m ∈ Finset.Icc 1 x, ((m.divisors.card : ℝ)) ^ 2 *
            ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
              Work.FIChain.atilc (m * N) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hper := tail_inner_le x Pz D m hPz hD hm1
  have hτ : (0 : ℝ) ≤ ((m.divisors.card : ℝ)) ^ 2 := by positivity
  calc ((m.divisors.card : ℝ)) ^ 2 *
        (∑ b₁ ∈ ((Work.FIChain.ProdP Pz).divisors).filter (fun b₁ : ℕ => D < b₁),
          ∑ n ∈ (Finset.Icc 1 x).filter
              (fun n => Work.FITop4.PiCond Pz n ∧ m * b₁ * n ≤ x),
            Work.FIChain.atilc (m * b₁ * n))
      ≤ ((m.divisors.card : ℝ)) ^ 2 *
          (∑ d ∈ Work.FIChain.Dsp Pz D,
            ∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
              Work.FIChain.atilc (m * N)) := mul_le_mul_of_nonneg_left hper hτ
    _ = ∑ d ∈ Work.FIChain.Dsp Pz D, ((m.divisors.card : ℝ)) ^ 2 *
          (∑ N ∈ (Finset.Icc 1 x).filter (fun N => d ∣ N ∧ m * N ≤ x),
              Work.FIChain.atilc (m * N)) := by rw [Finset.mul_sum]

end

end Work.FIChain
