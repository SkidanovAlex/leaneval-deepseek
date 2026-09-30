import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.prime_avoid
import Submission.Work.BMF.recursion.card_pair_fibre_sum
import Submission.Work.BMF.recursion.S1Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

open scoped BigOperators

noncomputable section

open Submission.Vinogradov (powerSums powerSums_eq_iff_matches)

/-- **Fibre decomposition of `S1pair`.**  The number of matching pairs of `S`-tuples in `[1,Q]` whose
head is pairwise distinct on both sides is `Σ_v #(hdSet ∩ fib v)²`, the sum running over the values
`v` of the moment map `powerSums k`.

This is `card_pair_fiber_sq` (module `S1Defs`) applied to the moment map and the set `hdSet`, using
`p ∈ solSet ↔ Matches S k Q p ↔ powerSums k p.1 = powerSums k p.2`. -/
theorem S1pair_eq_sum_fiber (S k Q : ℕ) (hkS : k ≤ S) :
    (S1pair S k Q hkS : ℝ)
      = ∑ v ∈ momImg S k Q,
          (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 := by
  classical
  have hpair : ((Finset.univ : Finset (PairSpace S Q)).filter
        (fun p => powerSums k p.1 = powerSums k p.2 ∧ p.1 ∈ hdSet S k Q hkS
          ∧ p.2 ∈ hdSet S k Q hkS))
      = (solSet S k Q).filter (fun p => HD hkS p.1 ∧ HD hkS p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, solSet, mem_hdSet,
      powerSums_eq_iff_matches]
  unfold S1pair
  rw [← hpair]
  rw [card_pair_fiber_sq (f := fun x : Tup S Q => powerSums k x) (A := hdSet S k Q hkS)]
  simp only [momImg]

/-- **Fibre decomposition of `I1`.**  The number of matching pairs of `S`-tuples in `[1,Q]` whose head
is pairwise distinct modulo `p` on both sides is `Σ_v #(hdpSet p ∩ fib v)²`.

This is `card_pair_fiber_sq` (module `S1Defs`) applied to the moment map and the set `hdpSet p`,
using `p ∈ solSet ↔ Matches S k Q p ↔ powerSums k p.1 = powerSums k p.2`. -/
theorem I1_eq_sum_fiber (S k Q p : ℕ) (hkS : k ≤ S) :
    (I1 S k Q p hkS : ℝ)
      = ∑ v ∈ momImg S k Q,
          (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 := by
  classical
  have hpair : ((Finset.univ : Finset (PairSpace S Q)).filter
        (fun q => powerSums k q.1 = powerSums k q.2 ∧ q.1 ∈ hdpSet S k Q p hkS
          ∧ q.2 ∈ hdpSet S k Q p hkS))
      = (solSet S k Q).filter (fun q => HDp p k hkS q.1 ∧ HDp p k hkS q.2) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, solSet, mem_hdpSet,
      powerSums_eq_iff_matches]
  unfold I1
  rw [← hpair]
  rw [card_pair_fiber_sq (f := fun x : Tup S Q => powerSums k x) (A := hdpSet S k Q p hkS)]
  simp only [momImg]

/-- **Prime-avoidance fibre bound.**  Fix a moment vector `v`.  Every tuple in the fibre
`{x | powerSums k x = v}` whose head is pairwise distinct (as integers) has — by `prime_avoid` —
some prime `p ∈ P` modulo which its head is still pairwise distinct.  Hence

`#(hdSet ∩ {powerSums k x = v}) ≤ Σ_{p ∈ P} #(hdpSet p ∩ {powerSums k x = v})`. -/
theorem card_fiber_le_sum (S k Q M : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (hMQ : Q < M ^ k)
    (P : Finset ℕ) (hPp : ∀ p ∈ P, Nat.Prime p) (hPM : ∀ p ∈ P, M < p)
    (hPc : k * (k - 1) * (k - 1) < 2 * P.card) (v : Fin (k + 1) → ℤ) :
    ((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card
      ≤ ∑ p ∈ P, ((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card := by
  classical
  have hsub : (hdSet S k Q hkS).filter (fun x => powerSums k x = v)
      ⊆ P.biUnion
          (fun p => (hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxA, hxv⟩ := hx
    have hHD : HD hkS x := mem_hdSet.mp hxA
    obtain ⟨p, hpP, hp⟩ :=
      prime_avoid k Q M (fun i => x (hIdx hkS i)) ((hd_head hkS x).mp hHD) hMQ P hPp hPM hPc
    exact Finset.mem_biUnion.mpr ⟨p, hpP, by
      rw [Finset.mem_filter]
      exact ⟨mem_hdpSet.mpr ((hdp_head hkS x).mpr hp), hxv⟩⟩
  calc ((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card
      ≤ (P.biUnion (fun p => (hdpSet S k Q p hkS).filter (fun x => powerSums k x = v))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, ((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card :=
        Finset.card_biUnion_le

/-- The number of matching pairs whose head is distinct on both sides is at most `|P|` times the
sum over `p ∈ P` of `I1(p)`, the number of matching pairs whose head is distinct *modulo* `p` on
both sides (Wooley, Michigan Math. J. **40** (1993), 175–180, §2, case (b): `S₁ ≤ |P| Σ_p I1(p)`).

Hypotheses: `P` is a set of primes all `> M`, `Q < M^k` and `k(k-1)² < 2|P|` (so that the
prime-avoidance `prime_avoid` applies).

Route.  Let `A := hdSet S k Q hkS`, `A_p := {x : HDp p k hkS x}` and
`R3p v := #(A_p ∩ fib v)`.  By the fibre decomposition `card_pair_fibre_sum`,
`S1pair = Σ_v #(A ∩ fib v)²`, and `I1 p = Σ_v #(A_p ∩ fib v)²` (again `card_pair_fibre_sum`,
using `p ∈ solSet ↔ Matches ↔ equality of moment vectors`).  For `x ∈ A ∩ fib v`, the tuple
`fun i => x (hIdx hkS i) : Tup k Q` has pairwise distinct entries, so `prime_avoid` gives some
`p ∈ P` with `HDp p k (le_refl k)` on it, i.e. `HDp p k hkS x`; hence
`#(A ∩ fib v) ≤ Σ_{p∈P} R3p v` and Cauchy–Schwarz over the finite sum
(`(Σ_p a_p)² ≤ |P| Σ_p a_p²`) gives `S1pair ≤ |P| Σ_p I1 p`. -/
theorem S1_le_I1 (S k Q M : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (hMQ : Q < M ^ k)
    (P : Finset ℕ) (hPp : ∀ p ∈ P, Nat.Prime p) (hPM : ∀ p ∈ P, M < p)
    (hPc : k * (k - 1) * (k - 1) < 2 * P.card) :
    (S1pair S k Q hkS : ℝ) ≤ (P.card : ℝ) * ∑ p ∈ P, (I1 S k Q p hkS : ℝ) := by
  classical
  have hstep : ∀ v ∈ momImg S k Q,
      (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2
        ≤ (P.card : ℝ) * ∑ p ∈ P,
            (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 := by
    intro v _
    have hle := card_fiber_le_sum S k Q M hk hkS hMQ P hPp hPM hPc v
    have hcast : (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card : ℝ)
        ≤ ∑ p ∈ P,
            (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hle
    calc (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2
        ≤ (∑ p ∈ P,
            (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
      _ ≤ (P.card : ℝ) * ∑ p ∈ P,
            (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
  calc (S1pair S k Q hkS : ℝ)
      = ∑ v ∈ momImg S k Q,
          (((hdSet S k Q hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 :=
        S1pair_eq_sum_fiber S k Q hkS
    _ ≤ ∑ v ∈ momImg S k Q, (P.card : ℝ) * ∑ p ∈ P,
          (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 :=
        Finset.sum_le_sum hstep
    _ = ∑ v ∈ momImg S k Q, ∑ p ∈ P, (P.card : ℝ) *
          (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
    _ = ∑ p ∈ P, ∑ v ∈ momImg S k Q, (P.card : ℝ) *
          (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 :=
        Finset.sum_comm
    _ = ∑ p ∈ P, (P.card : ℝ) * ∑ v ∈ momImg S k Q,
          (((hdpSet S k Q p hkS).filter (fun x => powerSums k x = v)).card : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
    _ = ∑ p ∈ P, (P.card : ℝ) * (I1 S k Q p hkS : ℝ) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [I1_eq_sum_fiber S k Q p hkS]
    _ = (P.card : ℝ) * ∑ p ∈ P, (I1 S k Q p hkS : ℝ) := by
        rw [Finset.mul_sum]

end

end Work.BMF.recursion
