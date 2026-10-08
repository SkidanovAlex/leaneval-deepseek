import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.SumMulBCount
import Submission.Work.CORE3.CommutingPairsEqCosetSum
import Submission.Work.CORE3.CosetPairCountValue

/-!
# `Work.CORE3.CommutingPairTallyCosets`

Bender 1981 §3, pp. 223–224.  The number `T` of pairs `(z, s)` of commuting involutions with
`z ∉ Ĥ` and `s ∈ Ĥ` — `Work.CORE3.commutingPairsOutsideHat B` — is `2 b₂ + 6 b₄`.

* `Work.CORE3.CommutingPairsEqCosetSum` (proved elsewhere) rewrites `T` as the sum of
  `cosetPairCount Ĥ c` over the nontrivial cosets `c` of `Ĥ` (via the bijection
  `(z, s) ↦ (z, z * s)`);
* `Work.CORE3.CosetPairCountValue` evaluates the summand of a coset `c ≠ 1` in terms of the
  number of involutions of `c`;
* `SumCosetValueBCount` (below) is the pure numerical summation.

The last two together give `Σ_c cosetPairCount Ĥ c = 2 b₂ + 6 b₄`.
-/

namespace Work.CORE3

open Work.GW2

/-- **Numerical summation.**  Summing `2` over the nontrivial cosets containing exactly two
involutions and `6` over those containing exactly four involutions gives `2 b₂ + 6 b₄`.  Here
`bCount Hh n` counts the nontrivial cosets of `Hh` containing exactly `n` involutions. -/
theorem SumCosetValueBCount (G : Type) [Group G] [Finite G] (Hh : Subgroup G)
    [Fintype (G ⧸ Hh)] [DecidableEq (G ⧸ Hh)] :
    (∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
       (if cosetInvCount Hh (Quotient.out c) = 2 then 2
         else if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0))
      = 2 * bCount Hh 2 + 6 * bCount Hh 4 := by
  classical
  -- Split each summand `f n = (2 if n = 2 else 0) + (6 if n = 4 else 0)`.
  have hsplit : ∀ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
      (if cosetInvCount Hh (Quotient.out c) = 2 then 2
        else if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0)
      = (if cosetInvCount Hh (Quotient.out c) = 2 then 2 else 0)
        + (if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0) := by
    intro c _
    by_cases h2 : cosetInvCount Hh (Quotient.out c) = 2
    · simp [h2]
    · by_cases h4 : cosetInvCount Hh (Quotient.out c) = 4
      · simp [h2, h4]
      · simp [h2, h4]
  have h1 : (∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        (if cosetInvCount Hh (Quotient.out c) = 2 then 2
          else if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0))
      = ∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        ((if cosetInvCount Hh (Quotient.out c) = 2 then 2 else 0)
          + (if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0)) :=
    Finset.sum_congr rfl hsplit
  rw [h1, Finset.sum_add_distrib]
  -- `Σ (2 if p c else 0) = 2 * #{c | p c}` and the same with `6`.
  have hA : (∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        (if cosetInvCount Hh (Quotient.out c) = 2 then 2 else 0))
      = 2 * ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
          (fun c => cosetInvCount Hh (Quotient.out c) = 2)).card := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rfl
  have hB : (∑ c ∈ Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)),
        (if cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0))
      = 6 * ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
          (fun c => cosetInvCount Hh (Quotient.out c) = 4)).card := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rfl
  rw [hA, hB]
  -- Identify the filtered cardinalities with `bCount Hh 2` and `bCount Hh 4`.
  have hb2 : bCount Hh 2
      = ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
          (fun c => cosetInvCount Hh (Quotient.out c) = 2)).card := by
    rw [bCount, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, ← Finset.filter_filter]
    rfl
  have hb4 : bCount Hh 4
      = ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
          (fun c => cosetInvCount Hh (Quotient.out c) = 4)).card := by
    rw [bCount, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, ← Finset.filter_filter]
    rfl
  rw [hb2, hb4]

theorem CommutingPairTallyCosets (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    (hLe4 : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y ≤ 4)
    (hFour : ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y = 4 →
      Work.CORE3.cosetPairCount B.Hhat y = 6) :
    (Work.CORE3.commutingPairsOutsideHat B).ncard
      = 2 * Work.GW2.bCount B.Hhat 2 + 6 * Work.GW2.bCount B.Hhat 4 := by
  classical
  haveI : Fintype (G ⧸ B.Hhat) := Fintype.ofFinite _
  rw [CommutingPairsEqCosetSum G B]
  have hstep : (∑ c ∈ Finset.univ.filter (fun c : G ⧸ B.Hhat => c ≠ ((1 : G) : G ⧸ B.Hhat)),
        Work.CORE3.cosetPairCount B.Hhat (Quotient.out c))
      = ∑ c ∈ Finset.univ.filter (fun c : G ⧸ B.Hhat => c ≠ ((1 : G) : G ⧸ B.Hhat)),
        (if Work.GW2.cosetInvCount B.Hhat (Quotient.out c) = 2 then 2
          else if Work.GW2.cosetInvCount B.Hhat (Quotient.out c) = 4 then 6 else 0) := by
    apply Finset.sum_congr rfl
    intro c hc
    exact CosetPairCountValue G B.Hhat hLe4 hFour c (Finset.mem_filter.mp hc).2
  rw [hstep]
  exact SumCosetValueBCount G B.Hhat

end Work.CORE3
