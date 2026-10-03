/-
# `Work.FIArea3.JointCount.maxPieceFinset_card_le` — the number of maximal pieces is at most `τ(d)`

For `d ≥ 1` the set `{z : ℤ[i] | d ∣ |z|²}` is the disjoint union of the principal ideals `w·ℤ[i]`
of the *maximal* piece generators `w` (`GaussPieceMax d w`), and `maxPieceFinset d` keeps one
representative per associate class (the fundamental domain `{0 < Re, 0 ≤ Im}`).  This file proves:

* `(maxPieceFinset d).card ≤ d.divisors.card`, i.e. the number of maximal pieces is at most `τ(d)`;
* `d ≤ |w|²` for every `w ∈ maxPieceFinset d` (the index of a maximal piece is at least `d`).

## Mathematics

Write `S = {w : ℤ[i] | w ∣ d ∧ d ∣ |w|²}` ("interpolating" elements, `IsSPt`).  The maximal pieces
are exactly the divisibility-minimal elements of `S` (`IsSPt_of_mem_maxPieceFinset`,
`Smin_of_mem_maxPieceFinset`).  If `w ∈ S` is minimal and `ρ` is a Gaussian prime dividing `w`,
then `d ∤ |w/ρ|²` (**descent**, `SStructure.descent`), since otherwise `w/ρ` would be a strictly
smaller element of `S` dividing `w`.

The descent pins down the exponents of `|w|²` for a minimal `w`:

* `p ≡ 1 (mod 4)`: `v_p(|w|²) = v_p(d)` (`splitPin`);
* `q ≡ 3 (mod 4)`: `v_q(|w|²) = v_q(d) + v_q(d) % 2` (`inertPin`) — the exponent `2 v_q(w)` is even
  and lies in `{v_q(d), v_q(d) + 1}`;
* `p = 2`: `v_2(|w|²) = v_2(d)` (`twoPin`).

Consequently **all** maximal pieces have the same norm `M`.  Since distinct elements of the
fundamental domain are non-associate (`fundUnique`), the elements of `maxPieceFinset d` inject into
the associate classes of Gaussian integers of norm `M`, a set of cardinality
`A M = ∏_{p ≡ 1 (4), p | M} (v_p(M) + 1)·[0 or 1]`.  Comparing exponents
(`A_le_tau_of_split_exp`) gives `A M ≤ τ(d)`, the product over the split primes being the
sub-product of `τ(d)` over all primes.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.maxPieceDefs
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.GaussPieceMax_arith
import Submission.Work.FIArea3.JointCount.SStructure
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.Diophantine.prime_three_mod_four_dvd_sq_add_sq
import Submission.Work.FIArea3.JointCount.splitPin
import Submission.Work.FIArea3.JointCount.inertPin
import Submission.Work.FIArea3.JointCount.twoPin
import Submission.Work.FIArea3.JointCount.A_le_tau_of_split_exp
import Submission.Work.FIArea3.JointCount.fundUnique

namespace Work.FIArea3.JointCount

open Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The norm of an element of `maxPieceFinset d` divides `d * d`: it divides the norm of `d`. -/
lemma gnorm_dvd_mul_self_of_mem_maxPieceFinset (d : ℕ) (_hd : 1 ≤ d) {w : GaussianInt}
    (hw : w ∈ maxPieceFinset d) : gnorm w ∣ d * d := by
  have hwd : w ∣ (d : GaussianInt) := (mem_maxPieceFinset_iff.mp hw).2.1.1.dvd_natCast
  have h2 : gnorm w ∣ gnorm (d : GaussianInt) := gnorm_dvd_of_dvd hwd
  rwa [GaussPieceMax_arith_gnorm_natCast d] at h2

/-- A prime dividing the norm of an element of `maxPieceFinset d` divides `d`. -/
lemma dvd_d_of_dvd_gnorm_of_mem_maxPieceFinset (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt}
    (hw : w ∈ maxPieceFinset d) {p : ℕ} (hp : p.Prime) (h : p ∣ gnorm w) : p ∣ d :=
  (hp.dvd_mul.mp (h.trans (gnorm_dvd_mul_self_of_mem_maxPieceFinset d hd hw))).elim id id

/-- The exponent of any prime in the norm `|w|²` of an element of `maxPieceFinset d` is the
exponent of that prime in `d`, except for primes `≡ 3 (mod 4)` where it may gain one. -/
lemma factorization_eq_of_mem_maxPieceFinset (d : ℕ) (hd : 1 ≤ d) {w₀ w : GaussianInt}
    (hw₀ : w₀ ∈ maxPieceFinset d) (hw : w ∈ maxPieceFinset d) (p : ℕ) :
    (gnorm w).factorization p = (gnorm w₀).factorization p := by
  have hSw := IsSPt_of_mem_maxPieceFinset d hd hw
  have hS₀ := IsSPt_of_mem_maxPieceFinset d hd hw₀
  have hmw := Smin_of_mem_maxPieceFinset d hd hw
  have hm₀ := Smin_of_mem_maxPieceFinset d hd hw₀
  by_cases hp : p.Prime
  · rcases Nat.Prime.eq_two_or_odd hp with hp2 | hodd
    · subst hp2
      rw [twoPin hd hSw hmw, twoPin hd hS₀ hm₀]
    · have hpodd : p % 2 = 1 := hodd
      have hpm : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hpm with hp4 | hp3
      · by_cases hpd : p ∣ d
        · rw [splitPin hd hSw hmw hp hp4 hpd, splitPin hd hS₀ hm₀ hp hp4 hpd]
        · have hnM : ¬ p ∣ gnorm w :=
            fun h => hpd (dvd_d_of_dvd_gnorm_of_mem_maxPieceFinset d hd hw hp h)
          have hnM₀ : ¬ p ∣ gnorm w₀ :=
            fun h => hpd (dvd_d_of_dvd_gnorm_of_mem_maxPieceFinset d hd hw₀ hp h)
          rw [Nat.factorization_eq_zero_of_not_dvd hnM, Nat.factorization_eq_zero_of_not_dvd hnM₀]
      · by_cases hpd : p ∣ d
        · rw [inertPin hd hSw hmw hp hp3 hpd, inertPin hd hS₀ hm₀ hp hp3 hpd]
        · have hnM : ¬ p ∣ gnorm w :=
            fun h => hpd (dvd_d_of_dvd_gnorm_of_mem_maxPieceFinset d hd hw hp h)
          have hnM₀ : ¬ p ∣ gnorm w₀ :=
            fun h => hpd (dvd_d_of_dvd_gnorm_of_mem_maxPieceFinset d hd hw₀ hp h)
          rw [Nat.factorization_eq_zero_of_not_dvd hnM, Nat.factorization_eq_zero_of_not_dvd hnM₀]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp, Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **All maximal pieces have the same norm.** -/
lemma gnorm_eq_of_mem_maxPieceFinset (d : ℕ) (hd : 1 ≤ d) {w₀ w : GaussianInt}
    (hw₀ : w₀ ∈ maxPieceFinset d) (hw : w ∈ maxPieceFinset d) :
    gnorm w = gnorm w₀ := by
  have hw0 : w ≠ 0 := by
    intro h
    have h1 : w ∣ (d : GaussianInt) := (mem_maxPieceFinset_iff.mp hw).2.1.1.dvd_natCast
    rw [h] at h1
    obtain ⟨c, hc⟩ := h1
    rw [zero_mul] at hc
    have : d = 0 := by exact_mod_cast hc
    omega
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    have h1 : w₀ ∣ (d : GaussianInt) := (mem_maxPieceFinset_iff.mp hw₀).2.1.1.dvd_natCast
    rw [h] at h1
    obtain ⟨c, hc⟩ := h1
    rw [zero_mul] at hc
    have : d = 0 := by exact_mod_cast hc
    omega
  have hM : gnorm w ≠ 0 := fun h => hw0 ((gnorm_eq_zero_iff w).mp h)
  have hM₀ : gnorm w₀ ≠ 0 := fun h => hw₀0 ((gnorm_eq_zero_iff w₀).mp h)
  refine Nat.eq_of_factorization_eq' hM hM₀ ?_
  ext p
  exact factorization_eq_of_mem_maxPieceFinset d hd hw₀ hw p

theorem maxPieceFinset_card_le (d : ℕ) (hd : 1 ≤ d) :
    (Work.FIArea3.JointCount.maxPieceFinset d).card ≤ d.divisors.card
    ∧ (∀ w ∈ Work.FIArea3.JointCount.maxPieceFinset d, d ≤ Work.FIPlan.gnorm w) := by
  constructor
  · rcases Finset.eq_empty_or_nonempty (maxPieceFinset d) with hemp | ⟨w₀, hw₀⟩
    · rw [hemp]
      exact Nat.zero_le _
    · obtain ⟨-, hmax₀, hre₀, him₀⟩ := mem_maxPieceFinset_iff.mp hw₀
      set M := gnorm w₀ with hMdef
      have hMpos : 1 ≤ M := by
        have := (GaussPieceMax_arith d hd).1 w₀ hmax₀
        omega
      have hdvd : d ∣ M := (IsSPt_of_mem_maxPieceFinset d hd hw₀).2
      have hMsub : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ d := by
        intro p hp hpM
        rcases hp.dvd_mul.mp
          (hpM.trans (gnorm_dvd_mul_self_of_mem_maxPieceFinset d hd hw₀)) with h | h
        · exact h
        · exact h
      have hsplit : ∀ p : ℕ, p.Prime → p % 4 = 1 → M.factorization p = d.factorization p := by
        intro p hp hp4
        by_cases hpd : p ∣ d
        · exact splitPin hd (IsSPt_of_mem_maxPieceFinset d hd hw₀)
            (Smin_of_mem_maxPieceFinset d hd hw₀) hp hp4 hpd
        · have hnM : ¬ p ∣ M := fun h => hpd (hMsub p hp h)
          rw [Nat.factorization_eq_zero_of_not_dvd hnM, Nat.factorization_eq_zero_of_not_dvd hpd]
      have hinj : Set.InjOn (fun w : GaussianInt => Associates.mk w) ↑(maxPieceFinset d) := by
        intro a ha b hb hab
        rw [Finset.mem_coe] at ha hb
        obtain ⟨-, -, hrea, hima⟩ := mem_maxPieceFinset_iff.mp ha
        obtain ⟨-, -, hreb, himb⟩ := mem_maxPieceFinset_iff.mp hb
        exact fundUnique hrea hima hreb himb (Associates.mk_eq_mk_iff_associated.mp hab)
      have hsub : (Associates.mk '' ↑(maxPieceFinset d) : Set (Associates GaussianInt))
          ⊆ (Associates.mk '' {z : GaussianInt | gnorm z = M}) := by
        rintro κ ⟨w, hw, rfl⟩
        refine ⟨w, ?_, rfl⟩
        rw [Set.mem_ofPred_eq]
        exact gnorm_eq_of_mem_maxPieceFinset d hd hw₀ (Finset.mem_coe.mp hw)
      have hfin : (Associates.mk '' {z : GaussianInt | gnorm z = M}).Finite := by
        have hset : ({z : GaussianInt | gnorm z = M} : Set GaussianInt)
            = ↑(Commons.NumberTheory.GaussianInt.elemF M) := by
          ext z
          rw [Finset.mem_coe, Set.mem_ofPred_eq, Commons.NumberTheory.GaussianInt.mem_elemF hMpos,
            gnorm]
        rw [hset]
        exact (Finset.finite_toSet _).image _
      calc (maxPieceFinset d).card
          = (↑(maxPieceFinset d) : Set GaussianInt).ncard := (Set.ncard_coe_finset _).symm
        _ = (Associates.mk '' ↑(maxPieceFinset d)).ncard := (hinj.ncard_image).symm
        _ ≤ (Associates.mk '' {z : GaussianInt | gnorm z = M}).ncard :=
            Set.ncard_le_ncard hsub hfin
        _ = Commons.NumberTheory.GaussianInt.A M := by
            rw [Commons.NumberTheory.GaussianInt.A_eq_ncard_image M hMpos]
            rfl
        _ ≤ d.divisors.card := A_le_tau_of_split_exp hd hdvd hMsub hsplit
  · intro w hw
    exact (GaussPieceMax_arith d hd).1 w (mem_maxPieceFinset_iff.mp hw).2.1

end

end Work.FIArea3.JointCount
