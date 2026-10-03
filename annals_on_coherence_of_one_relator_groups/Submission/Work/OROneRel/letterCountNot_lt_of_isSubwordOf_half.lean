import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.letterCountHalfAux
import Submission.Work.OROneRel.isReduced_replicate_of_fst_eq
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced
import Submission.Work.OROneRel.expSum_mk_eq_ofAdd_ssum
import Submission.Work.OROneRel.abs_ssum_le_tcount
import Submission.Work.OROneRel.exists_rotate_subword_decomposition

/-!
# Short subwords of a power of a relator involve essentially all letters only once

Let `r` be a cyclically reduced relator which is not a proper power, `t` a generator occurring in `r`
with exponent sum zero, and `v ≠ 1` a subword of a power of `r` with `2 * |v| ≤ |r|`.  Then the
number of letters of `v` other than `t` is strictly smaller than the number of letters of `r` other
than `t`:

`letterCountNot t v < letterCountNot t r`.

The point is that `v` is an arc of the cyclic word of `r` of length at most half the circumference,
so it misses at least as much as it contains; if the complementary arc consisted only of the letter
`t`, then (as `toWord r` is reduced) that arc would be a constant word `t ^ L` or `t ^ (-L)`, whence
`|σ_t v| = L = |r| - |v| ≥ |v|`, while trivially `|σ_t v| ≤` the number of `t`-letters of `v ≤ |v|`;
so all of `v` and the whole of `r` would consist of the letter `t`, contradicting `σ_t r = 0 ≠ 0`
for a nontrivial relator.

## Main declarations

* `Work.OROneRel.exists_replicate_of_isReduced_of_forall_fst_eq`;
* `Work.OROneRel.letterCountNot_lt_of_isSubwordOf_half`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- A reduced word all of whose letters have generator `t` is a constant word. -/
theorem exists_replicate_of_isReduced_of_forall_fst_eq (t : α) {L : List (α × Bool)}
    (hr : FreeGroup.IsReduced L) (h : ∀ p ∈ L, p.1 = t) :
    ∃ b : Bool, L = List.replicate L.length (t, b) := by
  cases L with
  | nil => exact ⟨true, rfl⟩
  | cons p L =>
    obtain ⟨c, hc⟩ := isReduced_replicate_of_fst_eq hr h
    have hpc : p = c := List.eq_replicate_length.mp hc p (by simp)
    have hc' : c = (t, c.2) := Prod.ext (by rw [← hpc]; exact h p (by simp)) rfl
    refine ⟨c.2, List.eq_replicate_length.mpr ?_⟩
    intro x hx
    exact (List.eq_replicate_length.mp hc x hx).trans hc'

/-- A reduced word all of whose letters have generator `t` has `|σ_t|` equal to its length. -/
theorem abs_ssum_eq_length_of_isReduced_of_forall_fst_eq (t : α) {L : List (α × Bool)}
    (hr : FreeGroup.IsReduced L) (h : ∀ p ∈ L, p.1 = t) :
    |ssum t L| = (L.length : ℤ) := by
  obtain ⟨b, hb⟩ := exists_replicate_of_isReduced_of_forall_fst_eq t hr h
  conv_lhs => rw [hb]
  rw [ssum_replicate]
  cases b <;> simp

theorem letterCountNot_lt_of_isSubwordOf_half {α : Type u} (r v : FreeGroup α) (t : α) (k : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r) (hpp : ¬ Work.OROneRel.IsProperPower r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hsigma : Work.OROneRel.expSum t r = 1)
    (hsub : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hhalf : 2 * Work.OROneRel.relatorNorm v ≤ Work.OROneRel.relatorNorm r) (hv1 : v ≠ 1) :
    Work.OROneRel.letterCountNot t v < Work.OROneRel.letterCountNot t r := by
  classical
  set W : List (α × Bool) := FreeGroup.toWord r with hW
  set V : List (α × Bool) := FreeGroup.toWord v with hV
  have hWr : FreeGroup.toWord r = W := hW.symm
  have hVv : FreeGroup.toWord v = V := hV.symm
  have hrcyc : FreeGroup.IsCyclicallyReduced W := hcyc
  have hredW : FreeGroup.IsReduced W := hrcyc.1
  have hredV : FreeGroup.IsReduced V := by rw [hV]; exact FreeGroup.isReduced_toWord
  have hnormr : relatorNorm r = W.length := by
    simp only [relatorNorm, FreeGroup.norm, ← hW]
  have hnormv : relatorNorm v = V.length := by
    simp only [relatorNorm, FreeGroup.norm, ← hV]
  -- `v ≠ 1` gives `0 < V.length`
  have hVne : V ≠ [] := by
    intro h
    rw [hV] at h
    exact hv1 (FreeGroup.toWord_eq_nil_iff.mp h)
  have hV1 : 0 < V.length := List.length_pos_iff.mpr hVne
  -- `t ∈ relatorLetters r` gives `0 < W.length`
  have hW1 : 0 < W.length := by
    have ht' : ∃ b : Bool, (t, b) ∈ FreeGroup.toWord r := by
      simpa only [relatorLetters, Set.mem_ofPred_eq] using ht
    obtain ⟨b, hb⟩ := ht'
    rw [hWr] at hb
    exact List.length_pos_iff.mpr (fun h => by simp [h] at hb)
  have h2VW : 2 * V.length ≤ W.length := by
    have h := hhalf
    simp only [hnormr, hnormv] at h
    exact h
  have hVW : V.length ≤ W.length := by omega
  have hlen : relatorNorm v < relatorNorm r := by
    rw [hnormv, hnormr]; omega
  -- the arc decomposition of `v` in the cyclic word of `r`
  obtain ⟨j, S, hVS, hSlen, hSred⟩ :=
    exists_rotate_subword_decomposition hcyc hsub hlen
  rw [hVv, hWr] at hVS
  rw [hnormr, hnormv] at hSlen
  have hWsum : W.length = V.length + S.length := by omega
  -- `r` and `v` as words
  have hr_eq : r = FreeGroup.mk W := by
    rw [hW]; exact (FreeGroup.mk_toWord (x := r)).symm
  have hv_eq : v = FreeGroup.mk V := by
    rw [hV]; exact (FreeGroup.mk_toWord (x := v)).symm
  -- letter counts
  have hcntV : letterCountNot t v = V.length - tcount t V := by
    rw [hv_eq, letterCountNot_mk_of_isReduced t hredV]
  have hcntR : letterCountNot t r = W.length - tcount t W := by
    rw [hr_eq, letterCountNot_mk_of_isReduced t hredW]
  have hcountW : tcount t W = tcount t V + tcount t S := by
    have h : tcount t (V ++ S) = tcount t (W.rotate j) := by rw [hVS]
    rw [tcount_append, tcount_rotate] at h
    exact h.symm
  -- the relator is nontrivial as a `t`-word
  have hposr : 0 < letterCountNot t r := by
    by_contra hcon
    have hr0 : letterCountNot t r = 0 := Nat.eq_zero_of_not_pos hcon
    have htau : tcount t W = W.length := by
      have h := hcntR
      have hle := tcount_le_length t W
      omega
    have hallW : ∀ p ∈ W, p.1 = t := (tcount_eq_length_iff t W).mp htau
    have habs : |ssum t W| = (W.length : ℤ) :=
      abs_ssum_eq_length_of_isReduced_of_forall_fst_eq t hredW hallW
    have hexp : Multiplicative.ofAdd (ssum t W) = 1 := by
      rw [← expSum_mk_eq_ofAdd_ssum t W, ← hr_eq]
      exact hsigma
    have hsum0 : ssum t W = 0 := by
      have h1 : Multiplicative.ofAdd (ssum t W) = Multiplicative.ofAdd (0 : ℤ) := by
        simpa using hexp
      exact Multiplicative.ofAdd.injective h1
    rw [hsum0] at habs
    simp only [abs_zero] at habs
    have hW1' : (0 : ℤ) < (W.length : ℤ) := by exact_mod_cast hW1
    omega
  -- the complementary arc contains a letter different from `t`
  have hSlt : tcount t S < S.length := by
    by_contra hcon
    have hSeq : tcount t S = S.length :=
      le_antisymm (tcount_le_length t S) (not_lt.mp hcon)
    have hallS : ∀ p ∈ S, p.1 = t := (tcount_eq_length_iff t S).mp hSeq
    have habsS : |ssum t S| = (S.length : ℤ) :=
      abs_ssum_eq_length_of_isReduced_of_forall_fst_eq t hSred hallS
    have hexp : Multiplicative.ofAdd (ssum t (V ++ S)) = 1 := by
      rw [hVS, ssum_rotate, ← expSum_mk_eq_ofAdd_ssum t W, ← hr_eq]
      exact hsigma
    have hsum0 : ssum t (V ++ S) = 0 := by
      have h1 : Multiplicative.ofAdd (ssum t (V ++ S)) = Multiplicative.ofAdd (0 : ℤ) := by
        simpa using hexp
      exact Multiplicative.ofAdd.injective h1
    rw [ssum_append] at hsum0
    have hVSsum : ssum t V = -ssum t S := by omega
    have habs : |ssum t V| = (S.length : ℤ) := by
      rw [hVSsum, abs_neg, habsS]
    have hbound : (S.length : ℤ) ≤ ((tcount t V : ℕ) : ℤ) := by
      have h := abs_ssum_le_tcount t V
      rwa [habs] at h
    have hSle : S.length ≤ tcount t V := by exact_mod_cast hbound
    have hVlenS : V.length ≤ S.length := by omega
    have hVeq : tcount t V = V.length :=
      le_antisymm (tcount_le_length t V) (le_trans hVlenS hSle)
    have htau : tcount t W = W.length := by
      rw [hcountW, hVeq, hSeq, hWsum]
    have hr0 : letterCountNot t r = 0 := by
      rw [hcntR, htau]
      simp
    omega
  rw [hcntV, hcntR]
  have hVt : tcount t V ≤ V.length := tcount_le_length t V
  omega

end Work.OROneRel
