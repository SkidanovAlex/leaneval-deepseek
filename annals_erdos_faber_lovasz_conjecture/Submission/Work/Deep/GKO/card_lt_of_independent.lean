import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.subsetDefs

/-!
# Independent sets in a lower-regular vertex set are small

If `G` is lower `(p,ε)`-regular on `U` with `ε < p` and `1 ≤ ε|U|`, then any independent
set `S ⊆ U` (no two vertices of `S` are adjacent) satisfies `|S| < 2ε|U| + 1`.

The argument is the standard one: if `|S| ≥ 2ε|U| + 1`, split `S` into a part `A` of
size `⌈ε|U|⌉` and its complement `B = S \ A`.  Both parts have size at least `ε|U|`
(the bound for `B` uses `⌈ε|U|⌉ < ε|U| + 1`), so lower `(p,ε)`-regularity forces
`(p - ε)|A||B| ≤ e(A,B)`, which is positive since `p > ε` and both parts are nonempty.
Hence `e(A,B) > 0`, i.e. there is an edge of `G` between `A` and `B` — an edge inside
the independent set `S`.  Contradiction.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO

open scoped BigOperators

/-- An independent subset of `U` has size less than `2ε|U| + 1`: given two disjoint parts of size at least `ε|U|` the lower-regularity hypothesis forces an edge between them. -/
lemma card_lt_of_independent {n : ℕ} {G : SimpleGraph (Fin n)} {U : Finset (Fin n)} {p ε : ℝ}
    (hlr : LowerRegOn G U p ε) (hεp : ε < p) (hε1 : 1 ≤ ε * (U.card : ℝ))
    {S : Finset (Fin n)} (hSU : S ⊆ U) (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y) :
    (S.card : ℝ) < 2 * (ε * (U.card : ℝ)) + 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hεNpos : 0 < ε * (U.card : ℝ) := lt_of_lt_of_le zero_lt_one hε1
  -- `m := ⌈ε|U|⌉` satisfies `ε|U| ≤ m < ε|U| + 1`.
  obtain ⟨m, hmge, hmlt⟩ :
      ∃ m : ℕ, ε * (U.card : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) < ε * (U.card : ℝ) + 1 :=
    ⟨Nat.ceil (ε * (U.card : ℝ)), Nat.le_ceil _, Nat.ceil_lt_add_one (le_of_lt hεNpos)⟩
  have hmle : m ≤ S.card := by
    have h' : (m : ℝ) < (S.card : ℝ) := by linarith
    have h'' : m < S.card := by exact_mod_cast h'
    omega
  -- Split `S` into `A` of size `m` and `B = S \ A`.
  obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq (s := S) (n := m) hmle
  have hBcard : (S \ A).card = S.card - m := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hAcard]
  have hBcast : ((S \ A).card : ℝ) = (S.card : ℝ) - (m : ℝ) := by
    rw [hBcard]
    exact Nat.cast_sub hmle
  have hBgt : ε * (U.card : ℝ) < ((S \ A).card : ℝ) := by linarith
  have hAUB : A ⊆ U := hAS.trans hSU
  have hBUB : (S \ A) ⊆ U := Finset.sdiff_subset.trans hSU
  have hdisj : Disjoint A (S \ A) := Finset.disjoint_sdiff
  have hAcardreal : ε * (U.card : ℝ) ≤ (A.card : ℝ) := by
    rw [hAcard]; exact hmge
  have hBcardreal : ε * (U.card : ℝ) ≤ ((S \ A).card : ℝ) := le_of_lt hBgt
  -- No edge of `G` crosses from `A` to `S \ A`, since both lie in the independent set `S`.
  have hcross : crossEdges G A (S \ A) = 0 := by
    rw [crossEdges, Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨q, hq⟩
    simp only [Finset.mem_filter] at hq
    obtain ⟨hqAB, hqp⟩ := hq
    obtain ⟨hqA, hqB⟩ := Finset.mem_product.mp hqAB
    exact hind q.1 (hAS hqA) q.2 ((Finset.mem_sdiff.mp hqB).1) hqp
  -- Lower regularity now yields a contradiction: a positive number `≤ 0`.
  have key := hlr A (S \ A) hAUB hBUB hdisj hAcardreal hBcardreal
  rw [hcross, Nat.cast_zero] at key
  have hm1 : 0 < m := by
    by_contra h
    push Not at h
    have h' : (m : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  have hApos : 0 < (A.card : ℝ) := by rw [hAcard]; exact_mod_cast hm1
  have hBpos : 0 < ((S \ A).card : ℝ) := by linarith
  have hprod : 0 < (p - ε) * (A.card : ℝ) * ((S \ A).card : ℝ) :=
    mul_pos (mul_pos (by linarith) hApos) hBpos
  exact absurd key (not_le.mpr hprod)

end Work.Deep.GKO
