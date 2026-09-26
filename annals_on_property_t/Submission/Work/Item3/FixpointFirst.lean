import Submission.Work.Item3.BoundedSegments
import Submission.Work.Item3.OldWitness
import Submission.Work.Item3.ClassStability
import Submission.Work.SystemReducedImage
import Submission.Work.ImageAggregate

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# Item 3, FixpointFirst: first subclaim of the no-reappearance — the balanced coordinate

Machine validation (`FallTwoRunNotes.md`; harness `/tmp/fg2`, 400 residual
examples, n = 3): after the fixpoint pass at the balanced coordinate `c`
(no strict move firing), `c` is **never** among the exactly-half-absorbed
candidates of the new automorphism.  This module proves the first subclaim of
that no-reappearance statement — the *plus-orientation* case of `i = p`:

    NoPassActive α' c A B  :=  no coordinate u != c ends with B or begins
        with B^(-1) (invRev B)   -- exactly the fixpoint predicate of the run

    fixpoint_no_plus_balanced_c : an interior aggregate factor
        es[j] = +α'(a_c) (word A ++ B, |A| = |B|, A nonempty) whose right
        neighbour covers invRev B (word = invRev B ++ Z) leads to `False`
        under NoPassActive

Proof spine: the right neighbour factor `es[j+1]` is `± α'(a_u)` for some
coordinate `u` (`ImageAggregate`); a `u != c` is excluded because the plus
case puts `u` in the begins-with-`B⁻¹` class and the minus case (via
`OldWitness.factor_inv_word_ends`) in the ends-with-`B` class — both killed
by `NoPassActive`; `u = c` is excluded because the plus case would force
`A = invRev B` (`ClassStability.A_ne_invRev_of_reduced_append`, the word of
`es[j]` is reduced), and the minus case creates an adjacent inverse factor
pair (`SystemReduced`).

Both orientations of `i = p` are now proven: the **minus-orientation**
`fixpoint_no_minus_balanced_c` (the occurrence `es[j] = (α'(a_c))⁻¹`) dies by
the *left-covering mirror* — its right covering classes are NOT the run's
fixpoint classes (the partial-symmetry obstacle documented earlier), but the
left neighbour covering `B_p` must lie in the run's classes, be `+w_c`
adjacent to `w_c⁻¹` (`SystemReduced`), or be `w_c⁻¹` itself whose word would
need to end with both `B_p` and `invRev A_p` (`ClassStability`).  What
remains open (recorded in `FallTwoRunNotes.md`): the `i < p` cases, which
consume the `CoverBound`/`BoundedSegments` machinery.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/



namespace Submission.Nielsen

/-- The **fixpoint predicate** at the balanced coordinate `c` (halves `A B`):
no coordinate other than `c` ends with `B` or begins with `B⁻¹` (`invRev B`).
This is exactly "no element of the pass classes remains", i.e. the state
reached by the fixpoint pass of the classical run. -/
def NoPassActive {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B : List (Fin n × Bool)) : Prop :=
  ∀ u : Fin n, u ≠ c →
    (¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of u)).toWord = Y ++ B) ∧
    (¬ ∃ Y : List (Fin n × Bool), (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Y)

/-- **The balanced coordinate is not half-absorbed at the fixpoint (first
subclaim, plus orientation).**  Suppose the aggregate of `a_m` in the post-fixpoint
automorphism `α'` has an interior occurrence of `+α'(a_c)` at factor `j` whose
word is `A ++ B` (`|A| = |B|`, `A` nonempty) and whose right neighbour covers
`invRev B` (`word = invRev B ++ Z`).  At the fixpoint no coordinate `u ≠ c`
ends with `B` or begins with `B⁻¹`, so the right neighbour factor `es[j+1]`
(± a basis image by `ImageAggregate`) would have to be `±α'(a_c)` itself:
the plus case would force `A = invRev B` (impossible for reduced nonempty
halves, `ClassStability`), the minus case an adjacent inverse factor pair
(impossible by `SystemReduced`).  Hence no such covering exists — the
right-covering half of a half-absorption of the balanced element is killed by
the fixpoint. -/
theorem fixpoint_no_plus_balanced_c {n : ℕ} (α' : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (A B Z : List (Fin n × Bool)) (m : Fin n) {j : ℕ}
    (hj : j < (imageAggregate α' m).length) (hjk : j + 1 < (imageAggregate α' m).length)
    (hEs : (imageAggregate α' m)[j] = α' (FreeGroup.of c))
    (hmid : ((imageAggregate α' m)[j]).toWord = A ++ B) (hAB : A.length = B.length)
    (hA : A ≠ [])
    (hright : ((imageAggregate α' m)[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (hfix : NoPassActive α' c A B) : False := by
  let es : List (FreeGroup (Fin n)) := imageAggregate α' m
  have hred : SystemReduced es := by simpa [es] using (SystemReduced_imageAggregate α' m)
  have himg : ImageAggregate α' es := by simpa [es] using (imageAggregate_isImageAggregate α' m)
  have himgN := himg (es[j + 1]) (by
    simpa [es] using (List.getElem_mem hjk))
  -- hEs/hmid/hright re-expressed with es
  have hEs' : es[j] = α' (FreeGroup.of c) := by simpa [es] using hEs
  have hmid' : (es[j]).toWord = A ++ B := by simpa [es] using hmid
  have hright' : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by simpa [es] using hright
  rcases himgN with ⟨u, hu1 | hu2⟩
  · -- es[j+1] = α'(a_u): its word is invRev B ++ Z, so w_u begins with invRev B
    by_cases huc : u = c
    · -- u = c: es[j+1] = α'(a_c) = es[j], so A ++ B = word(es[j]) = word(es[j+1]) = invRev B ++ Z
      subst u
      have hEsN : es[j + 1] = α' (FreeGroup.of c) := by simpa using hu1
      have hw : (α' (FreeGroup.of c)).toWord = FreeGroup.invRev B ++ Z := by
        rw [← hEsN]
        exact hright'
      have hw2 : A ++ B = FreeGroup.invRev B ++ Z := by
        rw [← hmid']
        rw [hEs']
        exact hw
      -- A = invRev B by taking the first |A| letters
      have htake := congrArg (fun w : List (Fin n × Bool) => w.take A.length) hw2
      have ht1 : (A ++ B).take A.length = A := by simp
      have ht2 : (FreeGroup.invRev B ++ Z).take A.length = FreeGroup.invRev B := by
        have hb : A.length = (FreeGroup.invRev B).length := by
          rw [FreeGroup.invRev_length, hAB]
        rw [hb]
        simp
      rw [ht1, ht2] at htake
      have hredAB : FreeGroup.IsReduced (A ++ B) := by
        have hwr : FreeGroup.IsReduced ((es[j]).toWord) :=
          FreeGroup.isReduced_toWord (x := es[j])
        rw [hmid'] at hwr
        exact hwr
      exact (A_ne_invRev_of_reduced_append A B hA hredAB) htake
    · -- u ≠ c: w_u begins with invRev B, contradicting the fixpoint
      have hbeg : ∃ Y : List (Fin n × Bool), (α' (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Y := by
        rw [← hu1]
        exact ⟨Z, hright'⟩
      exact (hfix u huc).2 hbeg
  · -- es[j+1] = (α'(a_u))⁻¹: its word invRev B ++ Z makes w_u end with B
    have hend : ∃ Y : List (Fin n × Bool), (α' (FreeGroup.of u)).toWord = Y ++ B := by
      exact factor_inv_word_ends α' es (j := j + 1) (u := u)
        (by simpa [es] using hjk) B Z (by simpa [es] using hright') hu2
    by_cases huc : u = c
    · -- u = c: es[j] = +α'(a_c), es[j+1] = (α'(a_c))⁻¹: adjacent inverse factors
      exact (adjacent_inverse_coordinate_ne α' es hred hj (by simpa [es] using hjk) hEs' hu2) huc
    · exact (hfix u huc).1 hend

/-! ### The minus orientation (i = p), via the left-covering mirror -/

/-- `L[(j - 1) + 1] = L[j]` for `0 < j` (getElem values at provably-equal
indices). -/
lemma getElem_index_shift {α : Type*} (L : List α) {j : ℕ} (h0 : 0 < j)
    (hj : j < L.length) : L[(j - 1) + 1] = L[j] := by
  apply congrArg L.get
  apply Fin.ext
  change (j - 1) + 1 = j
  omega

/-- **Minus orientation (i = p), left-covering mirror.**  The aggregate of
`a_m` in the post-fixpoint automorphism has an interior occurrence
`es[j] = (α'(a_c))⁻¹` (so `c`'s own word is `A_p ++ B_p`, the factor word
`invRev B_p ++ invRev A_p`) whose left neighbour covers `B_p`
(`es[j-1].toWord = X ++ B_p`).  At the fixpoint (no `u != c` ends with `B_p`
or begins with `B_p⁻¹`), the left neighbour factor `es[j-1] = ±α'(a_v)` with
`v != c` is excluded (plus: `w_v` ends with `B_p`; minus: `w_v` begins with
`B_p⁻¹`); `v = c` is excluded because the plus case makes `es[j-1] = α'(a_c)`
adjacent to `es[j] = (α'(a_c))⁻¹` (`SystemReduced`), and the minus case
`es[j-1] = (α'(a_c))⁻¹ = es[j]` forces `B_p = invRev A_p` by suffix comparison
of its word (`hmid`, `ClassStability`).  Hence no such covering exists. -/
theorem fixpoint_no_minus_balanced_c {n : ℕ} (α' : MulAut (FreeGroup (Fin n))) (c : Fin n)
    (Aₚ Bₚ X : List (Fin n × Bool)) (m : Fin n) {j : ℕ}
    (hj0 : 0 < j) (hj : j < (imageAggregate α' m).length)
    (hm : j - 1 < (imageAggregate α' m).length)
    (hEs : (imageAggregate α' m)[j] = (α' (FreeGroup.of c))⁻¹)
    (hmid : ((imageAggregate α' m)[j]).toWord = FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ)
    (hAB : Aₚ.length = Bₚ.length) (hA : Aₚ ≠ [])
    (hleft : ((imageAggregate α' m)[j - 1]).toWord = X ++ Bₚ)
    (hfix : NoPassActive α' c Aₚ Bₚ) : False := by
  let es : List (FreeGroup (Fin n)) := imageAggregate α' m
  have hred : SystemReduced es := by simpa [es] using (SystemReduced_imageAggregate α' m)
  have himg : ImageAggregate α' es := by simpa [es] using (imageAggregate_isImageAggregate α' m)
  have himgL := himg (es[j - 1]) (by simpa [es] using (List.getElem_mem hm))
  have hEs' : es[j] = (α' (FreeGroup.of c))⁻¹ := by simpa [es] using hEs
  have hmid' : (es[j]).toWord = FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ := by
    simpa [es] using hmid
  have hleft' : (es[j - 1]).toWord = X ++ Bₚ := by simpa [es] using hleft
  rcases himgL with ⟨v, hv1 | hv2⟩
  · -- es[j-1] = +α'(a_v): w_v's word ends with B_p
    have hend : ∃ Y : List (Fin n × Bool), (α' (FreeGroup.of v)).toWord = Y ++ Bₚ := by
      rw [← hv1]
      exact ⟨X, hleft'⟩
    by_cases hvc : v = c
    · -- v = c: es[j-1] = +α'(a_c), es[j] = (α'(a_c))⁻¹: adjacent inverse pair
      subst v
      have hip : (j - 1) + 1 < es.length := by
        have hsub : (j - 1) + 1 = j := by omega
        rw [hsub]
        exact (by simpa [es] using hj)
      have hne : es[(j - 1) + 1] ≠ (es[j - 1])⁻¹ := hred.2 (j - 1) hip
      exact hne (by
        rw [getElem_index_shift es (j := j) hj0 (by simpa [es] using hj)]
        rw [hEs']
        rw [hv1])
    · exact (hfix v hvc).1 hend
  · -- es[j-1] = (α'(a_v))⁻¹: its word ends with B_p ⟹ w_v begins with invRev B_p
    have hbeg : ∃ Y : List (Fin n × Bool),
        (α' (FreeGroup.of v)).toWord = FreeGroup.invRev Bₚ ++ Y := by
      have hw : (α' (FreeGroup.of v)) = (es[j - 1])⁻¹ := by
        rw [hv2]
        simp
      refine ⟨FreeGroup.invRev X, ?_⟩
      calc
        (α' (FreeGroup.of v)).toWord = ((es[j - 1])⁻¹).toWord := by rw [hw]
        _ = FreeGroup.invRev (es[j - 1].toWord) := by rw [FreeGroup.toWord_inv]
        _ = FreeGroup.invRev (X ++ Bₚ) := by rw [hleft']
        _ = FreeGroup.invRev Bₚ ++ FreeGroup.invRev X := by rw [FreeGroup.invRev_append]
    by_cases hvc : v = c
    · -- v = c: es[j-1] = (α'(a_c))⁻¹ = es[j]; word = hmid = invRev B_p ++ invRev A_p,
      -- but hleft says it ends with B_p: B_p = invRev A_p -- impossible.
      subst v
      have hwordEq : X ++ Bₚ = FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ := by
        calc
          X ++ Bₚ = (es[j - 1]).toWord := hleft'.symm
          _ = (es[j]).toWord := by
                have hE : es[j - 1] = es[j] := by rw [hv2, hEs']
                rw [hE]
          _ = FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ := hmid'
      have hsuf := congrArg (fun w : List (Fin n × Bool) => w.drop (w.length - Bₚ.length)) hwordEq
      have hd1 : (X ++ Bₚ).drop ((X ++ Bₚ).length - Bₚ.length) = Bₚ := by
        have hx : (X ++ Bₚ).length - Bₚ.length = X.length := by
          rw [List.length_append]
          omega
        rw [hx]
        simp
      have hd2 : (FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ).drop
          ((FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ).length - Bₚ.length) =
          FreeGroup.invRev Aₚ := by
        have hlen : (FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ).length - Bₚ.length =
            Aₚ.length := by
          rw [List.length_append, FreeGroup.invRev_length, FreeGroup.invRev_length]
          omega
        rw [hlen]
        have hb : (FreeGroup.invRev Bₚ).length = Aₚ.length := by
          rw [FreeGroup.invRev_length, hAB]
        have hdrop : (FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ).drop
            (FreeGroup.invRev Bₚ).length = FreeGroup.invRev Aₚ := by
          rw [List.drop_append_of_le_length le_rfl]
          simp
        rw [← hb]
        exact hdrop
      rw [hd1, hd2] at hsuf
      have hB : Bₚ = FreeGroup.invRev Aₚ := hsuf
      apply_fun FreeGroup.invRev at hB
      have hB' : FreeGroup.invRev Bₚ = Aₚ := by simpa [FreeGroup.invRev_invRev] using hB
      have hredAB : FreeGroup.IsReduced (Aₚ ++ Bₚ) := by
        have hwcr : FreeGroup.IsReduced ((α' (FreeGroup.of c)).toWord) :=
          FreeGroup.isReduced_toWord (x := α' (FreeGroup.of c))
        have hwc : (α' (FreeGroup.of c)).toWord = Aₚ ++ Bₚ := by
          have hwi : ((α' (FreeGroup.of c))⁻¹).toWord =
              FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ := by
            simpa [hEs'] using hmid'
          have hto : FreeGroup.invRev ((α' (FreeGroup.of c)).toWord) =
              FreeGroup.invRev (Aₚ ++ Bₚ) := by
            calc
              FreeGroup.invRev ((α' (FreeGroup.of c)).toWord)
                  = ((α' (FreeGroup.of c))⁻¹).toWord := by rw [FreeGroup.toWord_inv]
              _ = FreeGroup.invRev Bₚ ++ FreeGroup.invRev Aₚ := hwi
              _ = FreeGroup.invRev (Aₚ ++ Bₚ) := by rw [FreeGroup.invRev_append]
          have h2 := congrArg FreeGroup.invRev hto
          simpa [FreeGroup.invRev_invRev] using h2
        rw [hwc] at hwcr
        exact hwcr
      exact (A_ne_invRev_of_reduced_append Aₚ Bₚ hA hredAB) hB'.symm
    · exact (hfix v hvc).2 hbeg

end Submission.Nielsen
