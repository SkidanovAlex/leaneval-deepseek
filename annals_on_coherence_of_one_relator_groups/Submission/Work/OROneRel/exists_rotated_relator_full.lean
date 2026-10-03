import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.sigma_mk

set_option linter.style.haveILetI false

/-!
# Rotating a cyclically reduced relator so that a prescribed letter comes first

Given a cyclically reduced relator `r` (its reduced word `toWord r` is cyclically reduced) and a
generator `x` occurring in `r`, we produce a conjugate `r' = c * r * c⁻¹` (equivalently
`r = c * r' * c⁻¹`) whose reduced word begins with the letter `x` (with either sign), and which has
exactly the same combinatorial invariants as `r`: it is cyclically reduced, has the same length
(`relatorNorm`), the same set of letters (`relatorLetters`), and the same exponent sums `sigma t` for
every `t`.

The construction is the obvious one: write the reduced word `W = toWord r` of `r` as
`W = A ++ (x, b) :: V`, i.e. split it just before an occurrence of the letter `x`.  Then the cyclic
rotation `W.rotate A.length = ((x, b) :: V) ++ A` is again cyclically reduced (cyclic rotations of a
cyclically reduced word are cyclically reduced, `isCyclicallyReduced_rotate`), has the same length
and the same letters, and `mk (W.rotate A.length)` is conjugate to `mk W = r` by `mk A`.

The supporting list lemmas (`isReduced_append_self_iff`, `isReduced_append_append_self`,
`isCyclicallyReduced_rotate`) are the combinatorial content: a word is cyclically reduced exactly
when its doubling is reduced, and the doubling of a cyclic rotation sits inside the fourfold
repetition.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

open List

/-- A word is cyclically reduced exactly when its doubling `L ++ L` is reduced: the doubling is
reduced iff `L` is reduced and the last and first letters of `L` do not cancel. -/
lemma isReduced_append_self_iff (L : List (α × Bool)) :
    FreeGroup.IsReduced (L ++ L) ↔ FreeGroup.IsCyclicallyReduced L := by
  unfold FreeGroup.IsReduced FreeGroup.IsCyclicallyReduced
  rw [List.isChain_append]
  constructor
  · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, h1, h3⟩

/-- If `L ++ L` is reduced then so is `(L ++ L) ++ (L ++ L)`: the only new junction is between the
last and first letters of `L ++ L`, i.e. between the last and first letters of `L`, which is already
controlled by the reducedness of `L ++ L`. -/
lemma isReduced_append_append_self {L : List (α × Bool)} (h : FreeGroup.IsReduced (L ++ L)) :
    FreeGroup.IsReduced ((L ++ L) ++ (L ++ L)) := by
  unfold FreeGroup.IsReduced at h ⊢
  rw [List.isChain_append]
  refine ⟨h, h, ?_⟩
  intro y hy z hz
  rw [List.isChain_append] at h
  obtain ⟨_, _, h3⟩ := h
  have hLne : L ≠ [] := by rintro rfl; simp at hy
  rw [List.getLast?_append_of_ne_nil L hLne] at hy
  rw [List.head?_append_of_ne_nil L hLne] at hz
  exact h3 y hy z hz

/-- Cyclic rotations of a cyclically reduced word are cyclically reduced. -/
lemma isCyclicallyReduced_rotate {L : List (α × Bool)} {n : ℕ}
    (h : FreeGroup.IsCyclicallyReduced L) : FreeGroup.IsCyclicallyReduced (L.rotate n) := by
  rcases L with _ | ⟨a, L⟩
  · simp
  · rw [← isReduced_append_self_iff]
    have h2 : FreeGroup.IsReduced ((a :: L) ++ (a :: L)) := (isReduced_append_self_iff _).mpr h
    have h4 : FreeGroup.IsReduced (((a :: L) ++ (a :: L)) ++ ((a :: L) ++ (a :: L))) :=
      isReduced_append_append_self h2
    set k := n % (a :: L).length with hk
    have hklt : k < (a :: L).length := Nat.mod_lt _ (by simp)
    have hrot : (a :: L).rotate n = (a :: L).drop k ++ (a :: L).take k := by
      rw [← List.rotate_mod (a :: L) n, List.rotate_eq_drop_append_take hklt.le]
    rw [hrot]
    unfold FreeGroup.IsReduced at h4 ⊢
    set A := (a :: L).take k with hA
    set B := (a :: L).drop k with hB
    refine h4.infix ⟨A, B ++ A ++ B, ?_⟩
    have hLAB : (a :: L) = A ++ B := by
      rw [hA, hB]; exact (List.take_append_drop k (a :: L)).symm
    rw [hLAB]
    simp only [List.append_assoc]

/-- The exponent sum `sigmaList` is insensitive to the order in which the two blocks are
concatenated (it is an additive function of the multiset of letters). -/
lemma sigmaList_append_comm (t : α) (A V : List (α × Bool)) :
    sigmaList t (V ++ A) = sigmaList t (A ++ V) := by
  simp [sigmaList, List.map_append, List.sum_append, add_comm]

theorem exists_rotated_relator_full {α : Type u} [DecidableEq α] (r : FreeGroup α) (x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r) (hx : x ∈ Work.OROneRel.relatorLetters r) :
    ∃ (r' c : FreeGroup α), Work.OROneRel.IsCyclicallyReducedRelator r' ∧
      Work.OROneRel.relatorNorm r' = Work.OROneRel.relatorNorm r ∧ r = c * r' * c⁻¹ ∧
      Work.OROneRel.relatorLetters r' = Work.OROneRel.relatorLetters r ∧
      (∀ t : α, Work.OROneRel.sigma t r' = Work.OROneRel.sigma t r) ∧
      (r'.toWord.head? = some (x, true) ∨ r'.toWord.head? = some (x, false)) := by
  classical
  -- `Work.OROneRel`'s definitions use `Classical.decEq` internally; align the ambient instance.
  rw [Subsingleton.elim (inferInstanceAs (DecidableEq α)) (Classical.decEq α)]
  letI : DecidableEq α := Classical.decEq α
  -- `x` occurs in the reduced word of `r`, with some sign `b`.
  have hx' : ∃ b : Bool, (x, b) ∈ r.toWord := by
    simpa only [relatorLetters, Set.mem_ofPred_eq] using hx
  obtain ⟨b, hb⟩ := hx'
  -- split the reduced word just before that occurrence: `r.toWord = A ++ (x,b) :: V'`.
  obtain ⟨A, V', hWV⟩ := List.mem_iff_append.mp hb
  set V : List (α × Bool) := (x, b) :: V' with hV
  have hW : r.toWord = A ++ V := by rw [hWV, hV]
  -- `r` is cyclically reduced, hence so is the rotation `V ++ A`.
  have hWcyc : FreeGroup.IsCyclicallyReduced r.toWord := hcyc
  have hVA : V ++ A = (r.toWord).rotate A.length := by
    rw [hW, List.rotate_append_length_eq]
  have hcycVA : FreeGroup.IsCyclicallyReduced (V ++ A) := by
    rw [hVA]; exact isCyclicallyReduced_rotate hWcyc
  have hredVA : FreeGroup.IsReduced (V ++ A) := hcycVA.isReduced
  have htoWord : (FreeGroup.mk (V ++ A)).toWord = V ++ A := by
    rw [FreeGroup.toWord_mk, (FreeGroup.isReduced_iff_reduce_eq (L := V ++ A)).mp hredVA]
  refine ⟨FreeGroup.mk (V ++ A), FreeGroup.mk A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cyclically reduced
    rw [IsCyclicallyReducedRelator, htoWord]
    exact hcycVA
  · -- same norm
    rw [relatorNorm, relatorNorm, FreeGroup.norm, FreeGroup.norm, htoWord, hW]
    simp [List.length_append, Nat.add_comm]
  · -- conjugate
    have hr : r = FreeGroup.mk A * FreeGroup.mk V := by
      rw [(FreeGroup.mk_toWord (x := r)).symm, hW, FreeGroup.mul_mk]
    rw [hr, ← FreeGroup.mul_mk (L₁ := V) (L₂ := A)]
    group
  · -- same letters
    rw [relatorLetters, relatorLetters, htoWord, hW]
    ext a
    constructor
    · rintro ⟨b', hb'⟩
      refine ⟨b', ?_⟩
      rw [hVA] at hb'
      rw [List.mem_rotate] at hb'
      rwa [← hW]
    · rintro ⟨b', hb'⟩
      refine ⟨b', ?_⟩
      rw [hVA, List.mem_rotate]
      rwa [← hW] at hb'
  · -- same exponent sums
    intro t
    have hr : r = FreeGroup.mk (r.toWord) := (FreeGroup.mk_toWord (x := r)).symm
    rw [hr, sigma_mk t (r.toWord), sigma_mk t (V ++ A), hW, sigmaList_append_comm]
  · -- the first letter is `x`
    rw [htoWord]
    rcases b with _ | _
    · right
      rw [hV]; rfl
    · left
      rw [hV]; rfl

end Work.OROneRel
