import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-!
# `isWordProd_of_mem_mClose`

The matrix closure `mClose gensM k accM` is obtained from the seed list `accM` by `k` rounds
of `mF`, where one round appends, to every element already present, all its right products
with a generator:

`mF gensM accM = (accM ++ accM.flatMap (fun a => gensM.map (fun g => m9mul a g))).dedup`.

Hence, if every element of the seed list is a product of generators (`IsWordProd gensM`),
then so is every element of `mClose gensM k accM`, for every `k`.

The two ingredients are:
* `mem_mF`: a membership characterisation of one closure round;
* `isWordProd_mul`: right multiplication by a generator preserves being a word product
  (append the generator to the witnessing word).
-/

/-- Membership in one closure round: either the element was already present, or it is a right
product `m9mul b g` of an old element `b` by a generator `g`. -/
lemma mem_mF {gensM accM : List (List ℤ)} {a : List ℤ} (ha : a ∈ mF gensM accM) :
    a ∈ accM ∨ ∃ b ∈ accM, ∃ g ∈ gensM, m9mul b g = a := by
  rw [mF, List.mem_dedup, List.mem_append, List.mem_flatMap] at ha
  rcases ha with h | ⟨b, hb, hg⟩
  · exact Or.inl h
  · rw [List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    exact Or.inr ⟨b, hb, g, hg, rfl⟩

/-- Right multiplication by a generator preserves being a product of generators: append the
generator to the witnessing word. -/
lemma isWordProd_mul {gensM : List (List ℤ)} {a b : List ℤ}
    (ha : IsWordProd gensM a) (hb : b ∈ gensM) : IsWordProd gensM (m9mul a b) := by
  obtain ⟨w, hw, hfold⟩ := ha
  refine ⟨w ++ [b], ?_, ?_⟩
  · intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with h | rfl
    · exact hw x h
    · exact hb
  · rw [List.foldl_concat, hfold]

/-- Every element of the matrix closure is a product of generators. -/
theorem isWordProd_of_mem_mClose {gensM accM : List (List ℤ)}
    (hacc : ∀ a ∈ accM, IsWordProd gensM a) (k : ℕ) :
    ∀ l ∈ mClose gensM k accM, IsWordProd gensM l := by
  revert accM
  induction k with
  | zero =>
    intro accM hacc l hl
    exact hacc l hl
  | succ k ih =>
    intro accM hacc l hl
    rw [show mClose gensM (k + 1) accM = mClose gensM k (mF gensM accM) from rfl] at hl
    refine ih (accM := mF gensM accM) ?_ l hl
    intro a ha
    rcases mem_mF ha with h | ⟨b, hb, g, hg, rfl⟩
    · exact hacc a h
    · exact isWordProd_mul (hacc b hb) hg

end Work.SG
