import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If a map `g` commutes with every member `f i` of a family indexed by `L`, then
`g` commutes with the fold of the family. -/
lemma foldr_comm_apply {ι α : Type*} (L : List ι) (f : ι → α → α) (g : α → α)
    (h : ∀ i z, g (f i z) = f i (g z)) (x : α) :
    g (L.foldr f x) = L.foldr f (g x) := by
  induction L generalizing x with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    rw [h i (L.foldr f x), ih x]

/-- Two families of commuting endomorphisms: the fold of the composite family equals
the composite of the two folds. -/
lemma foldr_prod {ι α : Type*} (L : List ι) (F F' : ι → α → α)
    (hcomm : ∀ i j z, F i (F' j z) = F' j (F i z)) (x : α) :
    L.foldr F (L.foldr F' x) = L.foldr (fun i Q => F i (F' i Q)) x := by
  induction L generalizing x with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    rw [← foldr_comm_apply L F (F' i) (fun j z => (hcomm j i z).symm) (L.foldr F' x)]
    rw [ih x]

lemma foldr_two {ι α : Type*} (L : List ι) (G : ι → ℕ → α → α)
    (hmul : ∀ i n n', G i (n + n') = G i n ∘ G i n')
    (hcomm : ∀ i j n n' x, G i n (G j n' x) = G j n' (G i n x))
    (t t' : ι → ℕ) (x : α) :
    L.foldr (fun i Q => G i (t i) Q) (L.foldr (fun i Q => G i (t' i) Q) x)
      = L.foldr (fun i Q => G i (t i + t' i) Q) x := by
  have key := foldr_prod L (fun i => G i (t i)) (fun i => G i (t' i))
    (fun i j z => hcomm i j (t i) (t' j) z) x
  rw [key]
  have hfun : (fun i Q => G i (t i) (G i (t' i) Q)) = (fun i Q => G i (t i + t' i) Q) := by
    funext i Q
    rw [hmul i (t i) (t' i)]
    rfl
  rw [hfun]

end Work.BW
