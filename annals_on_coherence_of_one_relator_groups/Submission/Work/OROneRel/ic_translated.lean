import Mathlib
import Submission.Work.OROneRel.interval_defs

namespace Work.OROneRel

/-- Transport a `ReflTransGen` along a function sending `R`-steps to `R'`-steps. -/
lemma reflTransGen_map_of {R R' : ℤ → ℤ → Prop} {f : ℤ → ℤ}
    (hf : ∀ a b, R a b → R' (f a) (f b)) {a b : ℤ}
    (hab : Relation.ReflTransGen R a b) : Relation.ReflTransGen R' (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (hf _ _ hbc)

/-- `S` is invariant under translating the interval (and both endpoints) by `lo`. -/
lemma S_add_const {A B M lo x y : ℤ} (h : S 0 M A B x y) :
    S lo (lo + M) A B (x + lo) (y + lo) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine S.of (by omega) (by omega) (by omega) (by omega) ?_
  rcases h5 with h5 | h5 | h5 | h5
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; omega

theorem ic_translated {A B M : ℤ}
    (h : ∀ x y : ℤ, 0 ≤ x → x ≤ M → 0 ≤ y → y ≤ M →
      Relation.ReflTransGen (S 0 M A B) x y) (lo : ℤ) :
    ∀ x y : ℤ, lo ≤ x → x ≤ lo + M → lo ≤ y → y ≤ lo + M →
      Relation.ReflTransGen (S lo (lo + M) A B) x y := by
  intro x y hx hxM hy hyM
  have hxy : Relation.ReflTransGen (S 0 M A B) (x - lo) (y - lo) :=
    h (x - lo) (y - lo) (by omega) (by omega) (by omega) (by omega)
  have := reflTransGen_map_of (R := S 0 M A B) (R' := S lo (lo + M) A B)
    (f := fun z => z + lo) (fun a b hab => S_add_const hab) hxy
  simpa using this

end Work.OROneRel
