import Mathlib

namespace Work.ORDunwoody

/-- Pairing argument for a `ℕ`-valued function `h` into `ZMod 2`: if `R` is a symmetric,
irreflexive relation in which every element has a *unique* `R`-partner, if `h` is constant on
`R`-pairs, and if every `t ∈ S` has an `R`-partner inside `S`, then the values of `h` on `S`
pair up, so their sum vanishes. -/
theorem sum_eq_zero_of_partner {h : ℕ → ZMod 2} {R : ℕ → ℕ → Prop}
    (hsymm : ∀ a b, R a b → R b a) (hirrefl : ∀ a, ¬ R a a)
    (huniq : ∀ a b c, R a b → R a c → b = c) (hinv : ∀ a b, R a b → h a = h b)
    (S : Finset ℕ) (hS : ∀ t ∈ S, ∃ u ∈ S, R t u) : ∑ t ∈ S, h t = 0 := by
  classical
  -- Send each `t ∈ S` to its partner in `S`, chosen via `hS`; uniqueness (`huniq`) makes it
  -- an involution without fixed points, and `hinv` makes `h` invariant under it.
  refine Finset.sum_involution (fun t ht => Classical.choose (hS t ht)) ?_ ?_
    (fun a ha => (Classical.choose_spec (hS a ha)).1) ?_
  · -- a pair contributes `h a + h a = 0` in `ZMod 2`
    intro a ha
    rw [hinv a _ (Classical.choose_spec (hS a ha)).2]
    exact CharTwo.add_self_eq_zero _
  · -- the pairing has no fixed point, since `R` is irreflexive
    intro a ha _ hga
    have h1 : R a (Classical.choose (hS a ha)) := (Classical.choose_spec (hS a ha)).2
    rw [hga] at h1
    exact hirrefl a h1
  · -- the pairing is an involution, by uniqueness of the `R`-partner
    intro a ha
    exact huniq (Classical.choose (hS a ha))
      (Classical.choose (hS (Classical.choose (hS a ha))
        ((Classical.choose_spec (hS a ha)).1))) a
      (Classical.choose_spec (hS (Classical.choose (hS a ha))
        ((Classical.choose_spec (hS a ha)).1))).2
      (hsymm a (Classical.choose (hS a ha)) (Classical.choose_spec (hS a ha)).2)

end Work.ORDunwoody
