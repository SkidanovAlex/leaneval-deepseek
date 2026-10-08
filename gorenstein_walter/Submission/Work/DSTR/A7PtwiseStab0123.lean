import Mathlib
import Submission.Work.A7.Defs

/-
The pointwise stabilizer of `{0,1,2,3}` inside `A₇`.

If an even permutation `g` of `Fin 7` fixes `0,1,2,3` pointwise, then it fixes the complement
`{4,5,6}` as a set, so it restricts to a permutation of the three-element set `{4,5,6}`; being
even, this restriction is either the identity or a 3-cycle, which gives exactly the three
possibilities `1`, `(4 5 6)`, `(4 5 6)²`.

The proof is a direct finite case analysis on the images of `4` and `5`: the odd possibilities
are excluded with `Equiv.Perm.sign_swap`.
-/
namespace Work.DSTR

theorem A7PtwiseStab0123 : ∀ g : Equiv.Perm (Fin 7), Equiv.Perm.sign g = 1 →
    (∀ q ∈ ({0,1,2,3} : Finset (Fin 7)), g q = q) →
    g = 1 ∨ g = (Work.A7.a7ThreeCycle : Equiv.Perm (Fin 7)) ∨
      g = (Work.A7.a7ThreeCycle : Equiv.Perm (Fin 7)) ^ 2 := by
  intro g hsign hfix
  -- The images of `0,1,2,3` under `g`.
  have hfix0 : g 0 = 0 := hfix 0 (by decide)
  have hfix1 : g 1 = 1 := hfix 1 (by decide)
  have hfix2 : g 2 = 2 := hfix 2 (by decide)
  have hfix3 : g 3 = 3 := hfix 3 (by decide)
  -- Membership in `{0,1,2,3}` is preserved backwards by `g`.
  have hback : ∀ x : Fin 7, g x ∈ ({0,1,2,3} : Finset (Fin 7)) →
      x ∈ ({0,1,2,3} : Finset (Fin 7)) := by
    intro x hx
    have h2 : g (g x) = g x := hfix (g x) hx
    have h3 : g x = x := g.injective h2
    rw [← h3]; exact hx
  have hcomp : ({0,1,2,3} : Finset (Fin 7))ᶜ = {4,5,6} := by decide
  -- Hence `g` maps the complement `{4,5,6}` into itself.
  have hm : ∀ x : Fin 7, x ∉ ({0,1,2,3} : Finset (Fin 7)) →
      g x ∈ ({4,5,6} : Finset (Fin 7)) := by
    intro x hx
    rw [← hcomp, Finset.mem_compl]
    exact fun h => hx (hback x h)
  have h4 : g 4 = 4 ∨ g 4 = 5 ∨ g 4 = 6 := by
    have := hm 4 (by decide); simpa using this
  have h5 : g 5 = 4 ∨ g 5 = 5 ∨ g 5 = 6 := by
    have := hm 5 (by decide); simpa using this
  have h6 : g 6 = 4 ∨ g 6 = 5 ∨ g 6 = 6 := by
    have := hm 6 (by decide); simpa using this
  -- `g` is injective, so `g` separates distinct points.
  have hne : ∀ x y : Fin 7, x ≠ y → g x ≠ g y := fun x y h hh => h (g.injective hh)
  rcases h4 with h4 | h4 | h4
  · rcases h5 with h5 | h5 | h5
    · -- `g 5 = g 4`, impossible
      exact absurd h5 (by simpa [h4] using hne 5 4 (by decide))
    · -- `g = 1`
      have h6c : g 6 = 6 := by
        rcases h6 with h | h | h
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
        · exact h
      exact Or.inl (by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c)
    · -- `g = (5 6)`, odd
      have h6c : g 6 = 5 := by
        rcases h6 with h | h | h
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
        · exact h
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
      have hg : g = Equiv.swap 5 6 := by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c
      rw [hg] at hsign
      exact absurd hsign (by decide)
  · rcases h5 with h5 | h5 | h5
    · -- `g = (4 5)`, odd
      have h6c : g 6 = 6 := by
        rcases h6 with h | h | h
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
        · exact h
      have hg : g = Equiv.swap 4 5 := by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c
      rw [hg] at hsign
      exact absurd hsign (by decide)
    · -- `g 5 = g 4`, impossible
      exact absurd h5 (by simpa [h4] using hne 5 4 (by decide))
    · -- `g = (4 5 6)`
      have h6c : g 6 = 4 := by
        rcases h6 with h | h | h
        · exact h
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
      have hg : g = Work.A7.a7ThreeCyclePerm := by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c
      refine Or.inr (Or.inl ?_)
      rw [Work.A7.coe_a7ThreeCycle]
      exact hg
  · rcases h5 with h5 | h5 | h5
    · -- `g = (4 5 6)²`
      have h6c : g 6 = 5 := by
        rcases h6 with h | h | h
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
        · exact h
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
      have hg : g = Work.A7.a7ThreeCyclePerm ^ 2 := by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c
      refine Or.inr (Or.inr ?_)
      rw [Work.A7.coe_a7ThreeCycle]
      exact hg
    · -- `g = (4 6)`, odd
      have h6c : g 6 = 4 := by
        rcases h6 with h | h | h
        · exact h
        · exact absurd h (by simpa [h5] using hne 6 5 (by decide))
        · exact absurd h (by simpa [h4] using hne 6 4 (by decide))
      have hg : g = Equiv.swap 4 6 := by
        apply Equiv.ext
        intro x
        fin_cases x
        · exact hfix0
        · exact hfix1
        · exact hfix2
        · exact hfix3
        · exact h4
        · exact h5
        · exact h6c
      rw [hg] at hsign
      exact absurd hsign (by decide)
    · -- `g 5 = g 4`, impossible
      exact absurd h5 (by simpa [h4] using hne 5 4 (by decide))

end Work.DSTR
