import Mathlib
import Submission.Work.WilC4aU.Defs
import Submission.Work.WilC4aU.Supp

namespace Work.WilC4aU

/-- **C4aU.Support.**  If the fibre of `Y` at `c` is not eventually zero, then its `x`-support
contains a half line `[b, ∞)`.

This is where uniform finiteness (`hUF`) is used to produce the pair `(x, 2 x)` in the fibre.
`Submission/Work/WilC4aU/Supp.lean` provides `XSupp Y`, the `x`-support of `Y` over all parameters,
with two lemmas:
* `Work.WilC4aU.cons_mem_xSupp : Fin.cons x c ∈ XSupp Y ↔ ∃ y, Fin.cons x (Fin.cons y c) ∈ Y`;
* `Work.WilC4aU.xSupp_rexExist : RExpExist Y → RExpExist (XSupp Y)`.

Proof plan.  Put `S := {x : ℝ | Fin.cons x c ∈ XSupp Y} = {x | ∃ y, (x, y, c) ∈ Y}`
(by `cons_mem_xSupp`).  `¬ ZeroSect Y c` unfolds (`push_neg`) to
`∀ R, ∃ x ≥ R, ∃ y, (x,y,c) ∈ Y ∧ y ≠ 0`, so `S` is unbounded above.  Apply `hUF k (XSupp Y)`
(to `XSupp Y : Set (Fin (k + 1) → ℝ)`, so its fibre over `c` is `S`) to write
`S = ⋃₀ s` with `s : Finset (Set ℝ)` all of whose members are preconnected.  A finite union of
sets bounded above is bounded above, so some `I ∈ s` is unbounded above.  A preconnected subset
of `ℝ` is order-connected (`IsPreconnected.ordConnected`), hence an interval with
`Set.OrdConnected.out`; if `b ∈ I` and `I` is unbounded above then `[b, ∞) ⊆ I` (for `t ≥ b`,
pick `u ∈ I` with `u > t`, then `t ∈ Set.Icc b u ⊆ I`).  Any `b ∈ I` therefore works. -/
theorem xSupp_eventually {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hUF : WilkiesDesign.CG.UnifFiniteRExp) (hY : WilkiesDesign.RExpExist Y) {c : Fin k → ℝ}
    (hne : ¬ Work.WilC4aU.ZeroSect Y c) :
    ∃ b : ℝ, ∀ x ≥ b, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y := by
  -- The `x`-support set of the fibre at `c`, as a subset of `ℝ`.
  set S : Set ℝ := {x : ℝ | Fin.cons x c ∈ XSupp Y} with hSdef
  -- `¬ ZeroSect Y c` unfolds to witnesses with `y ≠ 0` at arbitrarily large `x`.
  have hne' : ∀ R : ℝ, ∃ x ≥ R, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0 := by
    intro R
    by_contra h
    refine hne ⟨R, fun x y hx hxy => ?_⟩
    by_contra hy
    exact h ⟨x, hx, y, hxy, hy⟩
  -- Hence `S` is unbounded above.
  have hunb : ¬ BddAbove S := by
    rw [not_bddAbove_iff]
    intro R
    obtain ⟨x, hxR, y, hxy, -⟩ := hne' (R + 1)
    exact ⟨x, by rw [hSdef]; exact cons_mem_xSupp.mpr ⟨y, hxy⟩,
      lt_of_lt_of_le (lt_add_one R) hxR⟩
  -- Uniform finiteness decomposes `S` into finitely many preconnected pieces.
  obtain ⟨N, hN⟩ := hUF k (XSupp Y) (xSupp_rexExist hY)
  obtain ⟨s, -, hpre, hunion⟩ := hN c
  have hunionS : S = ⋃₀ (s : Set (Set ℝ)) := by rw [hSdef]; exact hunion
  -- A finite union of bounded-above sets is bounded above, so one piece is unbounded above.
  obtain ⟨I, hIs, hIunb⟩ : ∃ I ∈ s, ¬ BddAbove I := by
    by_contra h
    have hbdd : ∀ i ∈ (s : Set (Set ℝ)), BddAbove i := by
      intro i hi
      by_contra hi'
      exact h ⟨i, by simpa using hi, hi'⟩
    have := (Set.Finite.bddAbove_biUnion (Finset.finite_toSet s)).mpr hbdd
    rw [← Set.sUnion_eq_biUnion] at this
    exact hunb (hunionS.symm ▸ this)
  -- `I` is preconnected, hence order-connected; a half line starting at any of its points is in it.
  obtain ⟨b, hb⟩ := nonempty_of_not_bddAbove hIunb
  refine ⟨b, fun x hx => ?_⟩
  have hxI : x ∈ I := by
    rw [not_bddAbove_iff] at hIunb
    obtain ⟨u, hu, hxu⟩ := hIunb x
    exact (hpre I hIs).ordConnected.out hb hu ⟨hx, le_of_lt hxu⟩
  have hxS : x ∈ S := by
    rw [hunionS]
    exact Set.subset_sUnion_of_mem hIs hxI
  rw [hSdef] at hxS
  exact cons_mem_xSupp.mp hxS

end Work.WilC4aU
