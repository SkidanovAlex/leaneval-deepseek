/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The range of an increasing map above the diagonal is an open ray

Let `f : ℝ → ℝ` be continuous and strictly increasing with `f x > x` for all `x`,
and suppose `f` is not surjective.  Then the range of `f` is exactly
`Ioi (sInf (range f))` — an open halfline.

The mathematical content, and where each hypothesis is used:

* `hgt : ∀ x, x < f x` makes `range f` **unbounded above** (`f M > M` for every
  `M`), so `range f` is never of the form `Iic _`.
* If `¬hnot` failed, i.e. if `range f` were **unbounded below**, then `f` would
  be surjective: given `y`, pick `z = f x₁ ∈ range f` with `f x₁ < y`; then
  `x₁ < f x₁ < y < f y`, and the intermediate value theorem on `[x₁, y]`
  produces `x` with `f x = y`.  Hence `¬hnot` forces `BddBelow (range f)`, which
  is what makes `sInf (range f)` the honest greatest lower bound (for an
  unbounded-below set, `sInf` in a conditionally complete linear order is the
  junk value `sInf ∅`).
* `range f ⊆ Ioi (sInf (range f))` is *strict*: for any `x`, pick `x - 1 < x`;
  then `f (x - 1) ∈ range f` and `f (x - 1) < f x`, so
  `sInf (range f) ≤ f (x - 1) < f x`.
* `Ioi (sInf (range f)) ⊆ range f`: if `y > sInf (range f)` then `y` is not a
  lower bound of `range f`, so `f x₁ < y` for some `x₁`, and `x₁ < f x₁ < y < f y`;
  the intermediate value theorem on `[x₁, y]` gives `f x = y`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

theorem range_eq_Ioi_sInf (f : ℝ → ℝ) (hcont : Continuous f) (hmono : StrictMono f)
    (hgt : ∀ x : ℝ, x < f x) (hnot : ¬ Function.Surjective f) :
    Set.range f = Set.Ioi (sInf (Set.range f)) := by
  -- A non-surjective such `f` has bounded-below range: otherwise it is surjective.
  have hbdd : BddBelow (Set.range f) := by
    by_contra h
    apply hnot
    intro y
    obtain ⟨z, hz, hzy⟩ := (not_bddBelow_iff.mp h) y
    obtain ⟨x₁, rfl⟩ := hz
    -- `x₁ < f x₁ = z < y < f y`, so `y` lies between two values of `f`.
    exact (intermediate_value_univ x₁ y hcont
      ⟨le_of_lt hzy, le_of_lt (hgt y)⟩).imp fun x hx => hx
  ext y
  simp only [Set.mem_range, Set.mem_Ioi]
  constructor
  · rintro ⟨x, rfl⟩
    -- `sInf (range f) ≤ f (x - 1) < f x`, so the inequality is strict.
    have h1 : sInf (Set.range f) ≤ f (x - 1) := csInf_le hbdd ⟨x - 1, rfl⟩
    have h2 : f (x - 1) < f x := hmono (by linarith)
    linarith
  · intro hy
    -- Since `sInf (range f) < y`, `y` is not a lower bound of the range.
    have hlt : ∃ b ∈ Set.range f, b < y := by
      by_contra hcon
      have hcon' : ∀ b ∈ Set.range f, y ≤ b := fun b hb =>
        le_of_not_gt fun hby => hcon ⟨b, hb, hby⟩
      have : y ≤ sInf (Set.range f) := le_csInf ⟨f 0, 0, rfl⟩ hcon'
      linarith
    obtain ⟨b, ⟨x₁, rfl⟩, hby⟩ := hlt
    -- `x₁ < f x₁ = b < y < f y`.
    exact (intermediate_value_univ x₁ y hcont
      ⟨le_of_lt hby, le_of_lt (hgt y)⟩).imp fun x hx => hx

end Work.Implosion.Chord
