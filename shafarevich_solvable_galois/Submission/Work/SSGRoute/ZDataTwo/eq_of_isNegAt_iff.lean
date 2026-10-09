import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A real infinite place of a number field is determined by its sign function on `kˣ`

Let `w` be a *real* infinite place of a number field `k`, and let `w'` be an infinite place of `k`
such that `IsNegAt w' a ↔ IsNegAt w a` for every unit `a : kˣ`.  Then `w = w'`.

## The mathematics

`IsNegAt w a` unfolds (see `ArchDefs.isNegAt_iff`) to `φ a < 0`, where `φ = embedding_of_isReal hw`
is the real embedding `k →+* ℝ` attached to the real place `w`.  Applying the hypothesis to
`a = -1` (which is negative at a real place, `isNegAt_neg_one`) shows that `w'` is real too, and
the hypothesis is exactly the statement that the two ring homomorphisms
`φ = embedding_of_isReal hw` and `ψ = embedding_of_isReal hw'` have the same sign on every
*nonzero* element of `k`.

Two such homomorphisms must be equal: an element of `k` is zero iff its image under `φ` is, so the
hypothesis upgrades to `0 < φ x ↔ 0 < ψ x` for all `x ≠ 0`, i.e. `φ` and `ψ` have the same
"rational cut".  Concretely, if `φ x < ψ x` then by density of `ℚ` in `ℝ`
(`exists_rat_btwn`) there is `r : ℚ` with `φ x < r < ψ x`; the element `x - r ∈ k` is nonzero
(since `φ (x - r) = φ x - r < 0`), so the hypothesis applies to it, and it yields
`φ x - r < 0 ↔ ψ x - r < 0`, i.e. `ψ x < r`, contradicting `r < ψ x`.  The case `ψ x < φ x` is
symmetric.  Thus `φ = ψ`.

Finally `w.embedding = w'.embedding` because on `ℂ` the embedding `w.embedding` is the composite
of `φ` with the inclusion `ℝ → ℂ` (`InfinitePlace.embedding_of_isReal_apply`), and for infinite
places the assignment `w ↦ w.embedding` is injective (`InfinitePlace.embedding_inj`).

This is the base case of the injectivity half of the Artin–Schreier dictionary between involutions
of `G_k` and real places of `k`.
-/

namespace Work.SSGRoute.ZDataTwo

/-- **A unital ring homomorphism `E →+* ℝ` is determined by its sign function on `Eˣ`.**  If two
ring homomorphisms have the same negative units, then, as the sign of `x ≠ 0` is the sign of its
image, they have the same rational cut; two copies of `ℚ` embedded in `ℝ` with the same cut
coincide by density of `ℚ` in `ℝ`. -/
private lemma ringHom_eq_of_lt_zero_iff {E : Type} [Field E] {φ ψ : E →+* ℝ}
    (h : ∀ a : Eˣ, φ (a : E) < 0 ↔ ψ (a : E) < 0) : φ = ψ := by
  -- It suffices to contradict `φ x < ψ x` (and symmetrically) for every `x : E`.
  have key : ∀ (φ ψ : E →+* ℝ), (∀ a : Eˣ, φ (a : E) < 0 ↔ ψ (a : E) < 0) → ∀ x, ¬ φ x < ψ x := by
    intro φ ψ h x hlt
    -- A rational strictly between `φ x` and `ψ x`.
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    -- The element `x - r` is nonzero, hence a unit, and the hypothesis applies to it.
    have hz : (x - (r : E)) ≠ 0 := by
      intro h0
      have h1 : φ (x - (r : E)) = 0 := by rw [h0, map_zero]
      simp at h1
      linarith
    have h1 : φ (x - (r : E)) < 0 := by simp; linarith
    have h2 : 0 < ψ (x - (r : E)) := by simp; linarith
    have h3 : ψ (x - (r : E)) < 0 :=
      (h (Units.mk0 (x - (r : E)) hz)).mp (by simpa using h1)
    linarith
  ext x
  rcases lt_trichotomy (φ x) (ψ x) with hlt | heq | hgt
  · exact absurd hlt (key φ ψ h x)
  · exact heq
  · exact absurd hgt (key ψ φ (fun a => (h a).symm) x)

theorem eq_of_isNegAt_iff {k : Type} [Field k] [NumberField k]
    {w w' : NumberField.InfinitePlace k} (hw : w.IsReal)
    (h : ∀ a : kˣ, Work.SSGRoute.ZDataTwo.IsNegAt w a ↔
      Work.SSGRoute.ZDataTwo.IsNegAt w' a) : w = w' := by
  -- `-1` is negative at the real place `w`, so it is negative at `w'`, so `w'` is real too.
  have hw' : w'.IsReal :=
    IsNegAt.isReal ((h (-1)).mp (isNegAt_neg_one hw))
  -- The two real embeddings have the same sign function on `kˣ`.
  have hsign : ∀ a : kˣ,
      NumberField.InfinitePlace.embedding_of_isReal hw (a : k) < 0 ↔
        NumberField.InfinitePlace.embedding_of_isReal hw' (a : k) < 0 := by
    intro a
    rw [← isNegAt_iff hw a, ← isNegAt_iff hw' a]
    exact h a
  have hφψ := ringHom_eq_of_lt_zero_iff hsign
  -- Equal real embeddings; compare the induced complex embeddings.
  rw [← NumberField.InfinitePlace.embedding_inj]
  ext x
  rw [← NumberField.InfinitePlace.embedding_of_isReal_apply hw x,
    ← NumberField.InfinitePlace.embedding_of_isReal_apply hw' x, hφψ]

end Work.SSGRoute.ZDataTwo
