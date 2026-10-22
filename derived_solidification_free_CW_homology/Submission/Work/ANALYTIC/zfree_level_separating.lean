import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.exists_level_enumeration

/-!
# Separating finitely many points of a light profinite set at one finite level

A light profinite set `T` is the limit of the tower of its finite components `T.component n`
(`T.diagram.obj ⟨n⟩`), and the projections `T.proj n : T ⟶ T.component n` are compatible with the
transition maps.  Consequently two distinct points of `T` are already distinguished by some
projection `T.proj n` (this is `Work.ATOM.proj_separates`, restated here in contrapositive form),
and since there are only finitely many pairs among finitely many points, a single level suffices
for all of them: this is `Work.ANALYTIC.zfree_level_separating`.

The result is the input that lets `ℤ[T]` be written as a filtered union of the `ℤ[T.component n]`
along injective maps, hence that a finite set of points of `T` is independent already in one of
the finite quotients.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite

noncomputable section

/-- The projections of a light profinite set are compatible: the projection of a point to level
`b` determines its projection to every lower level `a ≤ b`. -/
lemma proj_mono (T : LightProfinite.{0}) {a b : ℕ} (h : a ≤ b) {x y : ↥T}
    (hxy : T.proj b x = T.proj b y) : T.proj a x = T.proj a y := by
  rw [← Work.ATOM.proj_comp_itTr_apply T h x, hxy, Work.ATOM.proj_comp_itTr_apply T h y]

/-- Two distinct points of a light profinite set are separated by some projection to a finite
component.  (Contrapositive form of `Work.ATOM.proj_separates`.) -/
lemma exists_proj_ne (T : LightProfinite.{0}) {x y : ↥T} (h : x ≠ y) :
    ∃ n : ℕ, T.proj n x ≠ T.proj n y := by
  by_contra hc
  push_neg at hc
  exact h (Work.ATOM.proj_separates T hc)

/-- **Finitely many points of a light profinite set are separated by one finite level**: if
`t : Fin m → ↥T` is injective, then some projection `T.proj n` is injective on the image of `t`.
(Equivalently, `ℤ[t 0], …, ℤ[t (m-1)]` are linearly independent already in `ℤ[T.component n]`.) -/
theorem zfree_level_separating (T : LightProfinite.{0}) (m : ℕ) (t : Fin m → ↥T)
    (ht : Function.Injective t) :
    ∃ n : ℕ, ∀ j j' : Fin m, T.proj n (t j) = T.proj n (t j') → j = j' := by
  classical
  -- For every unordered pair of *distinct* indices there is a level separating that pair.
  have key : ∀ p : {p : Fin m × Fin m // p.1 ≠ p.2}, ∃ n : ℕ,
      T.proj n (t p.1.1) ≠ T.proj n (t p.1.2) :=
    fun p => exists_proj_ne T (fun h => p.2 (ht h))
  choose d hd using key
  -- The maximum of those finitely many levels separates every pair at once.
  refine ⟨(Finset.univ : Finset {p : Fin m × Fin m // p.1 ≠ p.2}).sup d, fun j j' hjj => ?_⟩
  by_contra hne
  have hmem : (⟨(j, j'), hne⟩ : {p : Fin m × Fin m // p.1 ≠ p.2}) ∈
      (Finset.univ : Finset {p : Fin m × Fin m // p.1 ≠ p.2}) := Finset.mem_univ _
  exact hd ⟨(j, j'), hne⟩ (proj_mono T (Finset.le_sup hmem) hjj)

end

end Work.ANALYTIC
