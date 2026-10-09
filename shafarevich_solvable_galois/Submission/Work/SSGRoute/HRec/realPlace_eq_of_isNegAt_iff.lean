import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A real infinite place is determined by its negativity predicate on `kˣ`

If `w` is a *real* infinite place of a number field `k` and another infinite place `w'` has exactly
the same negative units (`IsNegAt w a ↔ IsNegAt w' a` for all `a : kˣ`), then `w = w'`.

This is the base case of the injectivity half of the Artin–Schreier dictionary between involutions
of `G_k` and real places of `k`: combined with
`Work.SSGRoute.ZDataTwo.exists_realPlace_of_involution` (the existence half, which characterises
the involution `c` by `kummerChar a c = 1 ↔ IsNegAt w a`) it gives a well-defined map from
conjugacy classes of involutions to real places, which clause 2 of
`Work.SSGRoute.HRec.cupKummer_archMatchK` (injectivity of `vOf`) needs.

The proof: `IsNegAt w a` is `φ a < 0` for the real embedding `φ = embedding_of_isReal hw`
(`ArchDefs.isNegAt_iff`), so `w'` is real (apply the hypothesis to `-1`) with embedding `ψ`, and
`φ`, `ψ` have the same sign on every nonzero element of `k`.  Testing that on `x - q`, `q : ℚ`,
gives the same rational cut, hence `φ = ψ` (density of `ℚ` in `ℝ`), hence the same embedding
`k →+* ℂ`, hence `w = w'`.

Kept separate from `ZDataTwo/eq_of_isNegAt_iff.lean` (another owner's file, still carrying the
corresponding `sorry`) so that the statement is available without touching it.
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

/-- A ring homomorphism out of a `ℚ`-algebra sends rationals to rationals. -/
private lemma map_algebraMap_rat {k : Type} [Field k] [Algebra ℚ k] (f : k →+* ℝ) (q : ℚ) :
    f (algebraMap ℚ k q) = (q : ℝ) := by
  have h : (algebraMap ℚ k q : k) = (q : k) := by
    first
      | simp
      | rw [← Rat.num_div_den q, map_div₀, map_natCast, map_natCast, Rat.cast_def]
  rw [h]
  exact map_ratCast f q

theorem realPlace_eq_of_isNegAt_iff {k : Type} [Field k] [NumberField k]
    {w w' : NumberField.InfinitePlace k} (hw : w.IsReal)
    (h : ∀ a : kˣ, Work.SSGRoute.ZDataTwo.IsNegAt w a ↔
      Work.SSGRoute.ZDataTwo.IsNegAt w' a) : w = w' := by
  have hw' : w'.IsReal := (h (-1)).mp (Work.SSGRoute.ZDataTwo.isNegAt_neg_one hw) |>.isReal
  let φ := NumberField.InfinitePlace.embedding_of_isReal hw
  let ψ := NumberField.InfinitePlace.embedding_of_isReal hw'
  -- the two embeddings have the same sign on every nonzero element of `k`
  have hsign : ∀ u : kˣ, φ (u : k) < 0 ↔ ψ (u : k) < 0 := fun u =>
    (Work.SSGRoute.ZDataTwo.isNegAt_iff hw u).symm.trans
      ((h u).trans (Work.SSGRoute.ZDataTwo.isNegAt_iff hw' u))
  -- hence they have the same rational cuts
  have hcut : ∀ x : k, ∀ q : ℚ, (φ x < (q : ℝ)) ↔ (ψ x < (q : ℝ)) := by
    intro x q
    by_cases hxq : x = algebraMap ℚ k q
    · rw [hxq, map_algebraMap_rat φ q, map_algebraMap_rat ψ q]
    · have hx : x - algebraMap ℚ k q ≠ 0 := by
        intro h0
        exact hxq (sub_eq_zero.mp h0)
      have hlt : φ (x - algebraMap ℚ k q) < 0 ↔ ψ (x - algebraMap ℚ k q) < 0 :=
        hsign (Units.mk0 (x - algebraMap ℚ k q) hx)
      rw [map_sub, map_sub, map_algebraMap_rat φ q, map_algebraMap_rat ψ q] at hlt
      constructor
      · intro hx'
        have h2 : φ x - (q : ℝ) < 0 := by linarith
        have h3 := hlt.mp h2
        linarith
      · intro hx'
        have h2 : ψ x - (q : ℝ) < 0 := by linarith
        have h3 := hlt.mpr h2
        linarith
  have hφψ : ∀ x : k, φ x = ψ x := by
    intro x
    refine le_antisymm ?_ ?_
    · by_contra hcon
      push Not at hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
      exact absurd ((hcut x q).mpr hq1) (not_lt.mpr hq2.le)
    · by_contra hcon
      push Not at hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
      exact absurd ((hcut x q).mp hq1) (not_lt.mpr hq2.le)
  have hemb : w.embedding = w'.embedding := by
    ext x
    rw [← NumberField.InfinitePlace.embedding_of_isReal_apply hw x,
      ← NumberField.InfinitePlace.embedding_of_isReal_apply hw' x, hφψ x]
  rw [← NumberField.InfinitePlace.mk_embedding w, ← NumberField.InfinitePlace.mk_embedding w',
    hemb]

end Work.SSGRoute.HRec
