import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.zmap_ext_of_closed_cover
import Submission.Work.ANALYTIC.pointsDetectSetup
import Submission.Work.ANALYTIC.zcomboPieces
import Submission.Work.ANALYTIC.zmapCombo_restrict_piece_zero
import Submission.Work.ANALYTIC.piece_family_covers

/-!
# A finite point-null combination of `zmap`s is locally zero

Let `φ j : V ⟶ T` (`j : Fin m`) be finitely many maps of light profinite sets and `c j ∈ ℤ`
coefficients.  Assume that at every *point* `v` of `V` the combination of point classes
`∑ j, c j • [φ j v]` vanishes in `ℤ[T](∗)` (hypothesis `h`, phrased with `prePt`; cf.
`Work.ANALYTIC.pointValue_zmap_combo`), and assume `hind`, the linear independence of the point
classes of an injective tuple of points of `T`
(cf. `Work.ANALYTIC.points_detect_zfree_NatUnionInfty`).

Then the morphism `∑ j, c j • zmap (φ j) : ℤ[V] ⟶ ℤ[T]` is *locally* zero: there is a finite
cover `ι i : C i ⟶ V` of `V` such that `∑ j, c j • zmap (ι i ≫ φ j) = 0` for every `i`.

The cover is the family of pieces `Work.ANALYTIC.piece V T φ f` indexed by the *idempotent*
"pattern" functions `f : Fin m → Fin m` whose class coefficient sums vanish:

* `Work.ANALYTIC.piece_family_covers` — for every point `u` of `V` there is such a pattern `f`
  with `u ∈ pieceSet φ f`; it is obtained from `hind` through the grouping lemma
  `Work.ANALYTIC.fiber_sum_eq_zero` (a relation between point classes vanishes on every fibre).
* `Work.ANALYTIC.zmapCombo_restrict_piece_zero` — on the piece of such a pattern, the two maps
  `φ j` and `φ (f j)` agree, so the combination is a sum of the (vanishing) class coefficient
  sums, hence `0`.

The family of patterns is finite (`Fin m → Fin m`), and it is reindexed by `Fin m'` with
`m' = Fintype.card {f // …}` through `Fintype.equivFin`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid Opposite Classical

noncomputable section

namespace Work.ANALYTIC

theorem zfree_zmap_combo_locally_zero (T V : LightProfinite.{0})
    (hind : ∀ (m : ℕ) (t : Fin m → ↥T), Function.Injective t → ∀ c : Fin m → ℤ,
      (∑ j, c j • (Work.ANALYTIC.pointClassM T (t j))) = 0 → ∀ j, c j = 0)
    (m : ℕ) (φ : Fin m → (V ⟶ T)) (c : Fin m → ℤ)
    (h : ∀ v : ↥V, Work.ANALYTIC.prePt v (Work.ANALYTIC.zmapCombo φ c) = 0) :
    ∃ (m' : ℕ) (C : Fin m' → LightProfinite.{0}) (ι : ∀ i, C i ⟶ V),
      (∀ u : ↥V, ∃ i, ∃ x : ↥(C i), ι i x = u) ∧
      ∀ i, Work.ANALYTIC.zmapCombo (fun j => CategoryTheory.CategoryStruct.comp (ι i) (φ j)) c
        = 0 := by
  classical
  -- The patterns: idempotent functions whose class coefficient sums vanish.
  let Idx := {f : Fin m → Fin m //
    (∀ i, f (f i) = f i) ∧ (∀ i, ∑ k ∈ Finset.univ.filter (fun k => f k = f i), c k = 0)}
  let e : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
  let g : Fin (Fintype.card Idx) → (Fin m → Fin m) := fun k => (e.symm k).1
  refine ⟨Fintype.card Idx, (fun k => piece V T m φ (g k)),
    (fun k => pieceIncl V T m φ (g k)), ?_, ?_⟩
  · -- the pieces of the patterns cover `V`
    intro u
    obtain ⟨f, hf, hc, hu⟩ := piece_family_covers V T m φ c hind h u
    have hg : g (e ⟨f, And.intro hf hc⟩) = f := by simp [g]
    refine ⟨e ⟨f, And.intro hf hc⟩, ?_⟩
    show ∃ x : ↥(piece V T m φ (g (e ⟨f, And.intro hf hc⟩))),
      pieceIncl V T m φ (g (e ⟨f, And.intro hf hc⟩)) x = u
    rw [hg]
    exact ⟨⟨u, hu⟩, rfl⟩
  · -- the combination vanishes on each piece
    intro k
    exact zmapCombo_restrict_piece_zero V T m φ c (g k) (e.symm k).2.1 (e.symm k).2.2

end Work.ANALYTIC

end
