import Mathlib
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-- Face compatibility of the characteristic maps of a `Δ`-complex, transported
to the level of the standard simplex: the characteristic map of a face is the
restriction of the characteristic map of the simplex along the face inclusion
`i.succAbove`. -/
lemma DeltaSimplexMap.cls_face (χ : DeltaSimplexMap K X) {k : ℕ}
    (σ : Fin (K.card (k + 1))) (i : Fin (k + 2)) (z : StdSimplex ℝ (Fin (k + 1))) :
    χ.cls k (K.face σ i) z = χ.cls (k + 1) σ (StdSimplex.map i.succAbove z) := by
  rw [DeltaSimplexMap.cls, DeltaSimplexMap.cls]
  rw [χ.face_compat σ i]
  rw [singFace]
  rw [TopCat.toSSetObjEquiv_δ_apply]

/-- Renormalization of a point of the standard simplex with a vanishing
barycentric weight: if the weight at the vertex `i` is zero, then the point is
the image, under the face inclusion `i.succAbove`, of a point of the standard
`n`-simplex obtained by discarding that vertex. -/
lemma exists_stdSimplex_map_succAbove_eq {n : ℕ} (i : Fin (n + 1))
    (y : StdSimplex ℝ (Fin (n + 1))) (hi : y.weights i = 0) :
    ∃ y' : StdSimplex ℝ (Fin n), StdSimplex.map i.succAbove y' = y := by
  have hsupp : ↑y.weights.support ⊆ Set.range i.succAbove := by
    intro m hm
    rw [Fin.range_succAbove, Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hm) hi
  have hmap : Finsupp.mapDomain i.succAbove
        (Finsupp.comapDomain i.succAbove y.weights Fin.succAbove_right_injective.injOn)
      = y.weights :=
    Finsupp.mapDomain_comapDomain i.succAbove Fin.succAbove_right_injective y.weights hsupp
  refine ⟨⟨Finsupp.comapDomain i.succAbove y.weights Fin.succAbove_right_injective.injOn,
    ?_, ?_⟩, ?_⟩
  · intro k
    rw [Finsupp.comapDomain_apply]
    exact y.weights_nonneg _
  · rw [Finsupp.sum_fintype _ _ (by intro k; rfl)]
    simp only [Finsupp.comapDomain_apply]
    have himg : (Finset.univ : Finset (Fin n)).image i.succAbove = Finset.univ.erase i := by
      ext m
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨k, rfl⟩
        exact Fin.succAbove_ne i k
      · intro hm
        have hm' : m ∈ Set.range i.succAbove := by
          rw [Fin.range_succAbove]
          simpa using hm
        exact hm'
    rw [← Finset.sum_image (f := fun m : Fin (n + 1) => y.weights m) (g := i.succAbove)
      Fin.succAbove_right_injective.injOn, himg]
    have hper : ∑ x ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, y.weights x
        + y.weights i = ∑ x ∈ (Finset.univ : Finset (Fin (n + 1))), y.weights x :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    rw [hi, add_zero, StdSimplex.total_of_fintype] at hper
    exact hper
  · apply StdSimplex.ext
    exact hmap

/-- **The dimension bound.**  If a point of `X` which is the image of the open
simplex `p` is also in the image of the closed `j`-simplex `σ` under the
characteristic map, then `p.dim ≤ j`.  (Uses the realization: the uniqueness of
the open simplex through a point.) -/
lemma DeltaRealization.dim_le_of_cls_eq_real (R : DeltaRealization K X) (p : OpenSimplex K)
    {j : ℕ} (σ : Fin (K.card j)) (y : StdSimplex ℝ (Fin (j + 1)))
    (hy : ∀ i, 0 < y.weights i)
    (h : R.toDeltaSimplexMap.cls j σ y = R.toDeltaSimplexMap.real p) : p.dim ≤ j := by
  have hq : DeltaSimplexMap.real R.toDeltaSimplexMap (⟨j, σ, y, hy⟩ : OpenSimplex K)
      = DeltaSimplexMap.real R.toDeltaSimplexMap p := h
  have huniq := (R.bij (DeltaSimplexMap.real R.toDeltaSimplexMap p)).unique rfl hq
  rw [huniq]

/-- The general dimension bound, by induction on `j`: if
`χ.cls j σ y = real p` for an arbitrary (possibly boundary) point `y`, then
`p.dim ≤ j`. -/
lemma DeltaRealization.dim_le_aux (R : DeltaRealization K X) (p : OpenSimplex K) :
    ∀ (j : ℕ) (σ : Fin (K.card j)) (y : StdSimplex ℝ (Fin (j + 1))),
      R.toDeltaSimplexMap.cls j σ y = R.toDeltaSimplexMap.real p → p.dim ≤ j := by
  intro j
  induction j with
  | zero =>
    intro σ y h
    exact R.dim_le_of_cls_eq_real p σ y (fun i => by simp) h
  | succ j ih =>
    intro σ y h
    by_cases hall : ∀ i, 0 < y.weights i
    · exact R.dim_le_of_cls_eq_real p σ y hall h
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hi0 : y.weights i = 0 := le_antisymm (not_lt.mp hi) (y.weights_nonneg i)
      obtain ⟨y', hy'⟩ := exists_stdSimplex_map_succAbove_eq i y hi0
      have hfac := DeltaSimplexMap.cls_face R.toDeltaSimplexMap σ i y'
      rw [hy'] at hfac
      have h' : R.toDeltaSimplexMap.cls j (K.face σ i) y' = R.toDeltaSimplexMap.real p := by
        rw [hfac, h]
      exact le_trans (ih (K.face σ i) y' h') (Nat.le_succ j)

/-- **Characterization of the skeleta.**  For a realization `R` of a `Δ`-complex
`K` in `X`, a point lies in the `k`-skeleton `R.toDeltaSimplexMap.skelSet k` (the
union of the images of the closed simplices of dimension `≤ k`) if and only if
its open simplex has dimension `≤ k`.

Hints.  `x ∈ skelSet k` unfolds to `∃ j σ y, χ.cls j.1 σ y = x` with `j.2 : j.1 ≤ k`.
For `(←)`, `DeltaSimplexMap.real R.toDeltaSimplexMap p = (R.toDeltaSimplexMap.cls p.dim p.idx) p.pt`
by `rfl`, so `p` exhibits membership (with `skelSet_mono` if `p.dim < k`).  For
`(→)`, induct on `j`: the realization's bijection `R.bij x` gives the unique open
simplex `p` with `real p = x`; if all barycentric weights of `y` are positive then
`p = ⟨j, σ, y, _⟩` (since that open simplex also realizes `x`); otherwise pick `i`
with `y.weights i = 0`, write `y = StdSimplex.map (SimplexCategory.δ i) y'` for some
`y' : StdSimplex ℝ (Fin j)` (renormalize the remaining weights), and use face
compatibility (`DeltaSimplexMap.face_compat`, transported to the `StdSimplex` level
through `TopCat.toSSetObjEquiv`) to rewrite
`χ.cls j σ y = χ.cls (j-1) (K.face σ i) y'`, then apply the induction hypothesis. -/
theorem mem_skelSet_iff {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ) (x : X) :
    x ∈ R.toDeltaSimplexMap.skelSet k ↔
      ∃ p : OpenSimplex K, DeltaSimplexMap.real R.toDeltaSimplexMap p = x ∧ p.dim ≤ k := by
  constructor
  · intro hx
    rw [DeltaSimplexMap.skelSet] at hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨j, σ, y, hy⟩ := hx
    obtain ⟨p, hp, _⟩ := R.bij x
    refine ⟨p, hp, ?_⟩
    have h : R.toDeltaSimplexMap.cls j.1 σ y = R.toDeltaSimplexMap.real p := by
      rw [hy, hp]
    exact le_trans (R.dim_le_aux p j.1 σ y h) j.2
  · rintro ⟨p, hp, hpk⟩
    rw [← hp]
    exact R.toDeltaSimplexMap.skelSet_mono hpk (R.toDeltaSimplexMap.real_mem_skelSet p)

end

end Work.DeltaHomology
