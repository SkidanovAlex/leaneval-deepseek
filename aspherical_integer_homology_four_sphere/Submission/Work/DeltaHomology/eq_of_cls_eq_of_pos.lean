import Mathlib
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.SkelSet
import Submission.Work.DeltaHomology.mem_skelSet_iff

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

/-- **Interior points of a top-dimensional open simplex.**  If a point `y` of the standard
`n`-simplex — with no positivity hypothesis — is carried by the characteristic map of an
`n`-simplex `σ` to the realization of an open simplex `q` of dimension `n`, then all the
barycentric weights of `y` are strictly positive.  Equivalently, the characteristic map of
an `n`-simplex meets a *top*-dimensional open simplex only in its interior.

The proof reduces along a vanishing barycentric weight: if `y.weights i = 0` then the point
lies on the `i`-th face, `cls n σ y = cls (n-1) (K.face σ i) y''`, hence is a point of the
`(n-1)`-skeleton, so by `mem_skelSet_iff` it is realized by an open simplex of dimension
`≤ n-1` — contradicting `q.dim = n`. -/
lemma DeltaRealization.interior_of_cls_eq_real {n : ℕ} (R : DeltaRealization K X)
    (q : OpenSimplex K) (hqn : q.dim = n) (σ : Fin (K.card n))
    (y : StdSimplex ℝ (Fin (n + 1)))
    (h : R.toDeltaSimplexMap.cls n σ y = R.toDeltaSimplexMap.real q) :
    ∀ i, 0 < y.weights i := by
  rcases n with _ | m
  · intro i
    simp
  · intro i
    by_contra hi
    have hi0 : y.weights i = 0 := le_antisymm (not_lt.mp hi) (y.weights_nonneg i)
    obtain ⟨y'', hy''⟩ := exists_stdSimplex_map_succAbove_eq (n := m + 1) i y hi0
    have hfac := DeltaSimplexMap.cls_face R.toDeltaSimplexMap (k := m) σ i y''
    rw [hy''] at hfac
    have hmem : R.toDeltaSimplexMap.real q ∈ R.toDeltaSimplexMap.skelSet m := by
      rw [← h, ← hfac]
      exact R.toDeltaSimplexMap.cls_mem_skelSet le_rfl (K.face σ i) y''
    obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R m (R.toDeltaSimplexMap.real q)).mp hmem
    have hpq : p = q := (R.bij (R.toDeltaSimplexMap.real q)).unique hp rfl
    have : q.dim ≤ m := hpq ▸ hpd
    omega

/-- **Interior rigidity of characteristic maps.**  If an interior point `y` of the standard
`n`-simplex realizes the same point of `X` as an arbitrary point `y'` under the characteristic
map of a closed `n`-simplex `σ'`, then `σ = σ'` and `y = y'`.  (In particular `χ` is injective on
the interior of a closed simplex and the simplex index is determined by the point.) -/
theorem eq_of_cls_eq_of_pos {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    {n : ℕ} {σ σ' : Fin (K.card n)} {y y' : StdSimplex ℝ (Fin (n + 1))}
    (hy : ∀ i, 0 < y.weights i)
    (h : R.toDeltaSimplexMap.cls n σ y = R.toDeltaSimplexMap.cls n σ' y') :
    σ = σ' ∧ y = y' := by
  -- The unique open simplex realizing the common point.
  obtain ⟨q, hq, hquniq⟩ := R.bij (R.toDeltaSimplexMap.cls n σ y)
  have hqq : q = ⟨n, σ, y, hy⟩ := (hquniq ⟨n, σ, y, hy⟩ rfl).symm
  have hqdim : q.dim = n := by rw [hqq]
  -- The other point `y'` must be interior too.
  have hy' : ∀ i, 0 < y'.weights i := by
    apply R.interior_of_cls_eq_real q hqdim σ' y'
    show R.toDeltaSimplexMap.cls n σ' y' = R.toDeltaSimplexMap.real q
    rw [hq, h]
  -- Hence it defines an open simplex realizing the same point, so the two coincide.
  have hreal : R.toDeltaSimplexMap.real (⟨n, σ', y', hy'⟩ : OpenSimplex K)
      = R.toDeltaSimplexMap.cls n σ y := by
    show R.toDeltaSimplexMap.cls n σ' y' = R.toDeltaSimplexMap.cls n σ y
    rw [h]
  have hEq2 : (⟨n, σ', y', hy'⟩ : OpenSimplex K) = ⟨n, σ, y, hy⟩ :=
    (hquniq ⟨n, σ', y', hy'⟩ hreal).trans hqq
  have hidx : σ' = σ := by
    have h := congrArg (fun p : OpenSimplex K => (p.idx).val) hEq2
    exact Fin.ext h
  have hpt : y' = y := by
    have hheq : HEq (⟨n, σ', y', hy'⟩ : OpenSimplex K).pt (⟨n, σ, y, hy⟩ : OpenSimplex K).pt := by
      cases hEq2
      exact HEq.rfl
    exact eq_of_heq hheq
  exact ⟨hidx.symm, hpt.symm⟩

end

end Work.DeltaHomology
