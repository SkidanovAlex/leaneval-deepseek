import Mathlib
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.simplexStar_contractible
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.MayerVietoris
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.relChainsMap_homologyMap_isIso_of_interior
import Submission.Work.HomologyExtra.interior_simplexStar_union_interior_simplexCoverV

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The last-face pair map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)` is an epimorphism on relative homology

Let `B = simplexStar n` be the closed star of the last vertex of `∂Δⁿ⁺¹` and let
`Φ : (Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)` be the pair map given by the last face
(`Work.HomologyExtra.simplexFacePairHom n`).  The main result of this file is that `Φ` induces an
*epimorphism* on relative homology in degree `n`, i.e. that the class of the last face generates
`Hₙ(∂Δⁿ⁺¹, B) ≅ ℤ`.

This is the geometric input of the computation of the fundamental class of the sphere `∂Δⁿ⁺¹`:
it is what turns the class of the identity simplex of `Δⁿ` (`simplexGenMap`) into a generator of
`Hₙ(∂Δⁿ⁺¹)` (`epi_simplexBoundaryClass_of_epi_simplexGenMap`).

## Strategy

The map `Φ` is factored through the pair `(W, W ∩ B)`, where

`W = simplexCoverV n = {x ∈ ∂Δⁿ⁺¹ | x_last < 1/4}`

is the open neighbourhood of the last face already used for the Mayer–Vietoris cover.

* The **radial projection** `r : W → Δⁿ` (from the last vertex, `simplexRetractHom n`) and the
  corestriction `f : Δⁿ → W` of the last face map (`simplexFaceToCover n`) satisfy `f ≫ r = 𝟙`.
* The straight-line homotopy `x ↦ (1-λ)·(r ≫ f)(x) + λ·x` (`retractHomotopyHom n`) runs from
  `r ≫ f` to the identity of `W`; it stays inside `W` and preserves `W ∩ B`
  (`retractHomotopyStarHom n`).  Hence the pair maps
  `(Δⁿ, ∂Δⁿ) → (W, W ∩ B)` and `(W, W ∩ B) → (Δⁿ, ∂Δⁿ)` are mutually inverse up to homotopy, so
  the first one induces an isomorphism on relative homology in every degree
  (`isIso_relChainMap_facePairHomCover`).
* `interior B ∪ interior W = univ`, so the inclusion of pairs `(W, W ∩ B) → (∂Δⁿ⁺¹, B)` is a
  homology isomorphism by excision in the interior-cover form
  (`Work.Cohomology.relChainsMap_homologyMap_isIso_of_interior`).
* The composite of the two is `Φ`, so `Φ` induces an epimorphism on relative homology.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-! ## A constructor for the standard simplex from its weights -/

/-- The point of `Δ^{N-1}` with prescribed barycentric coordinates. -/
def relFacePairSimplexOfWeights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i) (h2 : ∑ i, g i = 1) :
    Convexity.StdSimplex ℝ (Fin N) :=
  ⟨Finsupp.equivFunOnFinite.symm g, fun i => by simpa using h1 i,
    by simpa [Finsupp.sum_fintype] using h2⟩

theorem relFacePairSimplexOfWeights_weights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) (i : Fin N) : (relFacePairSimplexOfWeights g h1 h2).weights i = g i := by
  simp [relFacePairSimplexOfWeights]

/-! ## The neighbourhood `W = {t < 1/4}` of the last face and the radial retraction onto `Δⁿ` -/

/-- The underlying point of the standard simplex of a point of `simplexCoverV n`. -/
abbrev coverPt (n : ℕ) (y : ↥(simplexCoverV n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) := y.1.1

/-- The last barycentric coordinate of a point of `simplexCoverV n`. -/
abbrev coverLast (n : ℕ) (y : ↥(simplexCoverV n)) : ℝ :=
  (coverPt n y).weights (Fin.last (n + 1))

theorem coverLast_lt (n : ℕ) (y : ↥(simplexCoverV n)) : coverLast n y < 1 / 4 := y.2

theorem coverLast_nonneg (n : ℕ) (y : ↥(simplexCoverV n)) : 0 ≤ coverLast n y :=
  (coverPt n y).weights_nonneg _

theorem one_sub_coverLast_pos (n : ℕ) (y : ↥(simplexCoverV n)) : 0 < 1 - coverLast n y := by
  linarith [coverLast_lt n y]

theorem sum_weights_castSucc_sub (n : ℕ) (y : ↥(simplexCoverV n)) :
    ∑ i : Fin (n + 1), (coverPt n y).weights (Fin.castSucc i) = 1 - coverLast n y := by
  have h := Fin.sum_univ_castSucc (fun j : Fin (n + 2) => (coverPt n y).weights j)
  have htot := (coverPt n y).total_of_fintype
  rw [htot] at h
  linarith [h]

/-- The barycentric coordinates of the radial projection of a point of `simplexCoverV n` onto `Δⁿ`
(from the last vertex). -/
def retractW (n : ℕ) (y : ↥(simplexCoverV n)) : Fin (n + 1) → ℝ :=
  fun i => (coverPt n y).weights (Fin.castSucc i) / (1 - coverLast n y)

theorem retractW_nonneg (n : ℕ) (y : ↥(simplexCoverV n)) : ∀ i, 0 ≤ retractW n y i := by
  intro i
  exact div_nonneg ((coverPt n y).weights_nonneg _) (le_of_lt (one_sub_coverLast_pos n y))

theorem retractW_total (n : ℕ) (y : ↥(simplexCoverV n)) : ∑ i, retractW n y i = 1 := by
  simp only [retractW]
  rw [← Finset.sum_div, sum_weights_castSucc_sub n y]
  exact div_self (ne_of_gt (one_sub_coverLast_pos n y))

/-- The radial projection of a point of `simplexCoverV n` onto `Δⁿ`. -/
def retractElem (n : ℕ) (y : ↥(simplexCoverV n)) : Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  relFacePairSimplexOfWeights (retractW n y) (retractW_nonneg n y) (retractW_total n y)

theorem retractElem_weights (n : ℕ) (y : ↥(simplexCoverV n)) (i : Fin (n + 1)) :
    (retractElem n y).weights i = retractW n y i :=
  relFacePairSimplexOfWeights_weights _ _ _ i

theorem continuous_coverPt (n : ℕ) : Continuous (coverPt n) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem continuous_coverLast (n : ℕ) : Continuous (coverLast n) :=
  (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
    (continuous_coverPt n)

theorem continuous_retractElem (n : ℕ) : Continuous (retractElem n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  change Continuous (fun y : ↥(simplexCoverV n) => (retractElem n y).weights i)
  rw [show (fun y : ↥(simplexCoverV n) => (retractElem n y).weights i) =
      fun y => retractW n y i from funext fun y => retractElem_weights n y i]
  simp only [retractW]
  exact Continuous.div
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
      (continuous_coverPt n))
    (continuous_const.sub (continuous_coverLast n))
    (fun y => ne_of_gt (one_sub_coverLast_pos n y))

/-- **The radial retraction of the neighbourhood `{t < 1/4}` of the last face onto `Δⁿ`.** -/
def simplexRetractHom (n : ℕ) : TopCat.of (simplexCoverV n) ⟶ simplex n :=
  TopCat.ofHom ⟨retractElem n, continuous_retractElem n⟩

theorem simplexRetractHom_apply (n : ℕ) (y : ↥(simplexCoverV n)) :
    (simplexRetractHom n y : Convexity.StdSimplex ℝ (Fin (n + 1))) = retractElem n y := rfl

theorem simplexRetractHom_weights (n : ℕ) (y : ↥(simplexCoverV n)) (i : Fin (n + 1)) :
    (simplexRetractHom n y).weights i = retractW n y i :=
  retractElem_weights n y i

theorem faceLast_mem_coverV (n : ℕ) (w : simplex n) :
    simplexFaceToBoundary n (Fin.last (n + 1)) w ∈ simplexCoverV n := by
  rw [mem_simplexCoverV]
  change ((simplexFace n (Fin.last (n + 1))) w).weights (Fin.last (n + 1)) < 1 / 4
  rw [weights_simplexFace_self]
  norm_num

/-- **The last face, as a map into the neighbourhood `{t < 1/4}`.** -/
def simplexFaceToCover (n : ℕ) : simplex n ⟶ TopCat.of (simplexCoverV n) :=
  TopCat.ofHom ⟨fun w => ⟨simplexFaceToBoundary n (Fin.last (n + 1)) w,
      faceLast_mem_coverV n w⟩, by fun_prop⟩

theorem coverPt_simplexFaceToCover (n : ℕ) (w : simplex n) :
    coverPt n ((simplexFaceToCover n) w) = (simplexFace n (Fin.last (n + 1))) w := rfl

theorem simplexFaceToCover_incl (n : ℕ) :
    simplexFaceToCover n ≫ Work.Homology.incl (simplexCoverV n) =
      simplexFaceToBoundary n (Fin.last (n + 1)) := by
  apply TopCat.hom_ext
  ext w
  rfl

theorem simplexFaceToCover_comp_retract (n : ℕ) :
    simplexFaceToCover n ≫ simplexRetractHom n = 𝟙 (simplex n) := by
  apply TopCat.hom_ext
  ext w i
  show (retractElem n ((simplexFaceToCover n) w)).weights i = w.weights i
  rw [retractElem_weights]
  show ((simplexFace n (Fin.last (n + 1))) w).weights (Fin.castSucc i) /
      (1 - ((simplexFace n (Fin.last (n + 1))) w).weights (Fin.last (n + 1))) = w.weights i
  rw [weights_simplexFace_last, weights_simplexFace_self]
  norm_num

theorem retractElem_mem_boundary (n : ℕ) (y : ↥(simplexCoverV n))
    (hy : (y : boundarySpace (n + 1)) ∈ simplexStar n) :
    retractElem n y ∈ simplexBoundary n := by
  obtain ⟨i, hi⟩ := mem_simplexStar.1 hy
  refine ⟨i, ?_⟩
  rw [retractElem_weights]
  show retractW n y i = 0
  rw [retractW]
  rw [show (coverPt n y).weights (Fin.castSucc i) = 0 from hi]
  simp



/-! ## The straight-line homotopy from `f ∘ r` to the identity of `W` -/

/-- The barycentric coordinates of the straight-line homotopy between
`x ↦ (f ∘ r)(x)` and the identity of `simplexCoverV n`. -/
def retractHomotopyW (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) : Fin (n + 2) → ℝ :=
  Fin.lastCases ((p.1 : ℝ) * coverLast n p.2)
    (fun i => (1 - (p.1 : ℝ)) *
        ((coverPt n p.2).weights (Fin.castSucc i) / (1 - coverLast n p.2)) +
      (p.1 : ℝ) * ((coverPt n p.2).weights (Fin.castSucc i)))

theorem retractHomotopyW_last (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    retractHomotopyW n p (Fin.last (n + 1)) = (p.1 : ℝ) * coverLast n p.2 := by
  simp [retractHomotopyW]

theorem retractHomotopyW_castSucc (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n))
    (i : Fin (n + 1)) :
    retractHomotopyW n p (Fin.castSucc i) =
      (1 - (p.1 : ℝ)) * ((coverPt n p.2).weights (Fin.castSucc i) / (1 - coverLast n p.2)) +
        (p.1 : ℝ) * ((coverPt n p.2).weights (Fin.castSucc i)) := by
  simp [retractHomotopyW]

theorem retractHomotopyW_nonneg (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    ∀ j, 0 ≤ retractHomotopyW n p j := by
  intro j
  have hlam0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have hlam1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  refine Fin.lastCases ?_ ?_ j
  · rw [retractHomotopyW_last]
    exact mul_nonneg hlam0 (coverLast_nonneg n p.2)
  · intro i
    rw [retractHomotopyW_castSucc]
    refine add_nonneg (mul_nonneg ?_ ?_) (mul_nonneg hlam0 ((coverPt n p.2).weights_nonneg _))
    · linarith
    · exact div_nonneg ((coverPt n p.2).weights_nonneg _) (le_of_lt (one_sub_coverLast_pos n p.2))

theorem retractHomotopyW_total (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    ∑ j, retractHomotopyW n p j = 1 := by
  rw [Fin.sum_univ_castSucc, retractHomotopyW_last]
  simp only [retractHomotopyW_castSucc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div,
    sum_weights_castSucc_sub]
  have hne : (1 - coverLast n p.2) ≠ 0 := ne_of_gt (one_sub_coverLast_pos n p.2)
  field_simp
  ring

def retractHomotopyElem (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  relFacePairSimplexOfWeights (retractHomotopyW n p) (retractHomotopyW_nonneg n p)
    (retractHomotopyW_total n p)

theorem retractHomotopyElem_weights (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n))
    (j : Fin (n + 2)) : (retractHomotopyElem n p).weights j = retractHomotopyW n p j :=
  relFacePairSimplexOfWeights_weights _ _ _ j

theorem coverPt_mem_boundary (n : ℕ) (y : ↥(simplexCoverV n)) :
    coverPt n y ∈ simplexBoundary (n + 1) := y.1.2

theorem retractHomotopyElem_mem_boundary (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    retractHomotopyElem n p ∈ simplexBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := coverPt_mem_boundary n p.2
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · refine ⟨Fin.castSucc i, ?_⟩
    rw [retractHomotopyElem_weights, retractHomotopyW_castSucc, hj]
    ring
  · refine ⟨Fin.last (n + 1), ?_⟩
    rw [retractHomotopyElem_weights, retractHomotopyW_last]
    simp only [coverLast, hj, mul_zero]

theorem retractHomotopyElem_mem_coverV (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) :
    (⟨retractHomotopyElem n p, retractHomotopyElem_mem_boundary n p⟩ :
      boundarySpace (n + 1)) ∈ simplexCoverV n := by
  rw [mem_simplexCoverV]
  change (retractHomotopyElem n p).weights (Fin.last (n + 1)) < 1 / 4
  rw [retractHomotopyElem_weights, retractHomotopyW_last]
  have h1 : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have h2 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  nlinarith [coverLast_lt n p.2, coverLast_nonneg n p.2]

theorem retractHomotopyElem_mem_star (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n))
    (hp : (p.2 : boundarySpace (n + 1)) ∈ simplexStar n) :
    (⟨retractHomotopyElem n p, retractHomotopyElem_mem_boundary n p⟩ :
      boundarySpace (n + 1)) ∈ simplexStar n := by
  obtain ⟨i, hi⟩ := mem_simplexStar.1 hp
  refine ⟨i, ?_⟩
  change (retractHomotopyElem n p).weights (Fin.castSucc i) = 0
  rw [retractHomotopyElem_weights, retractHomotopyW_castSucc, hi]
  ring

theorem continuous_retractHomotopyElem (n : ℕ) : Continuous (retractHomotopyElem n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun p : ↥unitInterval × ↥(simplexCoverV n) =>
    (retractHomotopyElem n p).weights j)
  rw [show (fun p : ↥unitInterval × ↥(simplexCoverV n) =>
        (retractHomotopyElem n p).weights j) =
      fun p => retractHomotopyW n p j from funext fun p => retractHomotopyElem_weights n p j]
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun p : ↥unitInterval × ↥(simplexCoverV n) =>
          retractHomotopyW n p (Fin.last (n + 1))) =
        fun p => (p.1 : ℝ) * coverLast n p.2 from funext fun p => retractHomotopyW_last n p]
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_coverLast n).comp continuous_snd)
  · intro i
    rw [show (fun p : ↥unitInterval × ↥(simplexCoverV n) =>
          retractHomotopyW n p (Fin.castSucc i)) =
        fun p => (1 - (p.1 : ℝ)) *
            ((coverPt n p.2).weights (Fin.castSucc i) / (1 - coverLast n p.2)) +
          (p.1 : ℝ) * ((coverPt n p.2).weights (Fin.castSucc i))
        from funext fun p => retractHomotopyW_castSucc n p i]
    refine Continuous.add (Continuous.mul ?_ ?_) (Continuous.mul ?_ ?_)
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    · refine Continuous.div ?_ ?_ ?_
      · exact (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
          ((continuous_coverPt n).comp continuous_snd)
      · exact continuous_const.sub ((continuous_coverLast n).comp continuous_snd)
      · intro p
        exact ne_of_gt (one_sub_coverLast_pos n p.2)
    · exact continuous_subtype_val.comp continuous_fst
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
        ((continuous_coverPt n).comp continuous_snd)

def retractHomotopyFun (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverV n)) : ↥(simplexCoverV n) :=
  ⟨⟨retractHomotopyElem n p, retractHomotopyElem_mem_boundary n p⟩,
    retractHomotopyElem_mem_coverV n p⟩

theorem continuous_retractHomotopyFun (n : ℕ) : Continuous (retractHomotopyFun n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_retractHomotopyElem n




/-! ## The homotopy from `r ≫ f` to the identity of the neighbourhood -/

/-- **The straight-line homotopy** from `r ≫ f` (the radial retraction followed by the corestriction
of the last face) to the identity of the neighbourhood `simplexCoverV n`. -/
def retractHomotopyHom (n : ℕ) :
    TopCat.Homotopy (simplexRetractHom n ≫ simplexFaceToCover n)
      (𝟙 (TopCat.of (simplexCoverV n))) where
  toFun := retractHomotopyFun n
  continuous_toFun := continuous_retractHomotopyFun n
  map_zero_left := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    apply Convexity.StdSimplex.ext
    ext j
    have h0 : ((0 : ↥unitInterval) : ℝ) = 0 := rfl
    show (retractHomotopyElem n ((0 : ↥unitInterval), y)).weights j =
      (coverPt n ((simplexFaceToCover n) ((simplexRetractHom n) y))).weights j
    refine Fin.lastCases ?_ ?_ j
    · rw [retractHomotopyElem_weights, retractHomotopyW_last, coverPt_simplexFaceToCover,
        weights_simplexFace_self, h0, zero_mul]
    · intro i
      rw [retractHomotopyElem_weights, retractHomotopyW_castSucc, coverPt_simplexFaceToCover,
        weights_simplexFace_last, simplexRetractHom_weights, retractW, h0]
      ring
  map_one_left := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    apply Convexity.StdSimplex.ext
    ext j
    have h1 : ((1 : ↥unitInterval) : ℝ) = 1 := rfl
    show (retractHomotopyElem n ((1 : ↥unitInterval), y)).weights j = (coverPt n y).weights j
    refine Fin.lastCases ?_ ?_ j
    · rw [retractHomotopyElem_weights, retractHomotopyW_last, h1, one_mul]
    · intro i
      rw [retractHomotopyElem_weights, retractHomotopyW_castSucc, h1]
      ring

/-- The points of the neighbourhood `simplexCoverV n` that lie in the closed star of the last
vertex, i.e. the subspace `W ∩ B` of the pair `(W, W ∩ B)`. -/
def simplexCoverStar (n : ℕ) : Set ↥(simplexCoverV n) :=
  {y | (y : boundarySpace (n + 1)) ∈ simplexStar n}

theorem mem_simplexCoverStar {n : ℕ} {y : ↥(simplexCoverV n)} :
    y ∈ simplexCoverStar n ↔ (y : boundarySpace (n + 1)) ∈ simplexStar n := Iff.rfl

/-! ## The map of pairs `(Δⁿ, ∂Δⁿ) → (W, W ∩ B)` and its retraction -/

/-- The pair map `(Δⁿ, ∂Δⁿ) → (W, W ∩ star)` given by the last face, corestricted to `W`. -/
def simplexFacePairHomCover (n : ℕ) :
    Work.Homology.PairHom (simplex n) (TopCat.of (simplexCoverV n)) (simplexBoundary n)
      (simplexCoverStar n) where
  hom := simplexFaceToCover n
  mapsTo := by
    intro w hw
    show ((simplexFaceToCover n) w : boundarySpace (n + 1)) ∈ simplexStar n
    have h : ((simplexFaceToCover n) w : boundarySpace (n + 1)) =
        simplexFaceToBoundary n (Fin.last (n + 1)) w := rfl
    rw [h]
    exact (simplexFacePairHom n).mapsTo w hw

/-- The pair map `(W, W ∩ star) → (Δⁿ, ∂Δⁿ)` given by the radial retraction. -/
def simplexRetractPairHom (n : ℕ) :
    Work.Homology.PairHom (TopCat.of (simplexCoverV n)) (simplex n) (simplexCoverStar n)
      (simplexBoundary n) where
  hom := simplexRetractHom n
  mapsTo := fun y hy => retractElem_mem_boundary n y hy

theorem simplexRetractPairHom_sub_apply (n : ℕ) (y : ↥(simplexCoverStar n)) :
    ((simplexRetractPairHom n).sub y : ↥(simplex n)) = simplexRetractHom n (y : ↥(simplexCoverV n)) :=
  rfl

theorem simplexFacePairHomCover_sub_apply (n : ℕ) (y : ↥(simplexBoundary n)) :
    ((simplexFacePairHomCover n).sub y : ↥(simplexCoverV n)) =
      simplexFaceToCover n y := rfl

theorem simplexFacePairHomCover_sub_comp_retract_sub (n : ℕ) :
    (simplexFacePairHomCover n).sub ≫ (simplexRetractPairHom n).sub =
      𝟙 (TopCat.of (simplexBoundary n)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun g : simplex n ⟶ simplex n => g (x : ↥(simplex n)))
    (simplexFaceToCover_comp_retract n)

/-- The homotopy of pairs witnessing that the radial retraction inverts the last-face map. -/
def retractHomotopyStarFun (n : ℕ) (p : ↥unitInterval × ↥(simplexCoverStar n)) :
    ↥(simplexCoverStar n) :=
  ⟨retractHomotopyFun n (p.1, (p.2 : ↥(simplexCoverV n))),
    (mem_simplexCoverStar).2 (retractHomotopyElem_mem_star n (p.1, (p.2 : ↥(simplexCoverV n))) p.2.2)⟩

theorem continuous_retractHomotopyStarFun (n : ℕ) : Continuous (retractHomotopyStarFun n) := by
  apply Continuous.subtype_mk
  exact (continuous_retractHomotopyFun n).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- **The homotopy of the pair `(W, W ∩ star)`** from `r ≫ f` to the identity. -/
def retractHomotopyStarHom (n : ℕ) :
    TopCat.Homotopy ((simplexRetractPairHom n).sub ≫ (simplexFacePairHomCover n).sub)
      (𝟙 (TopCat.of (simplexCoverStar n))) where
  toFun := retractHomotopyStarFun n
  continuous_toFun := continuous_retractHomotopyStarFun n
  map_zero_left := by
    intro y
    apply Subtype.ext
    exact (retractHomotopyHom n).map_zero_left (y : ↥(simplexCoverV n))
  map_one_left := by
    intro y
    apply Subtype.ext
    exact (retractHomotopyHom n).map_one_left (y : ↥(simplexCoverV n))

/-! ## The homotopies of the components of the pair map -/

def homotopy_faceToCover_comp_retract (n : ℕ) :
    TopCat.Homotopy (simplexFaceToCover n ≫ simplexRetractHom n) (𝟙 (simplex n)) := by
  rw [simplexFaceToCover_comp_retract]
  exact ContinuousMap.Homotopy.refl _

def homotopy_retract_comp_faceToCover (n : ℕ) :
    TopCat.Homotopy (simplexRetractHom n ≫ simplexFaceToCover n)
      (𝟙 (TopCat.of (simplexCoverV n))) :=
  retractHomotopyHom n

def homotopy_faceSub_comp_retractSub (n : ℕ) :
    TopCat.Homotopy ((simplexFacePairHomCover n).sub ≫ (simplexRetractPairHom n).sub)
      (𝟙 (TopCat.of (simplexBoundary n))) := by
  rw [simplexFacePairHomCover_sub_comp_retract_sub]
  exact ContinuousMap.Homotopy.refl _

def homotopy_retractSub_comp_faceSub (n : ℕ) :
    TopCat.Homotopy ((simplexRetractPairHom n).sub ≫ (simplexFacePairHomCover n).sub)
      (𝟙 (TopCat.of (simplexCoverStar n))) :=
  retractHomotopyStarHom n

/-! ## Quasi-isomorphisms of the components of the pair map -/

theorem isIso_homologyMap_chainMap_faceToCover (n k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (simplex n) (TopCat.of (simplexCoverV n))
        (simplexFaceToCover n)) k) :=
  Work.Cohomology.homologyEquiv ℤ (simplex n) (TopCat.of (simplexCoverV n))
    (simplexFaceToCover n) (simplexRetractHom n) (homotopy_faceToCover_comp_retract n)
    (homotopy_retract_comp_faceToCover n) k

theorem isIso_homologyMap_chainMap_faceSub (n k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (simplexBoundary n))
        (TopCat.of (simplexCoverStar n)) (simplexFacePairHomCover n).sub) k) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of (simplexBoundary n))
    (TopCat.of (simplexCoverStar n)) ((simplexFacePairHomCover n).sub)
    ((simplexRetractPairHom n).sub) (homotopy_faceSub_comp_retractSub n)
    (homotopy_retractSub_comp_faceSub n) k

/-! ## The pair map `(Δⁿ, ∂Δⁿ) → (W, W ∩ B)` is a homology isomorphism -/

/-- Compatibility of the two inclusions with the pair map, in the form required by
`Work.Cohomology.relChainsMapOf`. -/
theorem simplexFacePairHomCover_sub_comp_subtypeIncl (n : ℕ) :
    Work.Cohomology.subtypeIncl (simplex n) (simplexBoundary n) ≫
        (simplexFacePairHomCover n).hom =
      (simplexFacePairHomCover n).sub ≫
        Work.Cohomology.subtypeIncl (TopCat.of (simplexCoverV n)) (simplexCoverStar n) :=
  (Work.Homology.PairHom.sub_comp_incl (simplexFacePairHomCover n)).symm

theorem relProj_comp_relChainsMapOf (n : ℕ) :
    Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n) ≫
        Work.Cohomology.relChainsMapOf (simplex n) (TopCat.of (simplexCoverV n))
          (simplexBoundary n) (simplexCoverStar n) (simplexFacePairHomCover n).hom
          (simplexFacePairHomCover n).sub (simplexFacePairHomCover_sub_comp_subtypeIncl n) =
      Work.Homology.singChainMap Work.Homology.ZMod (simplexFacePairHomCover n).hom ≫
        Work.Homology.relProj Work.Homology.ZMod (TopCat.of (simplexCoverV n))
          (simplexCoverStar n) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains (simplex n)
    (simplexBoundary n)) (Work.Cohomology.inclChains (TopCat.of (simplexCoverV n))
      (simplexCoverStar n)) (Work.Cohomology.chainMap ℤ (TopCat.of (simplexBoundary n))
        (TopCat.of (simplexCoverStar n)) (simplexFacePairHomCover n).sub)
      (Work.Cohomology.chainMap ℤ (simplex n) (TopCat.of (simplexCoverV n))
        (simplexFacePairHomCover n).hom) _

theorem relChainMap_facePairHomCover_eq (n : ℕ) :
    Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n) =
      Work.Cohomology.relChainsMapOf (simplex n) (TopCat.of (simplexCoverV n))
        (simplexBoundary n) (simplexCoverStar n) (simplexFacePairHomCover n).hom
        (simplexFacePairHomCover n).sub (simplexFacePairHomCover_sub_comp_subtypeIncl n) := by
  apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod (simplex n)
    (simplexBoundary n))).1
  rw [← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod)
    (simplexFacePairHomCover n)]
  exact (relProj_comp_relChainsMapOf n).symm

theorem isIso_relChainMap_facePairHomCover (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n)) n) := by
  rw [relChainMap_facePairHomCover_eq n]
  exact Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := simplex n)
    (Y := TopCat.of (simplexCoverV n)) (A := simplexBoundary n) (B := simplexCoverStar n)
    (f := (simplexFacePairHomCover n).hom) (g := (simplexFacePairHomCover n).sub)
    (simplexFacePairHomCover_sub_comp_subtypeIncl n) n
    (isIso_homologyMap_chainMap_faceToCover n) (isIso_homologyMap_chainMap_faceSub n)

/-! ## The inclusion of pairs `(W, W ∩ B) → (X, B)` -/

def simplexCoverInclPairHom (n : ℕ) :
    Work.Homology.PairHom (TopCat.of (simplexCoverV n)) (boundarySpace (n + 1))
      (simplexCoverStar n) (simplexStar n) where
  hom := Work.Homology.incl (simplexCoverV n)
  mapsTo := by
    intro y hy
    change (Work.Homology.incl (simplexCoverV n) y : boundarySpace (n + 1)) ∈ simplexStar n
    rw [Work.Homology.incl_apply]
    exact hy

theorem relProj_comp_relChainsMap (n : ℕ) :
    Work.Homology.relProj Work.Homology.ZMod (TopCat.of (simplexCoverV n))
        (simplexCoverStar n) ≫
        Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
          (simplexStar n) =
      Work.Homology.singChainMap Work.Homology.ZMod (Work.Homology.incl (simplexCoverV n)) ≫
        Work.Homology.relProj Work.Homology.ZMod (boundarySpace (n + 1)) (simplexStar n) :=
  Work.Cohomology.cokernel_π_relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
    (simplexStar n)

theorem relChainMap_simplexCoverInclPairHom (n : ℕ) :
    Work.Homology.relChainMap Work.Homology.ZMod (simplexCoverInclPairHom n) =
      Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
        (simplexStar n) := by
  apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod (TopCat.of (simplexCoverV n))
    (simplexCoverStar n))).1
  rw [← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod)
    (simplexCoverInclPairHom n)]
  exact (relProj_comp_relChainsMap n).symm

/-! ## The factorization of the last-face pair map -/

theorem relChainMap_simplexFacePairHom_comp_eq (n : ℕ) :
    Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n) ≫
        Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
          (simplexStar n) =
      Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHom n) := by
  apply (cancel_epi (Work.Homology.relProj Work.Homology.ZMod (simplex n)
    (simplexBoundary n))).1
  calc Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n) ≫
        (Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n) ≫
          Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
            (simplexStar n))
      = (Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n) ≫
          Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n)) ≫
            Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
              (simplexStar n) := (Category.assoc _ _ _).symm
    _ = (Work.Homology.singChainMap Work.Homology.ZMod (simplexFacePairHomCover n).hom ≫
          Work.Homology.relProj Work.Homology.ZMod (TopCat.of (simplexCoverV n))
            (simplexCoverStar n)) ≫
            Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
              (simplexStar n) := by
        rw [← Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod)
          (simplexFacePairHomCover n)]
    _ = Work.Homology.singChainMap Work.Homology.ZMod (simplexFacePairHomCover n).hom ≫
          (Work.Homology.relProj Work.Homology.ZMod (TopCat.of (simplexCoverV n))
            (simplexCoverStar n) ≫
            Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
              (simplexStar n)) := Category.assoc _ _ _
    _ = Work.Homology.singChainMap Work.Homology.ZMod (simplexFacePairHomCover n).hom ≫
          (Work.Homology.singChainMap Work.Homology.ZMod (Work.Homology.incl (simplexCoverV n)) ≫
            Work.Homology.relProj Work.Homology.ZMod (boundarySpace (n + 1))
              (simplexStar n)) := by
        rw [relProj_comp_relChainsMap n]
    _ = (Work.Homology.singChainMap Work.Homology.ZMod (simplexFacePairHomCover n).hom ≫
          Work.Homology.singChainMap Work.Homology.ZMod (Work.Homology.incl (simplexCoverV n))) ≫
            Work.Homology.relProj Work.Homology.ZMod (boundarySpace (n + 1))
              (simplexStar n) := (Category.assoc _ _ _).symm
    _ = Work.Homology.singChainMap Work.Homology.ZMod
          ((simplexFacePairHomCover n).hom ≫ Work.Homology.incl (simplexCoverV n)) ≫
            Work.Homology.relProj Work.Homology.ZMod (boundarySpace (n + 1))
              (simplexStar n) := by
        rw [Work.Homology.singChainMap_comp]
    _ = Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n) ≫
          Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHom n) := by
        rw [show (simplexFacePairHomCover n).hom ≫ Work.Homology.incl (simplexCoverV n) =
            (simplexFacePairHom n).hom from simplexFaceToCover_incl n,
          Work.Homology.relChainMap_comp_relProj (R := Work.Homology.ZMod)
            (simplexFacePairHom n)]

theorem relChainMap_simplexFacePairHom_eq (n : ℕ) :
    Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHom n) =
      Work.Homology.relChainMap Work.Homology.ZMod (simplexFacePairHomCover n) ≫
        Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
          (simplexStar n) :=
  (relChainMap_simplexFacePairHom_comp_eq n).symm

/-! ## The main theorem -/

/-- **The pair map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)` induces an epimorphism on relative homology in
degree `n`.**  This is the geometric input of the computation of the fundamental class of the
sphere: the last face `F` of `∂Δⁿ⁺¹` (a closed disc whose boundary is the equator) generates
`Hₙ(∂Δⁿ⁺¹, B)`, where `B` is the closed star of the last vertex.

Proof.  Let `W = {x ∈ ∂Δⁿ⁺¹ | x_last < 1/4}` be the open neighbourhood of the last face and let
`B` be the closed star.  The radial projection `r : W → Δⁿ` (from the last vertex) and the
corestriction `f : Δⁿ → W` of the last face map satisfy `f ≫ r = 𝟙`, and the straight-line
homotopy `(1-λ)·(r ≫ f)(x) + λ·x` joins `r ≫ f` to the identity of `W`; it stays in `W` and in
`W ∩ B`.  Hence the pair maps `(Δⁿ, ∂Δⁿ) → (W, W ∩ B)` and `(W, W ∩ B) → (Δⁿ, ∂Δⁿ)` are mutually
inverse up to homotopy, so the first induces an isomorphism on relative homology
(`relChainsMapOf_homologyMap_isIso`).  Finally `interior B ∪ interior W = univ`, so excision
(`relChainsMap_homologyMap_isIso_of_interior`) shows that the inclusion of pairs
`(W, W ∩ B) → (∂Δⁿ⁺¹, B)` is also a homology isomorphism; the composite is the last-face pair
map, which is therefore an epimorphism. -/
theorem relHomologyMap_simplexFacePairHom_epi (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Epi (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (Work.HomologyExtra.simplexFacePairHom n)) := by
  haveI hΦ' : CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (simplexFacePairHomCover n)) :=
    isIso_relChainMap_facePairHomCover n
  haveI hR : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
        (simplexStar n)) n) :=
    Work.Cohomology.relChainsMap_homologyMap_isIso_of_interior (boundarySpace (n + 1))
      (simplexCoverV n) (simplexStar n)
      (interior_simplexStar_union_interior_simplexCoverV n) n
  haveI hR' : CategoryTheory.Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
        (simplexStar n)) n) := IsIso.epi_of_iso _
  rw [show Work.Homology.relHomologyMap Work.Homology.ZMod n
        (Work.HomologyExtra.simplexFacePairHom n) =
      Work.Homology.relHomologyMap Work.Homology.ZMod n (simplexFacePairHomCover n) ≫
        HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (boundarySpace (n + 1))
          (simplexCoverV n) (simplexStar n)) n from ?_]
  · exact epi_comp _ _
  · rw [Work.Homology.relHomologyMap, relChainMap_simplexFacePairHom_eq n,
      HomologicalComplex.homologyMap_comp]

/-- **The last-face pair map induces an isomorphism on relative homology in degree `n`**, i.e. the
class of the last face is a *generator* of `Hₙ(∂Δⁿ⁺¹, B) ≅ ℤ`.  This is the companion of
`relHomologyMap_simplexFacePairHom_epi`: both factors of the factorization of `Φ` are
isomorphisms, so `Φ` is one. -/
theorem relHomologyMap_simplexFacePairHom_isIso (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (Work.HomologyExtra.simplexFacePairHom n)) := by
  haveI h1 : CategoryTheory.IsIso (Work.Homology.relHomologyMap Work.Homology.ZMod n
      (simplexFacePairHomCover n)) :=
    isIso_relChainMap_facePairHomCover n
  haveI h2 : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap (boundarySpace (n + 1)) (simplexCoverV n)
        (simplexStar n)) n) :=
    Work.Cohomology.relChainsMap_homologyMap_isIso_of_interior (boundarySpace (n + 1))
      (simplexCoverV n) (simplexStar n)
      (interior_simplexStar_union_interior_simplexCoverV n) n
  rw [show Work.Homology.relHomologyMap Work.Homology.ZMod n
        (Work.HomologyExtra.simplexFacePairHom n) =
      Work.Homology.relHomologyMap Work.Homology.ZMod n (simplexFacePairHomCover n) ≫
        HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (boundarySpace (n + 1))
          (simplexCoverV n) (simplexStar n)) n from ?_]
  · infer_instance
  · rw [Work.Homology.relHomologyMap, relChainMap_simplexFacePairHom_eq n,
      HomologicalComplex.homologyMap_comp]

end

end Work.HomologyExtra
