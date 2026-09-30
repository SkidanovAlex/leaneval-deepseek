import Mathlib
import Submission.Work.HomologyExtra.SimplexFaceSetup
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inclusion of the equator into its collar is a homotopy equivalence

Let `∂Δⁿ⁺¹` be the boundary of the standard `(n+1)`-simplex and let

* `simplexEquator n = {x : ∂Δⁿ⁺¹ | x_last = 0 ∧ ∃ i ≠ last, x_i = 0}`, the equator `E`;
* `simplexStar n = {x : ∂Δⁿ⁺¹ | ∃ i ≠ last, x_i = 0}`, the union of the faces opposite the last
  vertex, and `simplexSouthCap n = {x | x_last < 1}`;
* `simplexCollar n = simplexStar n ∩ simplexSouthCap n`, the collar `T` of `E` inside `simplexStar`.

`Work.HomologyExtra.equatorInCollar n : E ⟶ T` is the inclusion of the equator into the collar.
This file proves that it is a homotopy equivalence.

The homotopy inverse is the radial projection away from the last vertex

`collarProjFun x`: `(collarProjFun x)_last = 0`, `(collarProjFun x)_i = x_i / (1 - x_last)`
(`i ≠ last`), which is well defined on the collar because `x_last < 1` there; the vanishing
coordinate `x_i = 0` witnessing `x ∈ simplexStar n` survives the renormalization, so the projection
lands in the equator.  The composite `collarProjFun ∘ equatorInCollar` is the identity of `E`
(the last coordinate of a point of `E` is `0`), while `equatorInCollar ∘ collarProjFun` is homotopic
to the identity of `T` through the straight line homotopy

`H_s(x) = (1-s) · x + s · collarProjFun x`,

which stays inside the collar: the vanishing coordinate stays `0`, and the last coordinate
`(1-s) x_last` stays `< 1`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-! ## A standard simplex element from its coordinates -/

private def stdSimplexMk {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i) (h2 : ∑ i, g i = 1) :
    Convexity.StdSimplex ℝ (Fin N) :=
  ⟨Finsupp.equivFunOnFinite.symm g, fun i => by simpa using h1 i,
    by simpa [Finsupp.sum_fintype] using h2⟩

private theorem stdSimplexMk_weights {N : ℕ} (g : Fin N → ℝ) (h1 : ∀ i, 0 ≤ g i)
    (h2 : ∑ i, g i = 1) (i : Fin N) :
    (stdSimplexMk g h1 h2).weights i = g i := by
  simp [stdSimplexMk]

private theorem sum_weights_castSucc {N : ℕ} (w : Convexity.StdSimplex ℝ (Fin (N + 1))) :
    ∑ i : Fin N, w.weights (Fin.castSucc i) + w.weights (Fin.last N) = 1 := by
  rw [← Fin.sum_univ_castSucc (fun j => w.weights j)]
  exact w.total_of_fintype

variable (n : ℕ)

/-! ## Coordinates of a point of the collar -/

private abbrev collarPt (x : ↥(simplexCollar n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  x.1.1.1

private abbrev collarLast (x : ↥(simplexCollar n)) : ℝ := (collarPt n x).weights (Fin.last (n + 1))

private theorem collarLast_lt_one (x : ↥(simplexCollar n)) : collarLast n x < 1 := x.1.2

private theorem star_exists (x : ↥(simplexCollar n)) :
    ∃ i : Fin (n + 1), (collarPt n x).weights (Fin.castSucc i) = 0 := x.2

private theorem one_sub_collarLast_pos (x : ↥(simplexCollar n)) : 0 < 1 - collarLast n x :=
  sub_pos.mpr (collarLast_lt_one n x)

/-! ## The radial projection of the collar onto the equator -/

/-- The barycentric coordinates of the projection of a collar point away from the last vertex. -/
private def collarProjW (x : ↥(simplexCollar n)) : Fin (n + 2) → ℝ :=
  Fin.lastCases 0 (fun i => (collarPt n x).weights (Fin.castSucc i) / (1 - collarLast n x))

private theorem collarProjW_last (x : ↥(simplexCollar n)) :
    collarProjW n x (Fin.last (n + 1)) = 0 := by
  simp [collarProjW]

private theorem collarProjW_castSucc (x : ↥(simplexCollar n)) (i : Fin (n + 1)) :
    collarProjW n x (Fin.castSucc i) =
      (collarPt n x).weights (Fin.castSucc i) / (1 - collarLast n x) := by
  simp [collarProjW]

private theorem collarProjW_nonneg (x : ↥(simplexCollar n)) : ∀ j, 0 ≤ collarProjW n x j := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · rw [collarProjW_last]
  · intro i
    rw [collarProjW_castSucc]
    exact div_nonneg ((collarPt n x).weights_nonneg _) (le_of_lt (one_sub_collarLast_pos n x))

private theorem collarProjW_total (x : ↥(simplexCollar n)) : ∑ j, collarProjW n x j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [collarProjW_last, collarProjW_castSucc, add_zero]
  rw [← Finset.sum_div]
  rw [show ∑ i : Fin (n + 1), (collarPt n x).weights (Fin.castSucc i) = 1 - collarLast n x from by
    linarith [sum_weights_castSucc (collarPt n x)]]
  exact div_self (ne_of_gt (one_sub_collarLast_pos n x))

private def collarProjElem (x : ↥(simplexCollar n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  stdSimplexMk (collarProjW n x) (collarProjW_nonneg n x) (collarProjW_total n x)

private theorem collarProjElem_weights (x : ↥(simplexCollar n)) (j : Fin (n + 2)) :
    (collarProjElem n x).weights j = collarProjW n x j :=
  stdSimplexMk_weights _ _ _ j

private theorem collarProjElem_mem_boundary (x : ↥(simplexCollar n)) :
    collarProjElem n x ∈ simplexBoundary (n + 1) :=
  ⟨Fin.last (n + 1), by rw [collarProjElem_weights, collarProjW_last]⟩

private theorem collarProjElem_mem_lastFace (x : ↥(simplexCollar n)) :
    (⟨collarProjElem n x, collarProjElem_mem_boundary n x⟩ : ↥(boundarySpace (n + 1))) ∈
      simplexLastFace n := by
  rw [mem_simplexLastFace, collarProjElem_weights, collarProjW_last]

private theorem collarProjElem_mem_equator (x : ↥(simplexCollar n)) :
    (⟨collarProjElem n x, collarProjElem_mem_boundary n x⟩ : ↥(boundarySpace (n + 1))) ∈
      simplexEquator n := by
  constructor
  · rw [collarProjElem_weights, collarProjW_last]
  · obtain ⟨i, hi⟩ := star_exists n x
    exact ⟨i, by rw [collarProjElem_weights, collarProjW_castSucc, hi, zero_div]⟩

/-- The radial projection of the collar onto the equator, as a function. -/
private def collarProjFun (x : ↥(simplexCollar n)) : ↥(equatorInLastFace n) :=
  ⟨⟨⟨collarProjElem n x, collarProjElem_mem_boundary n x⟩, collarProjElem_mem_lastFace n x⟩,
    collarProjElem_mem_equator n x⟩

private theorem continuous_collarPt :
    Continuous (fun x : ↥(simplexCollar n) => collarPt n x) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)

private theorem continuous_collarLast :
    Continuous (fun x : ↥(simplexCollar n) => collarLast n x) :=
  (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
    (continuous_collarPt n)

private theorem continuous_collarProjElem :
    Continuous (fun x : ↥(simplexCollar n) => collarProjElem n x) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun x : ↥(simplexCollar n) => (collarProjElem n x).weights j)
  rw [show (fun x : ↥(simplexCollar n) => (collarProjElem n x).weights j) =
      fun x => collarProjW n x j from funext fun x => collarProjElem_weights n x j]
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun x : ↥(simplexCollar n) => collarProjW n x (Fin.last (n + 1))) = fun _ => (0 : ℝ)
      from funext fun x => collarProjW_last n x]
    exact continuous_const
  · intro i
    rw [show (fun x : ↥(simplexCollar n) => collarProjW n x (Fin.castSucc i)) =
        fun x => (collarPt n x).weights (Fin.castSucc i) / (1 - collarLast n x)
      from funext fun x => collarProjW_castSucc n x i]
    refine Continuous.div ?_ ?_ ?_
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
        (continuous_collarPt n)
    · exact continuous_const.sub (continuous_collarLast n)
    · intro x
      exact ne_of_gt (one_sub_collarLast_pos n x)

private theorem continuous_collarProjFun :
    Continuous (fun x : ↥(simplexCollar n) => collarProjFun n x) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_collarProjElem n

/-! ## The projection is a left inverse of the inclusion -/

private theorem collarPt_equatorInCollar (y : ↥(equatorInLastFace n)) :
    collarPt n (equatorInCollar n y) = (↑↑↑y : Convexity.StdSimplex ℝ (Fin (n + 2))) := rfl

private theorem collarLast_equatorInCollar (y : ↥(equatorInLastFace n)) :
    collarLast n (equatorInCollar n y) =
      (↑↑↑y : Convexity.StdSimplex ℝ (Fin (n + 2))).weights (Fin.last (n + 1)) := rfl

private theorem collarProjElem_equatorInCollar (y : ↥(equatorInLastFace n)) :
    collarProjElem n (equatorInCollar n y) =
      (↑↑↑y : Convexity.StdSimplex ℝ (Fin (n + 2))) := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  rw [collarProjElem_weights]
  refine Fin.lastCases ?_ ?_ j
  · rw [collarProjW_last]
    exact ((y.2).1).symm
  · intro i
    rw [collarProjW_castSucc, collarPt_equatorInCollar n y, collarLast_equatorInCollar n y,
      (y.2).1]
    simp

private theorem collarProjFun_equatorInCollar (y : ↥(equatorInLastFace n)) :
    collarProjFun n (equatorInCollar n y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact collarProjElem_equatorInCollar n y

/-! ## The straight-line homotopy from the inclusion of the projection to the identity of the collar -/

private def collarHomotopyW (s : unitInterval) (x : ↥(simplexCollar n)) : Fin (n + 2) → ℝ :=
  fun j => (1 - (s : ℝ)) * (collarProjElem n x).weights j + (s : ℝ) * (collarPt n x).weights j

private theorem collarHomotopyW_nonneg (s : unitInterval) (x : ↥(simplexCollar n)) :
    ∀ j, 0 ≤ collarHomotopyW n s x j := by
  intro j
  rw [collarHomotopyW]
  exact add_nonneg
    (mul_nonneg (by linarith [s.2.2]) ((collarProjElem n x).weights_nonneg j))
    (mul_nonneg s.2.1 ((collarPt n x).weights_nonneg j))

private theorem collarHomotopyW_total (s : unitInterval) (x : ↥(simplexCollar n)) :
    ∑ j, collarHomotopyW n s x j = 1 := by
  simp only [collarHomotopyW]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    (collarProjElem n x).total_of_fintype, (collarPt n x).total_of_fintype]
  ring

private def collarHomotopyElem (s : unitInterval) (x : ↥(simplexCollar n)) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  stdSimplexMk (collarHomotopyW n s x) (collarHomotopyW_nonneg n s x) (collarHomotopyW_total n s x)

private theorem collarHomotopyElem_weights (s : unitInterval) (x : ↥(simplexCollar n))
    (j : Fin (n + 2)) :
    (collarHomotopyElem n s x).weights j = collarHomotopyW n s x j :=
  stdSimplexMk_weights _ _ _ j

private theorem collarProjElem_at_star (x : ↥(simplexCollar n)) (i : Fin (n + 1))
    (hi : (collarPt n x).weights (Fin.castSucc i) = 0) :
    (collarProjElem n x).weights (Fin.castSucc i) = 0 := by
  rw [collarProjElem_weights, collarProjW_castSucc, hi, zero_div]

private theorem collarHomotopyElem_mem_boundary (s : unitInterval) (x : ↥(simplexCollar n)) :
    collarHomotopyElem n s x ∈ simplexBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := star_exists n x
  refine ⟨Fin.castSucc i, ?_⟩
  rw [collarHomotopyElem_weights, collarHomotopyW, collarProjElem_at_star n x i hi, hi]
  ring

private theorem collarHomotopyElem_mem_southCap (s : unitInterval) (x : ↥(simplexCollar n)) :
    (⟨collarHomotopyElem n s x, collarHomotopyElem_mem_boundary n s x⟩ :
        ↥(boundarySpace (n + 1))) ∈ simplexSouthCap n := by
  show (collarHomotopyElem n s x).weights (Fin.last (n + 1)) < 1
  rw [collarHomotopyElem_weights, collarHomotopyW,
    show (collarProjElem n x).weights (Fin.last (n + 1)) = 0 from by
      rw [collarProjElem_weights, collarProjW_last]]
  rw [mul_zero, zero_add]
  calc (s : ℝ) * (collarPt n x).weights (Fin.last (n + 1))
      ≤ 1 * (collarPt n x).weights (Fin.last (n + 1)) :=
        mul_le_mul_of_nonneg_right s.2.2 ((collarPt n x).weights_nonneg _)
    _ = collarLast n x := one_mul _
    _ < 1 := collarLast_lt_one n x

private theorem collarHomotopyElem_mem_star (s : unitInterval) (x : ↥(simplexCollar n)) :
    (⟨collarHomotopyElem n s x, collarHomotopyElem_mem_boundary n s x⟩ :
        ↥(boundarySpace (n + 1))) ∈ simplexStar n := by
  obtain ⟨i, hi⟩ := star_exists n x
  refine ⟨i, ?_⟩
  show (collarHomotopyElem n s x).weights (Fin.castSucc i) = 0
  rw [collarHomotopyElem_weights, collarHomotopyW, collarProjElem_at_star n x i hi, hi]
  ring

private def collarHomotopyFun (p : unitInterval × ↥(simplexCollar n)) : ↥(simplexCollar n) :=
  ⟨⟨⟨collarHomotopyElem n p.1 p.2, collarHomotopyElem_mem_boundary n p.1 p.2⟩,
      collarHomotopyElem_mem_southCap n p.1 p.2⟩,
    collarHomotopyElem_mem_star n p.1 p.2⟩

private theorem continuous_collarHomotopyElem :
    Continuous (fun p : unitInterval × ↥(simplexCollar n) => collarHomotopyElem n p.1 p.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun p : unitInterval × ↥(simplexCollar n) =>
    (collarHomotopyElem n p.1 p.2).weights j)
  rw [show (fun p : unitInterval × ↥(simplexCollar n) => (collarHomotopyElem n p.1 p.2).weights j) =
      fun p => collarHomotopyW n p.1 p.2 j
    from funext fun p => collarHomotopyElem_weights n p.1 p.2 j]
  have hfst : Continuous (fun p : unitInterval × ↥(simplexCollar n) => ((p.1 : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have h1 : Continuous (fun p : unitInterval × ↥(simplexCollar n) =>
      (collarProjElem n p.2).weights j) :=
    ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp
      (continuous_collarProjElem n)).comp continuous_snd
  have h2 : Continuous (fun p : unitInterval × ↥(simplexCollar n) =>
      (collarPt n p.2).weights j) :=
    ((Convexity.StdSimplex.continuous_weights_apply ℝ j).comp
      (continuous_collarPt n)).comp continuous_snd
  rw [show (fun p : unitInterval × ↥(simplexCollar n) => collarHomotopyW n p.1 p.2 j) =
      fun p => (1 - ((p.1 : unitInterval) : ℝ)) * (collarProjElem n p.2).weights j +
        ((p.1 : unitInterval) : ℝ) * (collarPt n p.2).weights j from funext fun p => rfl]
  exact ((continuous_const.sub hfst).mul h1).add (hfst.mul h2)

private theorem continuous_collarHomotopyFun :
    Continuous (fun p : unitInterval × ↥(simplexCollar n) => collarHomotopyFun n p) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_collarHomotopyElem n

private theorem collarHomotopyFun_zero (x : ↥(simplexCollar n)) :
    collarHomotopyFun n (0, x) = equatorInCollar n (collarProjFun n x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (collarHomotopyElem n 0 x).weights j = (collarProjElem n x).weights j
  rw [collarHomotopyElem_weights, collarHomotopyW]
  simp

private theorem collarHomotopyFun_one (x : ↥(simplexCollar n)) :
    collarHomotopyFun n (1, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (collarHomotopyElem n 1 x).weights j = (collarPt n x).weights j
  rw [collarHomotopyElem_weights, collarHomotopyW]
  simp

/-! ## The homotopy equivalence -/

/-- The radial projection of the collar onto the equator, as a morphism of topological spaces. -/
private def collarProj : TopCat.of (simplexCollar n) ⟶ TopCat.of (equatorInLastFace n) :=
  TopCat.ofHom ⟨collarProjFun n, continuous_collarProjFun n⟩

private theorem equatorInCollar_comp_collarProj :
    equatorInCollar n ≫ collarProj n = 𝟙 (TopCat.of (equatorInLastFace n)) := by
  apply TopCat.Hom.ext
  apply ContinuousMap.ext
  intro y
  exact collarProjFun_equatorInCollar n y

private theorem collarProj_comp_equatorInCollar_apply (x : ↥(simplexCollar n)) :
    (TopCat.Hom.hom (collarProj n ≫ equatorInCollar n)) x =
      equatorInCollar n (collarProjFun n x) := rfl

private theorem id_collar_apply (x : ↥(simplexCollar n)) :
    (TopCat.Hom.hom (𝟙 (TopCat.of (simplexCollar n)))) x = x := rfl

private theorem collarProj_comp_equatorInCollar_homotopic :
    Nonempty (TopCat.Homotopy (collarProj n ≫ equatorInCollar n)
      (𝟙 (TopCat.of (simplexCollar n)))) :=
  ⟨ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × ↥(simplexCollar n) => collarHomotopyFun n p,
      continuous_collarHomotopyFun n⟩
    (fun x => by
      change collarHomotopyFun n (0, x) =
        (TopCat.Hom.hom (collarProj n ≫ equatorInCollar n)) x
      rw [collarHomotopyFun_zero n x, collarProj_comp_equatorInCollar_apply n x])
    (fun x => by
      change collarHomotopyFun n (1, x) = (TopCat.Hom.hom (𝟙 (TopCat.of (simplexCollar n)))) x
      rw [collarHomotopyFun_one n x, id_collar_apply n x])⟩

/-- **The inclusion of the equator into its collar `simplexCollar n = simplexStar n ∩ south cap`
is a homotopy equivalence.**  The homotopy inverse is the radial projection away from the last
vertex of `Δⁿ⁺¹`. -/
theorem equatorInCollar_isHomotopyEquivalence (n : ℕ) :
    Work.Homology.IsHomotopyEquivalence (Work.HomologyExtra.equatorInCollar n) :=
  ⟨collarProj n,
    by
      refine ⟨?_⟩
      rw [equatorInCollar_comp_collarProj n]
      exact TopCat.Homotopy.refl _,
    collarProj_comp_equatorInCollar_homotopic n⟩

end

end Work.HomologyExtra
