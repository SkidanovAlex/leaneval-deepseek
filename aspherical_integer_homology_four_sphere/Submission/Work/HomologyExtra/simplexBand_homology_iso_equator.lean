import Mathlib
import Submission.Work.HomologyExtra.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The band of `∂Δⁿ⁺¹` has the homology of the equator

The boundary `∂Δⁿ⁺¹` of the standard `(n+1)`-simplex is covered by the "north cap"
`{w_v > 0}` and the "south cap" `{w_v < 1}`, where `v = Fin.last (n+1)`; their
intersection is the **band** `simplexBand n = {0 < w_v < 1}`
(`Submission/Work/HomologyExtra/Basic.lean`).  Radially projecting away from the
vertex `v` turns the band into a collar on the **equator** `simplexEquator n`, the
boundary of the face opposite `v`.

This file proves that the projection is a homotopy equivalence, hence that the band
and the equator have isomorphic singular homology in every degree, which is the
geometric input of the Mayer–Vietoris computation of `H_*(∂Δⁿ⁺¹)`.

Concretely, in barycentric coordinates of `Δⁿ⁺¹` the map is

* `bandProjFun x`: `(bandProjFun x)_v = 0` and `(bandProjFun x)_i = x_i / (1 - x_v)`
  for `i ≠ v` (projection from the vertex `v`),
* `equatorInBandFun y`: `(equatorInBandFun y)_v = 1/2` and `(equatorInBandFun y)_i =
  y_i / 2` for `i ≠ v` (shrinking the equator into the band),

and they satisfy `bandProjFun ∘ equatorInBandFun = id` and
`equatorInBandFun ∘ bandProjFun ≃ id` by the straight-line homotopy inside the
band.

The helpers of this file are `private`: they are an implementation detail of the
single theorem `simplexBand_homology_iso_equator` below.
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

/-! ## The projection from the last vertex -/

variable (n : ℕ)

private abbrev bandPt (x : ↥(simplexBand n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) := x.1.1

private abbrev bandLast (x : ↥(simplexBand n)) : ℝ := (bandPt n x).weights (Fin.last (n + 1))

private abbrev eqPt (y : ↥(simplexEquator n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) := y.1.1

private theorem bandLast_lt_one (x : ↥(simplexBand n)) : bandLast n x < 1 := x.2.2

private theorem one_sub_bandLast_pos (x : ↥(simplexBand n)) : 0 < 1 - bandLast n x :=
  sub_pos.mpr (bandLast_lt_one n x)

/-- The barycentric coordinates of the projection of a band point from the last vertex. -/
private def bandProjW (x : ↥(simplexBand n)) : Fin (n + 2) → ℝ :=
  Fin.lastCases 0 (fun i => (bandPt n x).weights (Fin.castSucc i) / (1 - bandLast n x))

private theorem bandProjW_last (x : ↥(simplexBand n)) :
    bandProjW n x (Fin.last (n + 1)) = 0 := by
  simp [bandProjW]

private theorem bandProjW_castSucc (x : ↥(simplexBand n)) (i : Fin (n + 1)) :
    bandProjW n x (Fin.castSucc i) =
      (bandPt n x).weights (Fin.castSucc i) / (1 - bandLast n x) := by
  simp [bandProjW]

private theorem bandProjW_nonneg (x : ↥(simplexBand n)) : ∀ j, 0 ≤ bandProjW n x j := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · rw [bandProjW_last]
  · intro i
    rw [bandProjW_castSucc]
    exact div_nonneg ((bandPt n x).weights_nonneg _) (le_of_lt (one_sub_bandLast_pos n x))

private theorem bandProjW_total (x : ↥(simplexBand n)) : ∑ j, bandProjW n x j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [bandProjW_last, bandProjW_castSucc, add_zero]
  rw [← Finset.sum_div]
  rw [show ∑ i : Fin (n + 1), (bandPt n x).weights (Fin.castSucc i) = 1 - bandLast n x from by
    linarith [sum_weights_castSucc (bandPt n x)]]
  exact div_self (ne_of_gt (one_sub_bandLast_pos n x))

private def bandProjElem (x : ↥(simplexBand n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  stdSimplexMk (bandProjW n x) (bandProjW_nonneg n x) (bandProjW_total n x)

private theorem bandProjElem_weights (x : ↥(simplexBand n)) (j : Fin (n + 2)) :
    (bandProjElem n x).weights j = bandProjW n x j :=
  stdSimplexMk_weights _ _ _ j

private theorem bandProjElem_mem_boundary (x : ↥(simplexBand n)) :
    bandProjElem n x ∈ simplexBoundary (n + 1) :=
  ⟨Fin.last (n + 1), by rw [bandProjElem_weights, bandProjW_last]⟩

private theorem bandProjElem_mem_equator (x : ↥(simplexBand n)) :
    (⟨bandProjElem n x, bandProjElem_mem_boundary n x⟩ : ↥(boundarySpace (n + 1))) ∈
      simplexEquator n := by
  constructor
  · rw [bandProjElem_weights, bandProjW_last]
  · obtain ⟨i, hi⟩ := x.1.2
    have hne : i ≠ Fin.last (n + 1) := fun h => by
      rw [h] at hi
      exact absurd hi (ne_of_gt (x.2.1))
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
    · exact ⟨j, by rw [bandProjElem_weights, bandProjW_castSucc, hi, zero_div]⟩
    · exact absurd h hne

/-- The projection of the band onto the equator (radial projection from the last vertex). -/
private def bandProjFun (x : ↥(simplexBand n)) : ↥(simplexEquator n) :=
  ⟨⟨bandProjElem n x, bandProjElem_mem_boundary n x⟩, bandProjElem_mem_equator n x⟩

private theorem eqPt_bandProjFun (x : ↥(simplexBand n)) :
    eqPt n (bandProjFun n x) = bandProjElem n x := rfl

private theorem continuous_bandPt :
    Continuous (fun x : ↥(simplexBand n) => bandPt n x) :=
  continuous_subtype_val.comp continuous_subtype_val

private theorem continuous_bandLast :
    Continuous (fun x : ↥(simplexBand n) => bandLast n x) :=
  (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp (continuous_bandPt n)

private theorem continuous_bandProjElem :
    Continuous (fun x : ↥(simplexBand n) => bandProjElem n x) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun x : ↥(simplexBand n) => (bandProjElem n x).weights j)
  rw [show (fun x : ↥(simplexBand n) => (bandProjElem n x).weights j) = fun x => bandProjW n x j
    from funext fun x => bandProjElem_weights n x j]
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun x : ↥(simplexBand n) => bandProjW n x (Fin.last (n + 1))) = fun _ => (0 : ℝ)
      from funext fun x => bandProjW_last n x]
    exact continuous_const
  · intro i
    rw [show (fun x : ↥(simplexBand n) => bandProjW n x (Fin.castSucc i)) =
        fun x => (bandPt n x).weights (Fin.castSucc i) / (1 - bandLast n x)
      from funext fun x => bandProjW_castSucc n x i]
    refine Continuous.div ?_ ?_ ?_
    · exact (Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
        (continuous_bandPt n)
    · exact continuous_const.sub (continuous_bandLast n)
    · intro x
      exact ne_of_gt (one_sub_bandLast_pos n x)

private theorem continuous_bandProjFun :
    Continuous (fun x : ↥(simplexBand n) => bandProjFun n x) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_bandProjElem n

/-! ## Shrinking the equator into the band -/

private theorem eqPt_last (y : ↥(simplexEquator n)) :
    (eqPt n y).weights (Fin.last (n + 1)) = 0 := y.2.1

/-- The barycentric coordinates of the equator point shrunk to the middle of the band. -/
private def equatorInBandW (y : ↥(simplexEquator n)) : Fin (n + 2) → ℝ :=
  Fin.lastCases (1/2) (fun i => (1/2) * (eqPt n y).weights (Fin.castSucc i))

private theorem equatorInBandW_last (y : ↥(simplexEquator n)) :
    equatorInBandW n y (Fin.last (n + 1)) = 1/2 := by
  simp [equatorInBandW]

private theorem equatorInBandW_castSucc (y : ↥(simplexEquator n)) (i : Fin (n + 1)) :
    equatorInBandW n y (Fin.castSucc i) = (1/2) * (eqPt n y).weights (Fin.castSucc i) := by
  simp [equatorInBandW]

private theorem equatorInBandW_nonneg (y : ↥(simplexEquator n)) :
    ∀ j, 0 ≤ equatorInBandW n y j := by
  intro j
  refine Fin.lastCases ?_ ?_ j
  · rw [equatorInBandW_last]; norm_num
  · intro i
    rw [equatorInBandW_castSucc]
    exact mul_nonneg (by norm_num) ((eqPt n y).weights_nonneg _)

private theorem equatorInBandW_total (y : ↥(simplexEquator n)) :
    ∑ j, equatorInBandW n y j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [equatorInBandW_last, equatorInBandW_castSucc]
  have h2 : ∑ i : Fin (n + 1), (eqPt n y).weights (Fin.castSucc i) = 1 := by
    have := sum_weights_castSucc (eqPt n y)
    rw [eqPt_last n y] at this
    linarith [this]
  rw [← Finset.mul_sum, h2]
  norm_num

private def equatorInBandElem (y : ↥(simplexEquator n)) : Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  stdSimplexMk (equatorInBandW n y) (equatorInBandW_nonneg n y) (equatorInBandW_total n y)

private theorem equatorInBandElem_weights (y : ↥(simplexEquator n)) (j : Fin (n + 2)) :
    (equatorInBandElem n y).weights j = equatorInBandW n y j :=
  stdSimplexMk_weights _ _ _ j

private theorem equatorInBandElem_mem_boundary (y : ↥(simplexEquator n)) :
    equatorInBandElem n y ∈ simplexBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := y.2.2
  exact ⟨Fin.castSucc i,
    by rw [equatorInBandElem_weights, equatorInBandW_castSucc, hi, mul_zero]⟩

private theorem equatorInBandElem_mem_band (y : ↥(simplexEquator n)) :
    (⟨equatorInBandElem n y, equatorInBandElem_mem_boundary n y⟩ : ↥(boundarySpace (n + 1))) ∈
      simplexBand n := by
  constructor
  · rw [equatorInBandElem_weights, equatorInBandW_last]; norm_num
  · rw [equatorInBandElem_weights, equatorInBandW_last]; norm_num

/-- The equator shrunk to the middle of the band. -/
private def equatorInBandFun (y : ↥(simplexEquator n)) : ↥(simplexBand n) :=
  ⟨⟨equatorInBandElem n y, equatorInBandElem_mem_boundary n y⟩, equatorInBandElem_mem_band n y⟩

private theorem bandPt_equatorInBandFun (y : ↥(simplexEquator n)) :
    bandPt n (equatorInBandFun n y) = equatorInBandElem n y := rfl

private theorem bandLast_equatorInBandFun (y : ↥(simplexEquator n)) :
    bandLast n (equatorInBandFun n y) = 1/2 := by
  rw [bandLast, bandPt_equatorInBandFun, equatorInBandElem_weights, equatorInBandW_last]

private theorem bandProjW_equatorInBandFun (y : ↥(simplexEquator n)) (i : Fin (n + 1)) :
    bandProjW n (equatorInBandFun n y) (Fin.castSucc i) = (eqPt n y).weights (Fin.castSucc i) := by
  rw [bandProjW_castSucc, bandPt_equatorInBandFun, bandLast_equatorInBandFun,
    equatorInBandElem_weights, equatorInBandW_castSucc]
  field_simp
  ring

/-- **The projection is a left inverse of the shrinking map.** -/
private theorem bandProjFun_equatorInBandFun (y : ↥(simplexEquator n)) :
    bandProjFun n (equatorInBandFun n y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (bandProjElem n (equatorInBandFun n y)).weights j = (eqPt n y).weights j
  refine Fin.lastCases ?_ ?_ j
  · rw [bandProjElem_weights, bandProjW_last, eqPt_last]
  · intro i
    rw [bandProjElem_weights, bandProjW_equatorInBandFun]

private theorem continuous_eqPt :
    Continuous (fun y : ↥(simplexEquator n) => eqPt n y) :=
  continuous_subtype_val.comp continuous_subtype_val

private theorem continuous_equatorInBandElem :
    Continuous (fun y : ↥(simplexEquator n) => equatorInBandElem n y) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun y : ↥(simplexEquator n) => (equatorInBandElem n y).weights j)
  rw [show (fun y : ↥(simplexEquator n) => (equatorInBandElem n y).weights j) =
      fun y => equatorInBandW n y j from funext fun y => equatorInBandElem_weights n y j]
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun y : ↥(simplexEquator n) => equatorInBandW n y (Fin.last (n + 1))) =
        fun _ => (1/2 : ℝ) from funext fun y => equatorInBandW_last n y]
    exact continuous_const
  · intro i
    rw [show (fun y : ↥(simplexEquator n) => equatorInBandW n y (Fin.castSucc i)) =
        fun y => (1/2) * (eqPt n y).weights (Fin.castSucc i)
      from funext fun y => equatorInBandW_castSucc n y i]
    exact continuous_const.mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp (continuous_eqPt n))

private theorem continuous_equatorInBandFun :
    Continuous (fun y : ↥(simplexEquator n) => equatorInBandFun n y) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_equatorInBandElem n

/-! ## The straight-line homotopy from `equatorInBandFun ∘ bandProjFun` to the identity -/

private def bandHomotopyW (s : unitInterval) (x : ↥(simplexBand n)) : Fin (n + 2) → ℝ :=
  fun j => (1 - (s : ℝ)) * equatorInBandW n (bandProjFun n x) j +
    (s : ℝ) * (bandPt n x).weights j

private theorem bandHomotopyW_nonneg (s : unitInterval) (x : ↥(simplexBand n)) :
    ∀ j, 0 ≤ bandHomotopyW n s x j := by
  intro j
  rw [bandHomotopyW]
  exact add_nonneg
    (mul_nonneg (by linarith [s.2.2]) (equatorInBandW_nonneg n (bandProjFun n x) j))
    (mul_nonneg s.2.1 ((bandPt n x).weights_nonneg j))

private theorem bandHomotopyW_total (s : unitInterval) (x : ↥(simplexBand n)) :
    ∑ j, bandHomotopyW n s x j = 1 := by
  simp only [bandHomotopyW]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    equatorInBandW_total n (bandProjFun n x), (bandPt n x).total_of_fintype]
  ring

private theorem bandHomotopyW_last (s : unitInterval) (x : ↥(simplexBand n)) :
    bandHomotopyW n s x (Fin.last (n + 1)) =
      (1 - (s : ℝ)) * (1/2) + (s : ℝ) * (bandPt n x).weights (Fin.last (n + 1)) := by
  simp [bandHomotopyW, equatorInBandW_last]

private def bandHomotopyElem (s : unitInterval) (x : ↥(simplexBand n)) :
    Convexity.StdSimplex ℝ (Fin (n + 2)) :=
  stdSimplexMk (bandHomotopyW n s x) (bandHomotopyW_nonneg n s x) (bandHomotopyW_total n s x)

private theorem bandHomotopyElem_weights (s : unitInterval) (x : ↥(simplexBand n))
    (j : Fin (n + 2)) :
    (bandHomotopyElem n s x).weights j = bandHomotopyW n s x j :=
  stdSimplexMk_weights _ _ _ j

private theorem bandHomotopyElem_mem_boundary (s : unitInterval) (x : ↥(simplexBand n)) :
    bandHomotopyElem n s x ∈ simplexBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := x.1.2
  have hne : i ≠ Fin.last (n + 1) := fun h => by
    rw [h] at hi
    exact absurd hi (ne_of_gt (x.2.1))
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
  · refine ⟨Fin.castSucc j, ?_⟩
    have hpj : (bandProjElem n x).weights (Fin.castSucc j) = 0 := by
      rw [bandProjElem_weights, bandProjW_castSucc, hi, zero_div]
    rw [bandHomotopyElem_weights, bandHomotopyW, equatorInBandW_castSucc,
      eqPt_bandProjFun, hpj, hi]
    ring
  · exact absurd h hne

private theorem bandHomotopyElem_mem_band (s : unitInterval) (x : ↥(simplexBand n)) :
    (⟨bandHomotopyElem n s x, bandHomotopyElem_mem_boundary n s x⟩ :
        ↥(boundarySpace (n + 1))) ∈ simplexBand n := by
  constructor
  · rw [bandHomotopyElem_weights, bandHomotopyW_last]
    rcases lt_or_eq_of_le s.2.2 with hs | hs
    · have h1 : 0 < (1 - (s : ℝ)) * (1/2) := by nlinarith [hs]
      have h2 : 0 ≤ (s : ℝ) * (bandPt n x).weights (Fin.last (n + 1)) :=
        mul_nonneg s.2.1 ((bandPt n x).weights_nonneg _)
      linarith
    · rw [hs]
      simp only [sub_self, zero_mul, one_mul, zero_add]
      exact x.2.1
  · rw [bandHomotopyElem_weights, bandHomotopyW_last]
    rcases lt_or_eq_of_le s.2.2 with hs | hs
    · have h2 : (s : ℝ) * (bandPt n x).weights (Fin.last (n + 1)) ≤ (s : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (le_of_lt x.2.2) s.2.1
      nlinarith [hs]
    · rw [hs]
      simp only [sub_self, zero_mul, one_mul, zero_add]
      exact x.2.2

private def bandHomotopyFun (p : unitInterval × ↥(simplexBand n)) : ↥(simplexBand n) :=
  ⟨⟨bandHomotopyElem n p.1 p.2, bandHomotopyElem_mem_boundary n p.1 p.2⟩,
    bandHomotopyElem_mem_band n p.1 p.2⟩

private theorem continuous_equatorInBandW_bandProjFun (j : Fin (n + 2)) :
    Continuous (fun x : ↥(simplexBand n) => equatorInBandW n (bandProjFun n x) j) := by
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun x : ↥(simplexBand n) => equatorInBandW n (bandProjFun n x) (Fin.last (n + 1))) =
        fun _ => (1/2 : ℝ) from funext fun x => equatorInBandW_last n (bandProjFun n x)]
    exact continuous_const
  · intro i
    rw [show (fun x : ↥(simplexBand n) => equatorInBandW n (bandProjFun n x) (Fin.castSucc i)) =
        fun x => (1/2) * (bandProjElem n x).weights (Fin.castSucc i)
      from funext fun x => by rw [equatorInBandW_castSucc]; rfl]
    exact continuous_const.mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
        (continuous_bandProjElem n))

private theorem continuous_bandHomotopyElem :
    Continuous (fun p : unitInterval × ↥(simplexBand n) => bandHomotopyElem n p.1 p.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun p : unitInterval × ↥(simplexBand n) =>
    (bandHomotopyElem n p.1 p.2).weights j)
  rw [show (fun p : unitInterval × ↥(simplexBand n) => (bandHomotopyElem n p.1 p.2).weights j) =
      fun p => bandHomotopyW n p.1 p.2 j
    from funext fun p => bandHomotopyElem_weights n p.1 p.2 j]
  have hfst : Continuous (fun p : unitInterval × ↥(simplexBand n) => ((p.1 : unitInterval) : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hsnd : Continuous (fun p : unitInterval × ↥(simplexBand n) => bandPt n p.2) :=
    (continuous_bandPt n).comp continuous_snd
  refine Fin.lastCases ?_ ?_ j
  · rw [show (fun p : unitInterval × ↥(simplexBand n) =>
        bandHomotopyW n p.1 p.2 (Fin.last (n + 1))) =
        fun p => (1 - ((p.1 : unitInterval) : ℝ)) * (1/2) +
          ((p.1 : unitInterval) : ℝ) * (bandPt n p.2).weights (Fin.last (n + 1))
      from funext fun p => bandHomotopyW_last n p.1 p.2]
    exact (((continuous_const.sub hfst).mul continuous_const)).add (hfst.mul
      (((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp hsnd)))
  · intro i
    rw [show (fun p : unitInterval × ↥(simplexBand n) =>
        bandHomotopyW n p.1 p.2 (Fin.castSucc i)) =
        fun p => (1 - ((p.1 : unitInterval) : ℝ)) *
            (equatorInBandW n (bandProjFun n p.2) (Fin.castSucc i)) +
          ((p.1 : unitInterval) : ℝ) * (bandPt n p.2).weights (Fin.castSucc i)
      from funext fun p => rfl]
    exact ((continuous_const.sub hfst).mul
        ((continuous_equatorInBandW_bandProjFun n (Fin.castSucc i)).comp continuous_snd)).add
      (hfst.mul (((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp hsnd)))

private theorem continuous_bandHomotopyFun :
    Continuous (fun p : unitInterval × ↥(simplexBand n) => bandHomotopyFun n p) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_bandHomotopyElem n

private theorem bandHomotopyFun_zero (x : ↥(simplexBand n)) :
    bandHomotopyFun n (0, x) = equatorInBandFun n (bandProjFun n x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (bandHomotopyElem n 0 x).weights j =
    (equatorInBandElem n (bandProjFun n x)).weights j
  rw [bandHomotopyElem_weights, bandHomotopyW, equatorInBandElem_weights]
  simp

private theorem bandHomotopyFun_one (x : ↥(simplexBand n)) :
    bandHomotopyFun n (1, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  change (bandHomotopyElem n 1 x).weights j = (bandPt n x).weights j
  rw [bandHomotopyElem_weights, bandHomotopyW]
  simp

/-! ## The homotopy equivalence -/

/-- The projection of the band onto the equator, as a morphism of topological spaces. -/
private def bandProj : TopCat.of (simplexBand n) ⟶ TopCat.of (simplexEquator n) :=
  TopCat.ofHom ⟨bandProjFun n, continuous_bandProjFun n⟩

/-- The equator shrunk into the band, as a morphism of topological spaces. -/
private def equatorInBand : TopCat.of (simplexEquator n) ⟶ TopCat.of (simplexBand n) :=
  TopCat.ofHom ⟨equatorInBandFun n, continuous_equatorInBandFun n⟩

private theorem equatorInBand_comp_bandProj :
    equatorInBand n ≫ bandProj n = 𝟙 (TopCat.of (simplexEquator n)) := by
  apply TopCat.Hom.ext
  apply ContinuousMap.ext
  intro y
  exact bandProjFun_equatorInBandFun n y

private theorem bandProj_comp_equatorInBand_apply (x : ↥(simplexBand n)) :
    (TopCat.Hom.hom (bandProj n ≫ equatorInBand n)) x =
      equatorInBandFun n (bandProjFun n x) := rfl

private theorem id_band_apply (x : ↥(simplexBand n)) :
    (TopCat.Hom.hom (𝟙 (TopCat.of (simplexBand n)))) x = x := rfl

private theorem bandProj_comp_equatorInBand_homotopic :
    Nonempty (TopCat.Homotopy (bandProj n ≫ equatorInBand n)
      (𝟙 (TopCat.of (simplexBand n)))) :=
  ⟨ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × ↥(simplexBand n) => bandHomotopyFun n p, continuous_bandHomotopyFun n⟩
    (fun x => by
      change bandHomotopyFun n (0, x) =
        (TopCat.Hom.hom (bandProj n ≫ equatorInBand n)) x
      rw [bandHomotopyFun_zero n x, bandProj_comp_equatorInBand_apply n x])
    (fun x => by
      change bandHomotopyFun n (1, x) = (TopCat.Hom.hom (𝟙 (TopCat.of (simplexBand n)))) x
      rw [bandHomotopyFun_one n x, id_band_apply n x])⟩

private theorem bandProj_isHomotopyEquivalence :
    Work.Homology.IsHomotopyEquivalence (bandProj n) :=
  ⟨equatorInBand n, bandProj_comp_equatorInBand_homotopic n,
    by
      refine ⟨?_⟩
      rw [equatorInBand_comp_bandProj n]
      exact TopCat.Homotopy.refl _⟩

/-! ## The theorem -/

theorem simplexBand_homology_iso_equator (n j : ℕ) :
    Nonempty (Work.Homology.singHomology Work.Homology.ZMod j
        (TopCat.of (Work.HomologyExtra.simplexBand n)) ≅
      Work.Homology.singHomology Work.Homology.ZMod j
        (TopCat.of (Work.HomologyExtra.simplexEquator n))) :=
  Work.Homology.HomotopyEquivHomology Work.Homology.ZMod j (bandProj n)
    (bandProj_isHomotopyEquivalence n)

end

end Work.HomologyExtra
