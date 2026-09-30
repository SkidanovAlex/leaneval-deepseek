import Mathlib
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.simplexStar_contractible
import Submission.Work.HomologyExtra.simplexSouthCap_contractible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The last face of `∂Δⁿ⁺¹`, its equator, and the collar of the equator in the closed star

Definitions (and elementary lemmas) used by the proof that the face map
`(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)` (`Work.HomologyExtra.simplexFacePairHom`) is an isomorphism on relative
homology, where `B = simplexStar n` is the closed star of the last vertex of `∂Δⁿ⁺¹`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits


namespace Work.HomologyExtra

noncomputable section

/-! ## The barycentric coordinates of the last vertex -/

theorem starApex_nonneg (n : ℕ) : ∀ i, 0 ≤ starApex n i := by
  intro i; simp only [starApex]; split <;> norm_num

theorem starApex_sum (n : ℕ) : ∑ i, starApex n i = 1 := by simp [starApex]

/-- **The last vertex of `∂Δⁿ⁺¹`**, as a point. -/
def simplexLastVertex (n : ℕ) : ↥(boundarySpace (n + 1)) :=
  ⟨mkSimplex (starApex n) (starApex_nonneg n) (starApex_sum n), by
    refine ⟨0, ?_⟩
    rw [mkSimplex_weights]
    have h : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val h
      simp [Fin.val_last] at this
    simp [starApex, h]⟩

@[simp]
theorem simplexLastVertex_weights (n : ℕ) (i : Fin (n + 2)) :
    ((simplexLastVertex n : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights i =
      starApex n i := by
  show (mkSimplex (starApex n) (starApex_nonneg n) (starApex_sum n)).weights i = starApex n i
  rw [mkSimplex_weights]

theorem simplexLastVertex_last (n : ℕ) :
    ((simplexLastVertex n : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights
      (Fin.last (n + 1)) = 1 := by
  rw [simplexLastVertex_weights]; simp [starApex]

/-- The last vertex lies in the north cap (and hence, later, in the interior of the closed star). -/
theorem simplexLastVertex_mem_northCap (n : ℕ) :
    simplexLastVertex n ∈ simplexNorthCap n := by
  show 0 < ((simplexLastVertex n : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights
    (Fin.last (n + 1))
  rw [simplexLastVertex_last]; norm_num

/-- A point of `∂Δⁿ⁺¹` is the last vertex exactly when its last barycentric coordinate is `1`. -/
theorem eq_simplexLastVertex_iff (n : ℕ) (x : ↥(boundarySpace (n + 1))) :
    x = simplexLastVertex n ↔
      ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1)) = 1 := by
  constructor
  · intro h; rw [h, simplexLastVertex_last]
  · intro h
    apply Subtype.ext
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hsum : ∑ i : Fin (n + 1),
          ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.castSucc i) = 0 := by
        have htot := Convexity.StdSimplex.total_of_fintype
          ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))
        rw [Fin.sum_univ_castSucc] at htot
        linarith
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Convexity.StdSimplex.weights_nonneg
          (w := ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))) (Fin.castSucc i))).mp hsum
        j (Finset.mem_univ j)
      rw [hz, simplexLastVertex_weights]
      simp only [starApex]
      rw [if_neg (Fin.castSucc_lt_last j).ne]
    · rw [h, simplexLastVertex_weights]
      simp [starApex]

/-- **The south cap is the complement of the last vertex.** -/
theorem simplexSouthCap_eq_compl_lastVertex (n : ℕ) :
    simplexSouthCap n = {x : ↥(boundarySpace (n + 1)) | x ≠ simplexLastVertex n} := by
  ext x
  show ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1)) < 1 ↔
    x ≠ simplexLastVertex n
  constructor
  · intro h h1
    have h2 := (eq_simplexLastVertex_iff n x).mp h1
    rw [h2] at h; exact lt_irrefl 1 h
  · intro h
    refine lt_of_le_of_ne ?_ (fun h1 => h ((eq_simplexLastVertex_iff n x).mpr h1))
    have htot := Convexity.StdSimplex.total_of_fintype
      ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))
    calc ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1))
        ≤ ∑ i, ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights i :=
          Finset.single_le_sum
            (fun i _ => Convexity.StdSimplex.weights_nonneg
              (w := ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1))) i) (Finset.mem_univ _)
      _ = 1 := htot

/-! ## The face map `Δⁿ → A` -/

/-- **The face map `Δⁿ → ∂Δⁿ⁺¹` corestricted to the last face** `A = simplexLastFace n`. -/
def faceToLastFaceFun (n : ℕ) (w : ↥(simplex n)) : ↥(simplexLastFace n) :=
  ⟨simplexFaceToBoundary n (Fin.last (n + 1)) w, by
    rw [mem_simplexLastFace]
    exact weights_simplexFace_self n (Fin.last (n + 1)) w⟩

theorem faceToLastFaceFun_coe (n : ℕ) (w : ↥(simplex n)) :
    ((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) =
      simplexFaceToBoundary n (Fin.last (n + 1)) w := rfl

theorem continuous_faceToLastFaceFun (n : ℕ) : Continuous (faceToLastFaceFun n) :=
  Continuous.subtype_mk (by fun_prop) _

theorem faceToLastFaceFun_coe_stdSimplex (n : ℕ) (w : ↥(simplex n)) :
    (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
      simplex (n + 1)) = (simplexFace n (Fin.last (n + 1))) w := rfl

/-- The last barycentric coordinate of the face point vanishes. -/
theorem faceToLastFaceFun_weights_last (n : ℕ) (w : ↥(simplex n)) :
    (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
      simplex (n + 1)).weights (Fin.last (n + 1)) = 0 := by
  rw [faceToLastFaceFun_coe_stdSimplex]
  exact weights_simplexFace_self n (Fin.last (n + 1)) w

/-- The non-last barycentric coordinates of the face point are those of the source point. -/
theorem faceToLastFaceFun_weights_castSucc (n : ℕ) (w : ↥(simplex n)) (i : Fin (n + 1)) :
    (((faceToLastFaceFun n w : ↥(simplexLastFace n)) : ↥(boundarySpace (n + 1))) :
      simplex (n + 1)).weights (Fin.castSucc i) = (w : simplex n).weights i := by
  rw [faceToLastFaceFun_coe_stdSimplex]
  exact weights_simplexFace_last n w i

/-! ## The equator, and the collar inside the closed star -/

/-- The equator `E = simplexEquator n`, viewed as a subset of the last face `A`. -/
def equatorInLastFace (n : ℕ) : Set ↥(simplexLastFace n) :=
  {x | (x : ↥(boundarySpace (n + 1))) ∈ simplexEquator n}

/-- **The collar of the equator inside the closed star**: the part `T = B ∩ S` of the closed star
`B = simplexStar n` lying in the south cap `S = simplexSouthCap n`, viewed as a subset of `S`. -/
def simplexCollar (n : ℕ) : Set ↥(simplexSouthCap n) :=
  {x | (x : ↥(boundarySpace (n + 1))) ∈ simplexStar n}

theorem mem_simplexCollar {n : ℕ} {x : ↥(simplexSouthCap n)} :
    x ∈ simplexCollar n ↔ (x : ↥(boundarySpace (n + 1))) ∈ simplexStar n := Iff.rfl

theorem mem_equatorInLastFace {n : ℕ} {x : ↥(simplexLastFace n)} :
    x ∈ equatorInLastFace n ↔ (x : ↥(boundarySpace (n + 1))) ∈ simplexEquator n := Iff.rfl

/-- Membership in the equator, unfolded. -/
theorem mem_simplexEquator {n : ℕ} {x : ↥(boundarySpace (n + 1))} :
    x ∈ simplexEquator n ↔
      ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1)) = 0 ∧
        ∃ i : Fin (n + 1), ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights
          (Fin.castSucc i) = 0 := Iff.rfl

/-- The last face lies in the south cap. -/
theorem mem_southCap_of_mem_lastFace {n : ℕ} {x : ↥(boundarySpace (n + 1))}
    (h : x ∈ simplexLastFace n) : x ∈ simplexSouthCap n := by
  rw [mem_simplexLastFace] at h
  show ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1)) < 1
  rw [h]; norm_num

/-- The equator lies in the south cap. -/
theorem mem_southCap_of_mem_equator {n : ℕ} {x : ↥(boundarySpace (n + 1))}
    (h : x ∈ simplexEquator n) : x ∈ simplexSouthCap n := by
  obtain ⟨h0, -⟩ := h
  show ((x : ↥(boundarySpace (n + 1))) : simplex (n + 1)).weights (Fin.last (n + 1)) < 1
  rw [h0]; norm_num

/-- The equator lies in the closed star. -/
theorem mem_star_of_mem_equator {n : ℕ} {x : ↥(boundarySpace (n + 1))}
    (h : x ∈ simplexEquator n) : x ∈ simplexStar n := by
  obtain ⟨-, i, hi⟩ := h
  exact ⟨i, hi⟩

/-- **The inclusion of the equator into the collar** `E ⊆ T = B ∩ S`, as a map of spaces
`E ⟶ T` (where `E` is viewed as a subset of the last face `A`). -/
def equatorInCollar (n : ℕ) : TopCat.of (equatorInLastFace n) ⟶ TopCat.of (simplexCollar n) :=
  TopCat.ofHom ⟨fun x => ⟨⟨(x : ↥(boundarySpace (n + 1))), mem_southCap_of_mem_equator x.2⟩,
    mem_star_of_mem_equator x.2⟩, by fun_prop⟩

@[simp]
theorem equatorInCollar_coe (n : ℕ) (x : ↥(equatorInLastFace n)) :
    ((equatorInCollar n x : ↥(simplexCollar n)) : ↥(simplexSouthCap n)) =
      (⟨(x : ↥(boundarySpace (n + 1))), mem_southCap_of_mem_equator x.2⟩ :
        ↥(simplexSouthCap n)) := rfl

end

end Work.HomologyExtra
