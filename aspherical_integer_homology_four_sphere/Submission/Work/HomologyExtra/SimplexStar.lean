import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.CycleClass
import Submission.Work.HomologyExtra.simplexBoundaryChain_d
import Submission.Work.HomologyExtra.SimplexClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The closed star of a vertex of `∂Δⁿ⁺¹` and the face opposite it

For the induction that computes the fundamental class of the sphere `∂Δⁿ⁺¹` we use the
decomposition of `∂Δⁿ⁺¹` by the face `F` opposite the last vertex and the closed star `B` of that
vertex.  The fundamental cycle `zₙ = ∑ᵢ (-1)ⁱ Fᵢ` of `∂Δⁿ⁺¹` splits as
`zₙ = z_N + (-1)ᵃ F`, where `z_N` is the part supported in `B` (the faces `Fᵢ` with `i ≠ last`) and
`F = F_last` is the face opposite the last vertex.  Consequently the class of `zₙ` in the relative
homology `Hₙ(∂Δⁿ⁺¹, B)` is (up to sign) the class of the simplex `F`, which is the image of the
class of the identity simplex under the pair map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)`.

## Main definitions

* `Work.HomologyExtra.simplexStar n` — the closed star `B` of the last vertex of `Δⁿ⁺¹`;
* `Work.HomologyExtra.simplexLastFace n` — the face `F` opposite the last vertex;
* `Work.HomologyExtra.simplexFacePairHom n` — the pair map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-- **The closed star of the last vertex of `Δⁿ⁺¹`**: the points of the boundary at which some
coordinate other than the last vanishes, i.e. the union of the faces opposite the vertices other
than the last, which is the closed star of the last vertex. -/
def simplexStar (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | ∃ i : Fin (n + 1), (x : simplex (n + 1)).weights (Fin.castSucc i) = 0}

/-- **The face of `Δⁿ⁺¹` opposite its last vertex.** -/
def simplexLastFace (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | (x : simplex (n + 1)).weights (Fin.last (n + 1)) = 0}

theorem mem_simplexStar {n : ℕ} {x : boundarySpace (n + 1)} :
    x ∈ simplexStar n ↔ ∃ i : Fin (n + 1), (x : simplex (n + 1)).weights (Fin.castSucc i) = 0 :=
  Iff.rfl

theorem mem_simplexLastFace {n : ℕ} {x : boundarySpace (n + 1)} :
    x ∈ simplexLastFace n ↔ (x : simplex (n + 1)).weights (Fin.last (n + 1)) = 0 :=
  Iff.rfl

/-- The equator is the intersection of the star of the last vertex with the opposite face. -/
theorem simplexEquator_eq_inter (n : ℕ) :
    simplexEquator n = simplexStar n ∩ simplexLastFace n := by
  ext x
  simp only [simplexEquator, simplexStar, simplexLastFace, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨h1, h2⟩

/-- The star of the last vertex together with the opposite face covers the boundary. -/
theorem simplexStar_union_lastFace (n : ℕ) :
    simplexStar n ∪ simplexLastFace n = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true, simplexStar, simplexLastFace, Set.mem_ofPred_eq]
  rcases x.2 with ⟨i, hi⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact Or.inl ⟨j, hi⟩
  · exact Or.inr hi

/-- The last face is the (image of the) last face map: this is the map which omits the last
vertex of the simplex. -/
theorem simplexFace_last_apply (n : ℕ) (w : simplex n) :
    (simplexFace n (Fin.last (n + 1))) w
      = Convexity.StdSimplex.map (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) w := by
  show (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove) w = _
  rw [Fin.succAbove_last]

/-- The barycentric coordinates of the image of a point under the last face map. -/
theorem weights_simplexFace_last (n : ℕ) (w : simplex n) (j : Fin (n + 1)) :
    ((simplexFace n (Fin.last (n + 1))) w : Convexity.StdSimplex ℝ (Fin (n + 2))).weights
        (Fin.castSucc j)
      = (w : Convexity.StdSimplex ℝ (Fin (n + 1))).weights j := by
  have h := congrArg (fun (x : Convexity.StdSimplex ℝ (Fin (n + 2))) =>
    x.weights (Fin.castSucc j)) (simplexFace_last_apply n w)
  simp only [Convexity.StdSimplex.weights_map] at h
  rw [h]
  exact Finsupp.mapDomain_apply' (Set.univ : Set (Fin (n + 1))) (M := ℝ)
    ((w : Convexity.StdSimplex ℝ (Fin (n + 1))).weights)
    (by simp) (Set.injOn_univ.mpr (Fin.castSucc_injective _)) (Set.mem_univ j)

/-- The `i`-th barycentric coordinate of a point in the image of the `i`-th face map vanishes. -/
theorem weights_simplexFace_self (n : ℕ) (i : Fin (n + 2)) (w : simplex n) :
    ((simplexFace n i) w : Convexity.StdSimplex ℝ (Fin (n + 2))).weights i = 0 := by
  show (Convexity.StdSimplex.map i.succAbove (w : Convexity.StdSimplex ℝ (Fin (n + 1)))).weights i = 0
  rw [Convexity.StdSimplex.weights_map]
  exact Finsupp.mapDomain_of_notMem_range _ _ (by
    rintro ⟨k, hk⟩
    exact Fin.succAbove_ne i k hk)

/-- **The image of the `i`-th face map lies in the closed star of the last vertex**, for `i` not
the last vertex. -/
theorem simplexFaceToBoundary_mem_star (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1))
    (w : simplex n) : (simplexFaceToBoundary n i) w ∈ simplexStar n := by
  obtain ⟨j, rfl⟩ := (Fin.eq_castSucc_or_eq_last i).resolve_right hi
  refine ⟨j, ?_⟩
  show ((simplexFace n (Fin.castSucc j)) w : Convexity.StdSimplex ℝ (Fin (n + 2))).weights
      (Fin.castSucc j) = 0
  exact weights_simplexFace_self n _ w

/-- **The pair map `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)`** given by the face of `Δⁿ⁺¹` opposite its last
vertex: the last face map, which sends the boundary of `Δⁿ` (the equator of `∂Δⁿ⁺¹`) into the
closed star `B` of the last vertex. -/
def simplexFacePairHom (n : ℕ) :
    Work.Homology.PairHom (simplex n) (boundarySpace (n + 1)) (simplexBoundary n)
      (simplexStar n) where
  hom := simplexFaceToBoundary n (Fin.last (n + 1))
  mapsTo := by
    intro w hw
    have h := hw
    rw [simplexBoundary] at h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    show ((simplexFace n (Fin.last (n + 1))) w : Convexity.StdSimplex ℝ (Fin (n + 2))).weights
        (Fin.castSucc i) = 0
    rw [weights_simplexFace_last]
    exact hi

end

end Work.HomologyExtra

-- appended: the Mayer-Vietoris cover used in the induction

namespace Work.HomologyExtra

noncomputable section

open scoped Simplicial

/-- **The open neighbourhood of the closed star `simplexStar n`** used for the Mayer–Vietoris
cover of `∂Δⁿ⁺¹`: the points having some coordinate other than the last smaller than `1/4`. -/
def simplexCoverU (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | ∃ i : Fin (n + 1), (x : simplex (n + 1)).weights (Fin.castSucc i) < 1/4}

/-- **The open neighbourhood of the face opposite the last vertex** used for the
Mayer–Vietoris cover of `∂Δⁿ⁺¹`. -/
def simplexCoverV (n : ℕ) : Set (boundarySpace (n + 1)) :=
  {x | (x : simplex (n + 1)).weights (Fin.last (n + 1)) < 1/4}

theorem mem_simplexCoverU {n : ℕ} {x : boundarySpace (n + 1)} :
    x ∈ simplexCoverU n ↔
      ∃ i : Fin (n + 1), (x : simplex (n + 1)).weights (Fin.castSucc i) < 1/4 := Iff.rfl

theorem mem_simplexCoverV {n : ℕ} {x : boundarySpace (n + 1)} :
    x ∈ simplexCoverV n ↔ (x : simplex (n + 1)).weights (Fin.last (n + 1)) < 1/4 := Iff.rfl

theorem simplexStar_subset_coverU (n : ℕ) : simplexStar n ⊆ simplexCoverU n := by
  rintro x ⟨i, hi⟩
  exact ⟨i, by rw [hi]; norm_num⟩

theorem simplexLastFace_subset_coverV (n : ℕ) : simplexLastFace n ⊆ simplexCoverV n := by
  intro x hx
  exact lt_of_le_of_lt hx.le (by norm_num)

theorem simplexEquator_subset_coverInter (n : ℕ) :
    simplexEquator n ⊆ simplexCoverU n ∩ simplexCoverV n := by
  rw [simplexEquator_eq_inter]
  intro x hx
  exact ⟨simplexStar_subset_coverU n hx.1, simplexLastFace_subset_coverV n hx.2⟩

/-- The cover of `∂Δⁿ⁺¹` by `simplexCoverU n` and `simplexCoverV n`. -/
theorem simplexCoverU_union_coverV (n : ℕ) :
    simplexCoverU n ∪ simplexCoverV n = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have h : x ∈ simplexStar n ∪ simplexLastFace n := by
    rw [simplexStar_union_lastFace]; exact Set.mem_univ x
  rcases h with h | h
  · exact Or.inl (simplexStar_subset_coverU n h)
  · exact Or.inr (simplexLastFace_subset_coverV n h)

theorem isOpen_simplexCoverU (n : ℕ) : IsOpen (simplexCoverU n) := by
  have h : simplexCoverU n = ⋃ i : Fin (n + 1),
      (fun x : boundarySpace (n + 1) => (x : simplex (n + 1)).weights (Fin.castSucc i))
        ⁻¹' (Set.Iio (1/4)) := by
    ext x
    rw [mem_simplexCoverU, Set.mem_iUnion]
    exact exists_congr fun i => Iff.rfl
  rw [h]
  exact isOpen_iUnion fun i => isOpen_lt
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.castSucc i)).comp
      continuous_subtype_val) continuous_const

theorem isOpen_simplexCoverV (n : ℕ) : IsOpen (simplexCoverV n) :=
  isOpen_lt ((Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.last (n + 1))).comp
    continuous_subtype_val) continuous_const

/-- **The part of the fundamental cycle of `∂Δⁿ⁺¹` carried by the closed star of the last
vertex**: the alternating sum of the faces `Fᵢ` with `i ≠ last`, so that
`simplexBoundaryChain n = simplexStarPartChain n + (-1) ^ last • F_last`. -/
noncomputable def simplexStarPartChain (n : ℕ) :
    Work.Homology.ZMod ⟶
      (Work.Homology.singChain Work.Homology.ZMod (boundarySpace (n + 1))).X n :=
  ∑ i ∈ Finset.univ.erase (Fin.last (n + 1)),
    ((-1 : ℤ) ^ (i : ℕ)) • simplexBoundaryFaceChain n i

/-- **The inclusion of the equator `∂F = simplexEquator n` into `∂Δⁿ⁺¹`**, the last face map
restricted to the boundary `∂Δⁿ`. -/
def simplexEquatorIncl (n : ℕ) : boundarySpace n ⟶ boundarySpace (n + 1) :=
  Work.Homology.incl (simplexBoundary n) ≫ simplexFaceToBoundary n (Fin.last (n + 1))

end

end Work.HomologyExtra
