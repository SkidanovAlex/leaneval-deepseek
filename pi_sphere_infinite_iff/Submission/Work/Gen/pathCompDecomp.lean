import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Gen.PathCompDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Gen

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `π₀`-class of a point of `X`, as an element of the connected components of the singular
simplicial set of `X`.  By definition this is the condition defining `Work.Gen.pathComp`. -/
def pointComp (x : X) : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) :=
  SSet.π₀.mk (TopCat.toSSetObj₀Equiv (X := TopCat.of X).symm x)

/-- The continuous map underlying a singular `n`-simplex. -/
def simplexMap {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquivT (X := TopCat.of X) _ σ

@[simp]
theorem simplexMap_apply {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (z : stdSimplex ℝ (Fin (n + 1))) :
    simplexMap σ z = (TopCat.toSSetObjEquivT (X := TopCat.of X) _ σ) z := rfl

/-- **All points of the image of a simplex have the same `π₀`-class.**  The image of the standard
simplex is path connected (it is convex), so its points are joined by paths in `X`. -/
theorem pointComp_simplex_image_eq {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), X))
    (z z' : stdSimplex ℝ (Fin (n + 1))) : pointComp (f z) = pointComp (f z') := by
  have hseg : (segment ℝ (z : Fin (n + 1) → ℝ) (z' : Fin (n + 1) → ℝ)) ⊆
      stdSimplex ℝ (Fin (n + 1)) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).segment_subset z.2 z'.2
  have hJI : JoinedIn (stdSimplex ℝ (Fin (n + 1))) (z : Fin (n + 1) → ℝ)
      (z' : Fin (n + 1) → ℝ) := JoinedIn.of_segment_subset hseg
  have hJ : Joined (f z) (f z') := (hJI.joined_subtype).map f.continuous
  have key : ZerothHomotopy.mk (f z) = ZerothHomotopy.mk (f z') :=
    ZerothHomotopy.sound hJ.somePath
  have := congrArg (TopCat.zerothHomotopyEquiv (X := TopCat.of X)) key
  rwa [TopCat.zerothHomotopyEquiv_mk, TopCat.zerothHomotopyEquiv_mk] at this

/-- The `π₀`-class of a singular simplex: the class of the points of its image. -/
def simpComp {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌) :
    SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) :=
  pointComp (simplexMap σ (stdSimplex.vertex (0 : Fin (n + 1))))

/-- Every point of the image of `σ` lies in the component `simpComp σ`. -/
theorem pointComp_simplexMap_eq {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (z : stdSimplex ℝ (Fin (n + 1))) : pointComp (simplexMap σ z) = simpComp σ :=
  pointComp_simplex_image_eq _ z _

/-- **The `π₀`-class of a simplex is unchanged by taking faces.** -/
theorem simpComp_δ {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n + 1⦌)
    (i : Fin (n + 2)) : simpComp ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = simpComp σ := by
  rw [simpComp, simpComp, simplexMap, simplexMap, TopCat.toSSetObjEquivT_δ_apply]
  exact pointComp_simplex_image_eq _ _ _

/-- A chosen point of the path component `c`.  Every `π₀`-class is the class of a point. -/
def ptOfComp (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) : ↥(pathComp X c) :=
  let h : ∃ x : X, pointComp x = c := by
    obtain ⟨s, rfl⟩ := SSet.π₀.mk_surjective (X := TopCat.toSSet.obj (TopCat.of X)) c
    exact ⟨TopCat.toSSetObj₀Equiv (X := TopCat.of X) s, by
      rw [pointComp, Equiv.symm_apply_apply]⟩
  ⟨h.choose, h.choose_spec⟩

/-- The constant simplex at a point of a path component. -/
def constSimplex (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) (n : ℕ) :
    (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌ :=
  (TopCat.toSSetObjEquivT (X := pathComp X c) _).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) (ptOfComp c))

/-- The faces of a constant simplex are the constant simplices. -/
theorem constSimplex_δ (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) {n : ℕ}
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (pathComp X c)).δ i (constSimplex c (n + 1)) = constSimplex c n := by
  apply (TopCat.toSSetObjEquivT (X := pathComp X c) _).injective
  ext z
  rw [TopCat.toSSetObjEquivT_δ_apply]
  simp [constSimplex]

end

end Work.Gen

namespace Work.Gen

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- Naturality of `TopCat.toSSetObjEquivT` in the space: `toSSet` acts on simplices by
postcomposition.  (A local copy of `Work.Bordism.toSSetObjEquiv_map_apply`.) -/
theorem toSSetObjEquiv_map_apply' {Y Z : TopCat} (g : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj Y).obj n) :
    (TopCat.toSSetObjEquivT Z n) ((TopCat.toSSet.map g).app n x) =
      g.hom.comp ((TopCat.toSSetObjEquivT Y n) x) := rfl

/-- The simplicial map induced by the inclusion of a path component is injective on simplices: it
is postcomposition with the injective map `pathCompIncl X c`. -/
theorem toSSet_map_incl_injective (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) (n : ℕ) :
    Function.Injective
      ((TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app (Opposite.op ⦋n⦌)) := by
  intro t₁ t₂ h
  have hnat : ∀ t : (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌,
      (pathCompIncl X c).comp (TopCat.toSSetObjEquivT (X := pathComp X c) _ t) =
        TopCat.toSSetObjEquivT (X := TopCat.of X) _
          ((TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app _ t) := fun t => rfl
  have h' : (pathCompIncl X c).comp (TopCat.toSSetObjEquivT (X := pathComp X c) _ t₁) =
      (pathCompIncl X c).comp (TopCat.toSSetObjEquivT (X := pathComp X c) _ t₂) := by
    rw [hnat t₁, hnat t₂, h]
  apply (TopCat.toSSetObjEquivT (X := pathComp X c) (Opposite.op ⦋n⦌)).injective
  ext z
  exact Subtype.ext (ContinuousMap.congr_fun h' z)

/-- The `π₀`-class of a simplex lying in a fixed component is that component. -/
theorem simpComp_map_incl (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) {n : ℕ}
    (t : (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌) :
    simpComp ((TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app (Opposite.op ⦋n⦌) t) =
      c := by
  show pointComp (simplexMap _ (stdSimplex.vertex (0 : Fin (n + 1)))) = c
  rw [show simplexMap ((TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app
        (Opposite.op ⦋n⦌) t) = (pathCompIncl X c).comp (simplexMap t) from rfl]
  exact (simplexMap t (stdSimplex.vertex (0 : Fin (n + 1)))).2

/-- The lift of a simplex through the inclusion of the component containing it. -/
noncomputable def factorGenuine {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) (h : simpComp σ = c) :
    (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌ :=
  (TopCat.toSSetObjEquivT (X := pathComp X c) _).symm
    { toFun := fun z => ⟨simplexMap σ z, (pointComp_simplexMap_eq σ z).trans h⟩
      continuous_toFun := (simplexMap σ).continuous.subtype_mk
        (fun z => (pointComp_simplexMap_eq σ z).trans h) }

/-- **A simplex of `X` whose component is `c`, lifted to the component.**  For `simpComp σ = c`
this is a genuine lift of `σ` through the inclusion; when `simpComp σ ≠ c` we use the constant
simplex at a chosen point of `c`, so that the construction is defined for all pairs `(σ, c)` and
is compatible with faces. -/
noncomputable def factorWith {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) :
    (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌ :=
  letI := Classical.propDecidable
  if h : simpComp σ = c then factorGenuine σ c h else constSimplex c n

/-- When the component of `σ` is `c`, `factorWith σ c` is a lift of `σ` through the inclusion of
the component. -/
theorem factorWith_spec {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) (h : simpComp σ = c) :
    (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app (Opposite.op ⦋n⦌)
        (factorWith σ c) = σ := by
  rw [factorWith, dif_pos h]
  apply (TopCat.toSSetObjEquivT (X := TopCat.of X) (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_map_apply', factorGenuine, Equiv.apply_symm_apply]
  ext z
  rfl

/-- Any lift of `σ` through the inclusion of the component of `σ` is `factorWith σ c`
(the inclusion is injective on simplices). -/
theorem factorWith_unique {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌)
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)))
    (t : (TopCat.toSSet.obj (pathComp X c)) _⦋n⦌)
    (h : (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app (Opposite.op ⦋n⦌) t = σ) :
    t = factorWith σ c := by
  have hc : simpComp σ = c := by rw [← h]; exact simpComp_map_incl c t
  exact toSSet_map_incl_injective c n (by rw [h, factorWith_spec σ c hc])

/-- The lift `factorWith` is compatible with faces. -/
theorem factorWith_δ {n : ℕ} (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋n + 1⦌) (i : Fin (n + 2))
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) :
    factorWith ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) c =
      (TopCat.toSSet.obj (pathComp X c)).δ i (factorWith σ c) := by
  by_cases h : simpComp σ = c
  · have h' : simpComp ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = c := by
      rw [simpComp_δ, h]
    apply toSSet_map_incl_injective c n
    have e1 := factorWith_spec ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) c h'
    have e2 : (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app (Opposite.op ⦋n⦌)
        ((TopCat.toSSet.obj (pathComp X c)).δ i (factorWith σ c)) =
        (TopCat.toSSet.obj (TopCat.of X)).δ i σ := by
      rw [SSet.δ_naturality_apply, factorWith_spec σ c h]
    rw [e1, e2]
  · have h' : ¬ (simpComp ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = c) := by
      rw [simpComp_δ]; exact h
    rw [factorWith, dif_neg h', factorWith, dif_neg h, constSimplex_δ]

end

end Work.Gen
