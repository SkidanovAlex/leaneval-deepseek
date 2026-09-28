import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.retract_stdSimplex_cube
import Submission.Work.RatHurewicz.hasHLP_of_retract
import Submission.Work.Serre.exists_path_pullbackFst

/-!
# A Serre fibration is surjective on singular simplices

If `q : X → B` is a Serre fibration, `X` is nonempty and `B` is path connected, then the induced
map `Sing X → Sing B` of singular simplicial sets is surjective in every degree: every singular
`n`-simplex of `B` lifts to `X`.

The proof is the standard one.  The standard topological simplex `Δⁿ = stdSimplex ℝ (Fin (n+1))` is
a retract of the cube `I^{n+1}` (`Work.RatHurewicz.retract_stdSimplex_cube`), so the homotopy
lifting property transfers from cubes to `Δⁿ` (`Work.RatHurewicz.hasHLP_of_retract`).  Given a
singular `n`-simplex `sg : Δⁿ → B`, choose a point `x₀` of `X` over `sg y₀` for a point `y₀` of the
simplex (path lifting, `Work.Serre.exists_path_lift_of_isSerreFibration`, using that `B` is path
connected).  Since the simplex is contractible there is a homotopy from the identity of `Δⁿ` to the
constant map at `y₀`, hence `sg` is homotopic to the constant map at `sg y₀`; the homotopy lifting
property lifts this homotopy starting at the constant map at `x₀`, and the final map of the lifted
homotopy is the desired lift of `sg`.

The identification of `n`-simplices of `TopCat.toSSet.obj X` with continuous maps
`stdSimplex ℝ (Fin (n+1)) → X` is `TopCat.toSSetObjEquivT`, and its naturality with respect to
`toSSet.map (TopCat.ofHom q)` is `Work.Serre.toSSetObjEquiv_ofHom_apply` below.
-/

open scoped Topology unitInterval
open CategoryTheory

namespace Work.Serre

noncomputable section

/-- The value of the identification `TopCat.toSSetObjEquivT` on `toSSet.map (TopCat.ofHom q)` is
postcomposition with `q`.  This is the naturality of `TopCat.toSSetObjEquivT` with respect to the
functoriality of `TopCat.toSSet` in the space. -/
theorem toSSetObjEquiv_ofHom_apply {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (m : SimplexCategoryᵒᵖ)
    (x : (TopCat.toSSet.obj (TopCat.of X)).obj m)
    (t : stdSimplex ℝ (Fin (m.unop.len + 1))) :
    ((TopCat.toSSetObjEquivT (TopCat.of B) m)
        ((TopCat.toSSet.map (TopCat.ofHom q)).app m x)) t
      = q (((TopCat.toSSetObjEquivT (TopCat.of X) m) x) t) :=
  rfl

/-- **A Serre fibration is surjective on singular simplices.**  For a Serre fibration `q : X → B`
with `X` nonempty and `B` path connected, every singular `n`-simplex of `B` is the image of a
singular `n`-simplex of `X`. -/
theorem liftSurjectiveSerreFibration {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) [Nonempty X] [PathConnectedSpace B]
    (n : ℕ) :
    Function.Surjective ((TopCat.toSSet.map (TopCat.ofHom q)).app
      (Opposite.op (SimplexCategory.mk n))) := by
  -- the homotopy lifting property with respect to the standard `n`-simplex
  have hHLP : Work.StemsB.HasHLP q (stdSimplex ℝ (Fin (n + 1))) := by
    obtain ⟨i, r, hri⟩ := Work.RatHurewicz.retract_stdSimplex_cube n
    exact Work.RatHurewicz.hasHLP_of_retract q i r hri (hq (n + 1))
  -- the standard simplex is contractible
  haveI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨Pi.single 0 1, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩
  intro y
  set sg : C(stdSimplex ℝ (Fin (n + 1)), B) :=
    (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n))) y with hsg
  -- a homotopy from the identity of the simplex to a constant map
  obtain ⟨y₀, hΦ⟩ := id_nullhomotopic (stdSimplex ℝ (Fin (n + 1)))
  let Φ : (ContinuousMap.id (stdSimplex ℝ (Fin (n + 1)))).Homotopy
      (ContinuousMap.const _ y₀) := hΦ.some
  -- a point of `X` lying over `sg y₀`
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨γ⟩ := PathConnectedSpace.joined (q x) (sg y₀)
  obtain ⟨x₀, hx₀, -⟩ :=
    exists_path_lift_of_isSerreFibration q hq (e := x) (b := q x) (b' := sg y₀) rfl γ
  -- the homotopy from the constant map at `sg y₀` to `sg`
  have H : (ContinuousMap.const _ (sg y₀)).Homotopy sg :=
    { toContinuousMap :=
        ⟨fun p : I × stdSimplex ℝ (Fin (n + 1)) => sg (Φ.symm p),
          sg.continuous.comp Φ.symm.continuous⟩
      map_zero_left := by
        intro z
        show sg (Φ.symm (0, z)) = sg y₀
        rw [ContinuousMap.Homotopy.apply_zero]
        rfl
      map_one_left := by
        intro z
        show sg (Φ.symm (1, z)) = sg z
        rw [ContinuousMap.Homotopy.apply_one]
        rfl }
  -- the same homotopy, reindexed so that its initial map is the constant at `x₀`
  have HK : (q.comp (ContinuousMap.const _ x₀)).Homotopy sg :=
    { toContinuousMap := H.toContinuousMap
      map_zero_left := by
        intro z
        show H (0, z) = q x₀
        rw [H.apply_zero]
        exact hx₀.symm
      map_one_left := by
        intro z
        show H (1, z) = sg z
        exact H.apply_one z }
  obtain ⟨g, H', hH'⟩ := hHLP (ContinuousMap.const _ x₀) sg HK
  have hg : q.comp g = sg := by
    ext z
    show q (g z) = sg z
    have h := congrArg (fun F : C(I × (stdSimplex ℝ (Fin (n + 1))), B) => F (1, z)) hH'
    simp only [ContinuousMap.comp_apply] at h
    rw [show H'.toContinuousMap (1, z) = g z from H'.apply_one z] at h
    rw [show HK.toContinuousMap (1, z) = sg z from HK.map_one_left z] at h
    exact h
  refine ⟨(TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk n))).symm g, ?_⟩
  apply (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n))).injective
  rw [← hsg]
  show (TopCat.toSSetObjEquivT (TopCat.of B) (Opposite.op (SimplexCategory.mk n)))
      ((TopCat.toSSet.map (TopCat.ofHom q)).app (Opposite.op (SimplexCategory.mk n))
        ((TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op (SimplexCategory.mk n))).symm g)) = sg
  ext t
  rw [toSSetObjEquiv_ofHom_apply]
  rw [Equiv.apply_symm_apply]
  show q (g t) = sg t
  exact congrFun (congrArg DFunLike.coe hg) t

end

end Work.Serre
