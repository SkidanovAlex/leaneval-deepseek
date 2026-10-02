import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.serreFibration_fibre_homology_iso
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.Serre.mpathFst_ratHomologyIso
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.sphRatHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational homology of the strict fibre equals that of the homotopy fibre

For a Serre fibration `p : E → B` over a path-connected base, the *strict* fibre
`fibre p b₀ = p⁻¹{b₀}` and the *homotopy* fibre `homotopyFibre p e₀` (the space of pairs `(e,γ)`
with `γ` a path from `p e₀` to `p e`) have the same rational homology in every degree.

## The two steps

**(1) The strict fibre and the homotopy fibre at the same base point.**  For `c : B` the homotopy
fibre `homotopyFibre p c` is the pullback of `p` along the path–loop fibration
`evalOne B c : PathSpace B c → B`:
`homotopyFibre p c = bundlePullback B c E p = Pullback p (evalOne B c)`.
The strict fibre `fibre p c` is the fibre of the projection
`pullbackSnd p (evalOne B c) : Pullback p (evalOne B c) → PathSpace B c` over the *constant* path
`constPath B c`.  Since the based path space is contractible (`Work.StemsB.contractible_pathSpace`,
by the reparametrisation `(γ,t) ↦ (s ↦ γ (revI t * s))`, which fixes `constPath`), the engine
`Work.Serre.isZero_relChains_fibre_of_contraction` gives that the pair
`(Pullback p (evalOne B c), fibre p c)` has vanishing relative integral homology, so the inclusion
of the fibre is a homology isomorphism
(`Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains`).  This is
`nonempty_intHomology_iso_fibre_homotopyFibre` below.

**(2) Base point transport.**  For a path `γ` in `B` from `b₀` to `p e₀`, the fibre homology is
transported along `γ` (`Work.Serre.serreFibration_fibre_homology_iso`).

**(3) Coefficients.**  The two isomorphisms above are integral; the rational ones are obtained by
extending scalars along the flat ring homomorphism `ℤ → ℚ`
(`Work.StemsB.SphRat.chainComplexBaseChange`, `homologyMapBaseChange`).

The final statement `Work.Serre.strictFibre_ratH_homotopyFibre` combines the three.
-/

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Glue lemmas -/

/-- Fibres of the same map over equal base points are canonically homeomorphic: the identity of the
total space restricts to a homeomorphism between the two fibres. -/
def sfFibreCongr (q : C(E, B)) {b b' : B} (h : b = b') :
    Work.StemsB.fibre q b ≃ₜ Work.StemsB.fibre q b' where
  toFun x := ⟨x.1, by rw [x.2, h]⟩
  invFun x := ⟨x.1, by rw [x.2, ← h]⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val

/-- A homeomorphism of spaces induces an isomorphism of integral singular homology in every
degree. -/
theorem nonempty_intHomology_iso_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology n ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n) :=
  ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo e))⟩

/-- **The `ℤ → ℚ` transfer of homology isomorphisms.**  If the integral singular homologies of `X`
and `Y` in degree `j` are isomorphic, then so are the rational ones, since the rational singular
chain complex is the extension of scalars of the integral one along the flat ring homomorphism
`ℤ → ℚ` (`Work.StemsB.SphRat.chainComplexBaseChange`), which preserves homology. -/
theorem nonempty_ratH_iso_of_intHomology_iso (X Y : TopCat) (j : ℕ)
    (h : Nonempty ((Work.Cohomology.singularChains ℤ X).homology j ≅
      (Work.Cohomology.singularChains ℤ Y).homology j)) :
    Nonempty (ratH X j ≅ ratH Y j) := by
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (Int.castRingHom ℚ)) := fun _ => inferInstance
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  haveI : F.PreservesHomology := inferInstance
  have key : ∀ Z : TopCat, ratH Z j ≅ F.obj ((Work.Cohomology.singularChains ℤ Z).homology j) := by
    intro Z
    have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Work.Cohomology.singularChains ℤ Z) ≅ Work.Cohomology.singularChains ℚ Z :=
      Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj Z) (ModuleCat.of ℤ ℤ) ≪≫
        Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj Z)
          Work.StemsB.SphRat.extendScalarsIntRatIso
    exact (HomologicalComplex.homologyMapIso hΦ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange F (Work.Cohomology.singularChains ℤ Z) j).some
  obtain ⟨e⟩ := h
  exact ⟨key X ≪≫ F.mapIso e ≪≫ (key Y).symm⟩

/-! ## The based path space

The contraction of the based path space onto the constant path must be read in the time direction
required by `Work.Serre.isZero_relChains_fibre_of_contraction` (identity at `t = 0`, constant at
`t = 1`), so we reverse the reparametrisation of `Work.StemsB.pathReparam` with `revI`. -/

/-- The deformation of the based path space onto the constant path at `c`, read with the identity
at time `0`: `(γ, t) ↦ (s ↦ γ (revI t * s))`. -/
def sfPathContr (B : Type) [TopologicalSpace B] (c : B) :
    C(Work.StemsB.PathSpace B c × unitInterval, Work.StemsB.PathSpace B c) where
  toFun q := Work.StemsB.pathReparam B c (q.1, revI q.2)
  continuous_toFun := (Work.StemsB.pathReparam B c).continuous.comp
    (Continuous.prodMk continuous_fst (revI.continuous.comp continuous_snd))

theorem sfPathContr_apply (B : Type) [TopologicalSpace B] (c : B)
    (γ : Work.StemsB.PathSpace B c) (t s : unitInterval) :
    (sfPathContr B c (γ, t)).1 s = γ.1 (revI t * s) := rfl

@[simp] theorem sfPathContr_zero (B : Type) [TopologicalSpace B] (c : B)
    (γ : Work.StemsB.PathSpace B c) : sfPathContr B c (γ, 0) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [sfPathContr_apply, revI_zero, one_mul]

@[simp] theorem sfPathContr_one (B : Type) [TopologicalSpace B] (c : B)
    (γ : Work.StemsB.PathSpace B c) :
    sfPathContr B c (γ, 1) = Work.StemsB.constPath B c := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [sfPathContr_apply, revI_one, zero_mul, Work.StemsB.constPath_apply]
  exact γ.2

@[simp] theorem sfPathContr_const (B : Type) [TopologicalSpace B] (c : B) (t : unitInterval) :
    sfPathContr B c (Work.StemsB.constPath B c, t) = Work.StemsB.constPath B c := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [sfPathContr_apply, Work.StemsB.constPath_apply, Work.StemsB.constPath_apply]

/-! ## The homeomorphisms relating the pullback, the strict fibre and the homotopy fibre -/

/-- **The fibre of `pullbackSnd p (evalOne B c)` over the constant path is the strict fibre.**  An
element of the fibre is a pair `(e, γ)` with `p e = γ 1` and `γ = constPath B c`, i.e. a point
`e` with `p e = c`. -/
def sfPullbackFibreHomeo (p : C(E, B)) (c : B) :
    ↥{x : Work.StemsB.Pullback p (Work.StemsB.evalOne B c) |
        Work.StemsB.pullbackSnd p (Work.StemsB.evalOne B c) x = Work.StemsB.constPath B c} ≃ₜ
      Work.StemsB.fibre p c where
  toFun x := ⟨x.1.1.1, by
    have h : x.1.1.2 = Work.StemsB.constPath B c := x.2
    rw [x.1.2, h]
    exact Work.StemsB.constPath_apply B c 1⟩
  invFun e := ⟨⟨(e.1, Work.StemsB.constPath B c), by
    show p e.1 = (Work.StemsB.constPath B c).1 1
    rw [Work.StemsB.constPath_apply]
    exact e.2⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (x.2).symm
  right_inv e := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- **The pullback of `p` along the path–loop fibration is the homotopy fibre.**  Both are
subtypes of `E × PathSpace B c` cut out by the two orientations of the same equation
`p e = γ 1`. -/
def sfPullbackBundleHomeo (p : C(E, B)) (c : B) :
    Work.StemsB.Pullback p (Work.StemsB.evalOne B c) ≃ₜ Work.StemsB.bundlePullback B c E p where
  toFun x := ⟨x.1, x.2.symm⟩
  invFun y := ⟨y.1, y.2.symm⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := by
    refine Continuous.subtype_mk continuous_subtype_val _

/-! ## Step (1): the strict fibre and the homotopy fibre at the same base point -/

/-- **The strict fibre `p⁻¹{p e}` and the homotopy fibre of `p` at `e` have isomorphic integral
homology.**  The homotopy fibre `Work.RatHurewicz.homotopyFibre p e` is the pullback
`Pullback p (evalOne B (p e))` of `p` along the path–loop fibration based at `p e`, and the strict
fibre `fibre p (p e)` is the fibre of the projection of that pullback over the constant path.  The
based path space is contractible onto the constant path (`sfPathContr`), so the relative homology
of the pair vanishes in every degree (the E2(d) engine
`Work.Serre.isZero_relChains_fibre_of_contraction`) and the inclusion of the fibre is a homology
isomorphism. -/
theorem nonempty_intHomology_iso_fibre_homotopyFibre (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (e : E) (j : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (p e)))).homology j ≅
      (Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.RatHurewicz.homotopyFibre p e))).homology j) := by
  let ev : C(Work.StemsB.PathSpace B (p e), B) := Work.StemsB.evalOne B (p e)
  let P : TopCat := TopCat.of (Work.StemsB.Pullback p ev)
  let F : Set P := {x | Work.StemsB.pullbackSnd p ev x = Work.StemsB.constPath B (p e)}
  have hserre : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd p ev) := fun n =>
    Work.StemsB.hasHLP_pullback p ev (hp n)
  have hrel : ∀ m, IsZero ((Work.Cohomology.relChains P F).homology m) := fun m =>
    isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p ev) hserre
      (Work.StemsB.constPath B (p e)) (sfPathContr B (p e))
      (sfPathContr_zero B (p e)) (sfPathContr_one B (p e)) (sfPathContr_const B (p e)) m
  haveI hF : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains P F) j) :=
    isIso_inclChains_homologyMap_of_isZero_relChains F hrel j
  exact ⟨(nonempty_intHomology_iso_of_homeo (sfPullbackFibreHomeo p (p e)) j).some.symm ≪≫
    asIso (HomologicalComplex.homologyMap (Work.Cohomology.inclChains P F) j) ≪≫
    (nonempty_intHomology_iso_of_homeo (sfPullbackBundleHomeo p (p e)) j).some⟩

/-! ## Step (2): base point transport along a path -/

/-- **The fibre homology of a Serre fibration is transported along a path.**  If `γ` is a path in
`B` from `z` to `z'`, then the fibres of `q` over `z` and over `z'` have isomorphic integral
homology (`Work.Serre.serreFibration_fibre_homology_iso`, with the endpoint discrepancy absorbed by
`sfFibreCongr`). -/
theorem nonempty_intHomology_iso_fibre_of_path {X Z : Type} [TopologicalSpace X]
    [TopologicalSpace Z] (q : C(X, Z)) (hq : Work.StemsB.IsSerreFibration q) {z z' : Z}
    (γ : C(unitInterval, Z)) (h0 : γ 0 = z) (h1 : γ 1 = z') (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q z))).homology n ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q z'))).homology n) := by
  obtain ⟨e⟩ := serreFibration_fibre_homology_iso q hq γ n
  obtain ⟨e₀⟩ := nonempty_intHomology_iso_of_homeo (sfFibreCongr q h0.symm) n
  obtain ⟨e₁⟩ := nonempty_intHomology_iso_of_homeo (sfFibreCongr q h1) n
  exact ⟨e₀ ≪≫ e ≪≫ e₁⟩

/-! ## The theorem -/

theorem strictFibre_ratH_homotopyFibre {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (b₀ : B)
    (hB : PathConnectedSpace B) (j : ℕ) :
    Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j ≅
      Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j) := by
  obtain ⟨γ⟩ := PathConnectedSpace.joined b₀ (p e₀)
  have h0 : (γ : C(unitInterval, B)) 0 = b₀ := γ.source'
  have h1 : (γ : C(unitInterval, B)) 1 = p e₀ := γ.target'
  obtain ⟨e₁⟩ := nonempty_ratH_iso_of_intHomology_iso
    (TopCat.of (Work.StemsB.fibre p b₀)) (TopCat.of (Work.StemsB.fibre p (p e₀))) j
    (nonempty_intHomology_iso_fibre_of_path p hp γ h0 h1 j)
  obtain ⟨e₂⟩ := nonempty_ratH_iso_of_intHomology_iso
    (TopCat.of (Work.StemsB.fibre p (p e₀)))
    (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j
    (nonempty_intHomology_iso_fibre_homotopyFibre p hp e₀ j)
  exact ⟨e₁ ≪≫ e₂⟩

end

end Work.Serre
