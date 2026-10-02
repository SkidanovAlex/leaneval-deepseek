import Mathlib
import Submission.Work.Thom.tautologicalQuotient
import Submission.Work.Thom.sumEps
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.coreMorphism

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Stability of the Chern classes: the definitions

The reduction of *stability* `c_j(E ⊕ ε) = c_j(E)` (README ADDENDUM 23.3) to an explicit bundle
isomorphism is made precise here.  The key observation of this module is that one should **not**
work over the locus `{u ≠ 0}` of the punctured total space: instead one uses the tautological
section `s : B → V∖0`, `b ↦ (b, ∂)`, of the sum `V = E ⊕ ε¹` (with `∂` the unit vector of the
trivial summand), which is a continuous nowhere-zero section.  Then

* `s^*(π^*c_j(V)) = (π ∘ s)^* c_j(V) = c_j(V)`, so `c_j(V)` is recovered from the tautological
  quotient `Q_V = π^*V/ℂ·s` by pulling back along `s`;
* `s^*(Q_V)` is a bundle over `B` with fibre `ℂ^m`, canonically isomorphic to `E` by the fibrewise
  linear map "take the `E`-part of the representative with vanishing `ε`-coordinate".

## The linear algebra of the standard fibre

The summands of the identification `ℂ^{m+1} ≃ ℂ^m × ℂ¹` are

* `Work.Thom.EpartCLM m : ℂ^{m+1} →L[ℂ] ℂ^m`, `Work.Thom.epsVecCLM m : ℂ^{m+1} →L[ℂ] ℂ¹` and
  `Work.Thom.epsFunCLM m : ℂ^{m+1} →L[ℂ] ℂ` (the scalar `ε`-coordinate);
* `Work.Thom.jCLM m : ℂ^m →L[ℂ] ℂ^{m+1}`, `y ↦ (y, 0)`;
* `Work.Thom.sumUnit m = ∂`, the unit vector of the trivial summand.

## The section and the two bundles

* `Work.Thom.sumPoint`, `Work.Thom.sumSection` — the section `b ↦ (b, ∂)`;
* `Work.Thom.sumQuotient Z` — the pullback `s^*(Q_{Z ⊕ ε¹})`, a bundle over `B`;
* `Work.Thom.sumToZ`, `Work.Thom.sumToQ` — the two fibrewise maps of the isomorphism
  `Z ≅ s^*(Q_{Z⊕ε¹})`.
-/

namespace Work.Thom

open Work.TangentClasses

open scoped Topology

noncomputable section

/-! ## The linear algebra of the standard fibre `ℂ^{m+1} = ℂ^m × ℂ¹` -/

/-- The projection of the standard fibre `ℂ^{m+1}` onto its `ℂ^m`-part, along the identification
`Work.Thom.prodFinEquiv`. -/
def EpartCLM (m : ℕ) : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (ContinuousLinearMap.fst ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))).comp
    ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- The projection of the standard fibre `ℂ^{m+1}` onto its `ℂ¹`-part. -/
def epsVecCLM (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  (ContinuousLinearMap.snd ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1))).comp
    ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)))

/-- The scalar `ε`-coordinate of the standard fibre `ℂ^{m+1}`.  It is *not* the last coordinate of
`ℂ^{m+1}`: the identification of the sum `Z ⊕ ε¹` with the standard fibre is `prodFinEquiv`, an
arbitrary continuous linear equivalence. -/
def epsFunCLM (m : ℕ) : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] ℂ :=
  (evalCLM (0 : Fin 1)).comp (epsVecCLM m)

/-- The section `ℂ^m → ℂ^{m+1}`, `y ↦ (y, 0)`, of the `ε`-coordinate. -/
def jCLM (m : ℕ) : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)) :=
  ((prodFinEquiv m).toContinuousLinearMap).comp
    (ContinuousLinearMap.inl ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin 1)))

/-- **The unit vector `∂ = (0, 1)` of the trivial summand** in the standard fibre `ℂ^{m+1}`. -/
def sumUnit (m : ℕ) : EuclideanSpace ℂ (Fin (m + 1)) :=
  prodFinEquiv m (0, basisVec (0 : Fin 1))

/-! ## Continuity of a constant-family section, over an arbitrary normed field -/

section SectionGen

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {ι : Type*}

/-- **Continuity of a constant-family section of a bundle over an arbitrary normed field** — the
field-general form of `Work.Thom.continuous_section_mk`
(`Submission/Work/Thom/Continuous.lean`), whose proof uses no property of `ℝ`.  If `b : X → B` is
continuous and `g : X → F` takes values in the subspace of `F` fixed by every transition function
over `b x`, then `x ↦ ⟨b x, g x⟩` is a continuous section. -/
theorem continuous_section_mk_gen {X : Type*} [TopologicalSpace X]
    (Z : VectorBundleCore 𝕜 B F ι) (b : C(X, B)) (g : C(X, F))
    (h : ∀ x i j, b x ∈ Z.baseSet i ∩ Z.baseSet j → Z.coordChange i j (b x) (g x) = g x) :
    Continuous (fun x => (⟨b x, g x⟩ : Z.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set i := Z.indexAt (b x₀) with hi
  have hx0 : b x₀ ∈ Z.baseSet i := by rw [hi]; exact Z.mem_baseSet_at (b x₀)
  have hU : ∀ᶠ x in 𝓝 x₀, b x ∈ Z.baseSet i :=
    b.continuous.continuousAt.preimage_mem_nhds ((Z.isOpen_baseSet i).mem_nhds hx0)
  have hθ : ContinuousAt (fun x => (b x, g x)) x₀ :=
    b.continuous.continuousAt.prodMk g.continuous.continuousAt
  have hev : (fun x => (Z.localTriv i) (⟨b x, g x⟩ : Z.TotalSpace)) =ᶠ[𝓝 x₀]
      (fun x => (b x, g x)) := by
    filter_upwards [hU] with x hx
    rw [VectorBundleCore.localTriv_apply]
    exact Prod.ext rfl (h x (Z.indexAt (b x)) i ⟨Z.mem_baseSet_at (b x), hx⟩)
  refine (Z.localTriv i).continuousAt_of_comp_left ?_ hx0 ?_
  · show ContinuousAt (fun x => Z.proj (⟨b x, g x⟩ : Z.TotalSpace)) x₀
    rw [show (fun x => Z.proj (⟨b x, g x⟩ : Z.TotalSpace)) = fun x => b x from by funext x; rfl]
    exact b.continuous.continuousAt
  · show ContinuousAt (fun x => (Z.localTriv i) (⟨b x, g x⟩ : Z.TotalSpace)) x₀
    exact hθ.congr hev.symm

end SectionGen

section Stability

variable {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The unit vector `∂` is fixed by every transition function of `sumEps ι₀ Z`.**  This is the
content of the stability of `Z ⊕ ε¹`: the trivial summand has constant transition functions. -/
theorem sumEps_coordChange_sumUnit (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i j : ι × ι₀) (b : B) :
    (sumEps ι₀ Z).coordChange i j b (sumUnit m) = sumUnit m := by
  rw [sumEps_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    bundleSum_coordChange, ContinuousLinearMap.coe_prodMap']
  have hsymm : ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1))) (sumUnit m)
      = (0, basisVec (0 : Fin 1)) := by
    rw [sumUnit, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [hsymm, Prod.map_apply]
  show prodFinEquiv m ((Z.coordChange i.1 j.1 b) 0, (trivialVectorBundleCore ℂ B
    (EuclideanSpace ℂ (Fin 1)) ι₀).coordChange i.2 j.2 b (basisVec (0 : Fin 1))) = sumUnit m
  rw [map_zero, sumUnit]
  rfl

variable {ι₀ : Type} [Inhabited ι₀]

/-- The point `b ↦ (b, ∂)` of the total space of the sum `Z ⊕ ε¹`, over the standard fibre. -/
def sumPoint (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (realification (sumEps ι₀ Z)).TotalSpace :=
  ⟨b, sumUnit m⟩

/-- **The unit vector of the trivial summand is non-zero.** -/
theorem sumUnit_ne_zero (m : ℕ) : sumUnit m ≠ 0 := by
  intro h
  have h1 : ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1))) (sumUnit m)
      = ((prodFinEquiv m).symm : EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1))) 0 := by rw [h]
  rw [sumUnit, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h1
  simp only [map_zero] at h1
  have h2 : basisVec (0 : Fin 1) = 0 := congrArg Prod.snd h1
  have h3 := congrFun (congrArg WithLp.ofLp h2) (0 : Fin 1)
  rw [basisVec_apply] at h3
  exact one_ne_zero h3

/-- The section `b ↦ (b, ∂)` never vanishes. -/
theorem sumPoint_ne_zero (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (sumPoint ι₀ Z b).2 ≠ 0 :=
  sumUnit_ne_zero m

/-- **The tautological section of `Z ⊕ ε¹` along the trivial summand**, as a continuous map into the
punctured total space. -/
def sumSection (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    C(B, ↥(zeroComplement (realification (sumEps ι₀ Z)))) :=
  ⟨fun b => ⟨sumPoint ι₀ Z b, sumPoint_ne_zero ι₀ Z b⟩, by
    refine Continuous.subtype_mk ?_ _
    refine continuous_section_mk_gen (realification (sumEps ι₀ Z)) (ContinuousMap.id B)
      (ContinuousMap.const B (sumUnit m)) ?_
    intro b i j _
    rw [realification_coordChange]
    exact sumEps_coordChange_sumUnit ι₀ Z i j b⟩

/-- **The pullback of the tautological quotient along the tautological section**: the bundle
`s^*(Z ⊕ ε¹ / ℂ·s)` over `B`, of rank `m`. -/
def sumQuotient (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ((ι × ι₀) × Fin (m + 1)) :=
  bundleComap (tautQuotientCore (sumEps ι₀ Z)) (sumSection ι₀ Z)

/-- **The coordinate of the tautological section used by the tautological quotient**, at `b`. -/
def sumCoord (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) : Fin (m + 1) :=
  tqCoord (sumEps ι₀ Z) (sumSection ι₀ Z b)

/-- The index of the pullback of the tautological quotient, **explicitly**. -/
theorem sumQuotient_indexAt (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (sumQuotient ι₀ Z).indexAt b = ((Z.indexAt b, default), sumCoord ι₀ Z b) := by
  have hproj : ((sumSection ι₀ Z b : ↥(zeroComplement (realification (sumEps ι₀ Z)))) :
      (realification (sumEps ι₀ Z)).TotalSpace).1 = b := rfl
  rw [sumQuotient, bundleComap_indexAt, tautQuotientCore_indexAt, hproj, sumEps_indexAt,
    bundleSum_indexAt, sumCoord]
  rfl

/-- **The fibrewise map `s^*(Z ⊕ ε¹ / ℂ·s) → Z`**: the `E`-part of the representative of a class
with vanishing `ε`-coordinate.  In the quotient chart at `b` the coordinate vector `z : ℂ^m`
corresponds to `fillFun k z` (`k = sumCoord ι₀ Z b`); the class modulo `ℂ·∂` has a unique
representative with vanishing `ε`-coordinate, whose `E`-part is the image. -/
def sumToZ (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (EpartCLM m).comp (fillCLM (sumCoord ι₀ Z b))

/-- **The fibrewise map `Z → s^*(Z ⊕ ε¹ / ℂ·s)`**, the inverse of `Work.Thom.sumToZ`: the class of
`(y, 0)` modulo `ℂ·∂`. -/
def sumToQ (ι₀ : Type) [Inhabited ι₀]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
  (quoCLM (sumCoord ι₀ Z b) (sumUnit m)).comp (jCLM m)

end Stability



end

end Work.Thom
