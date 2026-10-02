import Submission.Work.PTGeometric.GenuineTransversality
import Submission.Work.Orient.Preimage

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: G5, the orientation of the transverse preimage, refined

`GenuineNullBordismData.orientation` (the datum of `Genuine.lean`) is the orientation of the
transverse preimage: the relative fundamental class induced by the ambient orientation together with
the **Thom class** of `γ_k`, with its boundary identified with the sum of the pieces' fundamental
classes (`hw`, the consumer's field) as an *oriented* bordism.

Following the project lead's addition (B) of 2026-09-25 this file splits that datum into the two named
inputs that actually produce it, so that neither the whole orientation datum nor the collar is
assumed:

* `HasOrientation` — **G5-(i)**: the transverse preimage is oriented by the ambient orientation and the
  Thom class of `γ_k` (an orientation family in the sense of
  `Work.Orient.IsHalfOrientationFamily`, the input of the ORIENT area).  Its *existence* of the
  relative fundamental class with the local-generator property is then ORIENT's theorem
  `Work.Orient.exists_relFundClass_of_halfOrientation`, which needs the collar (produced by
  construction, `GenuineNullBordismData.collar` / `Work.PTGeometric.Collar9`) and the named input
  `Work.Orient.RelativeFundamentalClassExists 8`;
* `BoundarySign` — **G5-(ii)**: the *sign* in the boundary identity.  ORIENT's boundary formula is
  deliberately sign-blind (`Work.Orient.BoundaryOrientationConvention`); the assertion that the class
  produced by ORIENT is the one whose boundary is the **sum** of the pieces' classes with `+` signs is
  the geometric statement, computed by TUBULAR's local degree `H₀^*U ⌢ [Sⁿ] = [V₀]`
  (`Work.Tubular.TubeLocalDegreeOnePoint`, the local degree of the collapse) together with the
  **cap-boundary formula** `∂(a ⌢ c) = (−1)^{|a|} (i^* a) ⌢ ∂c`, which is *already proved* in the
  workspace as `Work.Cohomology.cap_d` / `Work.Cohomology.pd_cap_boundary_boundary` and is therefore
  not an input.

`genuinePullbackOrientationData_of_orientation` re-assembles the datum from the two inputs, so the
deliverable can be run with them instead of the datum (`Assembly.lean`); the empty case `W = ∅` (in
which the preimage theorem's manifold may be empty, the datum being then vacuous) is handled
separately by the subsingleton of the homology of the empty boundary.

## Main definitions

* `Work.PTGeometric.HasOrientation`
* `Work.PTGeometric.BoundarySign`

## Main results

* `Work.PTGeometric.genuinePullbackOrientationData_of_orientation`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

variable {n k : ℕ}

/-- **G5-(i): the transverse preimage of the zero section carries an orientation.**

For every nonempty manifold model `W` of the preimage `F ⁻¹' X.core` there is an orientation family of
`W` (in the sense of `Work.Orient.IsHalfOrientationFamily`, i.e. a coherent choice of generators of
the local homology at every interior point): the orientation induced by the orientation of the
ambient `M` together with the orientation of the normal bundle of the core, i.e. the Thom class of
`γ_k` pulled back along the local trivialisations `Phi i`. -/
def HasOrientation (X : LocalCoreTarget n k) {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W] [Nonempty W]
    (hW : W ≃ₜ ↥(CorePreimage X F))
    (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (hW w : M) ∈ EndPreimage X F),
    ∃ γ : ∀ x : W, x ∉ (𝓡∂ 9).boundary W → Work.Orient.LocH (TopCat.of W) 9 x,
      Work.Orient.IsHalfOrientationFamily 8 (TopCat.of W) γ

/-- **G5-(ii): the sign of the boundary identity.**

For every nonempty manifold model `W` of the preimage and every orientation family `γ` of `W`, the
relative fundamental class produced by ORIENT (`Work.Orient.exists_relFundClass_of_halfOrientation`,
the `Classical.choose` of the existence theorem) has boundary *equal* to the sum of the pieces'
fundamental classes under the identification `bdryPreimage.trans e` of `∂W` with the pieces.

This is the statement whose proof is the local-degree computation: TUBULAR's
`Work.Tubular.TubeLocalDegreeOnePoint` (`U ⌢ c = z_*[V]`) fixes the sign, and the cap-boundary formula
`Work.Cohomology.cap_d` (already proved) transports it to the boundary identity.  It is stated as a
named input here because it is geometrically the statement that the *orientations* of the pieces are
the ones induced by the null-homotopy; ORIENT's own boundary formula is deliberately sign-blind. -/
def BoundarySign (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (X : LocalCoreTarget n k) (ι : Type) [Fintype ι] (Fam : ι → Work.ThomBordism.Man8)
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] (F : M → X.E)
    (e : ↥(EndPreimage X F) ≃ₜ (Σ i : ι, (Fam i).pt)) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
    [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W] [Nonempty W]
    (hW : W ≃ₜ ↥(CorePreimage X F))
    (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (hW w : M) ∈ EndPreimage X F)
    (γ : ∀ x : W, x ∉ (𝓡∂ 9).boundary W → Work.Orient.LocH (TopCat.of W) 9 x)
    (_hγ : Work.Orient.IsHalfOrientationFamily 8 (TopCat.of W) γ),
    ∃ bdryPreimage : ((𝓡∂ 9).boundary W) ≃ₜ ↥(EndPreimage X F),
      hPairδ (TopCat.of W) ((𝓡∂ 9).boundary W) 8
          (Classical.choose
            (Work.Orient.exists_relFundClass_of_halfOrientation hOrient W γ _hγ))
        = ∑ i, HomologicalComplex.homologyMap
            (Work.Cohomology.chainMap ℤ (Fam i).X (TopCat.of ((𝓡∂ 9).boundary W))
              (TopCat.ofHom ⟨fun y => (bdryPreimage.trans e).symm ⟨i, y⟩,
                (bdryPreimage.trans e).continuous_invFun.comp continuous_sigmaMk⟩)) 8 (Fam i).c

/-- **The orientation datum of `Genuine.lean` from its two G5 inputs.**

Given ORIENT's relative-fundamental-class existence theorem (whose input, the collar, is produced by
construction in `GenuineNullBordismData.collar`), the orientation family of the preimage
(`HasOrientation`) and the sign of the boundary identity (`BoundarySign`), the datum
`GenuinePullbackOrientationData` holds.

For a nonempty model `W` the relative fundamental class is ORIENT's
(`Work.Orient.exists_relFundClass_of_halfOrientation`), whose local-generator property is exactly the
field `w_fund` of the consumer and whose boundary is the sum by `BoundarySign`.  For the empty model
`W = ∅` the preimage is empty, both the local-generator property (no interior points) and the boundary
identity (the homology of the empty boundary is a subsingleton, so both sides vanish) are trivial. -/
theorem genuinePullbackOrientationData_of_orientation
    (hOrient : Work.Orient.RelativeFundamentalClassExists 8) {n k : ℕ} {X : LocalCoreTarget n k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] {F : M → X.E}
    {e : ↥(EndPreimage X F) ≃ₜ (Σ i : ι, (Fam i).pt)}
    (hγ : HasOrientation X F) (hsign : BoundarySign hOrient X ι Fam F e) :
    GenuinePullbackOrientationData X ι Fam F e := by
  intro W _tW _cW _mW _compW _t2W hW hbdry
  by_cases hne : Nonempty W
  · haveI := hne
    obtain ⟨γ, hγ'⟩ := hγ W hW hbdry
    obtain ⟨bdryPreimage, hsign'⟩ := hsign W hW hbdry γ hγ'
    obtain ⟨hw1, hw2, -⟩ :=
      Classical.choose_spec (Work.Orient.exists_relFundClass_of_halfOrientation hOrient W γ hγ')
    exact ⟨bdryPreimage, Classical.choose
      (Work.Orient.exists_relFundClass_of_halfOrientation hOrient W γ hγ'), hw2, hsign'⟩
  · -- the empty preimage: the preimage is empty, hence so is the end preimage; both the
    -- local-generator property and the boundary identity are then trivial
    haveI hbW : IsEmpty ↥((𝓡∂ 9).boundary W) := ⟨fun x => hne ⟨x.1⟩⟩
    haveI hbE : IsEmpty ↥(EndPreimage X F) := ⟨fun y => hne ⟨hW.symm ⟨y.1, y.2.2⟩⟩⟩
    refine ⟨?_, 0, ?_, ?_⟩
    · exact { toFun := fun x => (IsEmpty.false x).elim
              invFun := fun y => (IsEmpty.false y).elim
              left_inv := fun x => (IsEmpty.false x).elim
              right_inv := fun y => (IsEmpty.false y).elim
              continuous_toFun := continuous_iff_continuousAt.mpr fun x => (IsEmpty.false x).elim
              continuous_invFun := continuous_iff_continuousAt.mpr fun y => (IsEmpty.false y).elim }
    · intro x hx
      exact (hne ⟨x⟩).elim
    · haveI : Subsingleton
          ((Work.Cohomology.singularChains ℤ (TopCat.of ↥((𝓡∂ 9).boundary W))).homology 8) :=
        ModuleCat.subsingleton_of_isZero
          (Work.Cohomology.isZero_singularChains_homology_of_isEmpty
            (TopCat.of ↥((𝓡∂ 9).boundary W)) 8)
      rw [map_zero]
      exact (Finset.sum_eq_zero fun i _ => Subsingleton.elim _ _).symm

end

end Work.PTGeometric

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.Cohomology

variable {n k : ℕ}

/-- **The genuine geometric data with `G5` refined** (the project lead's addition (B)): the same as
`GenuineNullBordismData` with the orientation datum replaced by its two producing inputs, the
orientation family of the preimage (`HasOrientation`) and the sign of the boundary identity
(`BoundarySign`, whose proof is TUBULAR's local degree together with the cap-boundary formula). -/
structure GenuineNullBordismDataRefined (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (n k : ℕ) (X : LocalCoreTarget n k) (ι : Type) [Fintype ι] (Fam : ι → Work.ThomBordism.Man8) where
  /-- the disk with `N` holes -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  /-- the smooth null-homotopy of the collapse map, into the total space of `γ_k` -/
  c : M → X.E
  /-- smoothness of the null-homotopy -/
  contMDiff_c : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ c
  /-- transversality of the null-homotopy to the zero section -/
  transverse : IsCoreTransverse X (𝓡∂ ((8 + k) + 1)) c
  /-- transversality of the restriction to the boundary -/
  bndTransverse : IsCoreTransverseOnBoundary X c
  /-- the end preimage of the zero section is the disjoint union of the copies of the pieces -/
  endHomeo : ↥(EndPreimage X c) ≃ₜ (Σ i : ι, (Fam i).pt)
  /-- a collar of the preimage, by construction (addition (A)) -/
  collar : ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
      [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W]
      (hW : W ≃ₜ ↥(CorePreimage X c))
      (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (hW w : M) ∈ EndPreimage X c),
      Collar9 W
  /-- G5-(i): the orientation family of the preimage -/
  orientationFamily : HasOrientation X c
  /-- G5-(ii): the sign of the boundary identity -/
  boundarySign : BoundarySign hOrient X ι Fam c endHomeo

attribute [instance] GenuineNullBordismDataRefined.topologicalSpace
  GenuineNullBordismDataRefined.chartedSpace GenuineNullBordismDataRefined.isManifold
  GenuineNullBordismDataRefined.compactSpace GenuineNullBordismDataRefined.t2Space

/-- **The refined genuine data give the genuine data**: the orientation datum is re-assembled from
its two G5 inputs by `genuinePullbackOrientationData_of_orientation`. -/
def genuineNullBordismData_of_refined {hOrient : Work.Orient.RelativeFundamentalClassExists 8}
    {X : LocalCoreTarget n k} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (d : GenuineNullBordismDataRefined hOrient n k X ι Fam) :
    GenuineNullBordismData n k X ι Fam where
  M := d.M
  c := d.c
  contMDiff_c := d.contMDiff_c
  transverse := d.transverse
  bndTransverse := d.bndTransverse
  endHomeo := d.endHomeo
  collar := d.collar
  orientation :=
    genuinePullbackOrientationData_of_orientation hOrient d.orientationFamily d.boundarySign

/-- **The G5-refined geometric realisation** of the genuine Pontryagin–Thom class: as
`GenuineRealisation`, but producing the refined data (with the two named G5 inputs) instead of the
whole orientation datum. -/
structure GenuineRealisationRefined (hOrient : Work.Orient.RelativeFundamentalClassExists 8)
    (n k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) where
  /-- the manifold part of the Thom space, with the zero section as core -/
  X : LocalCoreTarget n k
  /-- the geometric realisation of a null-homotopy of a multiple of the genuine collapse class -/
  collapse : ∀ (ι : Type) [Fintype ι] (Fam : ι → Work.ThomBordism.Man8)
      (Nd : ∀ i, Work.ThomBordism.PontryaginThom.NormalBundlData (Fam i))
      (r : ∀ i, Work.Tubular.TubeThomRep k D (Fam i) (Nd i)) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (r i)) ^ m = 1 →
      GenuineNullBordismDataRefined hOrient n k X (Fin m × ι) (fun x => Fam x.2)

/-- **G6 from the G5-refined geometric realisation.** -/
theorem genuineTransversality_of_realisationRefined (hpre : LocalPreimageTheorem)
    {hOrient : Work.Orient.RelativeFundamentalClassExists 8} {n k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    (R : GenuineRealisationRefined hOrient n k D) : GenuineTransversality k D := by
  intro ι _ Fam Nd r m hm hpow
  exact ⟨m, hm, exists_nullBordismFamily_of_genuineData hpre
    (genuineNullBordismData_of_refined (R.collapse ι Fam Nd r m hm hpow))⟩

end

end Work.PTGeometric
