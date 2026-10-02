import Mathlib
import Submission.Work.StemsB.cohomology_collar_iso
import Submission.Work.Thom.ModelThomBase
import Submission.Work.StemsB.SerreSphereCollar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The collar pair of the sphere model carries a Thom class

For `b ≥ 1`, the pair `(Q, C)` with `Q = ↥(sphLoopBig b) × Y` and `C = sphLoopCollarProd b Y`
is a "Thom pair" over `Y`: there is a class `τ ∈ H^b(Q, C; ℤ)` for which cupping,
`x ↦ π^*(x) ⌣ τ`, is a bijection `H^k(Y; ℤ) → H^{k+b}(Q, C; ℤ)` in every degree `k`.

This upgrades the mere existence of the isomorphism `Work.StemsB.cohomology_collar_iso` to a
statement about a *specific* class, and it is the companion of the suspension class
`Work.StemsB.CollarSuspension` (`WangDerivation.lean`).

The proof transports the model Thom class of the trivial bundle
(`Work.Thom.modelThom_all`, i.e. `Work.Thom.ModelThom Y b`) along the chain of pair maps

  `(Y × ℝᵇ, Y × Sᵇ⁻¹) ⊇ (Y × Dᵇ, Y × Sᵇ⁻¹) ≅ (Y × Iᵇ, Y × ∂Iᵇ) ≅ (Iᵇ × Y, ∂Iᵇ × Y)`
  `  ← (eucBig b × Y, eucCollar b × Y) ≅ (↥(sphLoopBig b) × Y, sphLoopCollarProd b Y)`

using `Work.Thom.cupMap_transfer_fwd`, which moves a Thom class along a map of pairs whose
pullback on relative cohomology is bijective and which commutes with the projections to the base.
Each step's bijectivity is one of the geometric facts already available in this directory:

* `Work.Thom.bijective_relCohMap_discFull` (the disc pair is a deformation retract of the
  trivial bundle);
* `Work.Thom.bijective_relCohMap_of_homeomorph` (the radial cube/ball homeomorphism and the
  factor swap);
* `Work.Thom.bijective_relCohMap_of_homotopyEquiv` (the radial normalisation
  `collarNorm`, and the coordinate extraction `bigToEucMap`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

open CategoryTheory CategoryTheory.Limits

theorem collar_thomClass (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y] :
    ∃ τ : Work.Thom.RelCoh ℤ b (↥(Work.StemsB.sphLoopBig b) × Y)
        (Work.StemsB.sphLoopCollarProd b Y),
      ∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
        (Work.Thom.mixedCupC ℤ (Work.StemsB.sphLoopCollarProd b Y) k b)
          ((Work.Thom.CohMap (⟨fun p : ↥(Work.StemsB.sphLoopBig b) × Y => p.2, by fun_prop⟩ :
            C(↥(Work.StemsB.sphLoopBig b) × Y, Y)) ℤ k).hom x) τ) := by
  obtain ⟨σ₀, hσ₀⟩ := Work.Thom.modelThom_all Y PUnit (n := b) hb
  -- Step A: the disc pair `(Y × Dᵇ, Y × Sᵇ⁻¹)` attached to the trivial bundle.
  let fA : C(Y × Work.Thom.MBall b, Y × EuclideanSpace ℝ (Fin b)) :=
    ⟨fun q => (q.1, q.2.1), continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩
  let AA : Set (Y × EuclideanSpace ℝ (Fin b)) := {p | p.2 ∈ Work.Thom.mSph b}
  let BA : Set (Y × Work.Thom.MBall b) := {q | q.2.1 ∈ Work.Thom.mSph b}
  have hfA : ∀ q ∈ BA, fA q ∈ AA := fun q hq => hq
  have hbijA : ∀ m, Function.Bijective (Work.Thom.relCohMap fA BA AA hfA ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_discFull Y b m
  let πA : C(Y × Work.Thom.MBall b, Y) := ⟨Prod.fst, continuous_fst⟩
  have hπA : (Work.Thom.projFst Y b).comp fA = πA := by ext q; rfl
  let σ₁ := (Work.Thom.relCohMap fA BA AA hfA ℤ b).hom σ₀
  have hσ₁ : ∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
      (Work.Thom.mixedCupC ℤ BA k b) ((Work.Thom.CohMap πA ℤ k).hom x) σ₁) :=
    Work.Thom.cupMap_transfer_fwd fA AA BA hfA hbijA (Work.Thom.projFst Y b) πA hπA b σ₀ hσ₀
  -- Step B: the radial homeomorphism `Iᵇ ≅ Dᵇ`, carrying `∂Iᵇ` onto `Sᵇ⁻¹`.
  obtain ⟨eB, heB⟩ := Work.StemsB.eucCube_mBall_homeomorph b
  let hB : Y × ↥(Work.StemsB.eucCube b) ≃ₜ Y × Work.Thom.MBall b :=
    Homeomorph.prodCongr (Homeomorph.refl Y) eB
  let fB : C(Y × ↥(Work.StemsB.eucCube b), Y × Work.Thom.MBall b) := (hB : C(_, _))
  let BB : Set (Y × ↥(Work.StemsB.eucCube b)) := {q | q.2.1 ∈ Work.StemsB.eucBdry b}
  have hfB : ∀ q ∈ BB, fB q ∈ BA := fun q hq => (heB q.2).mp hq
  have hbijB : ∀ m, Function.Bijective (Work.Thom.relCohMap fB BB BA hfB ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homeomorph BB BA hB (fun x => heB x.2) ℤ m
  let πB : C(Y × ↥(Work.StemsB.eucCube b), Y) := ⟨Prod.fst, continuous_fst⟩
  have hπB : πA.comp fB = πB := by ext q; rfl
  let σ₂ := (Work.Thom.relCohMap fB BB BA hfB ℤ b).hom σ₁
  have hσ₂ : ∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
      (Work.Thom.mixedCupC ℤ BB k b) ((Work.Thom.CohMap πB ℤ k).hom x) σ₂) :=
    Work.Thom.cupMap_transfer_fwd fB BA BB hfB hbijB πA πB hπB b σ₁ hσ₁
  -- Step C: the swap of the two factors of the product.
  let hC : ↥(Work.StemsB.eucCube b) × Y ≃ₜ Y × ↥(Work.StemsB.eucCube b) :=
    Homeomorph.prodComm ↥(Work.StemsB.eucCube b) Y
  let fC : C(↥(Work.StemsB.eucCube b) × Y, Y × ↥(Work.StemsB.eucCube b)) := (hC : C(_, _))
  let BC : Set (↥(Work.StemsB.eucCube b) × Y) := Work.StemsB.eucBdryProd b Y
  have hfC : ∀ q ∈ BC, fC q ∈ BB := fun q hq => hq
  have hbijC : ∀ m, Function.Bijective (Work.Thom.relCohMap fC BC BB hfC ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homeomorph BC BB hC (fun x => Iff.rfl) ℤ m
  let πC : C(↥(Work.StemsB.eucCube b) × Y, Y) := ⟨Prod.snd, continuous_snd⟩
  have hπC : πB.comp fC = πC := by ext q; rfl
  let σ₃ := (Work.Thom.relCohMap fC BC BB hfC ℤ b).hom σ₂
  have hσ₃ : ∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
      (Work.Thom.mixedCupC ℤ BC k b) ((Work.Thom.CohMap πC ℤ k).hom x) σ₃) :=
    Work.Thom.cupMap_transfer_fwd fC BB BC hfC hbijC πB πC hπC b σ₂ hσ₂
  -- Step D: the radial normalisation `{|v|_∞ < 3/2} → {|v|_∞ ≤ 1}`.
  let hD1 : ContinuousMap.HomotopyEquiv (↥(Work.StemsB.eucBig b) × Y)
      (↥(Work.StemsB.eucCube b) × Y) :=
    { toFun := Work.StemsB.eucNormMap (Y:=Y) b
      invFun := Work.StemsB.eucCubeInclMap (Y:=Y) b
      left_inv := ⟨Work.StemsB.eucNormInclHomotopy (Y:=Y) b⟩
      right_inv := ⟨Work.StemsB.eucInclNormHomotopy (Y:=Y) b⟩ }
  let hD2 : ContinuousMap.HomotopyEquiv ↥(Work.StemsB.eucCollarProd b Y)
      ↥(Work.StemsB.eucBdryProd b Y) :=
    { toFun := Work.StemsB.eucNormRelMapFun (Y:=Y) b
      invFun := Work.StemsB.eucBdryInclMap (Y:=Y) b
      left_inv := ⟨Work.StemsB.eucNormBdryHomotopy (Y:=Y) b⟩
      right_inv := ⟨Work.StemsB.eucBdryNormHomotopy (Y:=Y) b⟩ }
  let fD : C(↥(Work.StemsB.eucBig b) × Y, ↥(Work.StemsB.eucCube b) × Y) :=
    Work.StemsB.eucNormMap (Y:=Y) b
  let BD : Set (↥(Work.StemsB.eucBig b) × Y) := Work.StemsB.eucCollarProd b Y
  have hfD : ∀ q ∈ BD, fD q ∈ BC :=
    fun q hq => Work.StemsB.collarNorm_mem_bdry_of_mem_collar b q.1.1 hq
  have hbijD : ∀ m, Function.Bijective (Work.Thom.relCohMap fD BD BC hfD ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homotopyEquiv BD BC fD hfD hD1 rfl hD2
      (fun q => rfl) m
  let πD : C(↥(Work.StemsB.eucBig b) × Y, Y) := ⟨Prod.snd, continuous_snd⟩
  have hπD : πC.comp fD = πD := by ext q; rfl
  let σ₄ := (Work.Thom.relCohMap fD BD BC hfD ℤ b).hom σ₃
  have hσ₄ : ∀ k : ℕ, Function.Bijective (fun x : Work.Thom.Coh ℤ k Y =>
      (Work.Thom.mixedCupC ℤ BD k b) ((Work.Thom.CohMap πD ℤ k).hom x) σ₄) :=
    Work.Thom.cupMap_transfer_fwd fD BC BD hfD hbijD πC πD hπD b σ₃ hσ₃
  -- Step E: the coordinate extraction `↥(sphLoopBig b) × Y ≅ ↥(eucBig b) × Y`.
  have hcomp1 : (Work.StemsB.eucToBigMap (Y:=Y) b).comp (Work.StemsB.bigToEucMap (Y:=Y) b) =
      ContinuousMap.id (↥(Work.StemsB.sphLoopBig b) × Y) := by
    have h := Work.StemsB.eucToBigMap_bigToEucMap (Y:=Y) b
    simpa using congrArg TopCat.Hom.hom h
  have hcomp2 : (Work.StemsB.bigToEucMap (Y:=Y) b).comp (Work.StemsB.eucToBigMap (Y:=Y) b) =
      ContinuousMap.id (↥(Work.StemsB.eucBig b) × Y) := by
    have h := Work.StemsB.bigToEucMap_eucToBigMap (Y:=Y) b
    simpa using congrArg TopCat.Hom.hom h
  have hrel1 : (Work.StemsB.eucToBigRelMap (Y:=Y) b).comp (Work.StemsB.bigToEucRelMap (Y:=Y) b) =
      ContinuousMap.id (↥(Work.StemsB.sphLoopCollarProd b Y)) := by
    have h := Work.StemsB.eucToBigRelMap_bigToEucRelMap (Y:=Y) b
    simpa using congrArg TopCat.Hom.hom h
  have hrel2 : (Work.StemsB.bigToEucRelMap (Y:=Y) b).comp (Work.StemsB.eucToBigRelMap (Y:=Y) b) =
      ContinuousMap.id (↥(Work.StemsB.eucCollarProd b Y)) := by
    have h := Work.StemsB.bigToEucRelMap_eucToBigRelMap (Y:=Y) b
    simpa using congrArg TopCat.Hom.hom h
  let hE1 : ContinuousMap.HomotopyEquiv (↥(Work.StemsB.sphLoopBig b) × Y)
      (↥(Work.StemsB.eucBig b) × Y) :=
    { toFun := Work.StemsB.bigToEucMap (Y:=Y) b
      invFun := Work.StemsB.eucToBigMap (Y:=Y) b
      left_inv := hcomp1 ▸ ContinuousMap.Homotopic.refl _
      right_inv := hcomp2 ▸ ContinuousMap.Homotopic.refl _ }
  let hE2 : ContinuousMap.HomotopyEquiv ↥(Work.StemsB.sphLoopCollarProd b Y)
      ↥(Work.StemsB.eucCollarProd b Y) :=
    { toFun := Work.StemsB.bigToEucRelMap (Y:=Y) b
      invFun := Work.StemsB.eucToBigRelMap (Y:=Y) b
      left_inv := hrel1 ▸ ContinuousMap.Homotopic.refl _
      right_inv := hrel2 ▸ ContinuousMap.Homotopic.refl _ }
  let fE : C(↥(Work.StemsB.sphLoopBig b) × Y, ↥(Work.StemsB.eucBig b) × Y) :=
    Work.StemsB.bigToEucMap (Y:=Y) b
  let BE : Set (↥(Work.StemsB.sphLoopBig b) × Y) := Work.StemsB.sphLoopCollarProd b Y
  have hfE : ∀ q ∈ BE, fE q ∈ BD := fun q hq => Work.StemsB.modelVec_mem_eucCollar b hq
  have hbijE : ∀ m, Function.Bijective (Work.Thom.relCohMap fE BE BD hfE ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homotopyEquiv BE BD fE hfE hE1 rfl hE2
      (fun q => rfl) m
  let πE : C(↥(Work.StemsB.sphLoopBig b) × Y, Y) := ⟨fun p => p.2, by fun_prop⟩
  have hπE : πD.comp fE = πE := by ext q; rfl
  refine ⟨(Work.Thom.relCohMap fE BE BD hfE ℤ b).hom σ₄, ?_⟩
  exact Work.Thom.cupMap_transfer_fwd fE BD BE hfE hbijE πD πE hπE b σ₄ hσ₄

end

end Work.StemsB
