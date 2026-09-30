import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Pi6.EMODD.sphTwoPi
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Pi6.EMM2.baseChangeModTwo
import Submission.Work.Pi6.EMM2.homologyModTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `H²(K(ℤ/2,2);𝕜) = 𝕜` for a field `𝕜` of characteristic `2`

`Work.Pi6.EMM2.secondCohZModTwo`: for a range model `X` of `K(ℤ/2,2)` through degree `M ≥ 2` and a
field `𝕜` of characteristic `2`, the cohomology `H²(X;𝕜) = H²(X;𝔽₂) ⊗_{𝔽₂} 𝕜` is one dimensional.

The proof has four steps.

* `X` is `1`-connected (`IsEMSpaceUpTo … 2 …`), so by the integral Hurewicz theorem
  (`Work.Stems.hurewicz_first_degree`, packaged as `Work.Pi6.EMODD.hurewiczMulEquivSpheres`)
  `H₂(X;ℤ) ≅ π₂(X) ≅ ℤ/2`, and by connectivity `H₁(X;ℤ) = 0`
  (`Work.Pi6.SQASM.connHomology`).
* The universal coefficient theorem over `ℤ` in the case where the `Tor` term vanishes (the mod-2
  Bockstein sequence `0 → H₂(X;ℤ)/2H₂(X;ℤ) → H₂(X;𝔽₂) → H₁(X;ℤ)[2] → 0`) gives
  `H₂(X;𝔽₂) ≅ 𝔽₂` (`Work.Pi6.EMM2.homologyModTwo`).
* Base change along `𝔽₂ → 𝕜` (`Work.Pi6.EMM2.baseChangeModTwo`, exact because `𝔽₂` is a field)
  gives `H₂(X;𝕜) ≅ 𝕜 ⊗_{𝔽₂} H₂(X;𝔽₂) ≅ 𝕜`.
* Kronecker duality over the field `𝕜` (`Work.Cohomology.kronH_bijective_field`) identifies
  `H²(X;𝕜)` with the `𝕜`-dual of `H₂(X;𝕜)`, hence with `𝕜`, and `finrank 𝕜 𝕜 = 1`.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits ModuleCat

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The unit of the base change `𝔽₂ → 𝕜`**: `𝕜 ⊗_{𝔽₂} 𝔽₂ ≅ 𝕜`.  This is the object part of the
unit comparison `ε` of the monoidal functor `ModuleCat.extendScalars (ZMod.castHom _ 𝕜)`
(`ModuleCat.extendScalars.monoidal`, `Functor.Monoidal.εIso`), at the tensor unit
`𝟙_ (ModuleCat (ZMod 2)) = ModuleCat.of (ZMod 2) (ZMod 2)`. -/
theorem extendScalarsZModTwoUnit (𝕜 : Type) [Field 𝕜] (h2 : CharP 𝕜 2) :
    Nonempty ((ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)).obj
      (ModuleCat.of (ZMod 2) (ZMod 2)) ≅ ModuleCat.of 𝕜 𝕜) := by
  let f := ZMod.castHom (by decide : 2 ∣ 2) 𝕜
  exact ⟨(Functor.Monoidal.εIso (F := ModuleCat.extendScalars f)).symm⟩

/-- **Cohomology is the dual of homology, and `finrank 𝕜 𝕜 = 1`.**  If the mod-`𝕜` homology
`H₂(X;𝕜)` is one dimensional then so is `H²(X;𝕜)`: the Kronecker pairing
(`Work.Cohomology.kronH_bijective_field`) is a `𝕜`-linear bijection from `H²(X;𝕜)` onto the dual of
`H₂(X;𝕜)`, and duality is an equivalence of finite dimensional vector spaces. -/
theorem finrankCohTwoOfIso (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X]
    (hK : Nonempty (Work.Pi6.HR 𝕜 X 2 ≅ ModuleCat.of 𝕜 𝕜)) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 2) = 1 := by
  obtain ⟨e⟩ := hK
  have hdual : Module.finrank 𝕜 (↥(Work.Pi6.HR 𝕜 X 2) →ₗ[𝕜] 𝕜) = 1 := by
    rw [← LinearEquiv.finrank_eq (LinearEquiv.dualMap (Iso.toLinearEquiv e))]
    rw [Module.finrank_linearMap 𝕜 𝕜 𝕜 𝕜, Module.finrank_self 𝕜, mul_one]
  have hkr := Work.Cohomology.kronH_bijective_field 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 2
  have e1 : ↥(Work.Pi6.Coh 𝕜 X 2) ≃ₗ[𝕜]
      (↥(Work.Pi6.HR 𝕜 X 2) →ₗ[𝕜] 𝕜) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 2) hkr
  rw [LinearEquiv.finrank_eq e1]
  exact hdual

/-- **`H²` of a `K(ℤ/2,2)` range model over a field of characteristic `2` is one dimensional.**
The hypothesis `hM : 2 ≤ M` is not used by the argument below (only the vanishing of `π₀`, `π₁`
and the value `π₂ ≅ ℤ/2` enter), but the statement keeps it to match the surrounding interfaces. -/
theorem secondCohZModTwo (𝕜 : Type) [Field 𝕜] (h2 : CharP 𝕜 2) {X : Type} [TopologicalSpace X]
    (x : X) {M : ℕ} (hM : 2 ≤ M) (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) M X x) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 2) = 1 := by
  have hconn : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) X x) := by
    intro i hi
    exact hX.2 i (by omega) (Or.inl hi)
  -- `H₁(X;ℤ) = 0`
  have hH1 : Subsingleton ↥(Work.Pi6.HR ℤ X 1) :=
    ModuleCat.subsingleton_of_isZero
      (Work.Pi6.SQASM.connHomology x 1 1 (fun j hj => hconn j (by omega)) (by norm_num) le_rfl)
  -- `H₂(X;ℤ) ≅ ℤ/2` (Hurewicz + `π₂(X) ≅ ℤ/2`)
  have hH2 : Nonempty (Work.Pi6.HR ℤ X 2 ≃ₗ[ℤ] ZMod 2) := by
    obtain ⟨eπ⟩ := hX.1
    obtain ⟨eh⟩ := Work.Pi6.EMODD.hurewiczMulEquivSpheres x 1 (by norm_num) hconn
    refine ⟨AddEquiv.toIntLinearEquiv ?_⟩
    exact (AddEquiv.toMultiplicative (G := ↥(Work.Pi6.HR ℤ X 2)) (H := ZMod 2)).symm
      (eh.symm.trans eπ)
  -- `H₂(X;𝔽₂) ≅ 𝔽₂` and base change to `𝕜`
  obtain ⟨hMod2⟩ := homologyModTwo X 1 hH1 hH2
  obtain ⟨hbc⟩ := baseChangeModTwo 𝕜 h2 (X := X) 2
  obtain ⟨hu⟩ := extendScalarsZModTwoUnit 𝕜 h2
  refine finrankCohTwoOfIso 𝕜 X ⟨?_⟩
  exact hbc ≪≫ (ModuleCat.extendScalars (ZMod.castHom (by decide : 2 ∣ 2) 𝕜)).mapIso hMod2 ≪≫ hu

end

end Work.Pi6.EMM2
