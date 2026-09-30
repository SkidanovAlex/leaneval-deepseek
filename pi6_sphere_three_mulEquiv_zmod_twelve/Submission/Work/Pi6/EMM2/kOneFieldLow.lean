import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.Pi6.EMM2.HRisoExtendScalars
import Submission.Work.Pi6.EMODD.kOneIntegralHomology
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.K2Z.baseChangeFlat
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.Cohomology.singularCohomology_zero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

/-!
# The cohomology of a range model of `K(ℤ,1)` over a field

For `Y` a model of `K(ℤ,1)` through degree `M` (`Work.Serre.IsEMSpaceUpTo ℤ 1 _ M Y y₀`) and any
field `𝕜`, the low-degree `𝕜`-cohomology of `Y` is that of the circle: `H⁰(Y;𝕜) = 𝕜`,
`H¹(Y;𝕜) = 𝕜`, and `H^q(Y;𝕜) = 0` for `2 ≤ q ≤ M`.

The integral homology `H_*(Y;ℤ)` is that of `S¹` in the range (`Work.Pi6.EMODD.kOneIntegralHomology`,
by Serre's comparison `Work.EMFG.kOneComparison` with the circle): `H₀ ≅ ℤ`, `H₁ ≅ ℤ` and
`H_q = 0` for `2 ≤ q ≤ M`.  Since `H_{q-1}(Y;ℤ)` is then torsion-free, hence flat over `ℤ`, the
universal coefficient theorem gives `H_q(Y;𝕜) ≅ H_q(Y;ℤ) ⊗[ℤ] 𝕜` in every degree (`HRisoExtendScalars`),
so `H₀(Y;𝕜) ≅ 𝕜`, `H₁(Y;𝕜) ≅ 𝕜` and `H_q(Y;𝕜) = 0` for `2 ≤ q ≤ M`.  The field universal
coefficient theorem `Work.StemsB.fieldDualUCT` (`H^q(Y;𝕜) ≅ Hom_𝕜(H_q(Y;𝕜),𝕜)`) then converts this
into the stated cohomology.
-/

/-- The `R`-linear equivalence underlying an isomorphism of `R`-modules. -/
noncomputable def kOneFieldLeOfIso {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) :
    ↥M ≃ₗ[R] ↥N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

/-- Torsion-freeness transfers along a linear equivalence. -/
theorem kOneField_isTorsionFree_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree ℤ M :=
  Function.Injective.moduleIsTorsionFree e e.injective e.map_smul

/-- The self-duality of a rank-one free module: `Hom_R(R,R) ≅ R` by evaluation at `1`. -/
noncomputable def kOneField_dualSelfEquiv (𝕜 : Type) [CommRing 𝕜] : (𝕜 →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] 𝕜 where
  toFun f := f 1
  map_add' f g := rfl
  map_smul' a f := rfl
  invFun a := a • LinearMap.id
  left_inv f := LinearMap.ext fun x => by
    show ((f 1) • (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜)) x = f x
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_comm]
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  right_inv a := by
    show (a • (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜)) 1 = a
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]

/-- A module isomorphic to the base field is one-dimensional. -/
theorem kOneField_finrank_eq_one_of_iso {𝕜 : Type} [Field 𝕜] {M : ModuleCat 𝕜}
    (e : M ≅ ModuleCat.of 𝕜 𝕜) : Module.finrank 𝕜 ↥M = 1 := by
  rw [LinearEquiv.finrank_eq (kOneFieldLeOfIso e)]
  simp

/-- Extension of scalars along `ℤ → 𝕜` preserves the zero object. -/
theorem kOneField_isZero_extendScalars {𝕜 : Type} [CommRing 𝕜] {M : ModuleCat ℤ}
    (h : IsZero M) : IsZero ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj M) :=
  Functor.map_isZero (ModuleCat.extendScalars (Int.castRingHom 𝕜)) h

/-- Vanishing of the `𝕜`-cohomology in degree `j` from the vanishing of the `𝕜`-homology, by the
field universal coefficient theorem `Work.StemsB.fieldDualUCT`
(`H^j(X;𝕜) ≅ Hom_𝕜(H_j(X;𝕜), 𝕜)`). -/
theorem kOneField_isZeroCohOfSubsingletonHR {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (j : ℕ) (h : Subsingleton ↥(Work.Pi6.HR 𝕜 X j)) : IsZero (Work.Pi6.Coh 𝕜 X j) := by
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) j
  have hsub : Subsingleton (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜) :=
    ⟨fun f g => LinearMap.ext fun y => by rw [h.elim y 0, map_zero, map_zero]⟩
  have hz : IsZero (ModuleCat.of 𝕜 (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜)) :=
    ModuleCat.isZero_of_subsingleton _
  change IsZero ((Work.Cohomology.dualComplex 𝕜
    (Work.Cohomology.singularChains 𝕜 (TopCat.of X))).homology j)
  exact IsZero.of_iso hz e

/-- `H⁰(X;𝕜) = 𝕜` for a space with trivial `π₀` (`Work.Cohomology.singularCohomology_zero`). -/
theorem kOneField_finrankCohZero {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] (x : X)
    (hX : Subsingleton (HomotopyGroup (Fin 0) X x)) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = 1 := by
  haveI : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x hX
  obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of X)
  have hfr : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 0) = Module.finrank 𝕜 (ModuleCat.of 𝕜 𝕜) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom))
  rw [hfr]
  simp

theorem kOneFieldLow {𝕜 : Type} [Field 𝕜] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) M Y y₀) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 0) = 1 ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ M → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 Y q)) := by
  classical
  -- Degree `1` lies in the range as soon as we replace `M` by `max M 1`.
  have hY' : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (max M 1) Y y₀ := by
    by_cases hM : M ≤ 1
    · rw [max_eq_right hM]
      refine ⟨hY.1, fun i hi hc => ?_⟩
      rcases hc with h | h
      · exact hY.2 i hi (Or.inl h)
      · exact hY.2 i hi (Or.inl (by omega))
    · rw [max_eq_left (by omega)]
      exact hY
  -- The integral homology of `Y` in the range is that of the circle.
  obtain ⟨hI1, hI2⟩ := Work.Pi6.EMODD.kOneIntegralHomology (max M 1) Y y₀ hY'
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ (TopCat.of Y)
  have hH0 : Nonempty (K.homology 0 ≅ ModuleCat.of ℤ ℤ) := hI1 0 (by norm_num) (by omega)
  have hH1 : Nonempty (K.homology 1 ≅ ModuleCat.of ℤ ℤ) := hI1 1 le_rfl (le_max_right M 1)
  have hHq : ∀ q : ℕ, 2 ≤ q → q ≤ max M 1 → IsZero (K.homology q) :=
    fun q h1 h2 => hI2 q h1 h2
  -- `H_i(Y;ℤ)` is torsion-free for `i ≤ M`, which is what the coefficient change needs.
  have hTF : ∀ i : ℕ, i ≤ max M 1 → Module.IsTorsionFree ℤ (K.homology i) := by
    intro i hi
    rcases lt_or_ge i 2 with h2 | h2
    · interval_cases i
      · exact kOneField_isTorsionFree_of_linearEquiv (kOneFieldLeOfIso hH0.some)
      · exact kOneField_isTorsionFree_of_linearEquiv (kOneFieldLeOfIso hH1.some)
    · haveI : Subsingleton ↥(K.homology i) :=
        ModuleCat.isZero_iff_subsingleton.mp (hHq i h2 hi)
      infer_instance
  -- Change of coefficients `ℤ → 𝕜` in the range.
  have hCC : ∀ q : ℕ, 1 ≤ q → q ≤ max M 1 →
      Nonempty (Work.Pi6.HR 𝕜 Y q ≅
        (ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ Y q)) := by
    intro q hq hqM
    have hTF' : Module.IsTorsionFree ℤ (Work.Pi6.HR ℤ Y (q - 1)) := hTF (q - 1) (by omega)
    have hchild := HRisoExtendScalars 𝕜 (X := Y) (q - 1) hTF'
    rwa [Nat.sub_add_cancel hq] at hchild
  -- `H₁(Y;𝕜) ≅ 𝕜`.
  have hHR1 : Nonempty (Work.Pi6.HR 𝕜 Y 1 ≅ ModuleCat.of 𝕜 𝕜) := by
    obtain ⟨e1⟩ := hCC 1 le_rfl (le_max_right M 1)
    obtain ⟨e2⟩ := hH1
    exact ⟨e1 ≪≫ (ModuleCat.extendScalars (Int.castRingHom 𝕜)).mapIso e2 ≪≫
      Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜⟩
  have hfin1 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 1) = 1 := by
    obtain ⟨e1⟩ := hHR1
    obtain ⟨eu⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of Y)) 1
    refine kOneField_finrank_eq_one_of_iso (eu ≪≫ ?_)
    exact LinearEquiv.toModuleIso
      ((LinearEquiv.arrowCongr (kOneFieldLeOfIso e1) (LinearEquiv.refl 𝕜 𝕜)).trans
        (kOneField_dualSelfEquiv 𝕜))
  refine ⟨?_, hfin1, ?_⟩
  · exact kOneField_finrankCohZero y₀ (hY'.2 0 (by norm_num) (Or.inl (by norm_num)))
  · intro q hq hqM
    have hqN : q ≤ max M 1 := le_trans hqM (le_max_left M 1)
    have hq1 : 1 ≤ q := by omega
    obtain ⟨eCC⟩ := hCC q hq1 hqN
    have hz := kOneField_isZero_extendScalars (𝕜 := 𝕜) (hHq q hq hqN)
    haveI : Subsingleton
        ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ Y q)) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    haveI : Subsingleton ↥(Work.Pi6.HR 𝕜 Y q) := (kOneFieldLeOfIso eCC).injective.subsingleton
    exact kOneField_isZeroCohOfSubsingletonHR q inferInstance

end Work.Pi6.EMM2
