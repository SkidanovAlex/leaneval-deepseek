import Mathlib
import Submission.Work.Pi6.EMM2.kOneFieldLow
import Submission.Work.Pi6.EMM2.hrExtendScalars
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The cohomology of a range model of `K(ℤ,1)` over a field, using the torsion-free
change-of-coefficients theorem

Same content as `Work.Pi6.EMM2.kOneFieldLow`, but with the single degree change of coefficients
`Work.Pi6.EMM2.HRisoExtendScalarsTF` (proved from `Work.Pi6.EMM2.extendScalars_homology_iso`)
in place of the stub `Work.Pi6.EMM2.HRisoExtendScalars`.
-/

namespace Work.Pi6.EMM2

open CategoryTheory CategoryTheory.Limits

theorem kOneFieldLowTF {𝕜 : Type} [Field 𝕜] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ)
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
    have hchild := HRisoExtendScalarsTF 𝕜 (X := Y) (q - 1) hTF'
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
