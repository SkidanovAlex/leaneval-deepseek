import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.singularCohomology_zero
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.EMODD.kOneIntegralHomology
import Submission.Work.Pi6.K2Z.baseChangeFlat
import Submission.Work.Pi6.K2Z.baseChangeCharP
import Submission.Work.Pi6.K2Z.bocksteinModP
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

noncomputable section

/-! ## Elementary module lemmas -/

/-- The linear equivalence underlying an isomorphism of `R`-modules. -/
def leOfIso {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) : ↥M ≃ₗ[R] ↥N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

/-- An isomorphism of `ℤ`-modules carries the subgroup of `p`-multiples onto the subgroup of
`p`-multiples. -/
theorem map_pMultiples (p : ℕ) {M N : ModuleCat ℤ} (e : M ≅ N) :
    AddSubgroup.map (leOfIso e).toAddEquiv (pMultiples p M).toAddSubgroup
      = (pMultiples p N).toAddSubgroup := by
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_pMultiples] at hy ⊢
    obtain ⟨z, hz⟩ := hy
    refine mem_pMultiples.mpr ⟨(leOfIso e) z, ?_⟩
    rw [← hz]
    exact (((leOfIso e).toAddEquiv.toAddMonoidHom).map_zsmul (p : ℤ) z).symm
  · intro hx
    rw [mem_pMultiples] at hx
    obtain ⟨z, hz⟩ := hx
    rw [AddSubgroup.mem_map]
    refine ⟨(p : ℤ) • (leOfIso e).symm z, ?_, ?_⟩
    · exact mem_pMultiples.mpr ⟨_, rfl⟩
    · have h2 : (leOfIso e) ((p : ℤ) • (leOfIso e).symm z) = x := by
        calc (leOfIso e) ((p : ℤ) • (leOfIso e).symm z)
            = (p : ℤ) • (leOfIso e) ((leOfIso e).symm z) :=
              ((leOfIso e).toAddEquiv.toAddMonoidHom.map_zsmul (p : ℤ) _)
          _ = (p : ℤ) • z := by rw [LinearEquiv.apply_symm_apply]
          _ = x := hz
      exact h2

/-- An additive equivalence between modules over the prime field `ℤ/p` is automatically
`ℤ/p`-linear. -/
def zmodLinearEquivOfAddEquiv (p : ℕ) [NeZero p] {M N : Type*} [AddCommGroup M]
    [Module (ZMod p) M] [AddCommGroup N] [Module (ZMod p) N] (e : M ≃+ N) : M ≃ₗ[ZMod p] N where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' := fun c x => by
    have hcast : ((c.val : ℤ) : ZMod p) = c := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val c
    calc e (c • x) = e (((c.val : ℤ) : ZMod p) • x) := by rw [hcast]
      _ = e ((c.val : ℤ) • x) := by rw [Int.cast_smul_eq_zsmul]
      _ = (c.val : ℤ) • e x := AddMonoidHom.map_zsmul (e.toAddMonoidHom) _ _
      _ = ((c.val : ℤ) : ZMod p) • e x := by rw [Int.cast_smul_eq_zsmul]
      _ = c • e x := by rw [hcast]
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- The quotient `ℤ ⧸ pℤ` is `ℤ/p` (as abelian groups). -/
theorem intQuotPMulEquivZMod (p : ℕ) :
    Nonempty ((ℤ ⧸ (pMultiples p (ModuleCat.of ℤ ℤ)).toAddSubgroup) ≃+ ZMod p) := by
  have h : (pMultiples p (ModuleCat.of ℤ ℤ)).toAddSubgroup
      = (Ideal.span {(p : ℤ)}).toAddSubgroup := by
    ext x
    rw [mem_pMultiples]
    constructor
    · rintro ⟨y, hy⟩
      exact Ideal.mem_span_singleton.mpr
        ⟨y, hy.symm.trans (zsmul_eq_mul y (p : ℤ)).symm⟩
    · intro hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨y, (zsmul_eq_mul y (p : ℤ)).trans hy.symm⟩
  rw [h]
  exact ⟨(Int.quotientSpanNatEquivZMod p).toAddEquiv⟩

/-- The self-duality of a field: `Hom_𝕜(𝕜,𝕜) ≅ 𝕜` by evaluation at `1`. -/
def dualSelfEquiv (𝕜 : Type) [CommRing 𝕜] : (𝕜 →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] 𝕜 where
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
theorem finrank_eq_one_of_iso {𝕜 : Type} [Field 𝕜] {M : ModuleCat 𝕜} (e : M ≅ ModuleCat.of 𝕜 𝕜) :
    Module.finrank 𝕜 ↥M = 1 := by
  rw [LinearEquiv.finrank_eq (leOfIso e)]
  simp

/-- Vanishing of `𝕜`-cohomology in a degree where the `𝕜`-homology vanishes, by the field universal
coefficient theorem. -/
theorem isZeroCohOfSubsingletonHR {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] (j : ℕ)
    (h : Subsingleton ↥(Work.Pi6.HR 𝕜 X j)) : IsZero (Work.Pi6.Coh 𝕜 X j) := by
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) j
  have hsub : Subsingleton (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜) :=
    ⟨fun f g => LinearMap.ext fun y => by rw [h.elim y 0, map_zero, map_zero]⟩
  have hz : IsZero (ModuleCat.of 𝕜 (↥(Work.Pi6.HR 𝕜 X j) →ₗ[𝕜] 𝕜)) :=
    ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso hz e

/-! ## The main theorem -/

theorem kOneField {𝕜 : Type} [Field 𝕜] (Y : Type) [TopologicalSpace Y] (y₀ : Y) (M : ℕ)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) M Y y₀) :
    Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 0) = 1 ∧
      Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ M → CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 Y q)) := by
  classical
  -- degree `1` is in the range after replacing `M` by `max M 1`
  have hY' : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (max M 1) Y y₀ := by
    by_cases hM : M ≤ 1
    · rw [max_eq_right hM]
      refine ⟨hY.1, fun i hi hc => ?_⟩
      rcases hc with h | h
      · exact hY.2 i hi (Or.inl h)
      · exact hY.2 i hi (Or.inl (by omega))
    · rw [max_eq_left (by omega)]
      exact hY
  obtain ⟨hI1, hI2⟩ := Work.Pi6.EMODD.kOneIntegralHomology (max M 1) Y y₀ hY'
  have hH0 : Nonempty (Work.Pi6.HR ℤ Y 0 ≅ ModuleCat.of ℤ ℤ) := hI1 0 (by norm_num) (by omega)
  have hH1 : Nonempty (Work.Pi6.HR ℤ Y 1 ≅ ModuleCat.of ℤ ℤ) := hI1 1 le_rfl (le_max_right M 1)
  have hHq : ∀ q : ℕ, 2 ≤ q → q ≤ max M 1 → IsZero (Work.Pi6.HR ℤ Y q) :=
    fun q h1 h2 => hI2 q h1 h2
  -- freeness of the integral homology in the range
  have hfree : ∀ i : ℕ, i ≤ max M 1 → Module.Free ℤ ↥(Work.Pi6.HR ℤ Y i) := by
    intro i hiM
    rcases i with _ | _ | k
    · exact Module.Free.of_equiv (hH0.some.toLinearEquiv.symm)
    · exact Module.Free.of_equiv (hH1.some.toLinearEquiv.symm)
    · have hiz : IsZero (Work.Pi6.HR ℤ Y (k + 2)) := hHq (k + 2) (by omega) hiM
      haveI : Subsingleton ↥(Work.Pi6.HR ℤ Y (k + 2)) :=
        ModuleCat.isZero_iff_subsingleton.mp hiz
      infer_instance
  have hpc : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀
      (hY.2 0 (by norm_num) (Or.inl (by norm_num)))
  haveI := hpc
  -- degree `0`
  have h0 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 Y 0) = 1 := by
    obtain ⟨e⟩ := Work.Cohomology.singularCohomology_zero 𝕜 (TopCat.of Y)
    rw [LinearEquiv.finrank_eq (leOfIso e)]
    simp
  refine ⟨h0, ?_, ?_⟩
  · -- degree `1`
    by_cases hchar : CharZero 𝕜
    · haveI : CharZero 𝕜 := hchar
      haveI : CharP 𝕜 0 := inferInstance
      have hfl : (Int.castRingHom 𝕜).Flat := by
        rw [RingHom.Flat]
        exact flat_int_congr _ _ (module_flat_int_of_charZero (𝕜 := 𝕜))
      obtain ⟨b1⟩ := Work.Pi6.K2Z.baseChangeFlat hfl Y 1
      obtain ⟨h1i⟩ := hH1
      have hHR1 : Nonempty (Work.Pi6.HR 𝕜 Y 1 ≅ ModuleCat.of 𝕜 𝕜) :=
        ⟨b1 ≪≫ (ModuleCat.extendScalars (Int.castRingHom 𝕜)).mapIso h1i
          ≪≫ Work.Pi6.K2Z.extendScalarsIntFieldIso 𝕜⟩
      obtain ⟨e1⟩ := hHR1
      obtain ⟨eu⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of Y)) 1
      refine finrank_eq_one_of_iso (eu ≪≫ ?_)
      exact LinearEquiv.toModuleIso
        ((LinearEquiv.arrowCongr (leOfIso e1) (LinearEquiv.refl 𝕜 𝕜)).trans
          (dualSelfEquiv 𝕜))
    · have hp0 : ringChar 𝕜 ≠ 0 := by
        intro h0'
        haveI : CharP 𝕜 0 := ringChar.of_eq h0'
        exact hchar (CharP.charP_to_charZero 𝕜)
      have hp : (ringChar 𝕜).Prime := CharP.char_prime_of_ne_zero 𝕜 hp0
      haveI : CharP 𝕜 (ringChar 𝕜) := inferInstance
      haveI : NeZero (ringChar 𝕜) := ⟨hp0⟩
      obtain ⟨eb⟩ := hrModP (ringChar 𝕜) hp Y 1 (by norm_num) (hfree 0 (by omega))
      have hmap := map_pMultiples (ringChar 𝕜) hH1.some
      have e2 : (↥(Work.Pi6.HR ℤ Y 1) ⧸
            (pMultiples (ringChar 𝕜) (Work.Pi6.HR ℤ Y 1)).toAddSubgroup) ≃+
          (ℤ ⧸ (pMultiples (ringChar 𝕜) (ModuleCat.of ℤ ℤ)).toAddSubgroup) :=
        QuotientAddGroup.congr _ _ (leOfIso hH1.some).toAddEquiv hmap
      obtain ⟨e3⟩ := intQuotPMulEquivZMod (ringChar 𝕜)
      have elin : ↥(Work.Pi6.HR (ZMod (ringChar 𝕜)) Y 1) ≃ₗ[ZMod (ringChar 𝕜)]
          ZMod (ringChar 𝕜) := zmodLinearEquivOfAddEquiv (ringChar 𝕜) (eb.trans (e2.trans e3))
      have eiso : Work.Pi6.HR (ZMod (ringChar 𝕜)) Y 1 ≅
          ModuleCat.of (ZMod (ringChar 𝕜)) (ZMod (ringChar 𝕜)) := LinearEquiv.toModuleIso elin
      obtain ⟨b1⟩ := Work.Pi6.K2Z.baseChangeCharP (𝕜 := 𝕜) (ringChar 𝕜) Y 1
      have hHR1 : Nonempty (Work.Pi6.HR 𝕜 Y 1 ≅ ModuleCat.of 𝕜 𝕜) :=
        ⟨b1 ≪≫ (ModuleCat.extendScalars (ZMod.castHom (dvd_refl (ringChar 𝕜)) 𝕜)).mapIso eiso
          ≪≫ Work.Pi6.K2Z.extendScalarsZModIso (ringChar 𝕜)⟩
      obtain ⟨e1⟩ := hHR1
      obtain ⟨eu⟩ := Work.StemsB.fieldDualUCT 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of Y)) 1
      refine finrank_eq_one_of_iso (eu ≪≫ ?_)
      exact LinearEquiv.toModuleIso
        ((LinearEquiv.arrowCongr (leOfIso e1) (LinearEquiv.refl 𝕜 𝕜)).trans
          (dualSelfEquiv 𝕜))
  · -- degrees `≥ 2`
    intro q hq hqM
    have hqN : q ≤ max M 1 := le_trans hqM (le_max_left M 1)
    have hqZ : IsZero (Work.Pi6.HR ℤ Y q) := hHq q hq hqN
    by_cases hchar : CharZero 𝕜
    · haveI : CharZero 𝕜 := hchar
      haveI : CharP 𝕜 0 := inferInstance
      have hfl : (Int.castRingHom 𝕜).Flat := by
        rw [RingHom.Flat]
        exact flat_int_congr _ _ (module_flat_int_of_charZero (𝕜 := 𝕜))
      obtain ⟨eCC⟩ := Work.Pi6.K2Z.baseChangeFlat hfl Y q
      have hz : IsZero ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ Y q)) :=
        Functor.map_isZero (ModuleCat.extendScalars (Int.castRingHom 𝕜)) hqZ
      haveI : Subsingleton
          ↥((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.Pi6.HR ℤ Y q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      haveI : Subsingleton ↥(Work.Pi6.HR 𝕜 Y q) := (leOfIso eCC).injective.subsingleton
      exact isZeroCohOfSubsingletonHR q inferInstance
    · have hp0 : ringChar 𝕜 ≠ 0 := by
        intro h0'
        haveI : CharP 𝕜 0 := ringChar.of_eq h0'
        exact hchar (CharP.charP_to_charZero 𝕜)
      have hp : (ringChar 𝕜).Prime := CharP.char_prime_of_ne_zero 𝕜 hp0
      haveI : CharP 𝕜 (ringChar 𝕜) := inferInstance
      haveI : NeZero (ringChar 𝕜) := ⟨hp0⟩
      obtain ⟨eb⟩ := hrModP (ringChar 𝕜) hp Y q (by omega) (hfree (q - 1) (by omega))
      haveI : Subsingleton ↥(Work.Pi6.HR ℤ Y q) := ModuleCat.isZero_iff_subsingleton.mp hqZ
      haveI : Subsingleton (↥(Work.Pi6.HR ℤ Y q) ⧸
          (pMultiples (ringChar 𝕜) (Work.Pi6.HR ℤ Y q)).toAddSubgroup) :=
        ⟨fun a b => by
          obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
          obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
          rw [Subsingleton.elim x y]⟩
      haveI : Subsingleton ↥(Work.Pi6.HR (ZMod (ringChar 𝕜)) Y q) :=
        eb.injective.subsingleton
      obtain ⟨eCC⟩ := Work.Pi6.K2Z.baseChangeCharP (𝕜 := 𝕜) (ringChar 𝕜) Y q
      have hz : IsZero ((ModuleCat.extendScalars
          (ZMod.castHom (dvd_refl (ringChar 𝕜)) 𝕜)).obj (Work.Pi6.HR (ZMod (ringChar 𝕜)) Y q)) :=
        Functor.map_isZero (ModuleCat.extendScalars (ZMod.castHom (dvd_refl (ringChar 𝕜)) 𝕜))
          (ModuleCat.isZero_of_subsingleton _)
      haveI : Subsingleton ↥((ModuleCat.extendScalars
          (ZMod.castHom (dvd_refl (ringChar 𝕜)) 𝕜)).obj (Work.Pi6.HR (ZMod (ringChar 𝕜)) Y q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      haveI : Subsingleton ↥(Work.Pi6.HR 𝕜 Y q) := (leOfIso eCC).injective.subsingleton
      exact isZeroCohOfSubsingletonHR q inferInstance

end

end Work.Pi6.K2Z
