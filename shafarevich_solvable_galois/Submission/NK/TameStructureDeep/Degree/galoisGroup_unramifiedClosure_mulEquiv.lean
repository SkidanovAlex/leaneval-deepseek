import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.NK.TameStructureDeep.Degree.continuous_of_continuous_compHomZMod
import Submission.NK.TameStructureDeep.Degree.exists_mulEquiv_zmod_algEquiv_adjoin_primitiveRoot
import Submission.NK.TameStructureDeep.Degree.iSup_adjoin_primitiveRoot_eq_top
import Submission.NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one
import Submission.NK.TameStructureDeep.Degree.zhat_eq_top_of_isClosed_of_compHomZMod_image_eq_univ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical NumberField
open IsDedekindDomain

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Degree


variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

noncomputable section

/-- The maximal unramified extension `κ(μ_{p'})` of `κ = K_𝔭`, inside the separable closure. -/
def unramifiedL : IntermediateField (𝔭.adicCompletion K) K' :=
  NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (residueChar 𝔭)

instance instIsGaloisUnramifiedL : IsGalois (𝔭.adicCompletion K) ↥(unramifiedL (K' := K') 𝔭) :=
  NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure (κ := 𝔭.adicCompletion K)
    (K' := K') (residueChar 𝔭)

/-- The level fields are nested: `κ⟮ζ_e⟯ ≤ κ⟮ζ_d⟯` when `e ∣ d`. -/
theorem levelRoot_pow_eq {e d : ℕ} (he : e ≠ 0) (hd : d ≠ 0) (hed : e ∣ d) :
    ∃ k : ℕ, levelRoot (K' := K') 𝔭 e = levelRoot (K' := K') 𝔭 d ^ k := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  obtain ⟨k, -, hk⟩ := (levelRoot_isPrimitiveRoot (K' := K') 𝔭 d hd).eq_pow_of_pow_eq_one
    (ξ := levelRoot (K' := K') 𝔭 e) ((levelRoot_isPrimitiveRoot (K' := K') 𝔭 e he).pow_eq_one_iff_dvd
      (levelN 𝔭 d) |>.mpr (levelN_dvd_levelN 𝔭 hed))
  exact ⟨k, hk.symm⟩

theorem levelField_le_levelField {e d : ℕ} (he : e ≠ 0) (hd : d ≠ 0) (hed : e ∣ d) :
    levelField (K' := K') 𝔭 e ≤ levelField (K' := K') 𝔭 d := by
  obtain ⟨k, hk⟩ := levelRoot_pow_eq (K' := K') 𝔭 he hd hed
  rw [levelField, levelField]
  refine IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_)
  rw [hk]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K)
    (levelRoot (K' := K') 𝔭 d)) k

/-- The chosen root of unity is primitive inside the level field. -/
theorem levelRoot_primitive_in_levelField (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root 𝔭 d⟩ :
      ↥(levelField (K' := K') 𝔭 d)) (levelN 𝔭 d) := by
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
  exact levelRoot_isPrimitiveRoot 𝔭 d hd

/-- **An automorphism of a level is determined by its value on `ζ_d`.** -/
theorem levelEquiv_ext_root (d : ℕ) (hd : d ≠ 0)
    {σ τ : Gal(↥(levelField (K' := K') 𝔭 d) / 𝔭.adicCompletion K)}
    (h : σ ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root 𝔭 d⟩ =
      τ ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root 𝔭 d⟩) : σ = τ := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  haveI hcyc : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelField (K' := K') 𝔭 d) := isCyclotomicExtension_levelField (K' := K') 𝔭 d hd
  have hζ := levelRoot_primitive_in_levelField (K' := K') 𝔭 d hd
  apply AlgEquiv.coe_toAlgHom_injective
  apply (hζ.powerBasis (𝔭.adicCompletion K)).algHom_ext
  exact h

/-- **The exponents `q ^ x` of a primitive level root only depend on `x` modulo the level.** -/
theorem levelRoot_pow_pow_modEq {e : ℕ} (he : e ≠ 0) {ζ : K'}
    (hζ : IsPrimitiveRoot ζ (levelN 𝔭 e)) {x y : ℕ} (h : x ≡ y [MOD e]) :
    ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ x) =
      ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ y) := by
  have hq : ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ e) = ζ := by
    have hone : 1 ≤ NK.LocalStructure.residueCard K 𝔭 ^ e :=
      Nat.one_le_pow _ _ (by have := two_le_residueCard 𝔭; omega)
    have h1 : levelN 𝔭 e + 1 = NK.LocalStructure.residueCard K 𝔭 ^ e := by
      rw [levelN]
      exact Nat.sub_add_cancel hone
    rw [← h1, pow_succ, hζ.pow_eq_one, one_mul]
  have hstep : ∀ m : ℕ, ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ (m + e)) =
      ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ m) := by
    intro m
    rw [pow_add, mul_comm, pow_mul, hq]
  have hiter : ∀ (a k : ℕ), ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ (a + e * k)) =
      ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ a) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hstep, ih]
  have key : ∀ m : ℕ, ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ m) =
      ζ ^ (NK.LocalStructure.residueCard K 𝔭 ^ (m % e)) := by
    intro m
    have hdecomp : m = m % e + e * (m / e) := (Nat.mod_add_div m e).symm
    conv_lhs => rw [hdecomp]
    exact hiter (m % e) (m / e)
  rw [key x, key y, h]

/-- The level `κ⟮ζ_d⟯` realised *inside* `κ(μ_{p'})`: this is the form in which the restriction
map of automorphisms is available. -/
noncomputable def levelFieldInL (d : ℕ) :
    IntermediateField (𝔭.adicCompletion K) ↥(unramifiedL (K' := K') 𝔭) :=
  IntermediateField.adjoin (𝔭.adicCompletion K)
    ({⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩} :
      Set ↥(unramifiedL (K' := K') 𝔭))

theorem mem_levelFieldInL_root (d : ℕ) :
    (⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩ :
      ↥(unramifiedL (K' := K') 𝔭)) ∈ levelFieldInL (K' := K') 𝔭 d :=
  IntermediateField.mem_adjoin_simple_self (𝔭.adicCompletion K) _

theorem levelRoot_isPrimitiveRoot_in_L (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩ :
      ↥(unramifiedL (K' := K') 𝔭)) (levelN 𝔭 d) :=
  IsPrimitiveRoot.coe_submonoidClass_iff.mp (levelRoot_isPrimitiveRoot (K' := K') 𝔭 d hd)

/-- The chosen generator `ζ_d` of a level, viewed inside `κ(μ_{p'})`. -/
noncomputable def levelGen (d : ℕ) : ↥(unramifiedL (K' := K') 𝔭) :=
  ⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩

/-- The chosen generator of a level, viewed inside the level. -/
noncomputable def levelGenInL (d : ℕ) : ↥(levelFieldInL (K' := K') 𝔭 d) :=
  ⟨levelGen (K' := K') 𝔭 d, mem_levelFieldInL_root (K' := K') 𝔭 d⟩

theorem levelGenInL_isPrimitiveRoot (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (levelGenInL (K' := K') 𝔭 d) (levelN 𝔭 d) := by
  rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
  exact levelRoot_isPrimitiveRoot_in_L (K' := K') 𝔭 d hd


theorem isCyclotomicExtension_levelFieldInL (d : ℕ) (hd : d ≠ 0) :
    IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelFieldInL (K' := K') 𝔭 d) := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  haveI hint : Algebra.IsIntegral (𝔭.adicCompletion K) ↥(unramifiedL (K' := K') 𝔭) := by
    haveI hK' : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
    refine ⟨fun x => ?_⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom _ ↥(unramifiedL (K' := K') 𝔭) K') (RingHom.injective
      (algebraMap ↥(unramifiedL (K' := K') 𝔭) K'))).mp (hK'.isIntegral (x : K'))
  rw [levelFieldInL]
  exact (levelRoot_isPrimitiveRoot_in_L (K' := K') 𝔭 d hd).intermediateField_adjoin_isCyclotomicExtension
    (𝔭.adicCompletion K)

instance isGalois_levelFieldInL (d : ℕ) [NeZero d] :
    IsGalois (𝔭.adicCompletion K) ↥(levelFieldInL (K' := K') 𝔭 d) := by
  haveI : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelFieldInL (K' := K') 𝔭 d) :=
    isCyclotomicExtension_levelFieldInL (K' := K') 𝔭 d (NeZero.ne d)
  exact IsCyclotomicExtension.isGalois {levelN 𝔭 d} (𝔭.adicCompletion K)
    ↥(levelFieldInL (K' := K') 𝔭 d)

instance normal_levelFieldInL (d : ℕ) [NeZero d] :
    Normal (𝔭.adicCompletion K) ↥(levelFieldInL (K' := K') 𝔭 d) :=
  IsGalois.to_normal

/-- **The restriction of an automorphism of `κ(μ_{p'})` to the cyclotomic level `d`.** -/
noncomputable def levelRestrict (d : ℕ) (hd : d ≠ 0) :
    Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K) →*
      Gal(↥(levelFieldInL (K' := K') 𝔭 d) / 𝔭.adicCompletion K) := by
  haveI : NeZero d := ⟨hd⟩
  exact AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := ↥(unramifiedL (K' := K') 𝔭))
    ↥(levelFieldInL (K' := K') 𝔭 d)

/-- The restriction map is the restriction of the automorphism. -/
theorem levelRestrict_apply (d : ℕ) (hd : d ≠ 0)
    (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (x : ↥(levelFieldInL (K' := K') 𝔭 d)) :
    (levelRestrict (K' := K') 𝔭 d hd σ) x = σ x := by
  haveI : NeZero d := ⟨hd⟩
  exact AlgEquiv.restrictNormalHom_apply (F := 𝔭.adicCompletion K)
    (K₁ := ↥(unramifiedL (K' := K') 𝔭)) (levelFieldInL (K' := K') 𝔭 d) σ x

/-- The level fields inside `κ(μ_{p'})` are nested. -/
theorem levelFieldInL_le_levelFieldInL {e d : ℕ} (he : e ≠ 0) (hd : d ≠ 0) (hed : e ∣ d) :
    levelFieldInL (K' := K') 𝔭 e ≤ levelFieldInL (K' := K') 𝔭 d := by
  obtain ⟨k, hk⟩ := levelRoot_pow_eq (K' := K') 𝔭 he hd hed
  rw [levelFieldInL, levelFieldInL]
  apply IntermediateField.adjoin_le_iff.mpr
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hgen : (⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩ :
      ↥(unramifiedL (K' := K') 𝔭)) ∈
      IntermediateField.adjoin (𝔭.adicCompletion K)
        ({⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩} :
          Set ↥(unramifiedL (K' := K') 𝔭)) :=
    IntermediateField.mem_adjoin_simple_self _ _
  have hpow : (⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩ :
      ↥(unramifiedL (K' := K') 𝔭)) ^ k ∈
      IntermediateField.adjoin (𝔭.adicCompletion K)
        ({⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩} :
          Set ↥(unramifiedL (K' := K') 𝔭)) := pow_mem hgen k
  have heq : (⟨levelRoot (K' := K') 𝔭 e, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 e⟩ :
      ↥(unramifiedL (K' := K') 𝔭)) =
      (⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩ :
        ↥(unramifiedL (K' := K') 𝔭)) ^ k := by
    apply Subtype.ext
    exact hk
  rwa [heq]

/-- **An automorphism of a level inside `κ(μ_{p'})` is determined by its action on `ζ_d`.** -/
theorem levelRestrict_ext_root (d : ℕ) (hd : d ≠ 0)
    {σ τ : Gal(↥(levelFieldInL (K' := K') 𝔭 d) / 𝔭.adicCompletion K)}
    (h : σ ⟨⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩,
        mem_levelFieldInL_root (K' := K') 𝔭 d⟩ =
      τ ⟨⟨levelRoot (K' := K') 𝔭 d, levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩,
        mem_levelFieldInL_root (K' := K') 𝔭 d⟩) : σ = τ := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  haveI hcyc : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelFieldInL (K' := K') 𝔭 d) :=
    isCyclotomicExtension_levelFieldInL (K' := K') 𝔭 d hd
  have hζ : IsPrimitiveRoot (⟨⟨levelRoot (K' := K') 𝔭 d,
      levelRoot_mem_unramifiedClosure (K' := K') 𝔭 d⟩, mem_levelFieldInL_root (K' := K') 𝔭 d⟩ :
      ↥(levelFieldInL (K' := K') 𝔭 d)) (levelN 𝔭 d) :=
    levelGenInL_isPrimitiveRoot (K' := K') 𝔭 d hd
  apply AlgEquiv.coe_toAlgHom_injective
  apply (hζ.powerBasis (𝔭.adicCompletion K)).algHom_ext
  exact h

end


/-- A `κ`-algebra isomorphism between the two realisations of the level `d`. -/
noncomputable def levelIso (d : ℕ) (hd : d ≠ 0) :
    ↥(levelFieldInL (K' := K') 𝔭 d) ≃ₐ[𝔭.adicCompletion K] ↥(levelField (K' := K') 𝔭 d) := by
  haveI h1 : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelFieldInL (K' := K') 𝔭 d) :=
    isCyclotomicExtension_levelFieldInL (K' := K') 𝔭 d hd
  haveI h2 : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelField (K' := K') 𝔭 d) := isCyclotomicExtension_levelField (K' := K') 𝔭 d hd
  exact IsCyclotomicExtension.algEquiv {levelN 𝔭 d} (𝔭.adicCompletion K)
    ↥(levelFieldInL (K' := K') 𝔭 d) ↥(levelField (K' := K') 𝔭 d)

/-- The canonical isomorphism `ℤ/d ≅ Gal(κ⟮ζ_d⟯/κ)` for the level realised inside `κ(μ_{p'})`,
obtained from the corresponding isomorphism for the level realised inside `K'`. -/
noncomputable def levelEquivInL
    (T : (d : ℕ) → (hd : d ≠ 0) → Multiplicative (ZMod d) ≃*
      Gal(↥(levelField (K' := K') 𝔭 d) / 𝔭.adicCompletion K)) (d : ℕ) (hd : d ≠ 0) :
    Multiplicative (ZMod d) ≃* Gal(↥(levelFieldInL (K' := K') 𝔭 d) / 𝔭.adicCompletion K) :=
  (T d hd).trans ((AlgEquiv.autCongr (levelIso (K' := K') 𝔭 d hd)).symm)

/-- **The canonical isomorphism acts on the generator by `ζ ↦ ζ ^ (q ^ a)`.** -/
theorem levelEquivInL_apply_gen
    (T : (d : ℕ) → (hd : d ≠ 0) → Multiplicative (ZMod d) ≃*
      Gal(↥(levelField (K' := K') 𝔭 d) / 𝔭.adicCompletion K))
    (hT : ∀ (d : ℕ) (hd : d ≠ 0) (a : Multiplicative (ZMod d)),
      T d hd a ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ =
        ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ ^
          (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val))
    (d : ℕ) (hd : d ≠ 0) (a : Multiplicative (ZMod d)) :
    levelEquivInL (K' := K') 𝔭 T d hd a (levelGenInL (K' := K') 𝔭 d) =
      (levelGenInL (K' := K') 𝔭 d) ^
        (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val) := by
  haveI : NeZero (levelN 𝔭 d) := ⟨levelN_ne_zero 𝔭 d hd⟩
  have hζ := levelRoot_primitive_in_levelField (K' := K') 𝔭 d hd
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (levelIso (K' := K') 𝔭 d hd)
    (levelGenInL (K' := K') 𝔭 d)) (by
      rw [← map_pow, (levelGenInL_isPrimitiveRoot (K' := K') 𝔭 d hd).pow_eq_one, map_one])
  calc levelEquivInL (K' := K') 𝔭 T d hd a (levelGenInL (K' := K') 𝔭 d)
      = (levelIso (K' := K') 𝔭 d hd).symm
          ((T d hd a) ((levelIso (K' := K') 𝔭 d hd) (levelGenInL (K' := K') 𝔭 d))) := rfl
    _ = (levelIso (K' := K') 𝔭 d hd).symm
          ((T d hd a) ((⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ :
            ↥(levelField (K' := K') 𝔭 d)) ^ j)) := by rw [hj]
    _ = (levelIso (K' := K') 𝔭 d hd).symm
          (((T d hd a) ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩) ^ j) := by
        rw [map_pow]
    _ = (levelIso (K' := K') 𝔭 d hd).symm
          (((⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ :
            ↥(levelField (K' := K') 𝔭 d)) ^
              (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val)) ^ j) := by
        rw [hT]
    _ = (levelIso (K' := K') 𝔭 d hd).symm
          (((⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ :
            ↥(levelField (K' := K') 𝔭 d)) ^ j) ^
              (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val)) := by
        rw [← pow_mul, mul_comm, pow_mul]
    _ = ((levelIso (K' := K') 𝔭 d hd).symm
          ((levelIso (K' := K') 𝔭 d hd) (levelGenInL (K' := K') 𝔭 d))) ^
            (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val) := by
        rw [← hj, map_pow]
    _ = (levelGenInL (K' := K') 𝔭 d) ^
          (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val) := by
        rw [AlgEquiv.symm_apply_apply]

/-- The two generators of the levels `e` and `d` for `e ∣ d`. -/
theorem levelGen_pow_eq {e d : ℕ} (he : e ≠ 0) (hd : d ≠ 0) (hed : e ∣ d) :
    ∃ k : ℕ, levelGen (K' := K') 𝔭 e = (levelGen (K' := K') 𝔭 d) ^ k := by
  obtain ⟨k, hk⟩ := levelRoot_pow_eq (K' := K') 𝔭 he hd hed
  exact ⟨k, Subtype.ext hk⟩

theorem levelGen_pow_pow_modEq {e y z : ℕ} (he : e ≠ 0) (h : y ≡ z [MOD e]) :
    (levelGen (K' := K') 𝔭 e) ^ (NK.LocalStructure.residueCard K 𝔭 ^ y) =
      (levelGen (K' := K') 𝔭 e) ^ (NK.LocalStructure.residueCard K 𝔭 ^ z) := by
  apply Subtype.ext
  push_cast
  exact levelRoot_pow_pow_modEq (K' := K') 𝔭 he (levelRoot_isPrimitiveRoot (K' := K') 𝔭 e he) h

/-- The canonical isomorphism `ℤ/d ≅ Gal(κ⟮ζ_d⟯/κ)` for the level realised inside `K'`. -/
noncomputable def levelEquiv (d : ℕ) (hd : d ≠ 0) :
    Multiplicative (ZMod d) ≃* Gal(↥(levelField (K' := K') 𝔭 d) / 𝔭.adicCompletion K) :=
  Classical.choose (exists_mulEquiv_zmod_algEquiv_adjoin_primitiveRoot (K' := K') 𝔭 hd
    (levelRoot_isPrimitiveRoot (K' := K') 𝔭 d hd))

theorem levelEquiv_apply_root (d : ℕ) (hd : d ≠ 0) (a : Multiplicative (ZMod d)) :
    levelEquiv (K' := K') 𝔭 d hd a
        ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ =
      ⟨levelRoot (K' := K') 𝔭 d, mem_levelField_root (K' := K') 𝔭 d⟩ ^
        (NK.LocalStructure.residueCard K 𝔭 ^ (Multiplicative.toAdd a).val) := by
  unfold levelEquiv
  exact Classical.choose_spec (exists_mulEquiv_zmod_algEquiv_adjoin_primitiveRoot (K' := K') 𝔭 hd
    (levelRoot_isPrimitiveRoot (K' := K') 𝔭 d hd)) a

/-- The `d`-th component of the map `Gal(κ(μ_{p'})/κ) → Ẑ`. -/
noncomputable def levelExp (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (d : ℕ) (hd : d ≠ 0) : Multiplicative (ZMod d) :=
  (levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd).symm (levelRestrict (K' := K') 𝔭 d hd σ)

theorem levelExp_apply (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (d : ℕ) (hd : d ≠ 0) :
    levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd (levelExp (K' := K') 𝔭 σ d hd) =
      levelRestrict (K' := K') 𝔭 d hd σ :=
  MulEquiv.apply_symm_apply _ _

/-- **The components are compatible: the level-`e` component is the reduction of the level-`d`
component for `e ∣ d`.** -/
theorem levelExp_compat (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    {e d : ℕ} (he : e ≠ 0) (hd : d ≠ 0) (hed : e ∣ d) :
    ZMod.castHom hed (ZMod e) (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)) =
      Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ e he) := by
  haveI : NeZero d := ⟨hd⟩
  haveI : NeZero e := ⟨he⟩
  have hd_act : σ (levelGen (K' := K') 𝔭 d) =
      (levelGen (K' := K') 𝔭 d) ^ (NK.LocalStructure.residueCard K 𝔭 ^
        (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val) := by
    have h2 : ((levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd)
        (levelExp (K' := K') 𝔭 σ d hd)) (levelGenInL (K' := K') 𝔭 d) =
        (levelGenInL (K' := K') 𝔭 d) ^ (NK.LocalStructure.residueCard K 𝔭 ^
          (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val) :=
      levelEquivInL_apply_gen (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭)
        (levelEquiv_apply_root (K' := K') 𝔭) d hd _
    rw [levelExp_apply (K' := K') 𝔭 σ d hd] at h2
    have h3 := congrArg (fun y : ↥(levelFieldInL (K' := K') 𝔭 d) =>
      (y : ↥(unramifiedL (K' := K') 𝔭))) h2
    rw [SubmonoidClass.coe_pow] at h3
    rw [levelRestrict_apply (K' := K') 𝔭 d hd σ (levelGenInL (K' := K') 𝔭 d)] at h3
    rw [show ((levelGenInL (K' := K') 𝔭 d : ↥(levelFieldInL (K' := K') 𝔭 d)) :
        ↥(unramifiedL (K' := K') 𝔭)) = levelGen (K' := K') 𝔭 d from rfl] at h3
    exact h3

  have he_act : σ (levelGen (K' := K') 𝔭 e) =
      (levelGen (K' := K') 𝔭 e) ^ (NK.LocalStructure.residueCard K 𝔭 ^
        (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val) := by
    obtain ⟨k, hk⟩ := levelGen_pow_eq (K' := K') 𝔭 he hd hed
    calc σ (levelGen (K' := K') 𝔭 e)
        = σ ((levelGen (K' := K') 𝔭 d) ^ k) := by rw [hk]
      _ = (σ (levelGen (K' := K') 𝔭 d)) ^ k := by rw [map_pow]
      _ = ((levelGen (K' := K') 𝔭 d) ^ (NK.LocalStructure.residueCard K 𝔭 ^
            (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val)) ^ k := by rw [hd_act]
      _ = ((levelGen (K' := K') 𝔭 d) ^ k) ^ (NK.LocalStructure.residueCard K 𝔭 ^
            (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val) := by
          rw [← pow_mul, mul_comm, pow_mul]
      _ = (levelGen (K' := K') 𝔭 e) ^ (NK.LocalStructure.residueCard K 𝔭 ^
            (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val) := by rw [← hk]
  have key : (levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) e he)
        (Multiplicative.ofAdd (ZMod.castHom hed (ZMod e)
          (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd))))
        (levelGenInL (K' := K') 𝔭 e) =
      (levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) e he)
        (levelExp (K' := K') 𝔭 σ e he) (levelGenInL (K' := K') 𝔭 e) := by
    apply Subtype.ext
    have h2 : ((levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) e he)
        (Multiplicative.ofAdd (ZMod.castHom hed (ZMod e)
          (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd))))
        (levelGenInL (K' := K') 𝔭 e) :
        ↥(unramifiedL (K' := K') 𝔭)) =
        (levelGenInL (K' := K') 𝔭 e : ↥(unramifiedL (K' := K') 𝔭)) ^
          (NK.LocalStructure.residueCard K 𝔭 ^
            (ZMod.castHom hed (ZMod e)
              (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd))).val) := by
      rw [levelEquivInL_apply_gen (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭)
        (levelEquiv_apply_root (K' := K') 𝔭) e he _]
      rw [SubmonoidClass.coe_pow]
      simp only [toAdd_ofAdd]
    rw [h2]
    have h4 : ((levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) e he)
        (levelExp (K' := K') 𝔭 σ e he) (levelGenInL (K' := K') 𝔭 e) :
        ↥(unramifiedL (K' := K') 𝔭)) = σ (levelGen (K' := K') 𝔭 e) := by
      rw [levelExp_apply (K' := K') 𝔭 σ e he]
      rw [levelRestrict_apply (K' := K') 𝔭 e he σ (levelGenInL (K' := K') 𝔭 e)]
      rw [show ((levelGenInL (K' := K') 𝔭 e : ↥(levelFieldInL (K' := K') 𝔭 e)) :
          ↥(unramifiedL (K' := K') 𝔭)) = levelGen (K' := K') 𝔭 e from rfl]
    rw [h4, he_act]
    rw [show ((levelGenInL (K' := K') 𝔭 e : ↥(levelFieldInL (K' := K') 𝔭 e)) :
        ↥(unramifiedL (K' := K') 𝔭)) = levelGen (K' := K') 𝔭 e from rfl]
    exact levelGen_pow_pow_modEq (K' := K') 𝔭 he (by
      have hcast : (ZMod.castHom hed (ZMod e)
          (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd))).val =
          (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd)).val % e := by
        rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      rw [Nat.ModEq, hcast, Nat.mod_mod])

  have hEq : Multiplicative.ofAdd (ZMod.castHom hed (ZMod e)
      (Multiplicative.toAdd (levelExp (K' := K') 𝔭 σ d hd))) = levelExp (K' := K') 𝔭 σ e he :=
    (levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) e he).injective
      (levelRestrict_ext_root (K' := K') 𝔭 e he key)
  exact congrArg Multiplicative.toAdd hEq

theorem levelGen_isPrimitiveRoot (d : ℕ) (hd : d ≠ 0) :
    IsPrimitiveRoot (levelGen (K' := K') 𝔭 d) (levelN 𝔭 d) :=
  levelRoot_isPrimitiveRoot_in_L (K' := K') 𝔭 d hd

theorem zpow_apply_eq_self {F E : Type*} [Field F] [Field E] [Algebra F E]
    (g : E ≃ₐ[F] E) {x : E} (h : g x = x) (m : ℤ) : (g ^ m) x = x := by
  have hstab : g ∈ MulAction.stabilizer (E ≃ₐ[F] E) x := by
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  have hpow := zpow_mem hstab m
  rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hpow

theorem levelGen_pow_of_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) (hnp : ¬ residueChar 𝔭 ∣ n)
    {ζ : ↥(unramifiedL (K' := K') 𝔭)} (hζ : IsPrimitiveRoot ζ n) :
    ∃ k : ℕ, ζ = (levelGen (K' := K') 𝔭 (Nat.totient n)) ^ k := by
  have htot : Nat.totient n ≠ 0 := fun h => hn (Nat.totient_eq_zero.mp h)
  have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpc := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hf, hqf⟩ := NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hpc
  have hcop : Nat.Coprime (NK.LocalStructure.residueCard K 𝔭) n := by
    rw [hqf]
    exact Nat.Coprime.pow_left f (hp.coprime_iff_not_dvd.mpr hnp)
  have hmod : NK.LocalStructure.residueCard K 𝔭 ^ Nat.totient n ≡ 1 [MOD n] :=
    Nat.ModEq.pow_totient hcop
  have hone : 1 ≤ NK.LocalStructure.residueCard K 𝔭 ^ Nat.totient n :=
    Nat.one_le_pow _ _ (by have := two_le_residueCard 𝔭; omega)
  have hdvd : n ∣ levelN 𝔭 (Nat.totient n) := by
    rw [levelN]
    exact (Nat.modEq_iff_dvd' hone).mp hmod.symm
  haveI : NeZero (levelN 𝔭 (Nat.totient n)) := ⟨levelN_ne_zero 𝔭 _ htot⟩
  obtain ⟨k, -, hk⟩ :=
    (levelGen_isPrimitiveRoot (K' := K') 𝔭 (Nat.totient n) htot).eq_pow_of_pow_eq_one
      (ξ := ζ) ((hζ.pow_eq_one_iff_dvd (levelN 𝔭 (Nat.totient n))).mpr hdvd)
  exact ⟨k, hk.symm⟩

theorem existsUnique_zhat_levelExp (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K)) :
    ∃! z : NK.LocalAnabelian.Zhat, ∀ (d : ℕ) (hd : d ≠ 0),
      compHomZMod d hd z = levelExp (K' := K') 𝔭 σ d hd :=
  zhat_existsUnique_compHomZMod_eq (fun d hd => levelExp (K' := K') 𝔭 σ d hd)
    (fun _d _e hd he h => levelExp_compat (K' := K') 𝔭 σ he hd h)

noncomputable def psiFun (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K)) :
    NK.LocalAnabelian.Zhat :=
  Classical.choose (existsUnique_zhat_levelExp (K' := K') 𝔭 σ).exists

theorem psiFun_spec (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (d : ℕ) (hd : d ≠ 0) :
    compHomZMod d hd (psiFun (K' := K') 𝔭 σ) = levelExp (K' := K') 𝔭 σ d hd :=
  Classical.choose_spec (existsUnique_zhat_levelExp (K' := K') 𝔭 σ).exists d hd

theorem levelExp_mul (σ τ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (d : ℕ) (hd : d ≠ 0) :
    levelExp (K' := K') 𝔭 (σ * τ) d hd =
      levelExp (K' := K') 𝔭 σ d hd * levelExp (K' := K') 𝔭 τ d hd := by
  have h1 : levelRestrict (K' := K') 𝔭 d hd (σ * τ) =
      levelRestrict (K' := K') 𝔭 d hd σ * levelRestrict (K' := K') 𝔭 d hd τ :=
    map_mul _ _ _
  unfold levelExp
  rw [h1, map_mul]

theorem levelExp_one (d : ℕ) (hd : d ≠ 0) :
    levelExp (K' := K') 𝔭 (1 : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K)) d hd = 1 := by
  unfold levelExp
  rw [map_one, map_one]

theorem psiFun_one :
    psiFun (K' := K') 𝔭 (1 : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K)) = 1 := by
  apply (existsUnique_zhat_levelExp (K' := K') 𝔭 1).unique
  · intro d hd; exact psiFun_spec (K' := K') 𝔭 1 d hd
  · intro d hd
    rw [map_one, levelExp_one]

theorem psiFun_mul (σ τ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K)) :
    psiFun (K' := K') 𝔭 (σ * τ) = psiFun (K' := K') 𝔭 σ * psiFun (K' := K') 𝔭 τ := by
  apply (existsUnique_zhat_levelExp (K' := K') 𝔭 (σ * τ)).unique
  · intro d hd; exact psiFun_spec (K' := K') 𝔭 (σ * τ) d hd
  · intro d hd
    rw [map_mul, psiFun_spec (K' := K') 𝔭 σ d hd, psiFun_spec (K' := K') 𝔭 τ d hd,
      levelExp_mul]

noncomputable def psiHom :
    Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K) →* NK.LocalAnabelian.Zhat where
  toFun := psiFun (K' := K') 𝔭
  map_one' := psiFun_one (K' := K') 𝔭
  map_mul' := psiFun_mul (K' := K') 𝔭

theorem psiHom_spec (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (d : ℕ) (hd : d ≠ 0) :
    compHomZMod d hd (psiHom (K' := K') 𝔭 σ) = levelExp (K' := K') 𝔭 σ d hd :=
  psiFun_spec (K' := K') 𝔭 σ d hd

theorem levelGen_fixed_of_psiFun_eq_one
    (σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K))
    (hσ : psiFun (K' := K') 𝔭 σ = 1) :
    ∀ d (hd : d ≠ 0), σ (levelGen (K' := K') 𝔭 d) = levelGen (K' := K') 𝔭 d := by
  intro d hd
  have h1 : levelExp (K' := K') 𝔭 σ d hd = 1 := by
    have h2 := psiFun_spec (K' := K') 𝔭 σ d hd
    rw [hσ, map_one] at h2
    exact h2.symm
  have h3 : levelRestrict (K' := K') 𝔭 d hd σ = 1 := by
    have h4 := levelExp_apply (K' := K') 𝔭 σ d hd
    rw [h1, map_one] at h4
    exact h4.symm
  haveI : NeZero d := ⟨hd⟩
  have hfix := (AlgEquiv.restrictNormal_eq_one_iff (levelFieldInL (K' := K') 𝔭 d) σ).mp h3
  exact hfix (levelGen (K' := K') 𝔭 d) (mem_levelFieldInL_root (K' := K') 𝔭 d)


theorem iSup_levelGen_eq_top :
    (⨆ (n : {n : ℕ // ¬ residueChar 𝔭 ∣ n}) (ζ : ↥(unramifiedL (K' := K') 𝔭))
      (_ : IsPrimitiveRoot ζ (n : ℕ)),
        IntermediateField.adjoin (𝔭.adicCompletion K)
          ({ζ} : Set ↥(unramifiedL (K' := K') 𝔭))) = ⊤ := by
  unfold unramifiedL
  exact iSup_adjoin_primitiveRoot_eq_top 𝔭

theorem psiHom_injective : Function.Injective (psiHom (K' := K') 𝔭) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hσ' : psiFun (K' := K') 𝔭 σ = 1 := hσ
  have hfix := levelGen_fixed_of_psiFun_eq_one (K' := K') 𝔭 σ hσ'
  have hfixall : (⊤ : IntermediateField (𝔭.adicCompletion K) ↥(unramifiedL (K' := K') 𝔭)) ≤
      IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← iSup_levelGen_eq_top (K' := K') 𝔭]
    refine iSup_le fun n => iSup_le fun ζ => iSup_le fun hζ => ?_
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    refine (IntermediateField.mem_fixedField_iff (Subgroup.zpowers σ) y).mpr ?_
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hn : (n : ℕ) ≠ 0 := fun h => n.2 (by rw [h]; exact dvd_zero _)
    obtain ⟨k, hk⟩ := levelGen_pow_of_isPrimitiveRoot (K' := K') 𝔭 hn n.2 hζ
    rw [hk, map_pow,
      zpow_apply_eq_self σ (hfix (Nat.totient ↑n) (fun h => hn (Nat.totient_eq_zero.mp h))) m]
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := hfixall trivial
  have h2 := (IntermediateField.mem_fixedField_iff (Subgroup.zpowers σ) x).mp hx σ
    (Subgroup.mem_zpowers σ)
  simpa only [AlgEquiv.one_apply] using h2

theorem psiHom_continuous : Continuous (psiHom (K' := K') 𝔭) := by
  apply continuous_of_continuous_compHomZMod
  intro d hd
  have h1 : (fun σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K) =>
      compHomZMod d hd (psiHom (K' := K') 𝔭 σ)) =
      fun σ => levelExp (K' := K') 𝔭 σ d hd := by
    funext σ; exact psiHom_spec (K' := K') 𝔭 σ d hd
  rw [h1]
  haveI : NeZero d := ⟨hd⟩
  haveI hcyc : IsCyclotomicExtension {levelN 𝔭 d} (𝔭.adicCompletion K)
      ↥(levelFieldInL (K' := K') 𝔭 d) := isCyclotomicExtension_levelFieldInL (K' := K') 𝔭 d hd
  haveI : FiniteDimensional (𝔭.adicCompletion K) ↥(levelFieldInL (K' := K') 𝔭 d) :=
    IsCyclotomicExtension.finiteDimensional {levelN 𝔭 d} (𝔭.adicCompletion K) _
  have hrestr : Continuous (fun σ : Gal(↥(unramifiedL (K' := K') 𝔭) / 𝔭.adicCompletion K) =>
      levelRestrict (K' := K') 𝔭 d hd σ) := by
    unfold levelRestrict
    exact InfiniteGalois.restrictNormalHom_continuous (levelFieldInL (K' := K') 𝔭 d)
  have hequiv : Continuous
      ((levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd).symm) :=
    continuous_of_discreteTopology
  unfold levelExp
  exact hequiv.comp hrestr

theorem levelExp_surjective (d : ℕ) (hd : d ≠ 0) :
    Function.Surjective (fun σ => levelExp (K' := K') 𝔭 σ d hd) := by
  intro a
  haveI : NeZero d := ⟨hd⟩
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := 𝔭.adicCompletion K)
    (K₁ := ↥(levelFieldInL (K' := K') 𝔭 d)) (E := ↥(unramifiedL (K' := K') 𝔭))
    ((levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd) a)
  refine ⟨σ, ?_⟩
  have hσ' : levelRestrict (K' := K') 𝔭 d hd σ =
      (levelEquivInL (K' := K') 𝔭 (levelEquiv (K' := K') 𝔭) d hd) a := hσ
  show levelExp (K' := K') 𝔭 σ d hd = a
  unfold levelExp
  rw [hσ']
  exact MulEquiv.symm_apply_apply _ _

theorem psiHom_range_eq_top : (psiHom (K' := K') 𝔭).range = ⊤ := by
  apply zhat_eq_top_of_isClosed_of_compHomZMod_image_eq_univ
  · have hcont := psiHom_continuous (K' := K') 𝔭
    have h : IsClosed (Set.range (psiHom (K' := K') 𝔭)) := (isCompact_range hcont).isClosed
    exact h
  · intro d hd
    rw [Set.eq_univ_iff_forall]
    intro a
    obtain ⟨σ, hσ⟩ := levelExp_surjective (K' := K') 𝔭 d hd a
    refine ⟨psiHom (K' := K') 𝔭 σ, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, ?_⟩
    rw [psiHom_spec (K' := K') 𝔭 σ d hd]
    exact hσ

theorem psiHom_surjective : Function.Surjective (psiHom (K' := K') 𝔭) := by
  intro z
  have hz : z ∈ (psiHom (K' := K') 𝔭).range := by
    rw [psiHom_range_eq_top (K' := K') 𝔭]
    trivial
  exact MonoidHom.mem_range.mp hz

theorem galoisGroup_unramifiedClosure_mulEquiv {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    Nonempty (Gal(↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))))
      / 𝔭.adicCompletion K) ≃* NK.LocalAnabelian.Zhat) :=
  ⟨MulEquiv.ofBijective (psiHom (K' := K') 𝔭)
    ⟨psiHom_injective (K' := K') 𝔭, psiHom_surjective (K' := K') 𝔭⟩⟩

end NK.TameStructureDeep.Degree
