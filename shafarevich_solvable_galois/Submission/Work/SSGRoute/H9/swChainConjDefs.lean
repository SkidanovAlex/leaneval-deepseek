import Mathlib
import Submission.Work.SSGRoute.H9.swPairingValueFrob
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.H9.swCount_eq_zero
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
import Submission.Work.SSGRoute.ZDataTwo.kummerCochar_conjElem
import Submission.Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugate route to the §4(b) chain: vocabulary

The chain value identity of Schmidt--Wingberg §4(b) is proved (see
`H9/NOTE_chain_route_conjugates.md`) by pairing each escape class with the *conjugate* of an escape
class at the sibling of the other escape prime.  This file fixes the vocabulary of that route:

* `conjUnit σ c` — the conjugate `c^σ ∈ Kˣ` of `c` by `σ ∈ G_k` (through its restriction to `K`);
* `galLift_apply_coe` — `galLift K σ` acts on `↥K` as `σ`;
* `galLift_conj_mem_fixingSubgroup` — `galLift K σ` normalises `↥K`;
* `swGesKConj_galLift_smul_iff` — `K`-conjugacy of places under the translation by `galLift K σ`.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

/-- **The conjugate `c^σ ∈ Kˣ`** of `c ∈ Kˣ` by `σ ∈ G_k` (through the restriction of `σ` to the
normal subextension `K|k`).  This is the element whose Kummer class is the `σ`-conjugate of the
Kummer class of `c`. -/
noncomputable def conjUnit {K : IntermediateField k Ω} [Normal k K] (σ : Ω ≃ₐ[k] Ω)
    (c : (↥K)ˣ) : (↥K)ˣ :=
  Units.map (AlgEquiv.restrictNormalHom K σ).toMonoidHom c

lemma conjUnit_mul {K : IntermediateField k Ω} [Normal k K] (σ : Ω ≃ₐ[k] Ω) (a b : (↥K)ˣ) :
    conjUnit σ (a * b) = conjUnit σ a * conjUnit σ b :=
  map_mul _ a b

lemma conjUnit_one {K : IntermediateField k Ω} [Normal k K] (σ : Ω ≃ₐ[k] Ω) :
    conjUnit σ (1 : (↥K)ˣ) = 1 :=
  map_one _

/-- The action of `galLift K σ` on an element of `K`, read in `Ω`. -/
lemma galLift_apply_coe {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (x : ↥K) :
    ((galLift K σ) x : Ω) = ((σ x : ↥K) : Ω) := by
  have h := AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K (galLift K σ) x
  rw [galLift_spec] at h
  exact h.symm

/-- `galLift K σ` maps `K` into itself. -/
lemma galLift_mem_of_mem {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) {x : Ω} (hx : x ∈ K) : (galLift K σ) x ∈ K := by
  have h := galLift_apply_coe (K := K) σ ⟨x, hx⟩
  rw [h]
  exact (σ ⟨x, hx⟩).2

/-- The inverse of `galLift K σ` maps `K` into itself. -/
lemma galLift_symm_mem_of_mem {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) {x : Ω} (hx : x ∈ K) : ((galLift K σ)⁻¹) x ∈ K := by
  have h : (galLift K σ) (((σ⁻¹) ⟨x, hx⟩ : ↥K) : Ω) = x := by
    rw [galLift_apply_coe (K := K) σ (σ⁻¹ ⟨x, hx⟩)]
    simp
  have hx' : ((galLift K σ)⁻¹) x = (((σ⁻¹) ⟨x, hx⟩ : ↥K) : Ω) := by
    apply (galLift K σ).injective
    rw [h]
    simp
  rw [hx']
  exact ((σ⁻¹) ⟨x, hx⟩).2

/-- **`galLift K σ` normalises `↥K`** (the left-handed form actually used below): conjugating an
element of `K.fixingSubgroup` by it stays in `K.fixingSubgroup`. -/
lemma galLift_conj_mem_fixingSubgroup {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (σ : K ≃ₐ[k] K) {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup) :
    (galLift K σ)⁻¹ * τ * galLift K σ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  intro x hx
  have hxK : ((galLift K σ) x) ∈ K := galLift_mem_of_mem σ hx
  change ((galLift K σ)⁻¹ * τ * galLift K σ) x = x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ _ hxK]
  exact AlgEquiv.symm_apply_apply (galLift K σ) x

/-- The other handedness of the normalisation. -/
lemma galLift_mul_conj_mem_fixingSubgroup {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (σ : K ≃ₐ[k] K) {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup) :
    galLift K σ * τ * (galLift K σ)⁻¹ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  intro x hx
  have hxK : ((galLift K σ)⁻¹) x ∈ K := galLift_symm_mem_of_mem σ hx
  change (galLift K σ * τ * (galLift K σ)⁻¹) x = x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ _ hxK]
  exact AlgEquiv.apply_symm_apply (galLift K σ) x

/-- **Translation invariance of the `Kˣ`-conjugate under `G_K`**: conjugating by an element of the
fixing subgroup changes nothing. -/
lemma conjUnit_eq_of_mem_fixingSubgroup {K : IntermediateField k Ω} [Normal k K]
    {ρ : Ω ≃ₐ[k] Ω} (hρ : ρ ∈ K.fixingSubgroup) (b : (↥K)ˣ) :
    conjUnit ρ b = b := by
  have h1 : AlgEquiv.restrictNormalHom K ρ = 1 := by
    rw [← IntermediateField.restrictNormalHom_ker K] at hρ
    simpa using hρ
  unfold conjUnit
  rw [h1]
  ext
  simp

/-- **Conjugation equivariance of the zero set of the Kummer cochain.**  The Kummer cochain of the
conjugate class `σ • b` vanishes at `τ` exactly when the Kummer cochain of `b` vanishes at
`σ⁻¹ τ σ`.  For odd `p` the two cochains differ by the cyclotomic character, so this is the correct
(and the only true) equivariance statement; it is what lets the Schmidt--Wingberg §4 conditions be
transferred between a class and its conjugates. -/
theorem swConjElemZero {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b : (↥K)ˣ) (σ τ : Ω ≃ₐ[k] Ω) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit σ b) τ = 0 ↔
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (σ⁻¹ * τ * σ) = 0 := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  have hmem_conj : ∀ (u ρ : Ω ≃ₐ[k] Ω), u ∈ K.fixingSubgroup → ρ⁻¹ * u * ρ ∈ K.fixingSubgroup := by
    intro u ρ hu
    rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
    intro x hx
    have hmem : ρ x ∈ K := by
      have h := Work.SSGRoute.algebraMap_restrictNormalHom (K := K) ρ ⟨x, hx⟩
      rw [show ρ x = ((AlgEquiv.restrictNormalHom K ρ ⟨x, hx⟩ : ↥K) : Ω) from h.symm]
      exact (AlgEquiv.restrictNormalHom K ρ ⟨x, hx⟩).2
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu _ hmem]
    exact AlgEquiv.symm_apply_apply ρ x
  by_cases hτ : τ ∈ K.fixingSubgroup
  · have hconj : σ⁻¹ * τ * σ ∈ K.fixingSubgroup := hmem_conj τ σ hτ
    have hαne : (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) ≠ 0 := Units.ne_zero _
    have hγne : σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) ≠ 0 := by
      rw [← map_zero σ]
      exact fun h => hαne (σ.injective h)
    have hpow : ((Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) ^ p)
        = algebraMap ↥K Ω (b : ↥K) := by
      rw [← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrtUnitZMod_pow, Units.coe_map]
      rfl
    have hγ : (Units.mk0 (σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω)) hγne) ^ p =
        Units.map (algebraMap ↥K Ω) (conjUnit (K := K) σ b) := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map]
      rw [← map_pow, hpow]
      exact (Work.SSGRoute.algebraMap_restrictNormalHom (K := K) σ (b : ↥K)).symm
    have hA : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (K := K) σ b) τ = 0 ↔
        τ (σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω))
          = σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) := by
      rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := conjUnit (K := K) σ b) hτ,
        Work.SSGRoute.kummerCharZMod_apply]
      rw [Work.SSGRoute.kummerIdx_congr p hζ' (conjUnit (K := K) σ b)
        (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p (conjUnit (K := K) σ b)) hγ
        ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩)]
      rw [Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq p hζ' (conjUnit (K := K) σ b)
        (Units.mk0 (σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω)) hγne) hγ
        ((IntermediateField.fixingSubgroupEquiv K) ⟨τ, hτ⟩), Units.val_mk0]
      exact Iff.rfl
    have hB : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (σ⁻¹ * τ * σ) = 0 ↔
        τ (σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω))
          = σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω) := by
      rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := b) hconj,
        Work.SSGRoute.kummerCharZMod_apply]
      rw [Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq p hζ' b
          (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b)
          (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p b)
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ⁻¹ * τ * σ, hconj⟩)]
      show ((σ⁻¹ * τ * σ : Ω ≃ₐ[k] Ω) (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω)
            = (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω)) ↔
          τ (σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω))
            = σ (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p b : Ω)
      constructor
      · intro h
        have h3 := congrArg (fun y => σ y) h
        simpa [AlgEquiv.mul_apply] using h3
      · intro h
        have h3 := congrArg (fun y => σ⁻¹ y) h
        simpa [AlgEquiv.mul_apply] using h3
    exact hA.trans hB.symm
  · have hconj : σ⁻¹ * τ * σ ∉ K.fixingSubgroup := by
      intro hmem
      apply hτ
      have heq : τ = σ * (σ⁻¹ * τ * σ) * σ⁻¹ := by group
      rw [heq]
      exact hmem_conj (σ⁻¹ * τ * σ) σ⁻¹ hmem
    simp only [Work.SSGRoute.ZSplit.nodeKummerCocharZMod, dif_neg hτ, dif_neg hconj]

/-- **`K`-conjugacy is invariant under translation by `galLift K σ`** (in the sharp form used to
transfer the confinements to the siblings). -/
theorem swGesKConj_galLift_smul_iff {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (σ : K ≃ₐ[k] K) (A B : ValuationSubring Ω) :
    Work.SSGRoute.gesKConj K (galLift K σ • A) B ↔
      Work.SSGRoute.gesKConj K A ((galLift K σ)⁻¹ • B) := by
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    refine ⟨(galLift K σ)⁻¹ * τ * galLift K σ, galLift_conj_mem_fixingSubgroup σ hτ, ?_⟩
    rw [mul_smul, mul_smul, hτA]
  · rintro ⟨τ, hτ, hτA⟩
    refine ⟨galLift K σ * τ * (galLift K σ)⁻¹, galLift_mul_conj_mem_fixingSubgroup σ hτ, ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hτA, smul_inv_smul]

/-- Symmetry of level-`K` conjugacy of places. -/
theorem gesKConj_symm'' {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : Work.SSGRoute.gesKConj K B A := by
  obtain ⟨τ, hτ, hτA⟩ := h
  exact ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, by rw [← hτA, inv_smul_smul]⟩

/-- **The prescription (condition (3)) transfers to the conjugates.**  If the sum `χ_i + χ_N`
vanishes on the local group of every sibling `Q` of `Q_i`, then the sum of the conjugate cones
`χ_i^σ + χ_N^σ` vanishes on the local group of `Q_i` itself.

Indeed, `χ_i^σ + χ_N^σ = χ_{(c_i c_N)^σ}`, and by `swConjElemZero` this vanishes at `y` exactly when
`χ_{c_i c_N}` vanishes at `σ̃⁻¹ y σ̃` (`σ̃ := galLift K σ`), which lies in the local group of the
`K`-class of `σ̃⁻¹ • Q_i`; that class is a sibling of `Q_i`
(`swGesKConj_galLift_smul_iff` against `siblingPlace_not_gesKConj`, using the complete splitting of
`Q_i`), so the prescription applies there. -/
theorem swPresc_conjUnit {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Qi : ValuationSubring Ω) (hQi : SSGRoute.IsSplitIn k K Qi)
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Qi Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Qi = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0) :
    ∀ y ∈ SSGRoute.decomp k Qi ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bi) y
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bN) y
        = 0 := by
  classical
  intro y hy
  have hyK : y ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hy).2
  have hyd : y ∈ SSGRoute.decomp k Qi := (Subgroup.mem_inf.mp hy).1
  have hnot : ¬ Work.SSGRoute.gesKConj K Qi ((galLift K σ)⁻¹ • Qi) := by
    intro hc
    refine Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ hQi ?_
    exact gesKConj_symm'' ((swGesKConj_galLift_smul_iff (K := K) σ Qi Qi).mpr hc)
  have hconjy : (galLift K σ)⁻¹ * y * galLift K σ ∈
      SSGRoute.decomp k ((galLift K σ)⁻¹ • Qi) ⊓ K.fixingSubgroup := by
    refine Subgroup.mem_inf.mpr ⟨?_, galLift_conj_mem_fixingSubgroup σ hyK⟩
    rw [SSGRoute.decomp_conj]
    exact Subgroup.mem_map.mpr ⟨y, hyd, rfl⟩
  have hkey : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (conjUnit (galLift K σ) bi) y
      + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (conjUnit (galLift K σ) bN) y
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
        (conjUnit (galLift K σ) (bi * bN)) y := by
    rw [← Pi.add_apply, ← Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK
      (conjUnit (galLift K σ) bi) (conjUnit (galLift K σ) bN)]
    exact (congrFun (congrArg (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ)
      (conjUnit_mul (K := K) (galLift K σ) bi bN)) y).symm
  rw [hkey]
  refine (swConjElemZero (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (b := bi * bN)
    (σ := galLift K σ) (τ := y)).mpr ?_
  have hz := hpresc ((galLift K σ)⁻¹ • Qi) ⟨(galLift K σ)⁻¹, rfl⟩ hnot
    ((galLift K σ)⁻¹ * y * galLift K σ) hconjy
  show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (bi * bN)
    ((galLift K σ)⁻¹ * y * galLift K σ) = 0
  rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK bi bN]
  exact hz


/-- **The prescription holds at the `σ`-sibling of `Q_i`.**  One instantiation of the prescription
hypothesis at the sibling place `galLift K σ • Q_i` (which is a genuine sibling of `Q_i` as soon as
`Q_i` is completely split in `K`); this is step `(δ)` of the chain. -/
theorem swPresc_sibling {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (bi bN : (↥K)ˣ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    (Qi : ValuationSubring Ω) (hQi : SSGRoute.IsSplitIn k K Qi)
    (hpresc : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k Qi Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • Qi = Q) →
      ∀ y ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0) :
    ∀ y ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K σ Qi) ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bi y
        + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ bN y = 0 :=
  fun y hy => hpresc (Work.SSGRoute.ZDataMup.siblingPlace K σ Qi) ⟨galLift K σ, rfl⟩
    (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ hQi) y hy


end Work.SSGRoute.H9
