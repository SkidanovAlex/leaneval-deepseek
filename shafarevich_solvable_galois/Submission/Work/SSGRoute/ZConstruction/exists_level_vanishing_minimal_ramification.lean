import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open scoped Pointwise Topology

open _root_.SSGRoute

/-!
# The minimal (`z`-explained) level on which an additive cochain vanishes

`Work.SSGRoute.ZConstruction.exists_level_vanishing_minimal_ramification`: for an additive, locally
constant cochain `z` on `G_K = K.fixingSubgroup` (with `K/k` finite Galois) there is a finite
Galois level `N ⊇ K` on whose Galois group `z` vanishes, chosen so that the ramification of `N` is
*explained* by the ramification of `z`:

> every finite place `B` that is unramified in `K`, and such that `z` kills the inertia of every
> `G_k`-conjugate of `B` (intersected with `G_K`), is unramified in `N`.

The level is the fixed field of `W = ⋂_{g} g (ker z) g⁻¹` (the largest normal subgroup of `G_k`
contained in `ker z|G_K`); `W` is open because `z` is locally constant, so its fixed field is finite
over `k`, and it is normal, so the fixed field is Galois over `k`.  Conversely, a place `B` whose
inertia is contained in `ker z` (which is what the hypothesis on `B` says, since `B` is unramified
in `K`) lies in every conjugate of `ker z`, hence in `W`: exactly the explanation of the
ramification of `N`.
-/

/-- An additive cochain on `G_K` vanishes at `1`. -/
lemma z_one_of_add {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} {E : Type} [AddCommGroup E] {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) :
    z 1 = 0 := by
  have h : z 1 = z 1 + z 1 := by
    simpa using hzadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
  have h2 : z 1 + 0 = z 1 + z 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem exists_level_vanishing_minimal_ramification
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {E : Type} [AddCommGroup E] {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : IsLocConstOn K.fixingSubgroup z) :
    ∃ N : IntermediateField k Ω, K ≤ N ∧ FiniteDimensional k N ∧ IsGalois k N ∧
      (∀ g ∈ N.fixingSubgroup, z g = 0) ∧
      ∀ B : ValuationSubring Ω, IsFinPlace k B → ¬ IsRamifiedIn k K B →
        (∀ τ : Ω ≃ₐ[k] Ω, ∀ σ ∈ K.fixingSubgroup, IsInertia k (τ • B) σ → z σ = 0) →
        ¬ IsRamifiedIn k N B := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hNormΩ : Normal k Ω := (isGalois_iff.mp hGalΩ).2
  haveI hNormK : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois K
  have hz1 : z 1 = 0 := z_one_of_add hzadd
  -- the subgroup of `G_K` on which `z` vanishes
  let Z : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {g | g ∈ K.fixingSubgroup ∧ z g = 0}
      mul_mem' := by
        intro a b ha hb
        exact ⟨K.fixingSubgroup.mul_mem ha.1 hb.1,
          by rw [hzadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨K.fixingSubgroup.one_mem, hz1⟩
      inv_mem' := by
        intro a ha
        refine ⟨K.fixingSubgroup.inv_mem ha.1, ?_⟩
        have h := hzadd a ha.1 a⁻¹ (K.fixingSubgroup.inv_mem ha.1)
        rw [mul_inv_cancel, hz1, ha.2, zero_add] at h
        exact h.symm }
  have hZmem : ∀ g : Ω ≃ₐ[k] Ω, g ∈ Z ↔ g ∈ K.fixingSubgroup ∧ z g = 0 := by
    intro g
    change (g ∈ K.fixingSubgroup ∧ z g = 0) ↔ (g ∈ K.fixingSubgroup ∧ z g = 0)
    exact Iff.rfl
  -- a *normal* open subgroup of `G_k` on which `z` vanishes (from local constancy)
  have hexU : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ U.Normal ∧
      ∀ u ∈ U, u ∈ K.fixingSubgroup → z u = 0 := by
    obtain ⟨U₀, hU₀open, hU₀c⟩ := hzloc
    have hmem : (U₀ : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 1 :=
      isOpen_iff_mem_nhds.mp hU₀open 1 U₀.one_mem
    obtain ⟨M, hMfin, hMnorm, hMle⟩ :=
      (krullTopology_mem_nhds_one_iff_of_normal k Ω (U₀ : Set (Ω ≃ₐ[k] Ω))).mp hmem
    haveI : FiniteDimensional k M := hMfin
    haveI : Normal k M := hMnorm
    haveI : IsGalois k M := by rw [isGalois_iff]; exact ⟨inferInstance, inferInstance⟩
    refine ⟨M.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen M,
      IsGalois.fixingSubgroup_normal_of_isGalois M, ?_⟩
    intro u hu huK
    have h := hU₀c 1 K.fixingSubgroup.one_mem u (hMle hu) huK
    rw [one_mul, hz1] at h
    exact h
  obtain ⟨U, hUo, hUn, hUvan⟩ := hexU
  have hUZK : U ⊓ K.fixingSubgroup ≤ Z := fun u hu => ⟨hu.2, hUvan u hu.1 hu.2⟩
  have hUfinkOpen :
      IsOpen ((U ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    hUo.inter (IntermediateField.fixingSubgroup_isOpen K)
  -- the largest normal subgroup of `G_k` contained in `Z`, as an explicit intersection
  let W : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {x | ∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z}
      mul_mem' := by
        intro x y hx hy g
        have h : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [h]; exact Z.mul_mem (hx g) (hy g)
      one_mem' := by
        intro g
        have h : g * 1 * g⁻¹ = 1 := by group
        rw [h]; exact Z.one_mem
      inv_mem' := by
        intro x hx g
        have h : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [h]; exact Z.inv_mem (hx g) }
  have hWmem : ∀ x : Ω ≃ₐ[k] Ω, x ∈ W ↔ ∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z := by
    intro x
    change (∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z) ↔ (∀ g : Ω ≃ₐ[k] Ω, g * x * g⁻¹ ∈ Z)
    exact Iff.rfl
  have hWZ : W ≤ Z := by
    intro x hx
    have h := (hWmem x).mp hx 1
    simpa using h
  have hWnorm : W.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hWmem]
    intro h
    have heq : h * (g * x * g⁻¹) * h⁻¹ = (h * g) * x * (h * g)⁻¹ := by group
    rw [heq]
    exact (hWmem x).mp hx (h * g)
  have hUWK : U ⊓ K.fixingSubgroup ≤ W := by
    intro x hx
    rw [hWmem x]
    intro g
    exact ⟨Subgroup.Normal.conj_mem hNormK x hx.2 g,
      hUvan (g * x * g⁻¹) (Subgroup.Normal.conj_mem hUn x hx.1 g)
        (Subgroup.Normal.conj_mem hNormK x hx.2 g)⟩
  have hWopen : IsOpen (W : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isOpen_mono hUWK hUfinkOpen
  have hWclosed : IsClosed (W : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen W hWopen
  have hNfix : (IntermediateField.fixedField W).fixingSubgroup = W :=
    InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) ⟨W, hWclosed⟩
  have hKN : K ≤ IntermediateField.fixedField W :=
    (IntermediateField.le_iff_le W K).mpr (hWZ.trans (fun g hg => ((hZmem g).mp hg).1))
  have hNfd : FiniteDimensional k (IntermediateField.fixedField W) :=
    (InfiniteGalois.isOpen_iff_finite (k := k) (K := Ω) (IntermediateField.fixedField W)).mp
      (by rw [hNfix]; exact hWopen)
  have hNgal : IsGalois k (IntermediateField.fixedField W) :=
    (InfiniteGalois.normal_iff_isGalois (k := k) (K := Ω) (IntermediateField.fixedField W)).mp
      (by rw [hNfix]; exact hWnorm)
  refine ⟨IntermediateField.fixedField W, hKN, hNfd, hNgal, ?_, ?_⟩
  · intro g hg
    rw [hNfix] at hg
    exact ((hZmem g).mp (hWZ hg)).2
  · intro B _hB hKunram hcond
    rintro ⟨σ, hσI, hσN⟩
    apply hσN
    rw [hNfix]
    have hσK : σ ∈ K.fixingSubgroup :=
      mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn K B hKunram σ hσI
    rw [hWmem σ]
    intro g
    exact ⟨Subgroup.Normal.conj_mem hNormK σ hσK g,
      hcond g (g * σ * g⁻¹) (Subgroup.Normal.conj_mem hNormK σ hσK g)
        ((isInertia_conj B g σ).mpr hσI)⟩

end Work.SSGRoute.ZConstruction
