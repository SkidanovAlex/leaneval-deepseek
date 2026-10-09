import Mathlib
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.grunwald_setup
import Submission.Work.SSGRoute.grunwald_kummer_idx
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` Kummer cochain for a general prime `p`: local dictionary and continuity

`Work.SSGRoute.ZSplit.nodeKummerCocharZMod` is the cocycle of `H¹(k_S|K, μ_p) ≅ Kˣ/(Kˣ)^p`
attached to `β ∈ Kˣ` (for `ζ_p ∈ K`), the general-`p` companion of the `p = 2` cochain
`Work.SSGRoute.nodeKummerCochar` of Schmidt--Wingberg's `p = 2` lane.

Here we prove the two structural facts which make it a *class* in the sense of
`Submission/Work/SSGRoute/Interfaces.lean` and which pin down its local behaviour:

* `nodeKummerCocharZMod_locConst` — it is locally constant on `G_K` (it factors through the finite
  Galois group of the Kummer field `K⟮√[p]β⟯`, whose fixing subgroup is open);
* `nodeKummerCocharZMod_eq_zero_iff_localPowClass` — **the local Kummer dictionary at the node's
  vocabulary**: the cochain vanishes on the level-`K` local group `decomp k A ⊓ K.fixingSubgroup`
  if and only if `β` is a local `p`-th power at the prime of `K` below `A`.  This is
  `Work.SSGRoute.local_kummer_dictionary` transported along the decomposition-group isomorphism
  `grunwaldSetupDecompEquiv`.

Together with `nodeKummerCocharZMod_add` (`FrobeniusValue.lean`) these are exactly the structural
facts which the Kummer-theoretic form of Schmidt--Wingberg's §4 construction needs: the
correspondence "class on `G_K` ↔ element of `Kˣ` modulo `p`-th powers", with "unramified at `A`"
meaning "local `p`-th power at the prime below `A`".
-/

open scoped Pointwise

namespace Work.SSGRoute.ZSplit

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime]
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

section LocConst

variable [IsAlgClosed Ω]

/-- **The level-`K` Kummer cochain is locally constant.**  The cochain factors through the finite
Galois group `Gal(K⟮√[p]β⟯/K)` of the Kummer field of `β`, whose fixing subgroup is open in
`G_k`; elements of `G_K` fixing the chosen `p`-th root have Kummer index `0`. -/
theorem nodeKummerCocharZMod_locConst (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    SSGRoute.IsLocConstOn K.fixingSubgroup (nodeKummerCocharZMod K ζ hζK hζ β) := by
  haveI hfdL : FiniteDimensional k
      ↥(IntermediateField.adjoin k {Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β}) :=
    IntermediateField.adjoin.finiteDimensional (K := k)
      (x := Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β)
      ((Algebra.IsAlgebraic.isIntegral (K := k) (A := Ω)).isIntegral _)
  refine ⟨K.fixingSubgroup ⊓ (IntermediateField.adjoin k
      {Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β}).fixingSubgroup, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen K).inter
      (IntermediateField.fixingSubgroup_isOpen _)
  · intro gg hg u hu huH
    obtain ⟨huK, huL⟩ := Subgroup.mem_inf.mp hu
    have hgu : gg * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huK
    rw [nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hgu,
      nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hg]
    have key : (⟨gg * u, hgu⟩ : ↥(K.fixingSubgroup)) = ⟨gg, hg⟩ * ⟨u, huK⟩ := Subtype.ext rfl
    rw [key, map_mul (IntermediateField.fixingSubgroupEquiv K)]
    show kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
        (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨gg, hg⟩ *
          (IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩) =
      kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
        (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨gg, hg⟩)
    rw [kummerCharZMod_apply, kummerCharZMod_apply]
    rw [kummerIdx_mul_apply]
    have hfix : ((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω)
          ((Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p β : Ωˣ) : Ω) =
        ((Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p β : Ωˣ) : Ω) := by
      have hmem : Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β ∈ (IntermediateField.adjoin k
          {Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β} : IntermediateField k Ω) :=
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      have hfixu : (u : Ω ≃ₐ[k] Ω) (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β) =
          Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp huL _ hmem
      have hcoe : ⇑((IntermediateField.fixingSubgroupEquiv K) ⟨u, huK⟩ : Ω ≃ₐ[↥K] Ω) =
          ⇑(u : Ω ≃ₐ[k] Ω) := by ext x; rfl
      rw [show ((Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p β : Ωˣ) : Ω) =
        Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β from rfl]
      exact (congrFun hcoe (Work.SSGRoute.kummerSqrtZMod (Ω := Ω) p β)).trans hfixu
    rw [kummerIdx_eq_zero_of_apply_eq p (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
      (Work.SSGRoute.kummerSqrtUnitZMod (Ω := Ω) p β)
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p β) _ hfix, add_zero]

end LocConst

/-- **The local Kummer dictionary at the node's vocabulary.**  For a finite place `A` of `Ω` over
the prime `𝔭` of `K`, the level-`K` Kummer cochain of `β` vanishes on the local group
`decomp k A ⊓ K.fixingSubgroup` if and only if `β` is a local `p`-th power at `𝔭`. -/
theorem nodeKummerCocharZMod_eq_zero_iff_localPowClass [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    ((∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        nodeKummerCocharZMod K ζ hζK hζ β σ = 0) ↔
      NK.UchidaKummer.localPowClass ↥K p 𝔭 β = 1) := by
  have hdict := Work.SSGRoute.local_kummer_dictionary p K (⟨ζ, hζK⟩ : ↥K)
    (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA 𝔭 h𝔭 β
  constructor
  · intro h
    rw [← hdict]
    intro τ hτ
    set x : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      (grunwaldSetupDecompEquiv k Ω K A).symm ⟨τ, hτ⟩ with hx
    have hxK : (x : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp x.2).2
    have h1 : kummerCharZMod (Ω := Ω) p (ζ := (⟨ζ, hζK⟩ : ↥K))
        (isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), hxK⟩) = 0 := by
      have h0 := h (x : Ω ≃ₐ[k] Ω) x.2
      rwa [nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β)
        hxK] at h0
    have h3 : ((IntermediateField.fixingSubgroupEquiv K)
          ⟨(x : Ω ≃ₐ[k] Ω), hxK⟩ : Ω ≃ₐ[↥K] Ω) = τ := by
      have h4 := (grunwaldSetupDecompEquiv k Ω K A).apply_symm_apply ⟨τ, hτ⟩
      exact congrArg Subtype.val h4
    rwa [h3] at h1
  · intro h σ hσ
    rw [nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β)
      (Subgroup.mem_inf.mp hσ).2]
    exact (hdict.mpr h) _ (grunwaldSetupDecompEquiv k Ω K A ⟨σ, hσ⟩).2

end Work.SSGRoute.ZSplit
