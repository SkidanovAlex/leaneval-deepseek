import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup
import Submission.Work.SSGRoute.P2Close.preTwo_agreement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.P2Close

theorem claimOfPinnedZero {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (Q : ValuationSubring Ω) (hQ : SSGRoute.IsFinPlace k Q)
    (hQsplit : SSGRoute.IsSplitIn k K Q)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (¬ Work.SSGRoute.gesKConj K Q B) →
      ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k B u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    (hpin : ∀ ρ : K ≃ₐ[k] K, ρ ≠ 1 → ρ ^ 2 = 1 →
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b))
        (fun _ => hQ) 0 ρ = 0) :
    ∀ σ : Ω ≃ₐ[k] Ω, σ ∉ K.fixingSubgroup → (SSGRoute.res k K σ) ^ 2 = 1 →
      ∀ u ∈ SSGRoute.decomp k (σ • Q) ⊓ K.fixingSubgroup,
        Work.SSGRoute.nodeKummerCochar K ζ hζK hζ b u = 0 := by
  classical
  intro σ hσK hσ2 u hu
  -- ## the image `t = res k K σ` of `σ` in `Gal(K|k)` is an involution `≠ 1`
  set t : K ≃ₐ[k] K := SSGRoute.res k K σ with ht
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : σ ∈ (SSGRoute.res k K).ker := by
      rw [MonoidHom.mem_ker, ← ht]
      exact h1
    exact hσK (by rwa [IntermediateField.restrictNormalHom_ker K] at hmem)
  have ht2 : t ^ 2 = 1 := by rw [ht]; exact hσ2
  -- ## the sibling place `galLift K t • Q` of `Q` at the index `t`
  have hAfin : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K t Q) :=
    (SSGRoute.isFinPlace_smul_iff Q (Work.SSGRoute.ZDataMup.galLift K t)).mpr hQ
  have hQA : ¬ Work.SSGRoute.gesKConj K Q (Work.SSGRoute.ZDataMup.siblingPlace K t Q) :=
    Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K ht1 hQsplit
  have hkillA : ∀ τ ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K t Q) τ →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0 :=
    fun τ hτK hτI => hconf _ hAfin hQA τ hτK hτI
  -- ## the Kummer level of `b` is finite, Galois and a number field
  haveI : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  haveI : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  haveI : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  -- ## a pinned Frobenius at the sibling place, whose Kummer value is `pinValue 0 t = 0`
  obtain ⟨⟨ψ, hψ⟩, hψpin⟩ := Work.SSGRoute.NodeS35.exists_pinned (K := K) (p := 2) ζ hζ hζK
    (fun _ => (Q, b)) 0 (Work.SSGRoute.ZDataMup.siblingPlace K t Q) hAfin hkillA
  have hpinv : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b))
          (fun _ => hQ) 0 t :=
    Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b))
      (fun _ => hQ) 0 t ht1 ψ hψ hψpin
  have h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b ψ = 0 := by
    rw [hpinv]
    exact hpin t ht1 ht2
  -- ## the whole local group at the sibling place vanishes (`pinnedZeroImpLocalGroup`)
  have hmain := Work.SSGRoute.NodeS37.pinnedZeroImpLocalGroup (K := K) ζ hζ hζK b
    (Work.SSGRoute.ZDataMup.siblingPlace K t Q) hAfin hkillA ψ hψ hψpin h0
  -- ## `σ • Q` is a `K`-conjugate of the sibling place
  have hAtt : Work.SSGRoute.gesKConj K (σ • Q) (Work.SSGRoute.ZDataMup.siblingPlace K t Q) := by
    refine ⟨Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹, ?_, ?_⟩
    · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_inv,
        Work.SSGRoute.ZDataMup.galLift_spec, ht, mul_inv_cancel]
    · show (Work.SSGRoute.ZDataMup.galLift K t * σ⁻¹) • (σ • Q)
        = Work.SSGRoute.ZDataMup.siblingPlace K t Q
      rw [mul_smul, inv_smul_smul, Work.SSGRoute.ZDataMup.siblingPlace]
  -- ## transport the vanishing from the sibling place to `σ • Q`
  obtain ⟨w, hwK, hwA⟩ := hAtt
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k (σ • Q) := (Subgroup.mem_inf.mp hu).1
  have hu'K : w * u * w⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hwK huK) (K.fixingSubgroup.inv_mem hwK)
  have hu'D : w * u * w⁻¹ ∈ SSGRoute.decomp k
      (Work.SSGRoute.ZDataMup.siblingPlace K t Q) := by
    show (w * u * w⁻¹) • (Work.SSGRoute.ZDataMup.siblingPlace K t Q)
      = Work.SSGRoute.ZDataMup.siblingPlace K t Q
    rw [mul_smul, mul_smul,
      show w⁻¹ • (Work.SSGRoute.ZDataMup.siblingPlace K t Q) = σ • Q from by
        rw [← hwA, inv_smul_smul],
      show u • (σ • Q) = σ • Q from MulAction.mem_stabilizer_iff.mp huD,
      ← hwA]
  have hval : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b (w * u * w⁻¹)
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u :=
    Work.SSGRoute.ZDataMup.nodeKummerCocharZMod_conj K ζ hζ hζK b hwK u
  have hfinal : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0 := by
    rw [← hval]
    exact hmain _ (Subgroup.mem_inf.mpr ⟨hu'D, hu'K⟩)
  rw [← nodeKummerCocharZMod_eq_nodeKummerCochar_apply (K := K) (ζ := ζ) (hζK := hζK)
    (hζ := hζ) (b := b) huK]
  exact hfinal

end Work.SSGRoute.P2Close
