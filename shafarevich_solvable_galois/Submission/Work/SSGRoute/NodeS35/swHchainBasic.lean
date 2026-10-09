import Mathlib
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.NodeS35.swChainValueH9_modp
import Submission.Work.SSGRoute.NodeS35.histCount
import Submission.Work.SSGRoute.NodeS34.swHchain_of_frobValues
import Submission.Work.SSGRoute.H9.swHistChi_presc_proved
import Submission.Work.SSGRoute.H9.swZSixOfHistK
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.myv2.sup_isMulCommutative
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The §4(b) chain of the odd-`p` core, from a `HistK` history

This file assembles the `hchain` input of `Work.SSGRoute.H9.ZSix_of_histK` — the vanishing of
`χ_{b_i} + χ_{b_j}` on the local groups of the siblings of the last escape prime — from the pieces:

* `Work.SSGRoute.NodeS35.pinValue_pigeonhole` supplies the shoe-box pair `i < j` and the matching of
  the pinned Frobenius values;
* `Work.SSGRoute.NodeS35.swChainValueH9_modp` (the §4(b) chain value identity, with the escape
  normalisation in its `ZMod p` form) supplies the value at the sibling of `Q_j`;
* `Work.SSGRoute.NodeS34.swFrobLift` pins the Frobenius elements at the levels the chain consumes;
* `Work.SSGRoute.NodeS34.swHchain_of_frobValues_of_isFrobAtPrime` promotes the value identity to the
  whole local group and extends it to every `k`-conjugate that is not `K`-conjugate.
-/

namespace Work.SSGRoute.NodeS35

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

section Basic

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- `K`-conjugacy is `k`-conjugacy. -/
theorem isConjPlace_of_gesKConj {A B : ValuationSubring Ω}
    (h : Work.SSGRoute.gesKConj K A B) : SSGRoute.IsConjPlace k A B :=
  ⟨h.choose, h.choose_spec.2⟩

/-- **The killing of a product of two classes.** -/
theorem kills_mul (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    {b c : (↥K)ˣ} {A : ValuationSubring Ω}
    (hb : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    (hc : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ c u = 0) :
    ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (b * c) u = 0 := by
  intro u huK huI
  rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK b c]
  simp only [Pi.add_apply]
  rw [hb u huK huI, hc u huK huI, add_zero]

/-- **A pinned Frobenius at an arbitrary level.**  Bundles the membership of
`Work.SSGRoute.NodeS34.swFrobLift` into a subtype, at a finite Galois abelian level `M` in which the
prime of `↥K` below `A` is unramified. -/
theorem exists_pinned_at (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M]
    [Normal ↥K M] [NumberField ↥M]
    (hcomm : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)) :
    ∃ p' : {ψ : Ω ≃ₐ[k] Ω // ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup},
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M
        ((IntermediateField.fixingSubgroupEquiv K) ⟨p'.1, (Subgroup.mem_inf.mp p'.2).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  obtain ⟨ψ, hψ, hmem, hpin⟩ := Work.SSGRoute.NodeS34.swFrobLift (K := K) (Ω := Ω) M hcomm A hA _
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA) hunr
  exact ⟨⟨ψ, Subgroup.mem_inf.mpr ⟨hmem, hψ⟩⟩, hpin⟩

/-- **The commutativity of a three-fold sup of Kummer levels.** -/
theorem hLevel_sup3_comm (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (b₁ b₂ b₃ : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₃)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁
      ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₃)] :
    ∀ a b : ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₃) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₃),
      a * b = b * a := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI h1 : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₁
  haveI g1 : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₁
  haveI h2 : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₂) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₂
  haveI g2 : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₂) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₂
  haveI h3 : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₃) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₃
  haveI g3 : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b₃) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' b₃
  haveI c1 : IsMulCommutative (↥(hLevel (Ω := Ω) (K := K) (p := p) b₁) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁)) :=
    IsMulCommutative.of_comm (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p)
      ⟨ζ, hζK⟩ hζ' b₁)
  haveI c2 : IsMulCommutative (↥(hLevel (Ω := Ω) (K := K) (p := p) b₂) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b₂)) :=
    IsMulCommutative.of_comm (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p)
      ⟨ζ, hζK⟩ hζ' b₂)
  haveI c3 : IsMulCommutative (↥(hLevel (Ω := Ω) (K := K) (p := p) b₃) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b₃)) :=
    IsMulCommutative.of_comm (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p)
      ⟨ζ, hζK⟩ hζ' b₃)
  haveI c12 : IsMulCommutative (↥(hLevel (Ω := Ω) (K := K) (p := p) b₁
        ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) b₁ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂)) :=
    Work.SSGRoute.myv2.sup_isMulCommutative (K := K)
      (hLevel (Ω := Ω) (K := K) (p := p) b₁) (hLevel (Ω := Ω) (K := K) (p := p) b₂)
  have hcomm := Work.SSGRoute.myv2.sup_isMulCommutative (K := K)
    (hLevel (Ω := Ω) (K := K) (p := p) b₁ ⊔ hLevel (Ω := Ω) (K := K) (p := p) b₂)
    (hLevel (Ω := Ω) (K := K) (p := p) b₃)
  intro a b
  exact hcomm.is_comm.comm a b

end Basic

end Work.SSGRoute.NodeS35
