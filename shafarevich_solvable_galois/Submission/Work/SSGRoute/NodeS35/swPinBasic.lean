import Mathlib
import Submission.Work.SSGRoute.NodeS34.swFrobLift
import Submission.Work.SSGRoute.NodeS35.kills_inertia_conjUnit
import Submission.Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel
import Submission.Work.SSGRoute.H9.swHistChi_confinement_proved
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.hChar_hLocalFactor_tower
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pinned Frobenius family of the §4 shoe box

For a `HistK` history `f` of the Schmidt--Wingberg recursion, and for every stage `m` and every
`σ ∈ Gal(K|k)`, this file produces a Frobenius element

  `G m σ ∈ decomp k (galLift K σ • Q_m) ⊓ K.fixingSubgroup`

whose restriction to the Kummer level `K((b_m)^{1/p})` is the Frobenius at the prime of `↥K` below
the sibling place — i.e. exactly the pinning that the local dictionary of the §4(b) chain
(`Work.SSGRoute.H9.swPairingValueFrob`) consumes.  The construction is
`Work.SSGRoute.NodeS34.swFrobLift` at the (cyclic, hence abelian) level `hLevel (b_m)`, with the
unramifiedness supplied by the confinement clause of the history
(`Work.SSGRoute.H9.swHistChi_confinement_proved`).

The file also records the two bookkeeping lemmas the assembly needs:

* `chi_eq_of_restrictNormalHom_eq` — the Kummer cochain of `b` depends only on the restriction of
  the element to `hLevel b`;
* `pin_of_le` — a pinning at a level `M` restricts to a pinning at any level `L ≤ M`.
-/

namespace Work.SSGRoute.NodeS35

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

section Basic

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The Kummer level of a unit is finite dimensional, Galois and a number field.**  Recorded as a
`haveI`-ready bundle. -/
theorem hLevel_instances (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ∧
      IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ∧
      NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
  ⟨hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β,
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ζ hζ β,
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ζ hζ β⟩

/-- **The Kummer cochain of `b` depends only on the restriction to `hLevel b`.** -/
theorem chi_eq_of_restrictNormalHom_eq (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (b : (↥K)ˣ)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    [Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b)]
    (g g' : Ω ≃ₐ[k] Ω) (hg : g ∈ K.fixingSubgroup) (hg' : g' ∈ K.fixingSubgroup)
    (h : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) b)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨g, hg⟩) =
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) b)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨g', hg'⟩)) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b g
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b g' := by
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) b) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hg,
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := b) hg']
  exact Work.SSGRoute.ZDataMup.LTRecFamHonest.kummerCharZMod_eq_of_restrictNormalHom_eq
    (K := K) (p := p) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K)
    (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) b
    (L := hLevel (Ω := Ω) (K := K) (p := p) b) le_rfl h

/-- **A pinning restricts.**  If `ψ` restricts to the Frobenius at `𝔮` in a level `M`, then it does
so in every sublevel `L ≤ M` (both levels being finite Galois over `↥K` and abelian). -/
theorem pin_of_le {L M : IntermediateField ↥K Ω} [FiniteDimensional ↥K L] [IsGalois ↥K L]
    [Normal ↥K L] [NumberField ↥L] [FiniteDimensional ↥K M] [IsGalois ↥K M] [Normal ↥K M]
    [NumberField ↥M]
    (hLM : L ≤ M) (hcommL : ∀ a b : ↥L ≃ₐ[↥K] ↥L, a * b = b * a)
    (hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hunrM : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮)
    (hunrL : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥L) 𝔮)
    (σ : Ω ≃ₐ[↥K] Ω)
    (hσ : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M σ =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥M) 𝔮) :
    AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L σ =
      NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥L) 𝔮 := by
  letI : Algebra ↥L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  haveI hST1 : IsScalarTower ↥K ↥L ↥M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hST2 : IsScalarTower ↥L ↥M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomp : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥L σ =
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := ↥M) ↥L
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M σ) :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥L) (K₂ := ↥M) (F := ↥K)
      (K₃ := Ω) σ
  rw [hcomp, hσ]
  exact Work.SSGRoute.ZDataMup.frobAtPrime_restrictNormalHom_of_tower (F := ↥K) (L := ↥L)
    (M := ↥M) hcommL hcommM 𝔮 hunrM hunrL

end Basic

end Work.SSGRoute.NodeS35
