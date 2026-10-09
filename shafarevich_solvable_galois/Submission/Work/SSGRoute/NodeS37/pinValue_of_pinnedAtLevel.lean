import Mathlib
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.H9.swPromotionLevel
import Submission.Work.SSGRoute.H9.swPinnedFrob_sublevel
import Submission.Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

/-- **The Kummer value of a `Λ`-pinned Frobenius is `pinValue`.**  Let `Λ` be a finite Galois
`↥K`-level containing the Kummer level `K(b^{1/2})` of `b ∈ Kˣ`.  If the class kills the inertia at
the sibling place `siblingPlace K ρ Q` and `ψ` lies in the local group of that sibling with its image
in `Gal(Λ/↥K)` equal to the canonical Frobenius, then `χ_b(ψ) = pinValue (Q,b) ρ`.  This is
`H9.histChi_eq_pinValue_of_frobFamily` with the `HistK` invariant replaced by the single inertia
hypothesis `hkill` (which is all its proof uses, through `swPinnedFrob_sublevel`). -/
theorem pinValue_of_pinnedAtLevel {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (b : (↥K)ˣ) (Q : ValuationSubring Ω) (hQ : SSGRoute.IsFinPlace k Q)
    (ρ : K ≃ₐ[k] K) (hρ : ρ ≠ 1)
    (Λ : IntermediateField ↥K Ω) [FiniteDimensional ↥K Λ] [IsGalois ↥K Λ] [NumberField ↥Λ]
    (hle : Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b ≤ Λ)
    (hkill : ∀ u ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b u = 0)
    (ψ : Ω ≃ₐ[k] Ω)
    (hψ : ψ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) ⊓ K.fixingSubgroup)
    (hpin : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥Λ)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q)
        ((Work.SSGRoute.isFinPlace_smul_iff (k := k) Q
          (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hQ))
      (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) Λ
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩))) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b ψ
      = Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b))
          (fun _ => hQ) 0 ρ := by
  classical
  -- the primitive `2`-th root of unity inside `↥K`
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the Kummer level `K(b^{1/2})` is finite, Galois and a number field over `↥K`
  haveI hfd : FiniteDimensional ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' b
  haveI hgal : IsGalois ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' b
  haveI hnorm : Normal ↥K
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    hgal.to_normal
  haveI hnf : NumberField
      ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b) :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
      (⟨ζ, hζK⟩ : ↥K) hζ' b
  -- the presentation of the Kummer sub-level `K(b^{1/2})` inside `Λ`
  obtain ⟨M, e, he, hfdM, hnfM, hnormM⟩ :=
    Work.SSGRoute.H9.swSubfieldOf (p := 2) (K := K) (Ω := Ω) Λ b hle
  haveI := hfdM
  haveI := hnfM
  haveI := hnormM
  -- the sibling place and its finiteness
  have hA : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) :=
    (Work.SSGRoute.isFinPlace_smul_iff (k := k) Q
      (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hQ
  -- the inertia-killing makes the Kummer level unramified at the sibling
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) b))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) hA) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := 2) ζ hζ hζK b
      (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) hA hkill
  -- restrict the `Λ`-pinning to the Kummer level
  have hpinW := Work.SSGRoute.H9.swPinnedFrob_sublevel 2 k Ω K ζ hζ hζK Λ b M e he
    (Work.SSGRoute.ZDataMup.siblingPlace K ρ Q) hA hunr ψ hψ hpin
  -- read it as a `pinValue`
  exact Work.SSGRoute.NodeS35.pinValue_eq (K := K) (p := 2) ζ hζ hζK (fun _ => (Q, b))
    (fun _ => hQ) 0 ρ hρ ψ hψ hpinW

end Work.SSGRoute.NodeS37
