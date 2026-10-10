import Mathlib.FieldTheory.Normal.Basic
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of a subfield `L ≤ M` of `Ω` to an intermediate field of `↥M`

`hLocalFactor_tower` (`NOTES_LTRecFam_session5.md` §3, obligation **(P4)**) is a corollary of
`Work.SSGRoute.ZDataMup.ArtinUniqueness.artinMap_restrictNormalHom_eq_abelian`, which is stated for
two *number fields* `K, M` and an `IntermediateField K M`.  Since our `L, M` are both intermediate
fields of `Ω`, the subfield `L` has to be transported:

* `hRestrict L M hLM : IntermediateField ↥K ↥M` -- the image of `L` in `M`
  (`IntermediateField.comap` along the inclusion `↥M →ₐ[↥K] Ω`), whose underlying set is
  `{x : ↥M | (x : Ω) ∈ L}`;
* `hRestrictEquiv L M hLM : ↥(hRestrict L M hLM) ≃ₐ[↥K] ↥L` -- the canonical `↥K`-algebra
  equivalence (the coercion, which is injective by construction and surjective by `hLM`);
* `hRestrictEquiv_toMonoidHom` -- the induced isomorphism of Galois groups, used to transport the
  Artin map of `L` to the Artin map of `hRestrict L M hLM`.
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open _root_.SSGRoute
open Classical

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- **The image of the subfield `L ≤ M` inside `M`**, as an intermediate field of `↥M/↥K`. -/
noncomputable def hRestrict (L M : IntermediateField K Ω) (hLM : L ≤ M) :
    IntermediateField K ↥M :=
  L.comap (IsScalarTower.toAlgHom K ↥M Ω)

theorem hRestrict_mem {L M : IntermediateField K Ω} (hLM : L ≤ M) (x : ↥M) :
    x ∈ hRestrict (K := K) L M hLM ↔ (x : Ω) ∈ L := Iff.rfl

/-- **The canonical `↥K`-algebra equivalence between the transported field and `↥L`.** -/
noncomputable def hRestrictEquiv (L M : IntermediateField K Ω) (hLM : L ≤ M) :
    ↥(hRestrict (K := K) L M hLM) ≃ₐ[K] ↥L :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨(x.1 : Ω), (hRestrict_mem (K := K) hLM x.1).mp x.2⟩
      map_one' := by
        refine Subtype.ext ?_
        rfl
      map_mul' := fun x y => by
        refine Subtype.ext ?_
        rfl
      map_zero' := by
        refine Subtype.ext ?_
        rfl
      map_add' := fun x y => by
        refine Subtype.ext ?_
        rfl
      commutes' := fun c => by
        refine Subtype.ext ?_
        rfl }
    ⟨fun x y h => by
      refine Subtype.ext ?_
      have h' : ((⟨(x.1 : Ω), _⟩ : ↥L) : Ω) = ((⟨(y.1 : Ω), _⟩ : ↥L) : Ω) :=
        congrArg (fun z : ↥L => (z : Ω)) h
      exact Subtype.ext h',
      fun y => by
        refine ⟨⟨⟨(y : Ω), hLM y.2⟩, (hRestrict_mem (K := K) hLM ⟨(y : Ω), hLM y.2⟩).mpr y.2⟩, ?_⟩
        refine Subtype.ext ?_
        rfl⟩

@[simp]
theorem hRestrictEquiv_apply {L M : IntermediateField K Ω} (hLM : L ≤ M)
    (x : ↥(hRestrict (K := K) L M hLM)) :
    ((hRestrictEquiv (K := K) L M hLM x : ↥L) : Ω) = (x.1 : Ω) := rfl

/-- **The conjugation homomorphism of Galois groups** induced by `hRestrictEquiv`: it lets one
transport the idèlic Artin map of `↥L/↥K` to a map into `Gal(↥(hRestrict L M hLM)/↥K)`, which is
what `artinMap_restrictNormalHom_eq_abelian` consumes. -/
noncomputable def hRestrictGalHom (L M : IntermediateField K Ω) (hLM : L ≤ M) :
    (↥L ≃ₐ[K] ↥L) →* (↥(hRestrict (K := K) L M hLM) ≃ₐ[K] ↥(hRestrict (K := K) L M hLM)) :=
  MonoidHom.mk' (fun σ => (hRestrictEquiv (K := K) L M hLM).trans
      (σ.trans (hRestrictEquiv (K := K) L M hLM).symm))
    (by
      intro σ τ
      ext x
      refine congrArg Subtype.val ?_
      simp only [AlgEquiv.mul_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply])

/-- **Two `K`-automorphisms of `Ω` which agree on `M` agree on any normal subfield `L ≤ M`.** -/
theorem restrictNormal_eq_of_agree_of_le {L M : IntermediateField K Ω}
    [Normal K L] [Normal K M] (hLM : L ≤ M) {σ τ : Ω ≃ₐ[K] Ω}
    (h : σ.restrictNormal M = τ.restrictNormal M) :
    σ.restrictNormal L = τ.restrictNormal L := by
  have hfixM : (σ⁻¹ * τ).restrictNormal M = 1 := by
    have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (σ⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv,
        show (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) σ = σ.restrictNormal M from rfl,
        show (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) τ = τ.restrictNormal M from rfl, h,
        inv_mul_cancel]
    exact h2
  have hfixMpoint : ∀ y ∈ M, (σ⁻¹ * τ) y = y :=
    (AlgEquiv.restrictNormal_eq_one_iff M (σ⁻¹ * τ)).mp hfixM
  have hfixL : (σ⁻¹ * τ).restrictNormal L = 1 := by
    rw [AlgEquiv.restrictNormal_eq_one_iff]
    intro x hx
    exact hfixMpoint x (hLM hx)
  have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) (σ⁻¹ * τ) = 1 := hfixL
  rw [map_mul, map_inv] at h2
  exact inv_mul_eq_one.mp h2

/-- **(P4-a) the restriction homomorphism `Gal(↥M/K) →* Gal(↥L/K)`**, defined through `Ω` by lifting
an automorphism of `↥M` to `Ω` (`AlgEquiv.liftNormal`) and restricting to the normal subfield
`L ⊆ M`.  The choice of lift is immaterial: two lifts of the same automorphism agree on `M ⊇ L`
(`restrictNormal_eq_of_agree_of_le`). -/
noncomputable def restrictMol (L M : IntermediateField K Ω) [Normal K L] [Normal K M]
    [Normal K Ω] (hLM : L ≤ M) :
    (↥M ≃ₐ[K] ↥M) →* (↥L ≃ₐ[K] ↥L) :=
  MonoidHom.mk' (fun σ => (σ.liftNormal Ω).restrictNormal L)
    (by
      intro σ τ
      have h1 : ((σ * τ).liftNormal Ω).restrictNormal M =
          ((σ.liftNormal Ω) * (τ.liftNormal Ω)).restrictNormal M := by
        have h3 : ((σ * τ).liftNormal Ω).restrictNormal M = σ * τ :=
          AlgEquiv.restrict_liftNormal (F := K) (E := Ω) (σ * τ)
        have h4 : ((σ.liftNormal Ω) * (τ.liftNormal Ω)).restrictNormal M = σ * τ := by
          show (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M)
            ((σ.liftNormal Ω) * (τ.liftNormal Ω)) = σ * τ
          rw [map_mul,
            show (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (σ.liftNormal Ω)
              = (σ.liftNormal Ω).restrictNormal M from rfl,
            show (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (τ.liftNormal Ω)
              = (τ.liftNormal Ω).restrictNormal M from rfl,
            AlgEquiv.restrict_liftNormal (F := K) (E := Ω) σ,
            AlgEquiv.restrict_liftNormal (F := K) (E := Ω) τ]
        exact h3.trans h4.symm
      have h2 := restrictNormal_eq_of_agree_of_le (L := L) (M := M) hLM h1
      rw [h2]
      exact map_mul (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) (σ.liftNormal Ω)
        (τ.liftNormal Ω))

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
