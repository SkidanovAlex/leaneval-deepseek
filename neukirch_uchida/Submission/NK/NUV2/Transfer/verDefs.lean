import Mathlib
import Submission.NK.NUV2.Transfer.exists_tauStarAction
import Submission.NK.Reconstruct.generalBaseChange
import Submission.NK.NUV2.Transfer.finiteVer
import Submission.NK.Reconstruct.generalBaseChange_galToGamma

/-!
# The transfer (Verlagerung) `Γ_M → Γ_L` and its norm formula

This file proves `NK.NUV2.Transfer.exists_ver_norm`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open NK.Reconstruct
open scoped commutatorElement

namespace NK.NUV2.Transfer

noncomputable section

/-! ## Group theoretic preliminaries on the transfer -/

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal]

/-- The conjugation formula for `MulAut.conjNormal`. -/
theorem conjNormal_apply' (h x : ↥H) :
    (↑(MulAut.conjNormal (H := H) (h : G)) : ↥H → ↥H) x = h * x * h⁻¹ := by
  ext : 1
  exact MulAut.conjNormal_apply (h : G) x

/-- Conjugation by an element of `H` is the identity on the abelianisation of `H`. -/
theorem abelianization_map_conjNormal_eq_id (h : ↥H) :
    Abelianization.map ((MulAut.conjNormal (H := H) (h : G)) : ↥H →* ↥H) = MonoidHom.id _ := by
  refine Abelianization.hom_ext _ _ (MonoidHom.ext fun x => ?_)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Abelianization.map_of, MonoidHom.id_apply]
  show (QuotientGroup.mk (((MulAut.conjNormal (H := H) (h : G)) : MulAut ↥H) x) : ↥H ⧸ commutator ↥H)
      = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  have hkey : (((MulAut.conjNormal (H := H) (h : G)) : MulAut ↥H) x)⁻¹ * x = ⁅h, x⁻¹⁆ := by
    ext : 1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    group
  rw [hkey]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) (Subgroup.mem_top x⁻¹)

theorem conjNormal_mul_eq' (a b : G) :
    (((MulAut.conjNormal (H := H) (a * b) : MulAut ↥H) : ↥H →* ↥H))
      = (((MulAut.conjNormal (H := H) a : MulAut ↥H) : ↥H →* ↥H)).comp
        (((MulAut.conjNormal (H := H) b : MulAut ↥H) : ↥H →* ↥H)) := by
  rw [map_mul]
  rfl

/-- **The conjugation action on `Ab(H)` depends only on the coset** of the conjugating element. -/
theorem abelianization_map_conjNormal_eq_of_mem {u u' : G} (hu : u'⁻¹ * u ∈ H) :
    (Abelianization.map ((MulAut.conjNormal (H := H) u : MulAut ↥H) : ↥H →* ↥H))
      = (Abelianization.map ((MulAut.conjNormal (H := H) u' : MulAut ↥H) : ↥H →* ↥H)) := by
  have hwu : u = u' * ((⟨u'⁻¹ * u, hu⟩ : ↥H) : G) := by
    rw [Subtype.coe_mk]
    group
  conv_lhs => rw [hwu]
  rw [conjNormal_mul_eq', ← Abelianization.map_comp,
    abelianization_map_conjNormal_eq_id ⟨u'⁻¹ * u, hu⟩, MonoidHom.comp_id]

/-! ## The auxiliary level -/

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
  (M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
  [NumberField ↥M.L] [NumberField ↥L.L] [FiniteDimensional ℚ ↥M.L] [FiniteDimensional ℚ ↥L.L]
  [Normal ℚ ↥L.L] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
  [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]

noncomputable def LV : IntermediateField ↥M.L Ω :=
  Subfield.toIntermediateField L.L.toSubfield (fun x : ↥M.L => hML x.2)

theorem algebraMap_LV_eq (x : ↥M.L) : algebraMap ↥M.L ↥(LV M L hML) x = ⟨(x : Ω), hML x.2⟩ := rfl

theorem algebraMap_LL_eq (x : ↥M.L) :
    (algebraMap ↥M.L ↥L.L x : Ω) = (x : Ω) :=
  (IsScalarTower.algebraMap_apply ↥M.L ↥L.L Ω x).symm

theorem algebraMap_LL_eq' (x : ↥M.L) :
    (algebraMap ↥M.L ↥L.L x) = (⟨(x : Ω), hML x.2⟩ : ↥L.L) := by
  apply Subtype.ext
  exact algebraMap_LL_eq M L x

theorem normal_LV : Normal ↥M.L (LV M L hML) := by
  refine (IntermediateField.normal_iff_forall_map_le' (F := ↥M.L) (L := Ω)).mpr ?_
  intro σ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map (S := LV M L hML)).mp hx
  have hnorm := (IntermediateField.normal_iff_forall_map_le' (F := ℚ) (L := Ω)).mp L.normal
    (σ.restrictScalars ℚ)
  exact hnorm ⟨y, hy, rfl⟩

noncomputable def overM (B : FrobLevel ↥L.L Ω) : IntermediateField ↥M.L Ω :=
  Subfield.toIntermediateField B.L.toSubfield
    (fun x : ↥M.L => by
      have h := B.L.algebraMap_mem' (⟨(x : Ω), hML x.2⟩ : ↥L.L)
      simpa using h)

instance overM_finite (B : FrobLevel ↥L.L Ω) : FiniteDimensional ↥M.L (overM M L hML B) :=
  inferInstanceAs (FiniteDimensional ↥M.L ↥B.L)

noncomputable def auxA (B : FrobLevel ↥L.L Ω) : FrobLevel ↥M.L Ω where
  L := IntermediateField.normalClosure ↥M.L (↥(overM M L hML B)) Ω
  finite := normalClosure.is_finiteDimensional ↥M.L ↥(overM M L hML B) Ω
  normal := normalClosure.normal ↥M.L ↥(overM M L hML B) Ω
  numberField := by
    haveI := normalClosure.is_finiteDimensional ↥M.L ↥(overM M L hML B) Ω
    exact NumberField.of_module_finite ↥M.L _

theorem le_auxA (B : FrobLevel ↥L.L Ω) : (B.L : Set Ω) ⊆ ((auxA M L hML B).L : Set Ω) :=
  fun x hx => IntermediateField.le_normalClosure _ (show x ∈ (overM M L hML B : Set Ω) from hx)

theorem auxA_mono {B B' : FrobLevel ↥L.L Ω} (h : B.L ≤ B'.L) :
    (auxA M L hML B).L ≤ (auxA M L hML B').L := by
  have hle : (overM M L hML B : IntermediateField ↥M.L Ω) ≤ overM M L hML B' := h
  refine (IntermediateField.normalClosure_le_iff_of_normal (F := ↥M.L) (L := Ω)
    (K₁ := overM M L hML B) (K₂ := (auxA M L hML B').L)).mpr ?_
  exact hle.trans (IntermediateField.le_normalClosure _)

theorem LV_le_auxA (B : FrobLevel ↥L.L Ω) : LV M L hML ≤ (auxA M L hML B).L :=
  fun x hx => le_auxA M L hML B (by
    have h := B.L.algebraMap_mem' (⟨x, hx⟩ : ↥L.L)
    simpa using h)

noncomputable def LA (B : FrobLevel ↥L.L Ω) : IntermediateField ↥M.L ↥(auxA M L hML B).L :=
  restrictLevelTo (LV M L hML) (auxA M L hML B).L (LV_le_auxA M L hML B)

example (B : FrobLevel ↥L.L Ω) : Algebra ↥(LA M L hML B) ↥(auxA M L hML B).L := inferInstance

/-- The identification of `L.L` inside the auxiliary level with `LV`. -/
noncomputable def LAEquiv (B : FrobLevel ↥L.L Ω) :
    ↥(LA M L hML B) ≃ₐ[↥M.L] ↥(LV M L hML) where
  toFun y := ⟨((y.1 : ↥(auxA M L hML B).L) : Ω), y.2⟩
  invFun x := ⟨⟨(x : Ω), LV_le_auxA M L hML B x.2⟩, x.2⟩
  left_inv y := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' y z := by ext; rfl
  map_add' y z := by ext; rfl
  commutes' c := by
    ext
    rw [algebraMap_LV_eq]
    rfl

/-- `L.L` inside the auxiliary level is normal over `M.L`. -/
instance normal_LA (B : FrobLevel ↥L.L Ω) : Normal ↥M.L (LA M L hML B) := by
  refine (IntermediateField.normal_iff_forall_fieldRange_le (F := ↥M.L)
    (K := LA M L hML B) (L := ↥(auxA M L hML B).L)).mpr ?_
  intro σ
  have hkey : ∀ x : ↥(LV M L hML),
      ((σ ((LAEquiv M L hML B).symm x) : ↥(auxA M L hML B).L) : Ω) ∈ LV M L hML := by
    intro x
    let τ : ↥(LV M L hML) →ₐ[↥M.L] Ω :=
      { toFun := fun x => ((σ ((LAEquiv M L hML B).symm x) : ↥(auxA M L hML B).L) : Ω)
        map_one' := by simp
        map_zero' := by simp
        map_mul' := by intro a b; simp [map_mul]
        map_add' := by intro a b; simp [map_add]
        commutes' := by
          intro c
          show ((σ ((LAEquiv M L hML B).symm (algebraMap ↥M.L ↥(LV M L hML) c))
            : ↥(auxA M L hML B).L) : Ω) = algebraMap ↥M.L Ω c
          have h1 : (LAEquiv M L hML B).symm (algebraMap ↥M.L ↥(LV M L hML) c)
              = algebraMap ↥M.L ↥(LA M L hML B) c := by
            apply (LAEquiv M L hML B).injective
            rw [AlgEquiv.apply_symm_apply]
            ext
            rw [algebraMap_LV_eq]
            rfl
          rw [h1, σ.commutes c]
          exact (IsScalarTower.algebraMap_apply ↥M.L ↥(auxA M L hML B).L Ω c).symm }
    exact ((IntermediateField.normal_iff_forall_fieldRange_le (F := ↥M.L) (L := Ω)).mp
      (normal_LV M L hML) τ) ⟨x, rfl⟩
  rintro y ⟨z, rfl⟩
  have hzz : (LAEquiv M L hML B).symm (LAEquiv M L hML B z) = z :=
    (LAEquiv M L hML B).symm_apply_apply z
  have := hkey (LAEquiv M L hML B z)
  rw [hzz] at this
  exact this


/-- `h : Gal(LV/M.L)` fixes (via its identification with `Gal(L.L/M.L)`) the image of the
algebra map. -/
theorem galLV_commutes (h : Gal(↥(LV M L hML)/↥M.L)) (c : ↥M.L) :
    h (algebraMap ↥M.L ↥L.L c) = algebraMap ↥M.L ↥L.L c := by
  have h1 := h.commutes' c
  rw [algebraMap_LV_eq] at h1
  rw [algebraMap_LL_eq']
  exact h1

theorem galLL_commutes (h : Gal(↥L.L/↥M.L)) (c : ↥M.L) :
    h (algebraMap ↥M.L ↥(LV M L hML) c) = algebraMap ↥M.L ↥(LV M L hML) c := by
  have h1 := h.commutes' c
  rw [algebraMap_LL_eq'] at h1
  rw [algebraMap_LV_eq]
  exact h1

/-- The "same function" identification of the automorphisms of `LV` with those of `L.L`
(both are the same subfield of `Ω`, with the same `M.L`-algebra structure). -/
noncomputable def galLVEquiv : (↥(LV M L hML) ≃ₐ[↥M.L] ↥(LV M L hML)) ≃* Gal(↥L.L/↥M.L) where
  toFun h := { toRingEquiv := h.toRingEquiv, commutes' := galLV_commutes M L hML h }
  invFun h := { toRingEquiv := h.toRingEquiv, commutes' := galLL_commutes M L hML h }
  left_inv h := by ext; rfl
  right_inv h := by ext; rfl
  map_mul' h k := by ext; rfl
/-- `L.L` inside `A` is stable under `Gal(A/M.L)`. -/
theorem LA_stable (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L)) :
    (LA M L hML B).map (σ : ↥(auxA M L hML B).L →ₐ[↥M.L] ↥(auxA M L hML B).L)
      ≤ LA M L hML B :=
  (IntermediateField.normal_iff_forall_map_le' (F := ↥M.L) (L := ↥(auxA M L hML B).L)).mp
    (normal_LA M L hML B) σ

/-- The restriction of an `M.L`-automorphism of `A.L` to `L.L` (inside `A`). -/
noncomputable def restrLA (B : FrobLevel ↥L.L Ω) :
    Gal(↥(auxA M L hML B).L/↥M.L) →* Gal(↥(LA M L hML B)/↥M.L) where
  toFun σ :=
    { toFun := fun y => ⟨σ y.1, LA_stable M L hML B σ (show σ y.1 ∈ (LA M L hML B).map
        (σ : ↥(auxA M L hML B).L →ₐ[↥M.L] ↥(auxA M L hML B).L) from ⟨y, y.2, rfl⟩)⟩
      invFun := fun y => ⟨σ.symm y.1, LA_stable M L hML B σ.symm (show σ.symm y.1 ∈
        (LA M L hML B).map (σ.symm : ↥(auxA M L hML B).L →ₐ[↥M.L] ↥(auxA M L hML B).L)
        from ⟨y, y.2, rfl⟩)⟩
      left_inv := fun y => Subtype.ext (σ.symm_apply_apply y.1)
      right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1)
      map_mul' := fun y z => Subtype.ext (map_mul σ y.1 z.1)
      map_add' := fun y z => Subtype.ext (map_add σ y.1 z.1)
      commutes' := fun c => Subtype.ext (σ.commutes c) }
  map_one' := by ext; rfl
  map_mul' := fun σ τ => by ext; rfl

@[simp] theorem restrLA_apply (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L))
    (y : ↥(LA M L hML B)) :
    ((restrLA M L hML B σ) y : ↥(auxA M L hML B).L) = σ y.1 := rfl

theorem mem_restrLA_ker_iff (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L)) :
    σ ∈ (restrLA M L hML B).ker ↔ ∀ y : ↥(LA M L hML B), σ y.1 = y.1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h y
    have h1 : ((restrLA M L hML B σ) y : ↥(auxA M L hML B).L) =
        ((1 : Gal(↥(LA M L hML B)/↥M.L)) y : ↥(auxA M L hML B).L) := by rw [h]
    simpa using h1
  · intro h
    refine AlgEquiv.ext (fun y => ?_)
    apply Subtype.ext
    simpa using h y

/-- Restricting an `M.L`-automorphism of the auxiliary level to `L.L`, then reading the result
as an automorphism of `L.L` (via the identification `LA ≃ LV ≃ L.L`). -/
noncomputable def resQ (B : FrobLevel ↥L.L Ω) :
    Gal(↥(auxA M L hML B).L/↥M.L) →* Gal(↥L.L/↥M.L) :=
  (galLVEquiv M L hML).toMonoidHom.comp
    ((algEquivConjHom (LAEquiv M L hML B)).comp (restrLA M L hML B))

/-- The subgroup of `Gal(A/M.L)` fixing `L.L` pointwise. -/
noncomputable def HA (B : FrobLevel ↥L.L Ω) : Subgroup Gal(↥(auxA M L hML B).L/↥M.L) :=
  (resQ M L hML B).ker

instance HA_normal (B : FrobLevel ↥L.L Ω) : (HA M L hML B).Normal := MonoidHom.normal_ker _

instance HA_finiteIndex (B : FrobLevel ↥L.L Ω) : (HA M L hML B).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient (H := HA M L hML B)

instance HA_fintypeQuotient (B : FrobLevel ↥L.L Ω) :
    Fintype (Gal(↥(auxA M L hML B).L/↥M.L) ⧸ (HA M L hML B)) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The transfer at the auxiliary level. -/
noncomputable def transferAb (B : FrobLevel ↥L.L Ω) :
    Abelianization Gal(↥(auxA M L hML B).L/↥M.L) →*
      Abelianization ↥(HA M L hML B) :=
  Abelianization.lift (MonoidHom.transfer (H := HA M L hML B)
    (Abelianization.of : ↥(HA M L hML B) →* Abelianization ↥(HA M L hML B)))

/-- The norm formula for the transfer. -/
theorem transferAb_norm (B : FrobLevel ↥L.L Ω) (x : Abelianization ↥(HA M L hML B)) :
    transferAb M L hML B (Abelianization.map (HA M L hML B).subtype x) =
      ∏ q : Gal(↥(auxA M L hML B).L/↥M.L) ⧸ (HA M L hML B),
        Abelianization.map
          ((MulAut.conjNormal (H := HA M L hML B) (Quotient.out q) : MulAut ↥(HA M L hML B))
            : ↥(HA M L hML B) →* ↥(HA M L hML B)) x :=
  (finiteVer (HA M L hML B)).2 x

/-- `L.L` is contained in the level `B`. -/
theorem LL_le_B (B : FrobLevel ↥L.L Ω) (c : ↥L.L) : (c : Ω) ∈ (B.L : Set Ω) := by
  have h := B.L.algebraMap_mem' c
  simpa using h

/-- The auxiliary level viewed over `L.L`. -/
noncomputable def auxAL (B : FrobLevel ↥L.L Ω) : FrobLevel ↥L.L Ω :=
  levelOverM (K := M) (M := NumFieldIn.ofIntermediateField L.L) hML (auxA M L hML B)
    (fun x hx => le_auxA M L hML B (LL_le_B (L := L) (B := B) ⟨x, hx⟩))

theorem le_auxAL (B : FrobLevel ↥L.L Ω) : B.L ≤ (auxAL M L hML B).L :=
  le_auxA M L hML B

/-- An `M.L`-automorphism of the auxiliary level fixing `L.L` pointwise is an `L.L`-automorphism. -/
noncomputable def convA (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L))
    (hσ : ∀ y : ↥(LA M L hML B), σ y.1 = y.1) : Gal(↥(auxAL M L hML B).L/↥L.L) where
  toFun := σ
  invFun := σ.symm
  left_inv := σ.left_inv
  right_inv := σ.right_inv
  map_mul' := σ.map_mul
  map_add' := σ.map_add
  commutes' := fun c => by
    have key : (algebraMap ↥L.L ↥(auxAL M L hML B).L c : ↥(auxA M L hML B).L) =
        ⟨(c : Ω), le_auxA M L hML B (LL_le_B (L := L) (B := B) c)⟩ := rfl
    have hmem : (⟨(c : Ω), le_auxA M L hML B (LL_le_B (L := L) (B := B) c)⟩ : ↥(auxA M L hML B).L)
        ∈ LA M L hML B := c.2
    have h := hσ ⟨⟨(c : Ω), le_auxA M L hML B (LL_le_B (L := L) (B := B) c)⟩, hmem⟩
    rw [show (algebraMap ↥L.L ↥(auxAL M L hML B).L c : ↥(auxA M L hML B).L) = _ from key]
    exact h

@[simp] theorem convA_apply (B : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML B).L/↥M.L))
    (hσ : ∀ y : ↥(LA M L hML B), σ y.1 = y.1) (x : ↥(auxAL M L hML B).L) :
    convA M L hML B σ hσ x = σ x := rfl

theorem HA_le_restrLA_ker (B : FrobLevel ↥L.L Ω) :
    HA M L hML B ≤ (restrLA M L hML B).ker := by
  intro σ hσ
  have h1 : galLVEquiv M L hML (algEquivConjHom (LAEquiv M L hML B) (restrLA M L hML B σ))
      = 1 := hσ
  have h2 : algEquivConjHom (LAEquiv M L hML B) (restrLA M L hML B σ) = 1 :=
    (galLVEquiv M L hML).injective h1
  have h3 : algEquivConjHom (LAEquiv M L hML B).symm
      (algEquivConjHom (LAEquiv M L hML B) (restrLA M L hML B σ)) = restrLA M L hML B σ := by
    ext x
    simp [algEquivConjHom, MulEquiv.trans_apply]
  rw [h2, map_one] at h3
  exact h3.symm

theorem mem_HA_fixes (B : FrobLevel ↥L.L Ω) (σ : ↥(HA M L hML B))
    (y : ↥(LA M L hML B)) : (σ : Gal(↥(auxA M L hML B).L/↥M.L)) y.1 = y.1 :=
  (mem_restrLA_ker_iff M L hML B _).mp (HA_le_restrLA_ker M L hML B σ.2) y

/-- The subgroup `H_A` as a group of `L.L`-automorphisms of the auxiliary level. -/
noncomputable def convH (B : FrobLevel ↥L.L Ω) :
    ↥(HA M L hML B) →* Gal(↥(auxAL M L hML B).L/↥L.L) where
  toFun σ := convA M L hML B σ.1 (mem_HA_fixes M L hML B σ)
  map_one' := by
    apply AlgEquiv.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    rfl

@[simp] theorem convH_apply (B : FrobLevel ↥L.L Ω) (σ : ↥(HA M L hML B))
    (x : ↥(auxA M L hML B).L) : convH M L hML B σ x = σ.1 x := rfl

/-- The restriction `Gal(A_L/L.L) →* Gal(B/L.L)`. -/
noncomputable def restrB (B : FrobLevel ↥L.L Ω) :
    Gal(↥(auxAL M L hML B).L/↥L.L) →* Gal(↥B.L/↥L.L) :=
  levelRestrictHom B (auxAL M L hML B) (le_auxAL M L hML B)

/-- The transfer, pushed to the level `B`. -/
noncomputable def transferEll (B : FrobLevel ↥L.L Ω) :
    LevelEllPart (auxA M L hML B).L 2 →* LevelEllPart B.L 2 where
  toFun x := ellComp 2 ((Abelianization.map (restrB M L hML B)).comp
    ((Abelianization.map (convH M L hML B)).comp
      (transferAb M L hML B)) ((x : LevelEllPart (auxA M L hML B).L 2) :
        Abelianization Gal(↥(auxA M L hML B).L/↥M.L)))
  map_one' := by
    have h1 : ((1 : ↥(LevelEllPart (auxA M L hML B).L 2)) :
        Abelianization Gal(↥(auxA M L hML B).L/↥M.L)) = 1 := rfl
    rw [h1]
    simp only [map_one]
    exact ellComp_one 2
  map_mul' x y := by
    have h1 : (((x * y : ↥(LevelEllPart (auxA M L hML B).L 2))) :
        Abelianization Gal(↥(auxA M L hML B).L/↥M.L))
        = ((x : LevelEllPart (auxA M L hML B).L 2) :
            Abelianization Gal(↥(auxA M L hML B).L/↥M.L))
          * ((y : LevelEllPart (auxA M L hML B).L 2) :
            Abelianization Gal(↥(auxA M L hML B).L/↥M.L)) := rfl
    rw [h1]
    simp only [map_mul]
    exact ellComp_mul 2 _ _


end

end NK.NUV2.Transfer
