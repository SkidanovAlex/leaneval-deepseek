import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.exists_autLTLevel_mulEquiv_apply_smulDiv
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open scoped ValuativeRel

/-! ### The canonical Lubin–Tate symbol at level `n`

Auxiliary construction: the "unit part" of a unit of `F`, i.e. the composite

`Fˣ →* Fˣ ⧸ ⟨π⟩ ≃* 𝒪[F]ˣ`,

which is a splitting of `𝒪[F]ˣ ↪ Fˣ` and has kernel `⟨π⟩`.
-/

section Aux

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- An irreducible element of the ring of integers of a nonarchimedean local field is a
uniformiser of the field. -/
theorem isUniformizer_of_irreducible (P : ↥(ValuativeRel.valuation F).integer)
    (hP : Irreducible P) :
    NK.LocalReciprocityLubinTate.IsUniformizer F (P : F) := by
  have hspan : IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer
      = Ideal.span {P} := Irreducible.maximalIdeal_eq hP
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span (ValuativeRel.valuation F) hspan

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The inclusion `𝒪[F]ˣ ↪ Fˣ` is injective. -/
theorem unitsIncl_injective :
    Function.Injective (NK.LocalReciprocityLubinTate.Units.unitsIncl F) :=
  Units.map_injective (f := (Subring.subtype (ValuativeRel.valuation F).integer).toMonoidHom)
    (fun _ _ h => Subtype.ext h)

/-- The reduction of units of `𝒪[F]` modulo `𝔪[F]` composed with the quotient map onto
`Fˣ ⧸ ⟨π⟩`. -/
noncomputable def unitPartMap (πu : Fˣ) :
    (↥(ValuativeRel.valuation F).integer)ˣ →* Fˣ ⧸ Subgroup.zpowers πu :=
  (QuotientGroup.mk' (Subgroup.zpowers πu)).comp
    (NK.LocalReciprocityLubinTate.Units.unitsIncl F)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem unitPartMap_apply (πu : Fˣ) (a : (↥(ValuativeRel.valuation F).integer)ˣ) :
    unitPartMap (F := F) πu a
      = QuotientGroup.mk' (Subgroup.zpowers πu)
          (NK.LocalReciprocityLubinTate.Units.unitsIncl F a) := rfl

/-- `unitPartMap` is a bijection: `⟨π⟩` is a complement of `𝒪[F]ˣ` in `Fˣ`. -/
theorem unitPartMap_bijective (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    Function.Bijective (unitPartMap (F := F) πu) := by
  constructor
  · intro a b hab
    have h1 : (NK.LocalReciprocityLubinTate.Units.unitsIncl F a)⁻¹
        * (NK.LocalReciprocityLubinTate.Units.unitsIncl F b)
        ∈ Subgroup.zpowers πu := by
      rw [← QuotientGroup.ker_mk' (Subgroup.zpowers πu), MonoidHom.mem_ker]
      have hab' : (QuotientGroup.mk' (Subgroup.zpowers πu))
            (NK.LocalReciprocityLubinTate.Units.unitsIncl F a)
          = (QuotientGroup.mk' (Subgroup.zpowers πu))
            (NK.LocalReciprocityLubinTate.Units.unitsIncl F b) := hab
      rw [map_mul, map_inv, hab', inv_mul_cancel]
    have hmem : NK.LocalReciprocityLubinTate.Units.unitsIncl F (a⁻¹ * b)
        ∈ Subgroup.zpowers πu := by
      simpa only [map_mul, map_inv] using h1
    have h2 : NK.LocalReciprocityLubinTate.Units.unitsIncl F (a⁻¹ * b) = 1 := by
      have h3 : NK.LocalReciprocityLubinTate.Units.unitsIncl F (a⁻¹ * b)
          ∈ Subgroup.zpowers πu ⊓ (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range :=
        ⟨hmem, ⟨a⁻¹ * b, rfl⟩⟩
      rw [NK.LocalReciprocityLubinTate.Units.inf_zpowers_range F πu hπ,
        Subgroup.mem_bot] at h3
      exact h3
    exact inv_mul_eq_one.mp (unitsIncl_injective (h2.trans (map_one _).symm))
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    have hx : x ∈ Subgroup.zpowers πu
        ⊔ (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range := by
      rw [NK.LocalReciprocityLubinTate.Units.sup_zpowers_range F πu hπ]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hb
    refine ⟨u, ?_⟩
    show (QuotientGroup.mk' (Subgroup.zpowers πu))
          (NK.LocalReciprocityLubinTate.Units.unitsIncl F u)
        = (QuotientGroup.mk' (Subgroup.zpowers πu)) x
    have ha1 : (QuotientGroup.mk' (Subgroup.zpowers πu)) a = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk' (Subgroup.zpowers πu)]
      exact ha
    rw [← hab, map_mul, ha1]
    exact (one_mul (QuotientGroup.mk' (Subgroup.zpowers πu)
      (NK.LocalReciprocityLubinTate.Units.unitsIncl F u))).symm

/-- The inverse of `unitPartMap`: the isomorphism `Fˣ ⧸ ⟨π⟩ ≃* 𝒪[F]ˣ`. -/
noncomputable def unitPartEquiv (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    (↥(ValuativeRel.valuation F).integer)ˣ ≃* Fˣ ⧸ Subgroup.zpowers πu :=
  MulEquiv.ofBijective (unitPartMap (F := F) πu) (unitPartMap_bijective (F := F) πu hπ)

/-- **The unit part of a unit of `F`**: the composite `Fˣ →* Fˣ ⧸ ⟨π⟩ ≃* 𝒪[F]ˣ`, a splitting of
`𝒪[F]ˣ ↪ Fˣ` with kernel `⟨π⟩`. -/
noncomputable def unitPartHom (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    Fˣ →* (↥(ValuativeRel.valuation F).integer)ˣ :=
  (unitPartEquiv (F := F) πu hπ).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.zpowers πu))

theorem unitPartEquiv_apply (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F))
    (a : (↥(ValuativeRel.valuation F).integer)ˣ) :
    unitPartEquiv (F := F) πu hπ a
      = QuotientGroup.mk' (Subgroup.zpowers πu)
          (NK.LocalReciprocityLubinTate.Units.unitsIncl F a) :=
  MulEquiv.ofBijective_apply _ _ _

theorem unitPartHom_apply (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (x : Fˣ) :
    unitPartHom (F := F) πu hπ x
      = (unitPartEquiv (F := F) πu hπ).symm
          (QuotientGroup.mk' (Subgroup.zpowers πu) x) := rfl

theorem unitPartHom_unitsIncl (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F))
    (a : (↥(ValuativeRel.valuation F).integer)ˣ) :
    unitPartHom (F := F) πu hπ (NK.LocalReciprocityLubinTate.Units.unitsIncl F a) = a := by
  rw [unitPartHom_apply, ← unitPartEquiv_apply (F := F) πu hπ a, MulEquiv.symm_apply_apply]

theorem unitPartHom_ker (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    (unitPartHom (F := F) πu hπ).ker = Subgroup.zpowers πu := by
  ext x
  rw [MonoidHom.mem_ker, unitPartHom_apply, MulEquiv.map_eq_one_iff]
  conv_rhs => rw [← QuotientGroup.ker_mk' (Subgroup.zpowers πu)]
  rw [MonoidHom.mem_ker]

theorem unitPartHom_surjective (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    Function.Surjective (unitPartHom (F := F) πu hπ) :=
  fun a => ⟨NK.LocalReciprocityLubinTate.Units.unitsIncl F a,
    unitPartHom_unitsIncl (F := F) πu hπ a⟩

/-- The unit part of `x` differs from `x` by an element of `⟨π⟩`. -/
theorem unitPartHom_spec (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (x : Fˣ) :
    (NK.LocalReciprocityLubinTate.Units.unitsIncl F (unitPartHom (F := F) πu hπ x))⁻¹ * x
      ∈ Subgroup.zpowers πu := by
  have hq : (QuotientGroup.mk' (Subgroup.zpowers πu))
        (NK.LocalReciprocityLubinTate.Units.unitsIncl F (unitPartHom (F := F) πu hπ x))
      = (QuotientGroup.mk' (Subgroup.zpowers πu)) x := by
    rw [← unitPartEquiv_apply (F := F) πu hπ (unitPartHom (F := F) πu hπ x),
      unitPartHom_apply, MulEquiv.apply_symm_apply]
  have hmem : (QuotientGroup.mk' (Subgroup.zpowers πu))
      ((NK.LocalReciprocityLubinTate.Units.unitsIncl F
        (unitPartHom (F := F) πu hπ x))⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hq, inv_mul_cancel]
  rw [← QuotientGroup.ker_mk' (Subgroup.zpowers πu), MonoidHom.mem_ker]
  exact hmem

/-- The reduction `𝒪[F]ˣ →* (𝒪[F] ⧸ 𝔪[F]^n)ˣ` is surjective. -/
theorem surjective_units_map_quot_maximalIdeal_pow (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (Units.map (Ideal.Quotient.mk
      (NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n)).toMonoidHom) := by
  set O := ↥(ValuativeRel.valuation F).integer
  set I : Ideal O := NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n
  have hIle : I ≤ IsLocalRing.maximalIdeal O := by
    rw [show I = NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n from rfl]
    exact (Ideal.pow_le_self (by omega : n ≠ 0)).trans le_rfl
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (⊤ : Ideal O) ≤ IsLocalRing.maximalIdeal O := h ▸ hIle
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.mp h1)
  haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  exact IsLocalRing.surjective_units_map_of_local_ringHom (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)

end Aux

/-! ### The canonical Lubin–Tate symbol at level `n` -/

theorem exists_ltSymbol_ker_eq {F : Type u} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ↥(ValuativeRel.valuation F).integer) (hP : Irreducible P) (n : ℕ) (hn : 1 ≤ n)
    (πu : Fˣ) (hπu : (πu : F) = (P : F))
    (M : NK.LocalReciprocityLubinTate.LubinTateModule ↥(ValuativeRel.valuation F).integer P
          (NK.LocalReciprocityLubinTate.residueCard F))
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq P
          (NK.LocalReciprocityLubinTate.residueCard F))
    (y : AlgebraicClosure F)
    (hy : y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n)
    (hyp : y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1)) :
    ∃ Φ : Fˣ →* (↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
          ↥(NK.LocalReciprocityLubinTate.LTLevel F (P : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n)),
      Function.Surjective Φ ∧
      MonoidHom.ker Φ = Subgroup.zpowers πu ⊔
        NK.LocalReciprocityLubinTate.higherUnits F n ∧
      (∀ (a : (↥(ValuativeRel.valuation F).integer)ˣ),
        ((Φ (NK.LocalReciprocityLubinTate.Units.unitsIncl F a))
            ⟨y, NK.LocalReciprocityLubinTate.LTdivisionSet_subset_LTLevel F (P : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n hy⟩ :
            AlgebraicClosure F) =
          NK.LocalReciprocityLubinTate.Eval.smulDiv P hP
            (NK.LocalReciprocityLubinTate.residueCard F) n
            (NK.LocalReciprocityLubinTate.two_le_residueCard F) M hy
            (a : ↥(ValuativeRel.valuation F).integer)) := by
  classical
  have hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F) := by
    have h := isUniformizer_of_irreducible (F := F) P hP
    rwa [hπu]
  obtain ⟨e, he⟩ := exists_autLTLevel_mulEquiv_apply_smulDiv P hP n hn M hpi y hy hyp
  let O := ↥(ValuativeRel.valuation F).integer
  let I : Ideal O := NK.LocalReciprocityLubinTate.maximalIdealOfIntegers F ^ n
  let L := NK.LocalReciprocityLubinTate.LTLevel F (P : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n
  let mkq : O →* (O ⧸ I) := (Ideal.Quotient.mk I).toMonoidHom
  let ψ : Oˣ →* (↥L ≃ₐ[F] ↥L) := e.toMonoidHom.comp (Units.map mkq)
  let ρ : Fˣ →* Oˣ := unitPartHom (F := F) πu hπ
  let Φ : Fˣ →* (↥L ≃ₐ[F] ↥L) := ψ.comp ρ
  refine ⟨Φ, ?_, ?_, ?_⟩
  · have hψsurj : Function.Surjective ψ := by
      intro τ
      obtain ⟨u, rfl⟩ := e.surjective τ
      obtain ⟨a, rfl⟩ := surjective_units_map_quot_maximalIdeal_pow (F := F) n hn u
      exact ⟨a, rfl⟩
    intro σ
    obtain ⟨a, rfl⟩ := hψsurj σ
    obtain ⟨x, rfl⟩ := unitPartHom_surjective (F := F) πu hπ a
    exact ⟨x, rfl⟩
  · have hkerψ : ψ.ker = NK.LocalReciprocityLubinTate.principalUnits F n := by
      ext a
      rw [MonoidHom.mem_ker]
      show e (Units.map mkq a) = 1 ↔ a ∈ NK.LocalReciprocityLubinTate.principalUnits F n
      rw [MulEquiv.map_eq_one_iff, NK.LocalReciprocityLubinTate.mem_principalUnits_iff,
        Units.ext_iff, Units.coe_map, Units.val_one]
      show ((Ideal.Quotient.mk I (a : O) : O ⧸ I) = 1 ↔ (a : O) - 1 ∈ I)
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    ext x
    rw [MonoidHom.mem_ker]
    have h1 : Φ x = 1 ↔ ρ x ∈ NK.LocalReciprocityLubinTate.principalUnits F n := by
      rw [show Φ x = ψ (ρ x) from rfl, ← MonoidHom.mem_ker (f := ψ), hkerψ]
    rw [h1]
    constructor
    · intro hu
      rw [Subgroup.mem_sup]
      refine ⟨(NK.LocalReciprocityLubinTate.Units.unitsIncl F (ρ x))⁻¹ * x,
        unitPartHom_spec (F := F) πu hπ x, NK.LocalReciprocityLubinTate.Units.unitsIncl F (ρ x),
        ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem _ hu
      · rw [mul_assoc, mul_comm x, inv_mul_cancel_left]
    · intro hx
      rw [Subgroup.mem_sup] at hx
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      have ha1 : ρ a = 1 := by
        rw [← MonoidHom.mem_ker, unitPartHom_ker (F := F) πu hπ]
        exact ha
      have hb' : b ∈ (NK.LocalReciprocityLubinTate.principalUnits F n).map
          (NK.LocalReciprocityLubinTate.Units.unitsIncl F) := hb
      rw [Subgroup.mem_map] at hb'
      obtain ⟨u, hu, rfl⟩ := hb'
      have hρx : ρ x = u := by
        rw [← hab, map_mul, ha1, unitPartHom_unitsIncl (F := F) πu hπ u]
        exact one_mul u
      rw [hρx]
      exact hu
  · intro a
    have hval : Φ (NK.LocalReciprocityLubinTate.Units.unitsIncl F a)
        = e (Units.map mkq a) := by
      show ψ (ρ (NK.LocalReciprocityLubinTate.Units.unitsIncl F a)) = e (Units.map mkq a)
      rw [show ρ (NK.LocalReciprocityLubinTate.Units.unitsIncl F a) = a
        from unitPartHom_unitsIncl (F := F) πu hπ a]
      rfl
    rw [hval]
    have hu : IsUnit (Ideal.Quotient.mk I (a : O)) :=
      IsUnit.map (Ideal.Quotient.mk I).toMonoidHom a.isUnit
    have hkey : Units.map mkq a = hu.unit :=
      Units.ext (by rw [Units.coe_map, IsUnit.unit_spec]; rfl)
    rw [hkey]
    exact he (a : O) hu

end NK.LocalReciprocityLubinTate.LubinTate
