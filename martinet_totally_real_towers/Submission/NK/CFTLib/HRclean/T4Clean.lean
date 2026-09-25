import Mathlib
import Submission.NK.CFTLib.HRclean.ARLClean
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.CFTLib.HRclean.ARLLocal
import Submission.NK.NUV2.ABHN.unitsLevelMap_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
import Submission.NK.FieldTheory.Galois.exists_liesOver_and_lift_decompSubgroup
import Submission.NK.CFTLib.HRclean.StabRestrictSurj
import Submission.NK.CFTLib.HRclean.LocalUnitsDescent

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.CFTLib.HRclean.T4

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-! ## The value of the local units representation on a unit -/

/-- The action of the decomposition group on the local units, in the multiplicative form used by
Hilbert 90. -/
lemma localUnitsRep_rho_ofMul (ŵ : NK.GlobalCFT.Place E)
    (s : MulAction.stabilizer Gal(E/K) ŵ) (v : (NK.GlobalCFT.Place.localField E ŵ)ˣ) :
    (NK.HassePrinciple.localUnitsRep K E ŵ).ρ s (Additive.ofMul v)
      = Additive.ofMul
          (Units.map ((NK.HassePrinciple.localAutHom ŵ) s).toMonoidHom v) := rfl

/-- The action of the decomposition group on the local units representation, written as the
multiplicative action of the group on the units. -/
lemma localUnitsRep_rho_apply (ŵ : NK.GlobalCFT.Place E)
    (s : MulAction.stabilizer Gal(E/K) ŵ)
    (x : (NK.HassePrinciple.localUnitsRep K E ŵ).V) :
    (NK.HassePrinciple.localUnitsRep K E ŵ).ρ s x
      = Additive.ofMul (s • (Additive.toMul (α := (NK.GlobalCFT.Place.localField E ŵ)ˣ) x)) :=
  rfl

/-! ## The coefficient map `M_wˣ → E_ŵˣ` is injective -/

/-- The local coefficient map `localCoeff : M_wˣ → E_ŵˣ` is injective (it is `Units.map` of the
injective ring homomorphism `M_w → E_ŵ`). -/
lemma localCoeff_injective (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    Function.Injective
      ⇑(NK.CFTLib.HRclean.ARL.localCoeff (K := K) (M := M) (E := E) w ŵ hw).hom := by
  -- the underlying function is `ofMul ∘ (localAlgebraMapUnits) ∘ toMul`
  have key : ∀ a : (Rep.res (NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
        (NK.HassePrinciple.localUnitsRep K M w)).V,
      Additive.toMul (α := (NK.GlobalCFT.Place.localField E ŵ)ˣ)
          ((NK.CFTLib.HRclean.ARL.localCoeff (K := K) (M := M) (E := E) w ŵ hw).hom a)
        = (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw)
            (Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
              (a : (NK.HassePrinciple.localUnitsRep K M w).V)) := fun a => rfl
  intro a b hab
  have h : (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw)
        (Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
          (a : (NK.HassePrinciple.localUnitsRep K M w).V))
      = (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw)
        (Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
          (b : (NK.HassePrinciple.localUnitsRep K M w).V)) := by
    have h2 := congrArg (fun x => Additive.toMul (α := (NK.GlobalCFT.Place.localField E ŵ)ˣ) x)
      hab
    exact (key a).symm.trans (h2.trans (key b))
  have h3 : Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
        (a : (NK.HassePrinciple.localUnitsRep K M w).V)
      = Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
        (b : (NK.HassePrinciple.localUnitsRep K M w).V) :=
    NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective hw h
  have h4 : Additive.ofMul (Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
        (a : (NK.HassePrinciple.localUnitsRep K M w).V))
      = Additive.ofMul (Additive.toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
        (b : (NK.HassePrinciple.localUnitsRep K M w).V)) := congrArg Additive.ofMul h3
  exact (ofMul_toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
      (a : (NK.HassePrinciple.localUnitsRep K M w).V)).symm.trans
    (h4.trans (ofMul_toMul (α := (NK.GlobalCFT.Place.localField M w)ˣ)
      (b : (NK.HassePrinciple.localUnitsRep K M w).V)))

/-! ## Hilbert 90 for the kernel of `stabRestrict` -/

/-- **Noether's form of Hilbert 90 for the kernel of the restriction map on decomposition
groups.**  Every multiplicative `1`-cocycle on `ker (stabRestrict)` with values in the local units
`E_ŵˣ` is a coboundary, where the group acts on `E_ŵˣ` through the injective homomorphism
`localAutHom ŵ` into the ring automorphisms of the local field. -/
lemma exists_units_div_ker_stabRestrict_aux (w : NK.GlobalCFT.Place M)
    (ŵ : NK.GlobalCFT.Place E) (hw : NK.GlobalCFT.Place.LiesOver ŵ w)
    (g : ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker →
      (NK.GlobalCFT.Place.localField E ŵ)ˣ)
    (hg : ∀ a b, g (a * b) = Units.map
      ((NK.HassePrinciple.localAutHom ŵ) (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom
      (g b) * g a) :
    ∃ β, ∀ a : ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker,
      g a = Units.map
        ((NK.HassePrinciple.localAutHom ŵ) (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom
        β / β := by
  haveI hF : Fintype Gal(E/K) := AlgEquiv.fintype K E
  haveI : Fintype ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker :=
    Fintype.ofFinite _
  refine NK.HassePrinciple.exists_units_div_of_isMulCocycle_ringEquiv
    ((NK.HassePrinciple.localAutHom ŵ).comp
      (NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker.subtype) ?_ g ?_
  · intro a b hab
    exact Subtype.ext (NK.HassePrinciple.localAutHom_injective ŵ hab)
  · intro a b
    exact hg a b

/-- **The coboundary condition of the inflation–restriction argument**, in the additive form
required by the abstract injectivity criterion: every additive `1`-cocycle on `ker (stabRestrict)`
with values in the local units is a coboundary. -/
lemma coboundary_ker_stabRestrict (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    ∀ α : ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker →
        Additive ((NK.GlobalCFT.Place.localField E ŵ)ˣ),
      (∀ a b, α (a * b) = Additive.ofMul
          ((a : MulAction.stabilizer Gal(E/K) ŵ)
            • Additive.toMul (α b)) + α a) →
      ∃ y : Additive ((NK.GlobalCFT.Place.localField E ŵ)ˣ),
        ∀ a, α a = Additive.ofMul
          ((a : MulAction.stabilizer Gal(E/K) ŵ)
            • Additive.toMul y) - y := by
  intro α hα
  have hcoc : ∀ a b, (fun c => Additive.toMul (α c)) (a * b) =
      Units.map ((NK.HassePrinciple.localAutHom ŵ)
        (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom
        ((fun c => Additive.toMul (α c)) b) * (fun c => Additive.toMul (α c)) a := by
    intro a b
    have hsmul : (a : MulAction.stabilizer Gal(E/K) ŵ) • Additive.toMul (α b)
        = Units.map ((NK.HassePrinciple.localAutHom ŵ)
            (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom (Additive.toMul (α b)) := rfl
    calc Additive.toMul (α (a * b))
        = Additive.toMul (Additive.ofMul
            ((a : MulAction.stabilizer Gal(E/K) ŵ) • Additive.toMul (α b)) + α a) := by
          rw [hα a b]
      _ = Additive.toMul (Additive.ofMul
            ((a : MulAction.stabilizer Gal(E/K) ŵ) • Additive.toMul (α b)))
          * Additive.toMul (α a) := toMul_add _ _
      _ = Units.map ((NK.HassePrinciple.localAutHom ŵ)
            (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom (Additive.toMul (α b))
          * Additive.toMul (α a) := by rw [toMul_ofMul, hsmul]
  obtain ⟨β, hβ⟩ := exists_units_div_ker_stabRestrict_aux (K := K) (M := M) (E := E) w ŵ hw
    (fun c => Additive.toMul (α c)) hcoc
  refine ⟨Additive.ofMul β, fun a => ?_⟩
  have hsmul : (a : MulAction.stabilizer Gal(E/K) ŵ) • β
      = Units.map ((NK.HassePrinciple.localAutHom ŵ)
          (a : MulAction.stabilizer Gal(E/K) ŵ)).toMonoidHom β := rfl
  have hgoal : Additive.ofMul ((a : MulAction.stabilizer Gal(E/K) ŵ) • β) - Additive.ofMul β
      = Additive.ofMul
          ((a : MulAction.stabilizer Gal(E/K) ŵ)
            • Additive.toMul (Additive.ofMul β)) - Additive.ofMul β := rfl
  rw [← hgoal, hsmul, ← ofMul_div, ← hβ a]
  exact (ofMul_toMul (α a)).symm

/-! ## The fixed units of the kernel come from the intermediate field -/

/-- Units of `E_ŵ` fixed by the whole kernel of `stabRestrict` lie in the image of `M_wˣ` (local
fixed field theorem for the relative extension `E/M`). -/
lemma localCoeff_surj_on_fixed (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    ∀ b : Additive ((NK.GlobalCFT.Place.localField E ŵ)ˣ),
      (∀ s : ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker,
        (s : MulAction.stabilizer Gal(E/K) ŵ) • Additive.toMul b = Additive.toMul b) →
      ∃ a : Additive ((NK.GlobalCFT.Place.localField M w)ˣ),
        Additive.ofMul ((NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw)
          (Additive.toMul a)) = b := by
  intro b hb
  have hb' : ∀ s : ↥(NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker,
      (NK.HassePrinciple.localUnitsRep.{0} K E ŵ).ρ
        (s : MulAction.stabilizer Gal(E/K) ŵ) (Additive.ofMul (Additive.toMul b))
        = Additive.ofMul (Additive.toMul b) := by
    intro s
    exact congrArg Additive.ofMul (hb s)
  obtain ⟨a, ha⟩ :=
    NK.CFTLib.HRclean.Descent.exists_localAlgebraMapUnits_eq_of_ker_fixed
      (K := K) (M := M) (E := E) w ŵ hw (Additive.toMul b) hb'
  exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩

/-! ## Injectivity of the local level map -/

/-- **Injectivity of the local level map** `H²(Γ_w, M_wˣ) → H²(Γ_ŵ, E_ŵˣ)`: the restriction of
the decomposition groups `Γ_ŵ ↠ Γ_w` (surjective, with kernel `D_ŵ(E/M)`) together with the
coefficient injection `M_wˣ ↪ E_ŵˣ`.

The proof is the abstract criterion `NK.NUV2.ABHN.groupCohomology_map_two_injective`: the
coefficient map is injective, its image is exactly the fixed units of the kernel (local fixed
field theorem), and `H¹` of the kernel vanishes by Hilbert 90. -/
theorem localLevelMap_injective (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    Function.Injective
      (NK.CFTLib.HRclean.ARL.localLevelMap (K := K) (M := M) (E := E) w ŵ hw).hom :=
  NK.NUV2.ABHN.groupCohomology_map_two_injective
    (NK.CFTLib.HRclean.ARL.stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
    (NK.CFTLib.HRclean.Descent.stabRestrict_surjective
      (K := K) (M := M) (E := E) w ŵ hw)
    (NK.HassePrinciple.localUnitsRep K M w)
    (NK.HassePrinciple.localUnitsRep K E ŵ)
    (NK.CFTLib.HRclean.ARL.localCoeff (K := K) (M := M) (E := E) w ŵ hw)
    (localCoeff_injective (K := K) (M := M) (E := E) w ŵ hw)
    (localCoeff_surj_on_fixed (K := K) (M := M) (E := E) w ŵ hw)
    (coboundary_ker_stabRestrict (K := K) (M := M) (E := E) w ŵ hw)

/-- **The local inflation is injective (localisation form).**  For `K ⊆ M ⊆ E` with `M/K` and
`E/K` Galois, a class `β ∈ H²(Gal(M/K), Mˣ)` has vanishing localisation at a place `w` of `M` if
and only if its level inflation to `E/K` has vanishing localisation at a place `ŵ` of `E` above `w`.

The easy direction `⟸` is the functoriality square for `locUnits` ("localisation commutes with
inflation").  The direction `⟹` is the injectivity of the map
`H²(Gal(M_w/K_v), M_wˣ) → H²(Gal(E_ŵ/K_v), E_ŵˣ)` induced by the surjection
`Gal(E_ŵ/K_v) ↠ Gal(M_w/K_v)` and the coefficient map `M_wˣ → E_ŵˣ`; it is an instance of
`Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general`
(general coefficient ring, so usable in the `CoeffInt` world) with Hilbert 90 for the finite Galois
extension of local fields `E_ŵ/M_w` (`NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep`
for the field extension `Place.localField M w ⊆ Place.localField E ŵ`, or the `ℤ`-world
`Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units`).

Useful assets on disk: `NK.HassePrinciple.liesOver_smul_of_restrict` (the stabiliser of `ŵ` maps
into the stabiliser of `w`), `NK.NUV2.LC.RouteB.locUnits_tower_eq_zero` and
`Submission/Work/NUV2/LC/LocalLevelSystem.lean` (the proved square
`unitsLevelMapTower ≫ locUnits = locUnits ≫ localLevelMap`), and the file
`Submission/Work/NUV2/ChebAux/Transfer/locUnits_res_inflation_eq_zero.lean` (proved: it constructs
`localLevelMapRho` and the restriction square for the `(rhoRestrict, unitsInclRepM)` pair).  Note
`NK.CFTLib.HRclean.ARL.inflation` (via the image field) and the `RouteD`/`LC` level maps (via
`AlgEquiv.restrictNormalHom` / fixed fields) are equal but not definitionally equal. -/
theorem locUnits_inflation_eq_zero_iff {K M E : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (β : groupCohomology (NK.HassePrinciple.unitsRep K M) 2)
    (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom β) = 0
      ↔ (NK.HassePrinciple.locUnits K M w).hom β = 0 := by
  -- the functoriality square: the localisation of the inflation is the local level map
  have hsq := NK.CFTLib.HRclean.ARL.locUnits_inflation_eq (K := K) (M := M) (E := E) w ŵ hw
  have hkey : (NK.HassePrinciple.locUnits K E ŵ).hom
        ((NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom β)
      = (NK.CFTLib.HRclean.ARL.localLevelMap (K := K) (M := M) (E := E) w ŵ hw).hom
        ((NK.HassePrinciple.locUnits K M w).hom β) := by
    have h := congrArg (fun f => f.hom β) hsq
    simpa only [ConcreteCategory.comp_apply] using h
  rw [hkey]
  refine ⟨?_, ?_⟩
  · intro h
    refine (localLevelMap_injective (K := K) (M := M) (E := E) w ŵ hw) ?_
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

end NK.CFTLib.HRclean.T4
