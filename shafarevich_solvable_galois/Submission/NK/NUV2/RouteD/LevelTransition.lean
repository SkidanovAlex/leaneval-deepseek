import Mathlib
import Submission.NK.NUV2.RouteD.LevelNat
import Submission.NK.NUV2.Final.LevelInfIdentity
import Submission.NK.NUV2.RouteF.transition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transition map on fundamental classes for arbitrary levels

For two levels `L ≤ E` of an ambient Galois extension, and a fundamental class `u` at the level `E`
(a generator of the cyclic group `H²(Gal(E/F), Eˣ)`), there is a fundamental class `v` at the level
`L` whose level inflation is `[E : L] • u`; it is unique by injectivity of the level inflation.

The point of the file is that this is proved for *arbitrary* levels, not only for levels presented
as fixed fields: the fixed-field case is
`NK.NUV2.RouteF.transition_generator`/`NK.NUV2.Final.levelInfMap_injective`, and the general
case follows by transporting along the canonical algebra isomorphism
`IntermediateField.restrictAlgEquiv` using the naturality of the level inflation
(`NK.NUV2.RouteD.levelInfMap_unitsCohIso`).
-/

open CategoryTheory Representation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2.RouteD

section Galois

variable {F A : Type} [Field F] [Field A] [Algebra F A]
variable {L E : IntermediateField F A} (h : L ≤ E)
variable [Algebra ↥L ↥E] [IsScalarTower F ↥L ↥E]
variable (hcan : ∀ x : ↥L, ((algebraMap ↥L ↥E x : ↥E) : A) = (x : A))

include hcan in
/-- The canonical-inclusion compatibility of the algebra structure on `↥E`. -/
theorem algebraMap_coe (x : ↥L) : ((algebraMap ↥L ↥E x : ↥E) : A) = (x : A) := hcan x

omit [IsScalarTower F ↥L ↥E] in
/-- The elementwise compatibility of `restrictAlgEquiv` with the canonical inclusions. -/
theorem restrictAlgEquiv_coe (x : ↥L) :
    (((IntermediateField.restrictAlgEquiv h) x : ↥(IntermediateField.restrict h)) : A)
      = (x : A) := by
  have hh := AlgEquiv.ofInjective_apply (IntermediateField.inclusion h)
    (IntermediateField.inclusion h).toRingHom.injective x
  have h2 : (IntermediateField.restrictAlgEquiv h) x
      = AlgEquiv.ofInjective (IntermediateField.inclusion h)
          (IntermediateField.inclusion h).toRingHom.injective x := rfl
  rw [h2]
  rw [show (((AlgEquiv.ofInjective (IntermediateField.inclusion h)
      (IntermediateField.inclusion h).toRingHom.injective x : ↥((IntermediateField.inclusion h).range)) :
        ↥E) : A)
      = ((IntermediateField.inclusion h x : ↥E) : A) from rfl]
  rfl

include hcan in
/-- `restrictAlgEquiv` is compatible with the algebra maps into `E`. -/
theorem restrictAlgEquiv_algebraMap (x : ↥L) :
    algebraMap ↥(IntermediateField.restrict h) ↥E ((IntermediateField.restrictAlgEquiv h) x)
      = algebraMap ↥L ↥E x := by
  apply Subtype.ext
  change (((IntermediateField.restrictAlgEquiv h) x : ↥(IntermediateField.restrict h)) : A)
    = ((algebraMap ↥L ↥E x : ↥E) : A)
  rw [restrictAlgEquiv_coe h x, hcan x]

variable [FiniteDimensional F ↥L] [IsGalois F ↥L] [FiniteDimensional F ↥E] [IsGalois F ↥E]

include hcan in
/-- The kernel of the restriction of `Gal(E/F)` to `L` is the fixing subgroup of `L` (as a subfield
of `E`). -/
theorem restrictKernel_eq_fixingSubgroup :
    (AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker
      = (IntermediateField.restrict h).fixingSubgroup := by
  ext σ
  simp only [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ y hy
    have hy' : (y : A) ∈ L := (IntermediateField.mem_restrict h y).mp hy
    set x : ↥L := ⟨(y : A), hy'⟩ with hx
    have hxy : algebraMap ↥L ↥E x = y := by
      apply Subtype.ext
      rw [hcan x]
    have h1 : algebraMap ↥L ↥E (((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)) σ) x)
        = σ (algebraMap ↥L ↥E x) := AlgEquiv.restrictNormal_commutes σ ↥L x
    rw [hσ, AlgEquiv.one_apply] at h1
    rw [← hxy, ← h1]
  · intro hσ
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    have hmem : algebraMap ↥L ↥E x ∈ (IntermediateField.restrict h) := by
      rw [IntermediateField.mem_restrict, hcan x]
      exact x.2
    have hfix : σ (algebraMap ↥L ↥E x) = algebraMap ↥L ↥E x := hσ _ hmem
    have h2 : algebraMap ↥L ↥E (((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)) σ) x)
        = σ (algebraMap ↥L ↥E x) := AlgEquiv.restrictNormal_commutes σ ↥L x
    rw [← hcan ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)) σ x), h2, hfix, hcan x]
    simp

include hcan in
/-- The fixed field of the kernel of the restriction of `Gal(E/F)` to `L` is the image of `L` in
`E`. -/
theorem fixedField_restrictKernel :
    IntermediateField.fixedField ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)
      = IntermediateField.restrict h := by
  rw [restrictKernel_eq_fixingSubgroup h hcan, IsGalois.fixedField_fixingSubgroup]

end Galois

section Transition

variable {F A : Type} [Field F] [Field A] [Algebra F A]
variable {L E : IntermediateField F A} (h : L ≤ E)
variable [Algebra ↥L ↥E] [IsScalarTower F ↥L ↥E]
variable (hcan : ∀ x : ↥L, ((algebraMap ↥L ↥E x : ↥E) : A) = (x : A))
variable [FiniteDimensional F ↥L] [IsGalois F ↥L] [FiniteDimensional F ↥E] [IsGalois F ↥E]

include h hcan in
/-- **Injectivity of the level inflation for arbitrary levels.**

The fixed-field case is `NK.NUV2.Final.levelInfMap_injective`; the general case is obtained by
transporting the source along the canonical algebra isomorphism from `L` to the fixed field of the
kernel of the restriction map, using the naturality
`NK.NUV2.RouteD.levelInfMap_unitsCohIso`. -/
theorem levelInfMap_injective_of_le :
    Function.Injective ⇑((levelInfMap (F := F) (M := ↥L) (L := ↥E)).hom) := by
  have hNfix : IntermediateField.fixedField
      ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)
      = IntermediateField.restrict h := fixedField_restrictKernel h hcan
  -- injectivity for the fixed field of the kernel
  have hinjR := NK.NUV2.Final.levelInfMap_injective (F := F) (L := ↥E)
    ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)
  -- the transport
  set ψ : ↥L ≃ₐ[F] ↥(IntermediateField.fixedField
      ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)) :=
    (IntermediateField.restrictAlgEquiv h).trans (IntermediateField.equivOfEq hNfix.symm) with hψdef
  have hψ : ∀ x : ↥L, algebraMap ↥(IntermediateField.fixedField
      ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)) ↥E (ψ x)
      = algebraMap ↥L ↥E x := by
    intro x
    apply Subtype.ext
    change (((IntermediateField.equivOfEq hNfix.symm)
        ((IntermediateField.restrictAlgEquiv h) x) : ↥(IntermediateField.fixedField
          ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker))) : A)
      = ((algebraMap ↥L ↥E x : ↥E) : A)
    rw [hcan x]
    simp only [IntermediateField.equivOfEq_apply]
    exact restrictAlgEquiv_coe h x
  have hnat := levelInfMap_unitsCohIso (F := F) (E := ↥L)
    (E' := ↥(IntermediateField.fixedField ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)))
    (E'' := ↥E) ψ hψ
  -- conclude
  intro x y hxy
  have hcomp : ⇑((levelInfMap (F := F) (M := ↥L) (L := ↥E)).hom)
      = ⇑((levelInfMap (F := F)
          (M := ↥(IntermediateField.fixedField ((AlgEquiv.restrictNormalHom (K₁ := ↥E) (E := ↥L)).ker)))
          (L := ↥E)).hom) ∘ ⇑((unitsCohIso ψ).hom) := by
    rw [← hnat]
    ext z
    rfl
  rw [hcomp] at hxy
  have h2 : (unitsCohIso ψ).hom.hom x = (unitsCohIso ψ).hom.hom y := hinjR hxy
  exact (unitsCohIso ψ).toLinearEquiv.injective h2

end Transition


/-- An injective additive homomorphism preserves the additive order. -/
lemma addOrderOf_apply_of_injective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f) (x : A) : addOrderOf (f x) = addOrderOf x := by
  rw [← Nat.card_zmultiples (f x), ← Nat.card_zmultiples x,
    show AddSubgroup.zmultiples (f x) = (AddSubgroup.zmultiples x).map f from (f.map_zmultiples x).symm]
  exact Nat.card_congr (AddSubgroup.equivMapOfInjective (AddSubgroup.zmultiples x) f hf).toEquiv.symm


section ExistsTransition

variable {F A : Type} [Field F] [Field A] [Algebra F A]
variable {L E : IntermediateField F A} (h : L ≤ E)
variable [Algebra ↥L ↥E] [IsScalarTower F ↥L ↥E]
variable (hcan : ∀ x : ↥L, ((algebraMap ↥L ↥E x : ↥E) : A) = (x : A))
variable [FiniteDimensional F ↥L] [IsGalois F ↥L] [FiniteDimensional F ↥E] [IsGalois F ↥E]

include h hcan in
/-- **The transition on fundamental classes for arbitrary levels.** -/
theorem exists_transition
    (N : Subgroup (↥E ≃ₐ[F] ↥E)) [N.Normal]
    (hNfix : IntermediateField.fixedField N = IntermediateField.restrict h)
    (hfinE : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2))
    (hcardE : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2)
      = Nat.card (↥E ≃ₐ[F] ↥E))
    (hcardL : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2)
      = Nat.card (↥L ≃ₐ[F] ↥L))
    (u : groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥E) 2)) :
    ∃ v : groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2,
      addOrderOf v = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) ∧
      (levelInfMap (F := F) (M := ↥L) (L := ↥E)) v
        = ((Nat.card (↥E ≃ₐ[F] ↥E) / Nat.card (↥L ≃ₐ[F] ↥L) : ℕ) : ℤ) • u := by
  haveI hgalFix : IsGalois F ↥(IntermediateField.fixedField N) :=
    IsGalois.of_fixedField_normal_subgroup N
  let ψ : ↥L ≃ₐ[F] ↥(IntermediateField.fixedField N) :=
    (IntermediateField.restrictAlgEquiv h).trans (IntermediateField.equivOfEq hNfix.symm)
  have hψ : ∀ x : ↥L, algebraMap ↥(IntermediateField.fixedField N) ↥E (ψ x)
      = algebraMap ↥L ↥E x := by
    intro x
    apply Subtype.ext
    change (((IntermediateField.equivOfEq hNfix.symm)
        ((IntermediateField.restrictAlgEquiv h) x) : ↥(IntermediateField.fixedField N)) : A)
      = ((algebraMap ↥L ↥E x : ↥E) : A)
    rw [hcan x]
    simp only [IntermediateField.equivOfEq_apply]
    exact restrictAlgEquiv_coe h x

  have hidx : N.index = Nat.card (↥L ≃ₐ[F] ↥L) := by
    calc N.index = Nat.card ((↥E ≃ₐ[F] ↥E) ⧸ N) := Subgroup.index_eq_card N
      _ = Nat.card (↥(IntermediateField.fixedField N) ≃ₐ[F] ↥(IntermediateField.fixedField N)) :=
          Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv
      _ = Nat.card (↥(IntermediateField.restrict h) ≃ₐ[F] ↥(IntermediateField.restrict h)) := by
          rw [hNfix]
      _ = Nat.card (↥L ≃ₐ[F] ↥L) :=
          (Nat.card_congr (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv h)).toEquiv).symm
  have hcardR : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F
      ↥(IntermediateField.fixedField N)) 2) = Nat.card (↥L ≃ₐ[F] ↥L) := by
    calc Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2)
        = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) :=
          Nat.card_congr (unitsCohIso ψ).toLinearEquiv.symm.toEquiv
      _ = Nat.card (↥L ≃ₐ[F] ↥L) := hcardL
  have hcardK : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F
      ↥(IntermediateField.fixedField N)) 2) = N.index := hcardR.trans hidx.symm
  obtain ⟨w, hwgen, hw⟩ := NK.NUV2.RouteF.transition_generator (F := F) (L := ↥E) N
    hfinE hcardE u hu hcardK
  have hnat_apply : ∀ x, (levelInfMap (F := F) (M := ↥(IntermediateField.fixedField N)) (L := ↥E))
      ((unitsCohIso ψ).hom.hom x) = (levelInfMap (F := F) (M := ↥L) (L := ↥E)) x := by
    intro x
    rw [← levelInfMap_unitsCohIso (F := F) (E := ↥L)
      (E' := ↥(IntermediateField.fixedField N)) (E'' := ↥E) ψ hψ]
    rfl
  have h2 : (unitsCohIso ψ).hom.hom ((unitsCohIso ψ).inv.hom w) = w :=
    CategoryTheory.Iso.inv_hom_id_apply (unitsCohIso ψ) w
  refine ⟨(unitsCohIso ψ).inv.hom w, ?_, ?_⟩
  · have h4 : addOrderOf ((unitsCohIso ψ).inv.hom w) = addOrderOf w := by
      have h5 : addOrderOf ((unitsCohIso ψ).hom.hom ((unitsCohIso ψ).inv.hom w))
          = addOrderOf w := congrArg addOrderOf h2
      have h6 : addOrderOf ((unitsCohIso ψ).hom.hom ((unitsCohIso ψ).inv.hom w))
          = addOrderOf ((unitsCohIso ψ).inv.hom w) :=
        addOrderOf_apply_of_injective ((unitsCohIso ψ).hom.hom).toAddMonoidHom
          (unitsCohIso ψ).toLinearEquiv.injective ((unitsCohIso ψ).inv.hom w)
      exact h6.symm.trans h5
    rw [h4, show Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2)
        = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F
            ↥(IntermediateField.fixedField N)) 2)
        from (Nat.card_congr (unitsCohIso ψ).toLinearEquiv.symm.toEquiv).symm]
    exact hwgen
  · rw [hidx] at hw
    rw [← hnat_apply ((unitsCohIso ψ).inv.hom w), h2]
    exact hw

end ExistsTransition

end NK.NUV2.RouteD

/-!
## WIP: `exists_transition` (the transition on fundamental classes for arbitrary levels)

The (almost complete) proof is preserved verbatim in `ScratchRD/LevelTransition_wip2.lean` and
`ScratchRD/LevelTransition_wip.lean`.  Everything is in place except two bookkeeping points in the
last part of the proof:

* in the generator bullet, `addOrderOf` must be transported along the isomorphism: prove
  `h4 : addOrderOf ((unitsCohIso ψ).inv.hom w) = addOrderOf w` by combining
  `congrArg addOrderOf h2` (`h2 : (unitsCohIso ψ).hom.hom ((unitsCohIso ψ).inv.hom w) = w`) with
  `addOrderOf_apply_of_injective` (proved in this file); do **not** use `rw [← h2]`, which also
  rewrites the `w` inside `ψ.inv w`;
* the `Nat.card_congr (unitsCohIso ψ).toLinearEquiv.toEquiv` in the two `show`/`calc` steps must be
  oriented so that the two occurrences of `↥L` (one from the hypothesis `hcardL`, one from the type
  of `ψ`) are syntactically identical; the cheapest fix is to prove both statements with `calc` and
  let defeq close the steps.

The statement itself is the one needed by the König construction (`RouteF`/`Final` vocabulary is
`↥(fixedField N)`; the transport from `↥L` to `↥(fixedField N)` is `ψ` as constructed there).
-/
