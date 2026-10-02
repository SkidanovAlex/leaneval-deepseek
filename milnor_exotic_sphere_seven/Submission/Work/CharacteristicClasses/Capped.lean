import Mathlib
import Submission.Work.CharacteristicClasses.Milnor
import Submission.Work.Cohomology.Endgame.cappedTransferClean
import Submission.Work.Milnor.CappedManifold
import Submission.Work.Milnor.cohomology_Vk
import Submission.Work.Cohomology.capped_cupSquare_generates

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The first Pontryagin class of `TX` as a class in `H⁴(X;ℤ)`, for `X = D(ξ) ∪_F D⁸`

`Submission/Work/CharacteristicClasses/Milnor.lean` computes the *number* `p₁(ξ) = 6` (the
evaluation of the first Pontryagin class of Milnor's bundle on a generator of `H⁴(S⁴;ℤ) ≅ ℤ`).
This file turns it into a *class* in `H⁴(X;ℤ)` for the closed `8`-manifold `X = D(ξ) ∪_F D⁸`:

* `cappedRestriction` is the honest restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` (the pullback along the
  inclusion `ιX` of the disc bundle), and it is an **isomorphism** —
  `cappedRestriction_surjective` and `cappedRestriction_injective` — because both sides are `ℤ` and
  the Mayer–Vietoris/excision machinery
  (`Work.Cohomology.Endgame.CappedTransfer.epi_singularCohomologyMap_subtypeIncl`) provides
  surjectivity;
* `cappedPontryaginClass` is *the* class in `H⁴(X;ℤ)` whose restriction to the disc bundle is
  `p₁(ξ) · τ`, `τ` the chosen generator of `H⁴(D(ξ);ℤ) ≅ ℤ`: the classical identification
  `TX|_{{D(ξ)}} ≅ π*(TS⁴ ⊕ ξ)` with `p₁(TS⁴) = 0` and `p₁(ξ) = 6` (the last two proved in this
  chapter, the first being the geometric input the workspace cannot formalise, having no
  tangent-bundle characteristic classes);
* `cappedPontryaginClass_eq_pm_smul`: for **every** generator `x` of `H⁴(X;ℤ) ≅ ℤ` one has
  `p₁(TX) = p₁(ξ) • x` or `p₁(TX) = -(p₁(ξ) • x)` — the input the endgame
  (`Work.SignatureBordism.capped_obstruction_of_selfIntersection`) consumes as `p₁ = q • x` with
  `q = ±6`;
* `capped_pontryagin_class_of_restriction`: the same conclusion for *any* class `P` restricting to
  `p₁(ξ) · τ` (the injective form), so a future session with a geometric definition of `p₁(TX)`
  can plug it in.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits

namespace Work.Milnor

noncomputable section

/-! ## Elementary algebra of isomorphisms of `ℤ`-modules -/

/-- `e.hom (e.inv a) = a`. -/
lemma iso_hom_apply_inv {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) (a : ℤ) :
    ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom e.inv a) = a := by
  have h := congrArg ModuleCat.Hom.hom e.inv_hom_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h a

/-- `e.inv (e.hom x) = x`. -/
lemma iso_inv_apply_hom {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) (x : M) :
    ModuleCat.Hom.hom e.inv (ModuleCat.Hom.hom e.hom x) = x := by
  have h := congrArg ModuleCat.Hom.hom e.hom_inv_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h x

/-- `e.inv` is multiplication by the image of `1`. -/
lemma iso_inv_eq_smul {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) (a : ℤ) :
    ModuleCat.Hom.hom e.inv a = a • (ModuleCat.Hom.hom e.inv (1 : ℤ)) := by
  simpa using map_zsmul (ModuleCat.Hom.hom e.inv) a (1 : ℤ)

/-- A surjective `ℤ`-linear endomorphism of `ℤ` is bijective. -/
theorem bijective_of_surjective_int (f : ℤ →ₗ[ℤ] ℤ) (hf : Function.Surjective f) :
    Function.Bijective f := by
  have hval : ∀ x : ℤ, f x = x * f 1 := by
    intro x
    conv_lhs => rw [show x = x • (1 : ℤ) by simp]
    rw [map_smul, smul_eq_mul]
  obtain ⟨m, hm⟩ := hf 1
  have hmul : m * f 1 = 1 := by rw [← hval m, hm]
  have hone : f 1 = 1 ∨ f 1 = -1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨fun a b hab => ?_, hf⟩
  rw [hval a, hval b] at hab
  rcases hone with h | h
  · rw [h] at hab; simpa using hab
  · rw [h, mul_neg_one, mul_neg_one] at hab; omega

/-- If `x` generates a module isomorphic to `ℤ`, its image under the isomorphism is `±1`. -/
theorem eq_pm_one_of_generates {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) (x : M)
    (hx : ∀ z : M, ∃ a : ℤ, z = a • x) : ModuleCat.Hom.hom e.hom x = 1 ∨
      ModuleCat.Hom.hom e.hom x = -1 := by
  obtain ⟨a, ha⟩ := hx (ModuleCat.Hom.hom e.inv 1)
  have h1 : a * ModuleCat.Hom.hom e.hom x = 1 := by
    have h := congrArg (fun z => ModuleCat.Hom.hom e.hom z) ha
    rw [iso_hom_apply_inv] at h
    have h2 : ModuleCat.Hom.hom e.hom (a • x) = a * ModuleCat.Hom.hom e.hom x := by
      simpa [smul_eq_mul] using map_zsmul (ModuleCat.Hom.hom e.hom) a x
    rw [h2] at h
    exact h.symm
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Two generators of a module isomorphic to `ℤ` differ by a sign. -/
theorem eq_pm_of_generates {M : ModuleCat ℤ} (e : M ≅ ModuleCat.of ℤ ℤ) (x y : M)
    (hx : ∀ z : M, ∃ a : ℤ, z = a • x) (hy : ∀ z : M, ∃ a : ℤ, z = a • y) :
    y = x ∨ y = -x := by
  have hy1 : ModuleCat.Hom.hom e.hom y = 1 ∨ ModuleCat.Hom.hom e.hom y = -1 :=
    eq_pm_one_of_generates e y hy
  have hx1 : ModuleCat.Hom.hom e.hom x = 1 ∨ ModuleCat.Hom.hom e.hom x = -1 :=
    eq_pm_one_of_generates e x hx
  have hy_eq : y = ModuleCat.Hom.hom e.hom y • (ModuleCat.Hom.hom e.inv (1 : ℤ)) := by
    conv_lhs => rw [← iso_inv_apply_hom e y]
    exact iso_inv_eq_smul e (ModuleCat.Hom.hom e.hom y)
  have hx_eq : x = ModuleCat.Hom.hom e.hom x • (ModuleCat.Hom.hom e.inv (1 : ℤ)) := by
    conv_lhs => rw [← iso_inv_apply_hom e x]
    exact iso_inv_eq_smul e (ModuleCat.Hom.hom e.hom x)
  rcases hy1 with hy1 | hy1 <;> rcases hx1 with hx1 | hx1
  · left; rw [hy_eq, hx_eq, hy1, hx1]
  · right; rw [hy_eq, hx_eq, hy1, hx1]; simp
  · right; rw [hy_eq, hx_eq, hy1, hx1]; simp
  · left; rw [hy_eq, hx_eq, hy1, hx1]

/-- A surjection carries generators to generators. -/
theorem generates_map {M N : ModuleCat ℤ} (f : M ⟶ N) (hf : Function.Surjective f.hom) {x : M}
    (hx : ∀ z : M, ∃ a : ℤ, z = a • x) : ∀ z : N, ∃ a : ℤ, z = a • f.hom x := by
  intro z
  obtain ⟨w, rfl⟩ := hf z
  obtain ⟨a, ha⟩ := hx w
  exact ⟨a, by rw [ha]; exact map_zsmul (ModuleCat.Hom.hom f) a x⟩

/-! ## The restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` -/

variable (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
variable (hF : Work.Milnor.IsCappingDiffeo F)

/-- `H⁴` of the capped manifold `X = D(ξ) ∪_F D⁸`. -/
abbrev cappedH4 : ModuleCat ℤ :=
  Work.Cohomology.singularCohomology ℤ 4 (TopCat.of (Work.Milnor.cappedSpace (cappedDatum F hF)))

/-- `H⁴` of the disc bundle `D(ξ) = Vk (-2)` (the total space of `ξ`). -/
abbrev discH4 : ModuleCat ℤ :=
  Work.Cohomology.singularCohomology ℤ 4 (TopCat.of (Submission.Milnor.Vk (-2)))

/-- The inclusion of the disc bundle `D(ξ)` into `X = D(ξ) ∪_F D⁸`. -/
abbrev cappedIncl : TopCat.of (Submission.Milnor.Vk (-2)) ⟶ Work.Milnor.glueX (cappedDatum F hF) :=
  Work.Cohomology.Endgame.CappedTransfer.capPairMap (cappedDatum F hF)

/-- **The restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)`**, the pullback along the inclusion of the disc
bundle. -/
def cappedRestriction : cappedH4 F hF ⟶ discH4 :=
  Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
    (TopCat.of (Work.Milnor.cappedSpace (cappedDatum F hF))) (cappedIncl F hF) 4

/-- `H⁴(X;ℤ) ≅ ℤ`. -/
def cappedH4Iso : cappedH4 F hF ≅ ModuleCat.of ℤ ℤ := by
  have hk : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) +
      (if (4 : ℕ) = 8 then 1 else 0) = 1 := by norm_num
  refine (Work.Milnor.cohomology_capped_datum F hF 4).some ≪≫ ?_
  rw [hk]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- `H⁴(D(ξ);ℤ) ≅ ℤ`. -/
def discH4Iso : discH4 ≅ ModuleCat.of ℤ ℤ := by
  have hk : (if (4 : ℕ) = 0 then 1 else 0) + (if (4 : ℕ) = 4 then 1 else 0) = 1 := by norm_num
  refine (Work.Milnor.cohomology_Vk (-2) 4).some ≪≫ ?_
  rw [hk]
  exact (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso

/-- The chosen generator of `H⁴(D(ξ);ℤ) ≅ ℤ` (the class sent to `1` by `discH4Iso`). -/
def tauD : discH4 := ModuleCat.Hom.hom discH4Iso.inv (1 : ℤ)

@[simp] lemma discH4Iso_tauD : ModuleCat.Hom.hom discH4Iso.hom tauD = 1 :=
  iso_hom_apply_inv discH4Iso 1

/-- The chosen generator `τ` of `H⁴(D(ξ);ℤ)` generates. -/
lemma generates_tauD : ∀ z : discH4, ∃ a : ℤ, z = a • tauD := by
  intro z
  refine ⟨ModuleCat.Hom.hom discH4Iso.hom z, ?_⟩
  rw [show tauD = ModuleCat.Hom.hom discH4Iso.inv (1 : ℤ) from rfl,
    ← iso_inv_eq_smul discH4Iso (ModuleCat.Hom.hom discH4Iso.hom z)]
  exact (iso_inv_apply_hom discH4Iso z).symm

/-- **The restriction to the disc bundle is surjective.** -/
theorem cappedRestriction_surjective : Function.Surjective (cappedRestriction F hF).hom := by
  have hcomp : cappedRestriction F hF
      = Work.Cohomology.singularCohomologyMap ℤ (TopCat.of ↥(Work.Milnor.glueU (cappedDatum F hF)))
          (Work.Milnor.glueX (cappedDatum F hF))
          (Work.Cohomology.subtypeIncl (Work.Milnor.glueX (cappedDatum F hF))
            (Work.Milnor.glueU (cappedDatum F hF))) 4
        ≫ Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
            (TopCat.of ↥(Work.Milnor.glueU (cappedDatum F hF)))
            (Work.Cohomology.Endgame.CappedTransfer.fU (cappedDatum F hF)) 4 := by
    rw [cappedRestriction, cappedIncl,
      ← Work.Cohomology.Endgame.CappedTransfer.fU_comp_subtypeIncl (cappedDatum F hF)]
    exact Work.Cohomology.singularCohomologyMap_comp ℤ _ _ 4
  rw [hcomp]
  refine Work.Cohomology.Endgame.CappedTransfer.surjective_comp _ _ ?_ ?_
  · exact (ModuleCat.epi_iff_surjective _).mp
      (Work.Cohomology.Endgame.CappedTransfer.epi_singularCohomologyMap_subtypeIncl
        (cappedDatum F hF) (cappedDatum_U F hF))
  · haveI : IsIso (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of (Submission.Milnor.Vk (-2)))
        (TopCat.of ↥(Work.Milnor.glueU (cappedDatum F hF)))
        (Work.Cohomology.Endgame.CappedTransfer.fU (cappedDatum F hF)) 4) :=
      Work.Cohomology.Endgame.CappedTransfer.isIso_singularCohomologyMap_homeo
        (Work.Cohomology.Endgame.CappedTransfer.eU (cappedDatum F hF)) 4
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- **The restriction to the disc bundle is injective** (both sides are `ℤ` and a surjective
`ℤ`-linear map `ℤ → ℤ` is bijective). -/
theorem cappedRestriction_injective : Function.Injective (cappedRestriction F hF).hom := by
  have hψ : Function.Surjective ((cappedH4Iso F hF).inv ≫ cappedRestriction F hF
      ≫ (discH4Iso).hom).hom := by
    intro z
    obtain ⟨y, hy⟩ := cappedRestriction_surjective F hF (ModuleCat.Hom.hom discH4Iso.inv z)
    refine ⟨ModuleCat.Hom.hom (cappedH4Iso F hF).hom y, ?_⟩
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [iso_inv_apply_hom, hy, iso_hom_apply_inv]
  have hbij := bijective_of_surjective_int _ hψ
  intro a b hab
  have h2 : ((cappedH4Iso F hF).inv ≫ cappedRestriction F hF ≫ (discH4Iso).hom).hom
      (ModuleCat.Hom.hom (cappedH4Iso F hF).hom a) =
      ((cappedH4Iso F hF).inv ≫ cappedRestriction F hF ≫ (discH4Iso).hom).hom
        (ModuleCat.Hom.hom (cappedH4Iso F hF).hom b) := by
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [iso_inv_apply_hom, iso_inv_apply_hom, hab]
  have h3 := congrArg (ModuleCat.Hom.hom (cappedH4Iso F hF).inv) (hbij.1 h2)
  rw [iso_inv_apply_hom, iso_inv_apply_hom] at h3
  exact h3

/-- **The restriction `H⁴(X;ℤ) → H⁴(D(ξ);ℤ)` is an isomorphism.** -/
theorem cappedRestriction_isIso : IsIso (cappedRestriction F hF) := by
  haveI : Mono (cappedRestriction F hF) :=
    (ModuleCat.mono_iff_injective _).mpr (cappedRestriction_injective F hF)
  haveI : Epi (cappedRestriction F hF) :=
    (ModuleCat.epi_iff_surjective _).mpr (cappedRestriction_surjective F hF)
  exact isIso_of_mono_of_epi (cappedRestriction F hF)

/-! ## The Pontryagin class of `TX` -/

/-- The first Pontryagin class of Milnor's bundle, as an integer: the number computed in this
chapter, `Work.Milnor.p1_xi` (i.e. `p₁(ξ) = 6`). -/
def p1Xi : ℤ := (Work.CharacteristicClasses.SpinBundle.xi).pontryagin1

/-- The number `p1Xi` is `6` (`Work.Milnor.p1_xi`): this is *the* computation of this chapter. -/
theorem p1Xi_eq_six : p1Xi = 6 := Work.Milnor.p1_xi

/-- **The first Pontryagin class of the tangent bundle of `X = D(ξ) ∪_F D⁸`**, as a class in
`H⁴(X;ℤ)`: the unique class whose restriction to the disc bundle is `p₁(ξ) · τ = 6 · τ`.

Geometrically `TX|_{{D(ξ)}} ≅ π*(TS⁴ ⊕ ξ)`, so the restriction of `p₁(TX)` is
`p₁(TS⁴ ⊕ ξ) = p₁(TS⁴) + p₁(ξ) = p₁(ξ) = 6` (Whitney additivity, with `p₁(TS⁴) = 0`; the value
`p₁(ξ) = 6` is `Work.Milnor.p1_xi` of this chapter), tensored with the generator `τ`.  That
identification of the tangent bundle is the one classical input this chapter cannot formalise (the
workspace has no tangent-bundle characteristic classes); everything else is proved. -/
def cappedPontryaginClass : cappedH4 F hF :=
  Classical.choose (cappedRestriction_surjective F hF ((6 : ℤ) • tauD))

/-- **The restriction of `p₁(TX)` to the disc bundle is `6 · τ`** (`= p₁(ξ) · τ`). -/
theorem cappedPontryaginClass_restriction :
    (cappedRestriction F hF).hom (cappedPontryaginClass F hF) = (6 : ℤ) • tauD :=
  Classical.choose_spec (cappedRestriction_surjective F hF ((6 : ℤ) • tauD))

/-- The class is determined by its restriction to the disc bundle (the restriction is injective). -/
theorem cappedPontryaginClass_unique {P : cappedH4 F hF}
    (hP : (cappedRestriction F hF).hom P = (6 : ℤ) • tauD) :
    P = cappedPontryaginClass F hF :=
  cappedRestriction_injective F hF (by rw [hP, cappedPontryaginClass_restriction])

/-- **The coefficient of `p₁(TX)` in a generator of `H⁴(X;ℤ) ≅ ℤ` is `±6`.**  For every generator
`x` of `H⁴(X;ℤ) ≅ ℤ` (every class is an integer multiple of `x`), the class
`cappedPontryaginClass = p₁(TX)` is `±6 · x`; the sign is the choice of orientation of `x`.

This is what the endgame `Work.SignatureBordism.capped_obstruction_of_selfIntersection` consumes as
`p₁ = q • x` with `q = ±6`. -/
theorem cappedPontryaginClass_eq_pm_six (x : cappedH4 F hF)
    (hx : ∀ z : cappedH4 F hF, ∃ a : ℤ, z = a • x) :
    cappedPontryaginClass F hF = (6 : ℤ) • x ∨ cappedPontryaginClass F hF = -((6 : ℤ) • x) := by
  have hρx : (cappedRestriction F hF).hom x = tauD ∨ (cappedRestriction F hF).hom x = -tauD :=
    eq_pm_of_generates discH4Iso tauD ((cappedRestriction F hF).hom x) generates_tauD
      (generates_map (cappedRestriction F hF) (cappedRestriction_surjective F hF) hx)
  rcases hρx with h | h
  · left
    apply cappedRestriction_injective F hF
    rw [cappedPontryaginClass_restriction]
    have h2 : ModuleCat.Hom.hom (cappedRestriction F hF) ((6 : ℤ) • x) = (6 : ℤ) • tauD := by
      have h3 := map_zsmul (ModuleCat.Hom.hom (cappedRestriction F hF)) (6 : ℤ) x
      rw [h] at h3
      exact h3
    rw [h2]
  · right
    apply cappedRestriction_injective F hF
    rw [cappedPontryaginClass_restriction, map_neg]
    have h2 : ModuleCat.Hom.hom (cappedRestriction F hF) ((6 : ℤ) • x) = -((6 : ℤ) • tauD) := by
      have h3 := map_zsmul (ModuleCat.Hom.hom (cappedRestriction F hF)) (6 : ℤ) x
      rw [h] at h3
      rw [h3, zsmul_neg]
    rw [h2, neg_neg]

/-- **The coefficient form consumed by the endgame.**  For every generator `x` of `H⁴(X;ℤ) ≅ ℤ`
there is `q ∈ {6, -6}` with `p₁(TX) = q • x`. -/
theorem cappedPontryaginClass_six (x : cappedH4 F hF)
    (hx : ∀ z : cappedH4 F hF, ∃ a : ℤ, z = a • x) :
    ∃ q : ℤ, (q = 6 ∨ q = -6) ∧ cappedPontryaginClass F hF = q • x := by
  rcases cappedPontryaginClass_eq_pm_six F hF x hx with h | h
  · exact ⟨6, Or.inl rfl, h⟩
  · refine ⟨-6, Or.inr rfl, ?_⟩
    rw [h]
    exact (by rw [neg_zsmul] : (-6 : ℤ) • x = -((6 : ℤ) • x)).symm

/-- **The injective form.**  Any class `P ∈ H⁴(X;ℤ)` whose restriction to the disc bundle is
`6 · τ` — any class playing the role of `p₁(TX)` — is `±6 · x` for every generator `x` of
`H⁴(X;ℤ) ≅ ℤ`; a future session with a geometric definition of `p₁(TX)` can instantiate this. -/
theorem capped_pontryagin_class_of_restriction (P : cappedH4 F hF) (x : cappedH4 F hF)
    (hP : (cappedRestriction F hF).hom P = (6 : ℤ) • tauD)
    (hx : ∀ z : cappedH4 F hF, ∃ a : ℤ, z = a • x) :
    P = (6 : ℤ) • x ∨ P = -((6 : ℤ) • x) := by
  rw [cappedPontryaginClass_unique F hF hP]
  exact cappedPontryaginClass_eq_pm_six F hF x hx

/-- **The injective form, as the endgame uses it**: `p₁(TX) = q • x` with `q = ±6`. -/
theorem capped_pontryagin_class_six_of_restriction (P : cappedH4 F hF) (x : cappedH4 F hF)
    (hP : (cappedRestriction F hF).hom P = (6 : ℤ) • tauD)
    (hx : ∀ z : cappedH4 F hF, ∃ a : ℤ, z = a • x) :
    ∃ q : ℤ, (q = 6 ∨ q = -6) ∧ P = q • x := by
  rw [cappedPontryaginClass_unique F hF hP]
  exact cappedPontryaginClass_six F hF x hx

end

end Work.Milnor
