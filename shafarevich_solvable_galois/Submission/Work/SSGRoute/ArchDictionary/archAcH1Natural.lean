import Mathlib
import Submission.Work.SSGRoute.ArchNat.archUniformNatural
import Submission.Work.SSGRoute.ArchDictionary.ac_addEquiv_H1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality in the coefficient of the archimedean `H¹` dictionary

`Work.SSGRoute.ArchDictionary.Ac K E c` is `H¹(⟨c⟩, E)` in the concrete shape
`Z¹(⟨c⟩,E)/B¹(⟨c⟩,E)` (cocycles on the cyclic subgroup `⟨c⟩` of `Gal(Ω/k)`, viewed as functions on
the whole Galois group).  `ac_addEquiv_H1` shows that this is *isomorphic* to the abstract
`Work.GroupCohomology.H1 ↥⟨c⟩ E` for every coefficient module `E`, but the isomorphism produced
there is chosen at each `E` separately and is not *natural*.

The present file builds **the canonical** isomorphism `acH1Equiv K c E : Ac K E c ≃+ H¹(⟨c⟩,E)` —
the restriction of a cocycle on `⟨c⟩` to `⟨c⟩`, followed by the quotient map — and proves that it
squares with the naturality maps of the coefficient: `ArchNat.AcMap` on the `Ac` side and
`GroupCohomology.mapH1` on the `H¹` side.  This is precisely the content of
`Work.SSGRoute.ArchDictionary.archAcH1Natural`.
-/

namespace Work.SSGRoute.ArchDictionary

open Work.SSGRoute

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- The action of `Ω ≃ₐ[k] Ω` on a `Gal(↥K/k)`-module `E`, pulled back along `res k K`. -/
abbrev resAct (K : IntermediateField k Ω) [Normal k K]
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    DistribMulAction (Ω ≃ₐ[k] Ω) E :=
  DistribMulAction.compHom E (SSGRoute.res k K)

/-- The `DistribMulAction` of the cyclic subgroup `⟨c⟩` on `E`, induced by `res k K`. -/
abbrev cycAct (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    DistribMulAction ↥(Subgroup.zpowers c) E :=
  @Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
    (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c)

/-- `Z¹(⟨c⟩, E)` with the action of `⟨c⟩` induced by `res k K`. -/
abbrev Z1c (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    AddSubgroup (↥(Subgroup.zpowers c) → E) :=
  @Work.GroupCohomology.Z1 ↥(Subgroup.zpowers c) E _ _ (cycAct K c E)

/-- `B¹(⟨c⟩, E)` with the action of `⟨c⟩` induced by `res k K`. -/
abbrev B1c (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    AddSubgroup (↥(Subgroup.zpowers c) → E) :=
  @Work.GroupCohomology.B1 ↥(Subgroup.zpowers c) E _ _ (cycAct K c E)

/-- `H¹(⟨c⟩, E)` with the action of `⟨c⟩` induced by `res k K`. -/
abbrev H1c (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] : Type :=
  @Work.GroupCohomology.H1 ↥(Subgroup.zpowers c) E _ _ (cycAct K c E)

/-- The quotient map `Z¹(⟨c⟩,E) → H¹(⟨c⟩,E)`. -/
abbrev H1πc (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    ↥(Z1c K c E) →+ H1c K c E :=
  @Work.GroupCohomology.H1π ↥(Subgroup.zpowers c) E _ _ (cycAct K c E)

/-- The restriction of a `1`-cocycle on `⟨c⟩` (a function on the whole Galois group) to the
subgroup `⟨c⟩`. -/
def acRho (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    ↥(Zc K E c) →+ ↥(Z1c K c E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  refine
    { toFun := fun b =>
        ⟨fun g => (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω), ?_⟩
      map_zero' := ?_
      map_add' := ?_ }
  · intro g h
    have hb := (b.2 : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
      (b : (Ω ≃ₐ[k] Ω) → E)) (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
    show (b : (Ω ≃ₐ[k] Ω) → E) ((g : ↥(Subgroup.zpowers c)) * h : ↥(Subgroup.zpowers c)) =
      g • ((b : (Ω ≃ₐ[k] Ω) → E) (h : Ω ≃ₐ[k] Ω)) +
        (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω)
    rw [Subgroup.coe_mul, hb, Subgroup.smul_def]
    exact add_comm _ _
  · apply Subtype.ext
    funext g
    rfl
  · intro a b
    apply Subtype.ext
    funext g
    rfl

/-- The zero-extension of a crossed homomorphism on `⟨c⟩` to the whole Galois group (a section
of `acRho`). -/
def acPsi (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    ↥(Z1c K c E) → ↥(Zc K E c) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  refine fun f =>
    ⟨fun g => if hg : g ∈ Subgroup.zpowers c then
        (f : ↥(Subgroup.zpowers c) → E) ⟨g, hg⟩ else 0, ?_⟩
  intro g hg h hh
  have hmul : g * h ∈ Subgroup.zpowers c := (Subgroup.zpowers c).mul_mem hg hh
  have hf := (f.2 : Work.GroupCohomology.IsCrossedHom ↥(Subgroup.zpowers c) E
    (f : ↥(Subgroup.zpowers c) → E)) ⟨g, hg⟩ ⟨h, hh⟩
  show (if hg : g * h ∈ Subgroup.zpowers c then
      (f : ↥(Subgroup.zpowers c) → E) ⟨g * h, hg⟩ else 0) =
    (if hg : g ∈ Subgroup.zpowers c then (f : ↥(Subgroup.zpowers c) → E) ⟨g, hg⟩ else 0) +
      (SSGRoute.res k K) g •
        (if hg : h ∈ Subgroup.zpowers c then (f : ↥(Subgroup.zpowers c) → E) ⟨h, hg⟩ else 0)
  rw [dif_pos hmul, dif_pos hg, dif_pos hh,
    show (⟨g * h, hmul⟩ : ↥(Subgroup.zpowers c)) = ⟨g, hg⟩ * ⟨h, hh⟩ from Subtype.ext rfl,
    hf, Subgroup.smul_def]
  exact add_comm _ _

theorem acRho_psi (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (f : ↥(Z1c K c E)) : acRho K c E (acPsi K c E f) = f := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  apply Subtype.ext
  funext g
  show (if hg : (g : Ω ≃ₐ[k] Ω) ∈ Subgroup.zpowers c then
      (f : ↥(Subgroup.zpowers c) → E) ⟨(g : Ω ≃ₐ[k] Ω), hg⟩ else 0) =
    (f : ↥(Subgroup.zpowers c) → E) g
  rw [dif_pos g.2]

theorem acRho_surjective (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Function.Surjective (acRho K c E) :=
  fun f => ⟨acPsi K c E f, acRho_psi K c E f⟩

/-- `B¹(⟨c⟩,E)` consists of the maps `g ↦ res(g) • a - a`. -/
theorem acMemB1 (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (f : ↥(Subgroup.zpowers c) → E) :
    f ∈ B1c K c E ↔ ∃ a : E, ∀ g : ↥(Subgroup.zpowers c),
      f g = (SSGRoute.res k K) (g : Ω ≃ₐ[k] Ω) • a - a := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  rw [B1c, Work.GroupCohomology.mem_B1_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun g => ?_⟩
    rw [← ha, Work.GroupCohomology.d0_apply, Subgroup.smul_def]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨a, funext fun g => ?_⟩
    rw [Work.GroupCohomology.d0_apply, ha g, Subgroup.smul_def]
    rfl

theorem acRho_mem_B1_iff (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] (b : ↥(Zc K E c)) :
    ((acRho K c E b : ↥(Z1c K c E)) : ↥(Subgroup.zpowers c) → E) ∈ B1c K c E ↔
      b ∈ Bc K E c := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  rw [acMemB1, mem_Bc]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun g hg => ?_⟩
    have h1 : (b : (Ω ≃ₐ[k] Ω) → E) g
        = (acRho K c E b : ↥(Subgroup.zpowers c) → E) ⟨g, hg⟩ := rfl
    rw [h1, ha ⟨g, hg⟩]
  · rintro ⟨m, hm⟩
    refine ⟨m, fun g => ?_⟩
    show (b : (Ω ≃ₐ[k] Ω) → E) (g : Ω ≃ₐ[k] Ω)
      = (SSGRoute.res k K) (g : Ω ≃ₐ[k] Ω) • m - m
    rw [hm (g : Ω ≃ₐ[k] Ω) g.2]

theorem acH1π_eq_zero_iff (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] (g : ↥(Z1c K c E)) :
    H1πc K c E g = 0 ↔ (g : ↥(Subgroup.zpowers c) → E) ∈ B1c K c E := by
  rw [H1πc, Work.GroupCohomology.H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_comap]
  exact Iff.rfl

/-- The composite `Z¹(⟨c⟩,E) → H¹(⟨c⟩,E)`. -/
def acTheta (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    ↥(Zc K E c) →+ H1c K c E :=
  (H1πc K c E).comp (acRho K c E)

theorem acTheta_ker (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    (acTheta K c E).ker = Bc K E c := by
  ext b
  rw [AddMonoidHom.mem_ker]
  show H1πc K c E (acRho K c E b) = 0 ↔ b ∈ Bc K E c
  rw [acH1π_eq_zero_iff, acRho_mem_B1_iff]

theorem acTheta_surjective (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Function.Surjective (acTheta K c E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := resAct K E
  intro y
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk'_surjective
    ((B1c K c E).comap (Z1c K c E).subtype) y
  refine ⟨acPsi K c E f, ?_⟩
  show H1πc K c E (acRho K c E (acPsi K c E f)) = y
  rw [acRho_psi]
  exact hf

/-- **The canonical isomorphism `Z¹(⟨c⟩,E)/B¹(⟨c⟩,E) ≅ H¹(⟨c⟩,E)`**, i.e. the comparison map
`ArchDictionary.Ac K E c →+ GroupCohomology.H1 ↥⟨c⟩ E`. -/
def acToH1 (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Ac (K := K) (E := E) c →+ H1c K c E :=
  QuotientAddGroup.lift (Bc K E c) (acTheta K c E) (acTheta_ker K c E).ge

theorem acToH1_mk (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] (x : ↥(Zc K E c)) :
    acToH1 K c E (QuotientAddGroup.mk' (Bc K E c) x) = H1πc K c E (acRho K c E x) := by
  change QuotientAddGroup.lift (Bc K E c) (acTheta K c E) (acTheta_ker K c E).ge
    (QuotientAddGroup.mk' (Bc K E c) x) = H1πc K c E (acRho K c E x)
  exact QuotientAddGroup.lift_mk' (Bc K E c) _ x

theorem acToH1_injective (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Function.Injective (acToH1 K c E) := by
  intro x y hxy
  obtain ⟨x0, rfl⟩ := QuotientAddGroup.mk'_surjective (Bc K E c) x
  obtain ⟨y0, rfl⟩ := QuotientAddGroup.mk'_surjective (Bc K E c) y
  rw [acToH1_mk, acToH1_mk] at hxy
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  have h1 : H1πc K c E (acRho K c E x0 - acRho K c E y0) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h2 : ((acRho K c E x0 - acRho K c E y0 : ↥(Z1c K c E)) :
      ↥(Subgroup.zpowers c) → E) ∈ B1c K c E :=
    (acH1π_eq_zero_iff K c E _).mp h1
  have h3 : acRho K c E x0 - acRho K c E y0 = acRho K c E (x0 - y0) :=
    (map_sub (acRho K c E) x0 y0).symm
  rw [h3] at h2
  exact (acRho_mem_B1_iff K c E (x0 - y0)).mp h2

theorem acToH1_surjective (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Function.Surjective (acToH1 K c E) := by
  intro y
  obtain ⟨z, hz⟩ := acTheta_surjective K c E y
  refine ⟨QuotientAddGroup.mk' (Bc K E c) z, ?_⟩
  rw [acToH1_mk]
  exact hz

/-- **The canonical, natural isomorphism `Ac K E c ≃+ H¹(⟨c⟩,E)`.** -/
noncomputable def acH1Equiv (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E] :
    Ac (K := K) (E := E) c ≃+ H1c K c E :=
  AddEquiv.ofBijective (acToH1 K c E) ⟨acToH1_injective K c E, acToH1_surjective K c E⟩

theorem acH1Equiv_apply (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (x : Ac (K := K) (E := E) c) :
    acH1Equiv K c E x = acToH1 K c E x :=
  AddEquiv.ofBijective_apply _ _ x

/-- `AcMap` on the class of a cocycle. -/
theorem acMap_mk (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (E₂ : Type) [AddCommGroup E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    (f : E →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (y : ↥(Zc K E c)) :
    Work.SSGRoute.ArchNat.AcMap f hf c (QuotientAddGroup.mk' (Bc K E c) y) =
      QuotientAddGroup.mk' (Bc K E₂ c)
        ⟨fun σ => f ((y : (Ω ≃ₐ[k] Ω) → E) σ),
          Work.SSGRoute.ArchNat.mem_Zc_of_equivariant f hf y.2⟩ := by
  unfold Work.SSGRoute.ArchNat.AcMap
  exact QuotientAddGroup.lift_mk' (Bc K E c) _ y

/-- **Naturality of the canonical isomorphism in the coefficient.** -/
theorem acH1Equiv_natural (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω)
    (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
    (E₂ : Type) [AddCommGroup E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    (f : E →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (hfe : @Work.GroupCohomology.IsEquivariant ↥(Subgroup.zpowers c) E E₂ _ _ _
      (cycAct K c E) (cycAct K c E₂) f)
    (x : Ac (K := K) (E := E) c) :
    acH1Equiv K c E₂ (Work.SSGRoute.ArchNat.AcMap f hf c x) =
      @Work.GroupCohomology.mapH1 ↥(Subgroup.zpowers c) E E₂ _ _ _
        (cycAct K c E) (cycAct K c E₂) f hfe (acH1Equiv K c E x) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (Bc K E c) x
  rw [acMap_mk]
  rw [acH1Equiv_apply, acH1Equiv_apply]
  rw [acToH1_mk, acToH1_mk]
  rw [Work.GroupCohomology.mapH1_H1π]
  congr 1

/-- **The archimedean `H¹` dictionary is natural in the coefficient module.**

There is a single family of additive isomorphisms `Ac K E c ≃+ H¹(⟨c⟩,E)`, defined uniformly in `E`,
which intertwines the map induced on `Ac` by an additive equivariant map `f : E →+ E₂` with
`GroupCohomology.mapH1`. -/
theorem archAcH1Natural (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (c : Ω ≃ₐ[k] Ω) :
    ∃ e : ∀ (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E],
        Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c ≃+
          @Work.GroupCohomology.H1 ↥(Subgroup.zpowers c) E _ _
            (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
              (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c)),
      ∀ (E : Type) [AddCommGroup E] [DistribMulAction (K ≃ₐ[k] K) E]
        (E₂ : Type) [AddCommGroup E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        (f : E →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (hfe : @Work.GroupCohomology.IsEquivariant ↥(Subgroup.zpowers c) E E₂ _ _ _
          (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c))
          (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E₂ _ _
            (DistribMulAction.compHom E₂ (SSGRoute.res k K)) (Subgroup.zpowers c)) f)
        (x : Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c),
        e E₂ (Work.SSGRoute.ArchNat.AcMap f hf c x) =
          @Work.GroupCohomology.mapH1 ↥(Subgroup.zpowers c) E E₂ _ _ _
            (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
              (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers c))
            (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E₂ _ _
              (DistribMulAction.compHom E₂ (SSGRoute.res k K)) (Subgroup.zpowers c))
            f hfe (e E x) := by
  classical
  refine ⟨fun E => acH1Equiv K c E, ?_⟩
  intro E instA instD E₂ instA₂ instD₂ f hf hfe x
  exact acH1Equiv_natural K c E E₂ f hf hfe x

end

end Work.SSGRoute.ArchDictionary
