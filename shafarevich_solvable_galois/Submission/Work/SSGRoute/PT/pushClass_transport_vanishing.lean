import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.local_duality_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

-- Instance discipline: the `Coeff`-module structure on the underlying type of a representation must
-- be the one stored in the representation (`Rep.hV2`), not one of the competing `ULift` structures
-- on `Coeff = ULift ℤ`.  (Same discipline as `powHomRepDefs`/`local_duality_ext`.)
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

-- **The transport of a `pushClass_lde` class is a `pushClass_lde` class.**  For a group map
-- `f : H →* G` and a coefficient map `ι : Rep.res f A ⟶ B`, the composition
-- `(extRes f (pushClass_lde p A φ)) ∘ mk₀ ι` — a class in `Ext¹_H(𝔽_p, B)` — is the pushout of the
-- coefficient sequence at the level `H` along the pushed-forward coefficient map
-- `(Rep.resFunctor f).map φ ≫ ι`.
--
-- This is the `mapExactFunctor_extClass` + `mk₀_comp_mk₀` + associativity computation, spelled out
-- inline (a scratch copy lives at `Submission/Work/SSGRoute/PT/extRes_pushClass_comp.lean`).
set_option backward.isDefEq.respectTransparency false in
lemma extRes_pushClass_lde_comp {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) {A : Rep Coeff G} {B : Rep Coeff H} (ι : Rep.res f A ⟶ B)
    (φ : unitRep G ⟶ A) :
    (SSGRoute.PTExt.extRes f (Work.SSGRoute.pushClass_lde p A φ)).comp
      (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1)
      = Work.SSGRoute.pushClass_lde p B ((Rep.resFunctor f).map φ ≫ ι) := by
  have hext : ((Work.SSGRoute.Phi1.coeffSES_shortExact G p).extClass).mapExactFunctor
      (Rep.resFunctor f) = (Work.SSGRoute.Phi1.coeffSES_shortExact H p).extClass := by
    rw [CategoryTheory.Abelian.Ext.mapExactFunctor_extClass]
  simp only [Work.SSGRoute.pushClass_lde, SSGRoute.PTExt.extRes,
    CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀, hext,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
    CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero]

/-- A `G`-map out of the trivial representation is `ℤ`-linear on `1`: `ψ c = c • ψ 1`. -/
lemma rep_hom_apply_eq_smul_one {G : Type} [Group G] {A : Rep Coeff G} (ψ : unitRep G ⟶ A)
    (c : Coeff) : ψ.hom c = c • ψ.hom (1 : Coeff) := by
  have h : ψ.hom c = ψ.hom (c • (1 : Coeff)) := by rw [smul_eq_mul, mul_one]
  rw [h, LinearMapClass.map_smul]

/-- **The `𝔽_p`-node of the archimedean level transport.**  Let `f : H →* G` be surjective,
`ι : Rep.res f A ⟶ B` injective, and every `H`-fixed point of `B` in the image of `ι` (the "local
invariants" input `globalCFT_localFixed_infinite`).  Then the transport of
`pushClass_lde p A φ ∈ Ext¹_G(𝔽_p, A)`, namely
`(extRes f (pushClass_lde p A φ)) ∘ mk₀ ι ∈ Ext¹_H(𝔽_p, B)`, vanishes only if
`pushClass_lde p A φ = 0`.

Route (both reviewers approved this statement; the same argument is the `hfp` hole of
`Submission.Work.SSGRoute.PT.archLevelPair_injective`, where the steps were verified individually
but the map-equality step hit instance-synthesis trouble — use `Rep.hom_ext` + `funext` on coerced
functions, not `Representation.IntertwiningMap.ext`/`LinearMap.ext`).
First identify `(extRes f (pushClass_lde p A φ)) ∘ mk₀ ι` with
`pushClass_lde p B ((Rep.resFunctor f).map φ ≫ ι)` — the `mapExactFunctor_extClass` +
`mk₀_comp_mk₀` + associativity computation, done **inline** with
`set_option backward.isDefEq.respectTransparency false in` (do not import
`Submission.Work.SSGRoute.PT.extRes_pushClass_comp`, that file is a reviewer scratch copy).
Then apply `Work.SSGRoute.pushClass_lde_eq_zero_iff_factors` at `H`:
`(res f φ) ≫ ι = unitMulByP H p ≫ ψ`.  Evaluating at `1 : Coeff` (`Rep.hom_comp`,
`Representation.IntertwiningMap.comp_apply`, `SSGRoute.Phi1.unitMulByP_apply`, `mul_one`, then
`map_smul` after rewriting `(p : Coeff) = (p : Coeff) • 1`) gives `ι (φ 1) = p • ψ 1`;
`ψ 1 ∈ B^H` (`Rep.hom_comm_apply` and triviality of the `unitRep H`-action), so `hinv` writes
`ψ 1 = ι a`; then `φ 1 = p • a` (`hι`, `map_smul`); `a ∈ A^G` because `f` is surjective (`hf`);
hence `φ = unitMulByP G p ≫ Work.SSGRoute.powHomRep a _` (pointwise: `φ.hom c = c • φ.hom 1
= c • (p • a) = (c * p) • a = (p * c) • a`), and `pushClass_lde_eq_zero_iff_factors` at `G` gives
the conclusion. -/
theorem pushClass_transport_vanishing {G H : Type} [Group G] [Group H] (p : ℕ) [Fact p.Prime]
    (f : H →* G) (hf : Function.Surjective f) {A : Rep Coeff G} {B : Rep Coeff H}
    (ι : Rep.res f A ⟶ B)
    (hι : Function.Injective (fun a => ι.hom a))
    (hinv : ∀ b : B.V, (∀ h : H, B.ρ h b = b) → ∃ a : A.V, ι.hom a = b)
    (φ : unitRep G ⟶ A) :
    (SSGRoute.PTExt.extRes f (Work.SSGRoute.pushClass_lde p A φ)).comp
        (CategoryTheory.Abelian.Ext.mk₀ ι) (add_zero 1) = 0 →
      Work.SSGRoute.pushClass_lde p A φ = 0 := by
  intro hx
  -- Step 1: the transport of a `pushClass_lde` class is the `pushClass_lde` class of `res f φ ≫ ι`.
  rw [extRes_pushClass_lde_comp p f ι φ] at hx
  -- Step 2: `pushClass_lde_eq_zero_iff_factors` at the level `H`.
  obtain ⟨ψ, hψ⟩ := (Work.SSGRoute.pushClass_lde_eq_zero_iff_factors p B _).mp hx
  -- `ψ.hom 1` is `H`-fixed (`ψ` is a map out of the trivial module).
  have hfixψ : ∀ h : H, B.ρ h (ψ.hom 1) = ψ.hom 1 := by
    intro h
    have hc := Rep.hom_comm_apply ψ h (1 : Coeff)
    simpa using hc.symm
  -- Every value of `ψ` is `c • ψ 1`.
  have hψeval : ∀ c : Coeff, ψ.hom c = c • ψ.hom (1 : Coeff) :=
    fun c => rep_hom_apply_eq_smul_one ψ c
  -- Step 3: evaluate `(res f φ) ≫ ι = unitMulByP H p ≫ ψ` at `1`.
  have hψ' : ((Rep.resFunctor f).map φ ≫ ι : unitRep H ⟶ B)
      = (Work.SSGRoute.Phi1.unitMulByP H p ≫ ψ : unitRep H ⟶ B) := hψ
  have h := congrArg (fun (k : unitRep H ⟶ B) => (Rep.Hom.hom k) (1 : Coeff)) hψ'
  have hL : (Rep.Hom.hom ((Rep.resFunctor f).map φ ≫ ι)) (1 : Coeff) = ι.hom (φ.hom 1) := by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, Rep.resMap_hom_apply]
  have hR : (Rep.Hom.hom (Work.SSGRoute.Phi1.unitMulByP H p ≫ ψ)) (1 : Coeff)
      = (p : Coeff) • ψ.hom 1 := by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
      Work.SSGRoute.Phi1.unitMulByP_apply, hψeval, mul_one]
  have h1 : ι.hom (φ.hom 1) = (p : Coeff) • ψ.hom 1 := hL.symm.trans (h.trans hR)
  -- Step 4: `hinv` writes `ψ 1 = ι a` with `a : A`.
  obtain ⟨a, ha⟩ := hinv (ψ.hom 1) hfixψ
  -- Step 5: `φ 1 = p • a`.
  have hφ1 : φ.hom (1 : Coeff) = (p : Coeff) • a := by
    apply hι
    change ι.hom (φ.hom 1) = ι.hom ((p : Coeff) • a)
    rw [h1, ← ha, LinearMapClass.map_smul]
  -- Step 6: `a` is `G`-fixed, using that `f` is surjective.
  have hafixG : ∀ g : G, A.ρ g a = a := by
    intro g
    obtain ⟨h, rfl⟩ := hf g
    apply hι
    change ι.hom (A.ρ (f h) a) = ι.hom a
    have hc := Rep.hom_comm_apply ι h a
    rw [Rep.coe_res_obj_ρ'] at hc
    rw [hc, ha, hfixψ h]
  -- Step 7: `φ = unitMulByP G p ≫ powHomRep a`, pointwise.
  have hφfac : φ = SSGRoute.Phi1.unitMulByP G p ≫ Work.SSGRoute.powHomRep a hafixG := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    show φ.hom c
      = (Rep.Hom.hom (SSGRoute.Phi1.unitMulByP G p ≫ Work.SSGRoute.powHomRep a hafixG)) c
    rw [rep_hom_apply_eq_smul_one φ c, hφ1, Rep.hom_comp,
      Representation.IntertwiningMap.comp_apply,
      Work.SSGRoute.Phi1.unitMulByP_apply, Work.SSGRoute.powHomRep_apply,
      smul_smul, mul_comm]
  -- Step 8: `pushClass_lde_eq_zero_iff_factors` at the level `G`.
  rw [Work.SSGRoute.pushClass_lde_eq_zero_iff_factors p A φ]
  exact ⟨Work.SSGRoute.powHomRep a hafixG, hφfac⟩

end Work.SSGRoute.PT
