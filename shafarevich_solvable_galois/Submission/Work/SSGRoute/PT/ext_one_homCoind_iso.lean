import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.ext_h1_bridge
import Submission.Work.SSGRoute.ext_level_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext¹_G(X, Kˣ) ≅ H¹(Γ, Hom_ℤ(X, Ωˣ))`

For a number field `k`, an algebraic closure `Ω/k` with `Γ = Gal(Ω/k)`, a finite Galois
subextension `K/k` with `G = Gal(K/k)`, and a `G`-module `X` (a `Rep Coeff G`) which is finitely
generated as a `ℤ`-module, the group `Ext¹_G(X, Kˣ)` is identified with the continuous cohomology
`H¹(Γ, Hom_ℤ(X.V, Ωˣ))` for the conjugation action `(σ·φ)x = σ·φ((σ|_K)⁻¹ · x)`.

The proof runs the *two* long exact sequences attached to a finite free cover
`0 → X₁ → F → X → 0` of `X`:

* the `Ext`-sequence in the first variable of `Hom(-, Kˣ)`: `Ext⁰(X₁,Kˣ) ↠ Ext¹(X,Kˣ)` with
  kernel `im(Ext⁰(F,Kˣ) → Ext⁰(X₁,Kˣ))` (the middle term is projective);
* the cohomology sequence of the induced short exact sequence of discrete `Γ`-modules
  `0 → Hom(X,Ωˣ) → Hom(F,Ωˣ) → Hom(X₁,Ωˣ) → 0` (right exactness is divisibility of `Ωˣ`):
  `H⁰(Hom(X₁,Ωˣ)) ↠ H¹(Hom(X,Ωˣ))`, whose middle term vanishes by Shapiro + Hilbert 90.

The two `H⁰`-groups are identified by `homRep_unitsK_formula` (`Hom_Rep(M, Kˣ) ≅ Hom(X,Ωˣ)^Γ`),
with its naturality (`homRep_unitsK_formula_natural`) making the identification compatible with the
two maps out of `H⁰(Hom(F,Ωˣ))`; the first isomorphism theorem then assembles the equivalence.

This is the abstract form of the `hExtHomCoind` step used inside `ext_h1_bridge`.
-/

open CategoryTheory

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace Work.SSGRoute.PT

open SSGRoute.PTExt

noncomputable section

theorem ext_one_homCoind_iso (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ X.V] :
    Nonempty (CategoryTheory.Abelian.Ext X (SSGRoute.PTExt.unitsK k K) 1 ≃+
      Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K X)) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  obtain ⟨n, pic, hpic⟩ :=
    repFG_free_cover (G := K ≃ₐ[k] K) X (show RepFG X from ‹Module.Finite ℤ X.V›)
  let S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)) :=
    ShortComplex.mk (Limits.kernel.ι pic) pic (Limits.kernel.condition pic)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel pic) inferInstance hpic
  have hExt := ext_connecting_range_ker hS (unitsK k K)
  -- the connecting map `Ext⁰(R,Kˣ) ↠ Ext¹(X,Kˣ)` and its kernel
  let ΦE : Abelian.Ext S.X₁ (unitsK k K) 0 →+ Abelian.Ext X (unitsK k K) 1 :=
    hS.extClass.precomp (unitsK k K) (by norm_num : 1 + 0 = 1)
  have hΦEsurj : Function.Surjective ΦE := (AddMonoidHom.range_eq_top).mp hExt.1
  let pre : Abelian.Ext S.X₂ (unitsK k K) 0 →+ Abelian.Ext S.X₁ (unitsK k K) 0 :=
    (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
  have hΦEker : ΦE.ker = pre.range := hExt.2
  -- ===== the cohomology side =====
  have hfsurj : Function.Surjective (Rep.Hom.hom pic) := (Rep.epi_iff_surjective pic).mp hpic
  let uHom : S.X₁.V →+ S.X₂.V :=
    { toFun := fun x => Rep.Hom.hom S.f x
      map_zero' := map_zero (Rep.Hom.hom S.f)
      map_add' := fun a b => map_add (Rep.Hom.hom S.f) a b }
  let gFun : homCoind k Ω K S.X₂ →+ homCoind k Ω K S.X₁ :=
    { toFun := fun φ => φ.comp uHom
      map_zero' := by ext x; rfl
      map_add' := by intro a b; ext x; rfl }
  have hG : ∀ (ψ : homCoind k Ω K S.X₂) (y : S.X₁.V),
      gFun ψ y = ψ (Rep.Hom.hom S.f y) := fun ψ y => rfl
  have gFun_mem : ∀ φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)),
      gFun φ ∈ (@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) := by
    intro φ hφ
    intro σ
    apply AddMonoidHom.ext
    intro x
    rw [show (σ • (gFun φ)) x
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)) from rfl]
    have h1 : gFun φ (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x)
        = φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)) := by
      rw [hG, Rep.hom_comm_apply]
    have h3 : homCoind.smulHom (k := k) (Ω := Ω) σ
          ((gFun φ) (S.X₁.ρ ((SSGRoute.res k K) σ)⁻¹ x))
        = homCoind.smulHom (k := k) (Ω := Ω) σ
            (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x))) := by
      rw [h1]
    have h2 : homCoind.smulHom (k := k) (Ω := Ω) σ
          (φ (S.X₂.ρ ((SSGRoute.res k K) σ)⁻¹ (Rep.Hom.hom S.f x)))
        = φ (Rep.Hom.hom S.f x) :=
      DFunLike.congr_fun (hφ σ) (Rep.Hom.hom S.f x)
    rw [h3, h2]
    exact (hG φ x).symm
  let g : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) →+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (gFun.comp (AddSubgroup.subtype _)).codRestrict _ (fun φ => gFun_mem φ.1 φ.2)
  have hg : ∀ (ψ : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)))
      (x : S.X₁.V), Subtype.val (g ψ) x = Subtype.val ψ (Rep.Hom.hom S.f x) := by
    intro ψ x
    exact hG (ψ : homCoind k Ω K S.X₂) x
  haveI hsub : Subsingleton (@Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (homCoind k Ω K (Rep.free Coeff (K ≃ₐ[k] K) (Fin n))) _ _
      (homCoind.instAddCommGroup (Rep.free Coeff (K ≃ₐ[k] K) (Fin n)))
      (homCoind.instDistribMulActionAlgEquiv (Rep.free Coeff (K ≃ₐ[k] K) (Fin n)))) :=
    homCoind_H1_free_conj_v2 (k := k) (Ω := Ω) (K := K) (ι := Fin n)
  obtain ⟨δ, hδsurj, hδker⟩ :=
    homCoind_H0_restrict_ker_conj (k := k) (Ω := Ω) (K := K) (ι := Fin n) pic hfsurj g hg
  -- ===== the two `H⁰`'s are the same =====
  obtain ⟨ΦR, hΦR⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₁
  obtain ⟨ΦF, hΦF⟩ := homRep_unitsK_formula (k := k) (Ω := Ω) (K := K) S.X₂
  have hnat := homRep_unitsK_formula_natural (k := k) (Ω := Ω) (K := K) S.f ΦR ΦF hΦR hΦF g hg
  let ΨR : Abelian.Ext S.X₁ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) :=
    (Abelian.Ext.addEquiv₀).trans ΦR
  let ΨF : Abelian.Ext S.X₂ (unitsK k K) 0 ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₂) _
          (homCoind.instAddCommGroup S.X₂) (homCoind.instDistribMulActionAlgEquiv S.X₂)) :=
    (Abelian.Ext.addEquiv₀).trans ΦF
  have hpre1 : ∀ f : S.X₂ ⟶ unitsK k K,
      pre (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f) := by
    intro f
    change (Abelian.Ext.mk₀ S.f).precomp (unitsK k K) (by norm_num : 0 + 0 = 0)
        (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (S.f ≫ f)
    rw [ext_precomp_mk₀]
  have hΨR : ∀ f : S.X₁ ⟶ unitsK k K, ΨR (Abelian.Ext.mk₀ f) = ΦR f := by
    intro f
    show ΦR (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦR f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hΨF : ∀ f : S.X₂ ⟶ unitsK k K, ΨF (Abelian.Ext.mk₀ f) = ΦF f := by
    intro f
    show ΦF (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f)) = ΦF f
    rw [ext_addEquiv₀_mk₀_ehb]
  have hpre : ∀ x : Abelian.Ext S.X₂ (unitsK k K) 0, ΨR (pre x) = g (ΨF x) := by
    intro x
    rw [show x = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ x) from
      (Abelian.Ext.mk₀_addEquiv₀_apply x).symm]
    rw [hpre1 (Abelian.Ext.addEquiv₀ x), hΨR (S.f ≫ Abelian.Ext.addEquiv₀ x),
      hΨF (Abelian.Ext.addEquiv₀ x)]
    exact hnat (Abelian.Ext.addEquiv₀ x)
  have hmap : AddSubgroup.map ΨR.toAddMonoidHom ΦE.ker = δ.ker := by
    rw [hΦEker, hδker]
    have h1 : AddSubgroup.map ΨR.toAddMonoidHom pre.range =
        (ΨR.toAddMonoidHom.comp pre).range := by
      rw [AddMonoidHom.range_eq_map pre, AddSubgroup.map_map,
        ← AddMonoidHom.range_eq_map (ΨR.toAddMonoidHom.comp pre)]
    rw [h1]
    have h2 : ΨR.toAddMonoidHom.comp pre = g.comp ΨF.toAddMonoidHom := by
      apply AddMonoidHom.ext
      intro y
      exact hpre y
    rw [h2, AddMonoidHom.range_eq_map (g.comp ΨF.toAddMonoidHom), ← AddSubgroup.map_map,
      ← AddMonoidHom.range_eq_map ΨF.toAddMonoidHom,
      (AddMonoidHom.range_eq_top).mpr ΨF.surjective]
    exact (AddMonoidHom.range_eq_map g).symm
  -- ===== collecting the isomorphism `Ext¹ ≃+ H¹(Γ, homCoind (X))` =====
  let e1 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+ Abelian.Ext X (unitsK k K) 1 :=
    QuotientAddGroup.quotientKerEquivOfSurjective ΦE hΦEsurj
  let e2 : Abelian.Ext S.X₁ (unitsK k K) 0 ⧸ ΦE.ker ≃+
      ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker :=
    QuotientAddGroup.congr _ _ ΨR hmap
  let e3 : ↥(@Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω) (homCoind k Ω K S.X₁) _
          (homCoind.instAddCommGroup S.X₁) (homCoind.instDistribMulActionAlgEquiv S.X₁)) ⧸ δ.ker ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X) _ _
          (homCoind.instAddCommGroup X) (homCoind.instDistribMulActionAlgEquiv X) :=
    QuotientAddGroup.quotientKerEquivOfSurjective δ hδsurj
  have hExtHomCoind : Abelian.Ext X (unitsK k K) 1 ≃+
      @Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K X) _ _
          (homCoind.instAddCommGroup X) (homCoind.instDistribMulActionAlgEquiv X) :=
    e1.symm.trans (e2.trans e3)
  exact ⟨hExtHomCoind⟩

end

end Work.SSGRoute.PT
