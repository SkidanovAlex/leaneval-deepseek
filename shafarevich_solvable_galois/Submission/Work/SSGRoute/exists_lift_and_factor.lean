import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits SSGRoute.PTExt

/-- **Elementwise exactness of a short exact sequence of representations.**
If `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` is short exact in `Rep k G` and `b : S.X₂` is killed by
`S.g`, then `b` lies in the range of `S.f`.  This is the concrete ("elementwise") form of the
exactness at the middle term.

The statement is deliberately *coefficient-generic*: the proof applies the forgetful functor
`Rep k G ⥤ ModuleCat k` (which preserves homology) and then uses the elementwise exactness
criterion for short complexes of modules.  Keeping `k` an abstract ring variable is essential,
because for the concrete coefficient ring `Coeff = ULift ℤ` the generic `Module Coeff X.V`
instance search for an abstract `X : Rep Coeff G` runs into a `ULift`-instance diamond. -/
theorem exists_of_shortExact_ker {k : Type} [Ring k] {G : Type} [Group G]
    (S : ShortComplex (Rep.{0} k G)) (hS : S.ShortExact) (b : S.X₂)
    (hb : S.g b = 0) : ∃ a : S.X₁, S.f a = b := by
  have hT : (S.map (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).Exact :=
    (S.exact_map_iff_of_faithful (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).2 hS.exact
  have hbT : (S.map (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).g b = 0 := hb
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).1 hT b hbT
  exact ⟨a, ha⟩

/-- **Lifting an inhomogeneous cocycle through a short exact sequence of representations**
(coefficient-generic form).  This is the general version of
`Work.SSGRoute.exists_lift_and_factor`, for an arbitrary coefficient ring `k`.

Given a short exact sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` in `Rep k G` and an inhomogeneous
`n`-cocycle `z` with values in `S.X₃`, there is a cochain `y₂` with values in `S.X₂` lifting `z`
and a cochain `x` with values in `S.X₁` with `S.f ∘ x = d y₂`; moreover `x` is again a cocycle. -/
theorem exists_lift_and_factor_gen (n : ℕ) {k : Type} [CommRing k] (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} k G)) (hS : S.ShortExact)
    (z : (Fin n → G) → S.X₃)
    (hz : ConcreteCategory.hom (inhomogeneousCochains.d S.X₃ n) z = 0) :
    ∃ (y₂ : (Fin n → G) → S.X₂) (x : (Fin (n + 1) → G) → S.X₁),
      ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f n) y₂ = z ∧
      (⇑(Rep.Hom.hom S.f) ∘ x =
        ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n + 1)) y₂) ∧
      ConcreteCategory.hom (inhomogeneousCochains.d S.X₁ (n + 1)) x = 0 := by
  have hg : Function.Surjective ⇑(Rep.Hom.hom S.g) := (Rep.epi_iff_surjective S.g).1 hS.epi_g
  have hf : Function.Injective ⇑(Rep.Hom.hom S.f) := (Rep.mono_iff_injective S.f).1 hS.mono_f
  -- Step 1: lift the cocycle `z` pointwise through the surjection `S.g`.
  let y₂ : (Fin n → G) → S.X₂ := fun t => Classical.choose (hg (z t))
  have hy₂ : ∀ t, Rep.Hom.hom S.g (y₂ t) = z t := fun t => Classical.choose_spec (hg (z t))
  have hlift : ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f n) y₂ = z := by
    rw [show ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f n)
        = (Rep.Hom.hom S.g).compLeft (Fin n → G) from
      groupCohomology.cochainsMap_id_f_hom_eq_compLeft S.g n]
    ext t; exact hy₂ t
  have hz' : ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₃).d n (n+1)) z = 0 := by
    rw [groupCohomology.inhomogeneousCochains.d_def]; exact hz
  have hcomm := HomologicalComplex.Hom.comm
      (groupCohomology.cochainsMap (MonoidHom.id G) S.g) n (n+1)
  -- Step 2: `d y₂` is killed by `S.g`, because `d z = 0` and `cochainsMap` commutes with `d`.
  have key : ∀ t, Rep.Hom.hom S.g
      ((ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n+1))) y₂ t) = 0 := by
    intro t
    have h := ConcreteCategory.congr_hom hcomm y₂
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    rw [hlift, hz'] at h
    have h2 : ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f (n+1))
        = (Rep.Hom.hom S.g).compLeft (Fin (n+1) → G) :=
      groupCohomology.cochainsMap_id_f_hom_eq_compLeft S.g (n+1)
    rw [h2] at h
    exact congr_fun h.symm t
  -- Step 3: factor `d y₂` through `S.f` pointwise (exactness at the middle term).
  choose x hx using fun t => exists_of_shortExact_ker S hS
      ((ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n+1))) y₂ t) (key t)
  have hfac : ⇑(Rep.Hom.hom S.f) ∘ x =
      ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n+1)) y₂ := by
    funext t
    exact hx t
  -- Step 4: `x` is a cocycle: `S.f ∘ d x = d (S.f ∘ x) = d (d y₂) = 0` and `S.f` is injective.
  have hdx : ConcreteCategory.hom (inhomogeneousCochains.d S.X₁ (n+1)) x = 0 := by
    have hcomm2 := HomologicalComplex.Hom.comm
        (groupCohomology.cochainsMap (MonoidHom.id G) S.f) (n+1) (n+2)
    have h3 : ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.f).f (n+1))
        = (Rep.Hom.hom S.f).compLeft (Fin (n+1) → G) :=
      groupCohomology.cochainsMap_id_f_hom_eq_compLeft S.f (n+1)
    have h4 : ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.f).f (n+2))
        = (Rep.Hom.hom S.f).compLeft (Fin (n+2) → G) :=
      groupCohomology.cochainsMap_id_f_hom_eq_compLeft S.f (n+2)
    have h := ConcreteCategory.congr_hom hcomm2 x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h3, h4] at h
    have hleft : ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d (n+1) (n+2))
        (((Rep.Hom.hom S.f).compLeft (Fin (n+1) → G)) x) = 0 := by
      have e : ((Rep.Hom.hom S.f).compLeft (Fin (n+1) → G)) x
          = ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n+1)) y₂ := by
        funext t
        rw [LinearMap.compLeft_apply, Function.comp_apply]
        exact congr_fun hfac t
      rw [e, ← ConcreteCategory.comp_apply, groupCohomology.inhomogeneousCochains.d_def,
        groupCohomology.inhomogeneousCochains.d_def,
        groupCohomology.inhomogeneousCochains.d_comp_d]
      simp
    have hright : ((Rep.Hom.hom S.f).compLeft (Fin (n+2) → G))
        (ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₁).d (n+1) (n+2)) x) = 0 := by
      rw [← h]; exact hleft
    have hfinal : ConcreteCategory.hom
        ((groupCohomology.inhomogeneousCochains S.X₁).d (n+1) (n+2)) x = 0 := by
      funext t
      show ((ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₁).d (n+1) (n+2))) x) t = 0
      have h8' : (Rep.Hom.hom S.f)
          (((ConcreteCategory.hom
              ((groupCohomology.inhomogeneousCochains S.X₁).d (n+1) (n+2))) x) t) = 0 := by
        have h9 := congr_fun hright t
        rw [LinearMap.compLeft_apply, Function.comp_apply] at h9
        exact h9
      exact hf (by rw [h8', map_zero])
    rw [← groupCohomology.inhomogeneousCochains.d_def S.X₁ (n+1)]
    exact hfinal
  exact ⟨y₂, x, hlift, hfac, hdx⟩

/-- **Lifting an inhomogeneous cocycle through a short exact sequence of representations.**
Given a short exact sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` in `Rep Coeff G` and an
inhomogeneous `n`-cocycle `z` with values in `S.X₃`, there is a cochain `y₂` with values in
`S.X₂` lifting `z` (`S.g ∘ y₂ = z`) and a cochain `x` with values in `S.X₁` with `S.f ∘ x = d y₂`;
moreover `x` is again a cocycle. -/
theorem exists_lift_and_factor (n : ℕ) (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact)
    (z : (Fin n → G) → S.X₃)
    (hz : ConcreteCategory.hom (inhomogeneousCochains.d S.X₃ n) z = 0) :
    ∃ (y₂ : (Fin n → G) → S.X₂) (x : (Fin (n + 1) → G) → S.X₁),
      ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f n) y₂ = z ∧
      (⇑(Rep.Hom.hom S.f) ∘ x =
        ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n + 1)) y₂) ∧
      ConcreteCategory.hom (inhomogeneousCochains.d S.X₁ (n + 1)) x = 0 :=
  exists_lift_and_factor_gen (k := SSGRoute.PTExt.Coeff) n G S hS z hz

end Work.SSGRoute
