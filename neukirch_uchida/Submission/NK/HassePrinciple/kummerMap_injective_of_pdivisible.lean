/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Injectivity of the level-wise Kummer map for `p`-divisible units

Let `L/K` be a field extension, `G = Gal(L/K)`, let `p : ℕ` and let

  `kummerMap p K L : H²(G, μ_p(L)) ⟶ H²(G, Lˣ)`

be the map on second cohomology induced by the inclusion `μ_p(L) ↪ Lˣ`
(`NK.HassePrinciple.Mu`).  The present file proves the classical statement that this map is
**injective** as soon as

* the `p`-th power map on `Lˣ` is surjective, i.e. every unit of `L` is a `p`-th power
  (hypothesis `hdiv`), and
* `H¹(G, Lˣ) = 0` (hypothesis `h1`, Noether's generalisation of Hilbert 90, which for finite Galois
  `L/K` is `NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep`).

The mathematics is the long exact cohomology sequence of the short exact sequence of
`ℤ[G]`-modules

  `0 ⟶ μ_p(L) ⟶ Lˣ --(·)^p--> Lˣ ⟶ 0`,

which is exact precisely because `(·)^p` has kernel `μ_p(L)` and is surjective by `hdiv`.  In the
long exact sequence

  `H¹(G, Lˣ) ⟶ H²(G, μ_p(L)) --kummerMap--> H²(G, Lˣ)`

the group `H¹(G, Lˣ)` vanishes by `h1`, so the kernel of the Kummer map is trivial.

## Contents

* `NK.HassePrinciple.unitsPow` — the `p`-th power endomorphism of the units, as a morphism of
  `CoeffInt`-linear representations;
* `NK.HassePrinciple.kummerShortComplex` — the short complex
  `μ_p(L) ⟶ Lˣ --(·)^p--> Lˣ` of representations;
* `NK.HassePrinciple.kummerShortComplex_shortExact` — it is short exact when every unit is a
  `p`-th power;
* `NK.HassePrinciple.kummerMap_injective_of_pdivisible` — the injectivity of the Kummer map on
  `H²`.

## Implementation note

The coefficient ring is `CoeffInt = ULift ℤ`, and `ULift.module` is a generic instance for
`Module (ULift R) M`.  For a *variable* `A : Rep (ULift ℤ) G` this instance competes with the
module structure `A.hV2` stored in the structure, which makes instance search produce a structure
that the kernel does not accept (`synthesized ULift.module, inferred A.hV2`).  Giving `Rep.hV1`
and `Rep.hV2` a higher instance priority inside one section restores the intended (structure)
instances and makes the standard `Rep`-machinery — `forget₂ (Rep k G) (ModuleCat k)` and the
reflection of exactness `Functor.reflects_exact_of_faithful` — usable.
-/

import Mathlib
import Submission.NK.HassePrinciple.Mu

open CategoryTheory Representation

universe u

namespace NK.HassePrinciple

section KummerShortExact

/- `ULift.module` competes with the module structure stored in a representation (see the module
docstring); prefer the structure instances, as intended. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **The `p`-th power map on the units**, as a morphism of `CoeffInt`-linear representations of
`Gal(L/K)`.  On `Additive Lˣ` (the additive notation for the units) it is multiplication by
`p`. -/
noncomputable def unitsPow (p : ℕ) :
    (unitsRep K L : Rep.{u, u, u} CoeffInt Gal(L/K)) ⟶
      (unitsRep K L : Rep.{u, u, u} CoeffInt Gal(L/K)) :=
  Rep.ofHom
    ⟨(p : ℕ) • (LinearMap.id : Additive Lˣ →ₗ[ULift ℤ] Additive Lˣ), by
      intro g
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
      change p • (g • x) = g • (p • x)
      rw [smul_comm]⟩

@[simp]
lemma unitsPow_apply (p : ℕ) (x : (unitsRep K L).V) :
    (unitsPow (K := K) (L := L) p).hom x = p • x := rfl

/-- The short complex of `CoeffInt`-linear `Gal(L/K)`-representations

  `μ_p(L) ⟶ Lˣ --(·)^p--> Lˣ`

given by the Kummer inclusion followed by the `p`-th power map. -/
noncomputable def kummerShortComplex (p : ℕ) :
    ShortComplex (Rep.{u, u, u} CoeffInt Gal(L/K)) where
  X₁ := muRep p K L
  X₂ := unitsRep K L
  X₃ := unitsRep K L
  f := kummerIncl p K L
  g := unitsPow p
  zero := by
    ext x
    show unitsPow p ((kummerIncl p K L) x) = 0
    change p • (Additive.ofMul
      ((Additive.toMul (α := rootsOfUnity p L) x : rootsOfUnity p L) : Lˣ)) = 0
    rw [← ofMul_pow]
    rw [show (((Additive.toMul (α := rootsOfUnity p L) x : rootsOfUnity p L) : Lˣ)) ^ p = 1 from
      (mem_rootsOfUnity p _).mp x.2]
    rfl

lemma kummerIncl_injective (p : ℕ) : Function.Injective (kummerIncl p K L).hom := by
  intro x y h
  change Additive.ofMul (α := Lˣ) (Additive.toMul (α := rootsOfUnity p L) x) =
    Additive.ofMul (α := Lˣ) (Additive.toMul (α := rootsOfUnity p L) y) at h
  exact Subtype.ext (Additive.toMul.injective h)

lemma unitsPow_surjective (p : ℕ) (hdiv : ∀ x : Lˣ, ∃ y : Lˣ, y ^ p = x) :
    Function.Surjective (unitsPow (K := K) (L := L) p).hom := by
  intro y
  let y'' : Additive Lˣ := y
  obtain ⟨y', hy'⟩ := hdiv (Additive.toMul y'')
  refine ⟨Additive.ofMul y', ?_⟩
  change p • Additive.ofMul y' = y''
  rw [← ofMul_pow, hy', ofMul_toMul]

/-- If `x` lies in the kernel of the `p`-th power map on the units, then it is a `p`-th root of
unity, i.e. it lies in the image of `μ_p(L) ↪ Lˣ`. -/
lemma exists_kummerIncl_eq_of_unitsPow_eq_zero (p : ℕ)
    {x : ((unitsRep K L : Rep.{u, u, u} CoeffInt Gal(L/K))).V}
    (hx : (unitsPow (K := K) (L := L) p).hom x = 0) :
    ∃ y : ((muRep p K L : Rep.{u, u, u} CoeffInt Gal(L/K))).V,
      (kummerIncl p K L).hom y = x := by
  let x' : Additive Lˣ := x
  have hx' : p • x' = 0 := hx
  have h1 : (p • x').toMul = x'.toMul ^ p := toMul_nsmul p x'
  rw [hx', toMul_zero] at h1
  refine ⟨Additive.ofMul ⟨x'.toMul, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity]; exact h1.symm
  · change Additive.ofMul x'.toMul = x
    rw [ofMul_toMul]

/-- **The Kummer sequence is short exact** when every unit is a `p`-th power: the short complex
`μ_p(L) ⟶ Lˣ --(·)^p--> Lˣ` is short exact. -/
lemma kummerShortComplex_shortExact (p : ℕ) (hdiv : ∀ x : Lˣ, ∃ y : Lˣ, y ^ p = x) :
    (kummerShortComplex (K := K) (L := L) p).ShortExact where
  exact := (forget₂ (Rep.{u, u, u} CoeffInt Gal(L/K)) (ModuleCat.{u} CoeffInt))
    |>.reflects_exact_of_faithful _
      ((ShortComplex.moduleCat_exact_iff _).2 fun _ hx =>
        exists_kummerIncl_eq_of_unitsPow_eq_zero (K := K) (L := L) p hx)
  mono_f := (Rep.mono_iff_injective _).2 (kummerIncl_injective (K := K) (L := L) p)
  epi_g := (Rep.epi_iff_surjective _).2 (unitsPow_surjective (K := K) (L := L) p hdiv)

/-- **The Kummer map `H²(Gal(L/K), μ_p(L)) → H²(Gal(L/K), Lˣ)` is injective** when every unit of
`L` is a `p`-th power and `H¹(Gal(L/K), Lˣ) = 0`.

This is the level-wise form of the Kummer injection
`H²(G_K, μ_p) ↪ H²(G_K, K̄ˣ) = Br(K)` of the Hasse-principle chapter: the long exact cohomology
sequence of `0 → μ_p(L) → Lˣ → Lˣ → 0` exhibits `ker(kummerMap)` as the image of the connecting
map `δ : H¹(Gal(L/K), Lˣ) → H²(Gal(L/K), μ_p(L))`, and `H¹(Gal(L/K), Lˣ) = 0`. -/
theorem kummerMap_injective_of_pdivisible {K L : Type u} [Field K] [Field L] [Algebra K L] (p : ℕ)
    (hdiv : ∀ x : Lˣ, ∃ y : Lˣ, y ^ p = x)
    (h1 : Subsingleton (groupCohomology (NK.HassePrinciple.unitsRep K L) 1)) :
    Function.Injective (fun x => (NK.HassePrinciple.kummerMap p K L).hom x) := by
  have hij : 1 + 1 = 2 := rfl
  have hS := kummerShortComplex_shortExact (K := K) (L := L) p hdiv
  -- exactness of `H¹(G, Lˣ) ⟶ H²(G, μ_p(L)) ―kummerMap→ H²(G, Lˣ)`
  have hEx := ShortComplex.Exact.moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₁_exact (k := CoeffInt) (G := Gal(L/K)) hS hij)
  have hsub : Subsingleton ↑(groupCohomology.mapShortComplex₁ hS hij).X₁ := h1
  -- `H¹(G, Lˣ) = 0`, so the image of the connecting map is trivial
  have hfrange : LinearMap.range (groupCohomology.mapShortComplex₁ hS hij).f.hom = ⊥ :=
    (Submodule.eq_bot_iff _).mpr (fun y hy => by
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
      rw [← hz, show z = 0 from hsub.elim z 0, map_zero])
  have hkg : LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom = ⊥ := by
    rw [← hEx, hfrange]
  intro a b hab
  have hmem : a - b ∈ LinearMap.ker (kummerMap p K L).hom := by
    rw [LinearMap.mem_ker]
    have hab' : (kummerMap p K L).hom a = (kummerMap p K L).hom b := hab
    rw [map_sub, hab', sub_self]
  have h0 : a - b = 0 := by
    rw [show LinearMap.ker (kummerMap p K L).hom
        = LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom from rfl, hkg] at hmem
    exact (Submodule.mem_bot CoeffInt).mp hmem
  exact sub_eq_zero.mp h0

end KummerShortExact

end NK.HassePrinciple
