/-
Copyright: the martinet_totally_real_towers team.

# Adding a coboundary to a `1`-cocycle changes `delta1Fun` by a `1`-coboundary

The raw connecting cochain `S.delta1Fun` (degree `1 → 2`) is defined by choosing a set-theoretic
section `sect` of the projection `g` of the coefficient sequence, so it depends on that choice.
Its *class* modulo `2`-coboundaries, however, does not: if `c` is a `1`-cocycle with values in `C`
and `γ : C`, then replacing `c` by `c + d⁰γ` (the same cohomology class) changes `S.delta1Fun` by
the `1`-coboundary `d¹u`, where

`u σ = S.invFun (S.sect (c σ + d⁰γ σ) - S.sect (c σ) - (σ • S.sect γ - S.sect γ))`

is the difference of the two sections of `g`, read in `A`.  This is the statement that the
connecting homomorphism `H¹(C) → H²(A)` is well defined.

The key point making `invFun` usable is that `f` is injective, so `invFun` is the honest inverse
of the inclusion `A ↪ B` on the image of `f` (rather than an arbitrary choice of preimage).
-/

import Mathlib
import Submission.Work.ConCohomology.Setup
import Submission.Work.ConCohomology.invFun_eq_of

namespace Work.ConCohomology

variable {G : Type*} [Group G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- If `b` lies in the image of `f`, then `S.f (S.invFun b) = b`. -/
lemma f_invFun_eq_of_exists (S : CoeffSES G A B C) {b : B} (hb : ∃ a : A, S.f a = b) :
    S.f (S.invFun b) = b := by
  have h : S.invFun b = Classical.choose hb := invFun_eq_of S (Classical.choose_spec hb)
  rw [h]
  exact Classical.choose_spec hb

/-- If `g b = 0` then `b` lies in the image of `f`, so `S.f (S.invFun b) = b`. -/
lemma f_invFun_eq_of_g_eq_zero (S : CoeffSES G A B C) {b : B} (hb : S.g b = 0) :
    S.f (S.invFun b) = b :=
  f_invFun_eq_of_exists S ((S.exact b).1 hb)

/-- `invFun` is additive along the image of `f`: adding `f w` to a point of the image adds `w`
to the preimage. -/
lemma invFun_add_f (S : CoeffSES G A B C) {b : B} (hb : ∃ a : A, S.f a = b) (w : A) :
    S.invFun (b + S.f w) = S.invFun b + w := by
  have h1 : S.f (S.invFun b) = b := f_invFun_eq_of_exists S hb
  have h2 : S.f (S.invFun b + w) = b + S.f w := by rw [EqHom.map_add, h1]
  exact invFun_eq_of S h2

/-- The core computation: if `u` measures, for every `ν`, the difference between the section of
`g` at `c ν + d⁰γ ν` and the section at `c ν` translated by `ν • sect γ - sect γ`, then
`delta1Fun (c + d⁰γ) - delta1Fun c = d¹u` (pointwise, for `c` a `1`-cocycle). -/
lemma delta1Fun_add_d0_eq (S : CoeffSES G A B C) (c : G → C) (hc : IsCocycle1 c) (γ : C)
    (u : G → A)
    (hu : ∀ ν : G, S.sect (c ν + d0Fun (G := G) γ ν)
      = S.sect (c ν) + (ν • S.sect γ - S.sect γ) + S.f (u ν))
    (σ τ : G) :
    S.delta1Fun (fun ν => c ν + d0Fun (G := G) γ ν) (σ, τ) - S.delta1Fun c (σ, τ)
      = d1Fun (G := G) u (σ, τ) := by
  simp only [CoeffSES.delta1Fun_apply, d1Fun_apply]
  have hα : σ • S.sect (c τ + d0Fun (G := G) γ τ)
        - S.sect (c (σ * τ) + d0Fun (G := G) γ (σ * τ))
        + S.sect (c σ + d0Fun (G := G) γ σ)
      = (σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ))
        + S.f (σ • u τ - u (σ * τ) + u σ) := by
    rw [hu τ, hu (σ * τ), hu σ]
    simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, smul_add, smul_sub, mul_smul]
    abel
  have hβ : ∃ a : A, S.f a = σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ) := by
    refine (S.exact _).1 ?_
    simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
    rw [hc σ τ]
    abel
  rw [hα, invFun_add_f S hβ (σ • u τ - u (σ * τ) + u σ)]
  abel

lemma delta1Fun_add_coboundary {G : Type*} [Group G] {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : CoeffSES G A B C) (c : G → C) (hc : IsCocycle1 c) (γ : C) :
    ∃ u : G → A, S.delta1Fun (fun σ => c σ + d0Fun (G := G) γ σ) - S.delta1Fun c
      = d1Fun (G := G) u := by
  refine ⟨fun ν => S.invFun (S.sect (c ν + d0Fun (G := G) γ ν) - S.sect (c ν)
      - (ν • S.sect γ - S.sect γ)), funext fun p => ?_⟩
  obtain ⟨σ, τ⟩ := p
  refine delta1Fun_add_d0_eq S c hc γ _ (fun ν => ?_) σ τ
  have h : S.f (S.invFun (S.sect (c ν + d0Fun (G := G) γ ν) - S.sect (c ν)
      - (ν • S.sect γ - S.sect γ)))
      = S.sect (c ν + d0Fun (G := G) γ ν) - S.sect (c ν) - (ν • S.sect γ - S.sect γ) := by
    refine f_invFun_eq_of_g_eq_zero S ?_
    simp only [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, d0Fun_apply]
    abel
  rw [h]
  abel

end Work.ConCohomology
