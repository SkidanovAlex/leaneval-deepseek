/-
Copyright: the martinet_totally_real_towers team.

# `delta1Fun_add_coboundary`, with a *locally constant* choice of `u`

The module `Work.ConCohomology.delta1Fun_add_coboundary` shows that adding a coboundary `d⁰γ` to a
`1`-cocycle `c` with values in `C` changes the raw connecting cochain `S.delta1Fun` by an honest
`1`-coboundary: there *exists* a function `u : G → A` with

`S.delta1Fun (c + d⁰γ) - S.delta1Fun c = d¹u`.

For the connecting homomorphism `H¹(G,C) → H²(G,A)` one needs the more precise statement that `u`
can be taken *locally constant* -- i.e. that the difference of the two connecting cochains lies in
the image of `d¹Hom : C¹(G,A) → C²(G,A)`, not merely in the image of `d¹` on all functions.  This
module supplies that: the witness

`u ν = S.invFun (S.sect (c ν + d⁰γ ν) - S.sect (c ν) - (ν • S.sect γ - S.sect γ))`

is locally constant, because

* `ν ↦ c ν + d⁰γ ν` is locally constant (`c` is a cochain and `d⁰γ = ν • γ - γ` is locally
  constant as `C` is a discrete `G`-module), hence so is `ν ↦ S.sect (c ν + d⁰γ ν)` -- a locally
  constant function stays locally constant after post-composition with the *arbitrary* function
  `S.sect`, and likewise with `S.invFun`,
* `ν ↦ ν • S.sect γ - S.sect γ` is locally constant since `B` is a discrete `G`-module.

The algebraic identity `S.delta1Fun (c + d⁰γ) - S.delta1Fun c = d¹u` for this particular `u` is
the computation already performed for the unbundled statement; it is reproduced here in a form
that applies to the locally constant witness.
-/

import Mathlib
import Submission.Work.ConCohomology.Setup

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

section Aux

variable {G : Type*} [Group G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- `invFun` is a section of `f` on the image of `f`. -/
private lemma invFun_f_eq_of_exists (S : CoeffSES G A B C) {b : B}
    (hb : ∃ a : A, S.f a = b) : S.f (S.invFun b) = b := by
  simp only [CoeffSES.invFun_eq, hb, dite_true]
  exact Classical.choose_spec hb

/-- If `g b = 0` then `b` lies in the image of `f`, hence `f (S.invFun b) = b`. -/
private lemma invFun_f_eq_of_g_eq_zero (S : CoeffSES G A B C) {b : B} (hb : S.g b = 0) :
    S.f (S.invFun b) = b :=
  invFun_f_eq_of_exists S ((S.exact b).1 hb)

/-- `invFun` is additive along the image of `f`. -/
private lemma invFun_add_of_exists (S : CoeffSES G A B C) {b : B}
    (hb : ∃ a : A, S.f a = b) (w : A) : S.invFun (b + S.f w) = S.invFun b + w := by
  have h1 : S.f (S.invFun b) = b := invFun_f_eq_of_exists S hb
  have h2 : S.f (S.invFun b + w) = b + S.f w := by rw [EqHom.map_add, h1]
  exact S.injective_f (by rw [invFun_f_eq_of_exists S ⟨_, h2⟩, h2])

/-- The core computation: if `u` measures, for every `ν`, the difference between the section of
`g` at `c ν + d⁰γ ν` and the section at `c ν` translated by `ν • sect γ - sect γ`, then
`delta1Fun (c + d⁰γ) - delta1Fun c = d¹u` (pointwise, for `c` a `1`-cocycle). -/
private lemma delta1Fun_add_d0_eq (S : CoeffSES G A B C) (c : G → C) (hc : IsCocycle1 c)
    (γ : C) (u : G → A)
    (hu : ∀ ν : G, S.sect (c ν + d0Fun (G := G) γ ν)
      = S.sect (c ν) + (ν • S.sect γ - S.sect γ) + S.f (u ν)) (σ τ : G) :
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
  rw [hα, invFun_add_of_exists S hβ (σ • u τ - u (σ * τ) + u σ)]
  abel

end Aux

lemma exists_cochain_delta1Fun_add_coboundary {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (c : Cochain1 G C) (hc : IsCocycle1 (c : G → C)) (γ : C) :
    ∃ u : Cochain1 G A,
      S.delta1Fun (fun σ => (c : G → C) σ + d0Fun (G := G) γ σ) - S.delta1Fun (c : G → C)
        = d1Fun (G := G) (u : G → A) := by
  -- The candidate `u` is locally constant: it is `S.invFun` applied to a locally constant
  -- `B`-valued function of `ν`.
  have harg : IsLocallyConstant fun ν : G =>
      S.sect ((c : G → C) ν + d0Fun (G := G) γ ν) - S.sect ((c : G → C) ν)
        - (ν • S.sect γ - S.sect γ) := by
    have h1 : IsLocallyConstant fun ν : G => S.sect ((c : G → C) ν + d0Fun (G := G) γ ν) :=
      (c.isLocallyConstant.add (isLocallyConstant_d0Fun (G := G) γ)).comp S.sect
    have h2 : IsLocallyConstant fun ν : G => S.sect ((c : G → C) ν) :=
      c.isLocallyConstant.comp S.sect
    have h3 : IsLocallyConstant fun ν : G => ν • S.sect γ :=
      isLocallyConstant_smul_comp (φ := fun _ : G => S.sect γ)
        (IsLocallyConstant.const (S.sect γ)) continuous_id
    exact (h1.sub h2).sub (h3.sub (IsLocallyConstant.const (S.sect γ)))
  refine ⟨⟨fun ν : G => S.invFun (S.sect ((c : G → C) ν + d0Fun (G := G) γ ν)
      - S.sect ((c : G → C) ν) - (ν • S.sect γ - S.sect γ)), harg.comp S.invFun⟩, ?_⟩
  funext p
  obtain ⟨σ, τ⟩ := p
  simp only [Pi.sub_apply]
  refine delta1Fun_add_d0_eq S (c : G → C) hc γ
    (fun ν : G => S.invFun (S.sect ((c : G → C) ν + d0Fun (G := G) γ ν)
      - S.sect ((c : G → C) ν) - (ν • S.sect γ - S.sect γ))) (fun ν => ?_) σ τ
  -- The argument of `S.invFun` has vanishing `g`-image, so `S.f` inverts `S.invFun` on it.
  have hg : S.g (S.sect ((c : G → C) ν + d0Fun (G := G) γ ν) - S.sect ((c : G → C) ν)
      - (ν • S.sect γ - S.sect γ)) = 0 := by
    simp only [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, d0Fun_apply]
    abel
  rw [invFun_f_eq_of_g_eq_zero S hg]
  abel

end Work.ConCohomology
