/-
Copyright: the martinet_totally_real_towers team.

# Exactness at `H¹(G,B)` for a short exact sequence of coefficient modules

This module proves the exactness of

`H¹(G,A) --H¹(f)--> H¹(G,B) --H¹(g)--> H¹(G,C)`

at the middle term: a class `x ∈ H¹(G,B)` is killed by `H¹(g)` if and only if it is in the image
of `H¹(f)`.

The proof is the classical one, done entirely on the level of cochains.  Write `x = [z]` for a
continuous crossed homomorphism `z : G → B`.  If `H¹(g)[z] = 0` then `g ∘ z` is a coboundary, say
`g (z σ) = σ • γ - γ` for a locally constant `γ : G → C`, and one considers

`w σ = z σ - (σ • s - s)`,  where `s = S.sect γ` is a lift of `γ`,

which lies in `ker g = im f` by construction; set `a σ = S.invFun (w σ)`, the unique preimage of
`w σ` under the inclusion `f : A → B`.  Then `f (a σ) = z σ - (σ • s - s)`, so `f ∘ a` differs from
`z` by the coboundary `d⁰(-s)`: the class of `z` lies in the image of `H¹(f)` as soon as `a` is a
cocycle.  To see that `a` is one, note that `f (d¹a (σ,τ)) = σ • w τ - w (σ*τ) + w σ`, and this
vanishes because `z` is a cocycle and `s` is a section of `g` (the `s`-terms cancel); injectivity
of `f` then gives `d¹a = 0`.  Finally `a` is locally constant because `f ∘ a = w` is, and `f` is
injective.

The converse direction is immediate: `H¹(g) ∘ H¹(f)` is induced by `g ∘ f = 0`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Aux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-- `g ∘ f = 0` for a short exact sequence of coefficient modules. -/
private lemma aux_g_f_eq_zero (S : CoeffSES G A B C) (a : A) : S.g (S.f a) = 0 :=
  (S.exact (S.f a)).mpr ⟨a, rfl⟩

/-- On the image of `f`, the chosen set-theoretic inverse `S.invFun` inverts `S.f`. -/
private lemma aux_f_invFun (S : CoeffSES G A B C) {b : B} (hb : S.g b = 0) :
    S.f (S.invFun b) = b := by
  have h : ∃ a : A, S.f a = b := (S.exact b).mp hb
  rw [CoeffSES.invFun_eq, dite_eq_left h]
  exact Classical.choose_spec h

/-- A function whose composite with an injective map is locally constant is itself locally
constant. -/
private lemma aux_isLocallyConstant_of_injective_comp {X Y Z : Type*} [TopologicalSpace X]
    {φ : X → Y} {ψ : X → Z} (hψ : IsLocallyConstant ψ) (f : Y → Z) (hf : Injective f)
    (h : ∀ x, f (φ x) = ψ x) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, hU, hxU, hUc⟩ := hψ.exists_open x
  exact ⟨U, hU, hxU, fun y hy => hf (by rw [h y, h x, hUc y hy])⟩

end Aux

lemma exact_H1_B {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (x : H1 G B) :
    H1Map S.g x = 0 ↔ ∃ y : H1 G A, H1Map S.f y = x := by
  constructor
  · intro hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro z hx
    change H1Map S.g (H1.mk z) = 0 at hx
    rw [H1Map_mk, H1.mk_eq_zero_iff, mem_B1', mem_B1] at hx
    obtain ⟨γ, hγ⟩ := hx
    -- `z` is a `1`-cocycle
    have hzc : ∀ σ τ : G, (z : Cochain1 G B) (σ * τ) =
        (z : Cochain1 G B) σ + σ • (z : Cochain1 G B) τ :=
      fun σ τ => mem_Z1.mp z.2 σ τ
    -- `g ∘ z` is the coboundary of `γ`
    have hγ' : ∀ σ : G, σ • γ - γ = S.g ((z : Cochain1 G B) σ) := by
      intro σ
      have h := DFunLike.congr_fun hγ σ
      simpa only [d0Hom_apply, Z1Map_coe, cochain1Map_apply] using h
    -- the corrected cocycle, which now takes values in `ker g = im f`
    let w : G → B := fun σ => (z : Cochain1 G B) σ - d0Fun (G := G) (S.sect γ) σ
    have hw_loc : IsLocallyConstant w :=
      ((z : Cochain1 G B).isLocallyConstant).sub (isLocallyConstant_d0Fun (G := G) (S.sect γ))
    have hw_g : ∀ σ : G, S.g (w σ) = 0 := by
      intro σ
      have h1 : S.g (w σ) = S.g ((z : Cochain1 G B) σ) - (σ • γ - γ) := by
        simp only [w, d0Fun_apply, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
      rw [h1, ← hγ' σ, sub_self]
    -- the unique preimage of `w` under the inclusion `f`
    let za : G → A := fun σ => S.invFun (w σ)
    have hza_f : ∀ σ : G, S.f (za σ) = w σ := fun σ => aux_f_invFun S (hw_g σ)
    have hza_loc : IsLocallyConstant za :=
      aux_isLocallyConstant_of_injective_comp (φ := za) (ψ := w) hw_loc S.f S.injective_f
        (fun σ => hza_f σ)
    -- `za` is a cocycle, because `f` is injective and `z` is one
    have hza_coc : IsCocycle1 za := by
      rw [isCocycle1_iff_d1Fun]
      funext p
      obtain ⟨σ, τ⟩ := p
      apply S.injective_f
      show S.f (d1Fun (G := G) za (σ, τ)) = S.f 0
      rw [map_zero]
      have h : S.f (d1Fun (G := G) za (σ, τ)) = σ • w τ - w (σ * τ) + w σ := by
        simp only [d1Fun_apply, EqHom.map_add, EqHom.map_sub, EqHom.map_smul]
        rw [hza_f τ, hza_f (σ * τ), hza_f σ]
      rw [h]
      simp only [w, d0Fun_apply, smul_sub, smul_smul]
      rw [hzc σ τ]
      abel
    let zaC : Z1 G A := ⟨⟨za, hza_loc⟩, mem_Z1.mpr hza_coc⟩
    -- `f ∘ za` differs from `z` by the coboundary `d⁰(-s)`
    refine ⟨H1.mk zaC, ?_⟩
    rw [H1Map_mk]
    change H1.mk (Z1Map S.f zaC) = H1.mk z
    rw [H1.mk_eq_mk_iff, mem_B1', mem_B1]
    refine ⟨-S.sect γ, ?_⟩
    ext σ
    simp only [d0Hom_apply, AddSubgroup.coe_sub, Z1Map_coe, cochain1Map_apply,
      LocallyConstant.coe_sub, Pi.sub_apply, smul_neg]
    change -(σ • S.sect γ) - -S.sect γ = S.f (za σ) - (z : Cochain1 G B) σ
    rw [hza_f σ]
    simp only [w, d0Fun_apply]
    abel
  · rintro ⟨y, hy⟩
    rw [← hy]
    refine QuotientAddGroup.induction_on y ?_
    intro za
    change H1Map S.g (H1Map S.f (H1.mk za)) = 0
    rw [H1Map_mk, H1Map_mk]
    rw [show Z1Map S.g (Z1Map S.f za) = 0 from ?_, H1.mk_zero]
    -- `g ∘ f = 0`, so the composite of the two induced maps kills every class
    refine Subtype.ext ?_
    refine LocallyConstant.ext fun σ => ?_
    show S.g (S.f ((za : Cochain1 G A) σ)) = 0
    exact aux_g_f_eq_zero S ((za : Cochain1 G A) σ)

end Work.ConCohomology
