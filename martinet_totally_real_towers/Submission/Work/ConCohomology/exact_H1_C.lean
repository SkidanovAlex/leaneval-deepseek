/-
Copyright: the martinet_totally_real_towers team.

# Exactness at `H¹(G,C)`: the kernel of `δ¹` is the image of `H¹(G,B)`

For a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules (`S : CoeffSES G A B C`)
the connecting homomorphism `δ¹ = connecting1 S : H¹(G,C) → H²(G,A)` fits into the long exact
sequence

  `H¹(G,A) --H¹Map S.f--> H¹(G,B) --H¹Map S.g--> H¹(G,C) --δ¹--> H²(G,A)`,

and this module proves the exactness at `H¹(G,C)`: an element `x` of `H¹(G,C)` is killed by `δ¹`
if and only if it is the image of an element of `H¹(G,B)`.

Both inclusions are proved on representatives, by comparing the chosen set-theoretic section
`sect` of the projection `g` with a section coming from an explicit cocycle.

* `connecting1 S (H1Map S.g y) = 0` for every `y : H¹(G,B)`.  Given a `1`-cocycle `w : G → B`
  representing `y`, the crossed homomorphism `c = g ∘ w : G → C` admits the *canonical* section
  `σ ↦ w σ`; on it the raw connecting cochain `δ¹c` vanishes, since `d¹w = 0`.  Comparing it with
  the chosen section `sect ∘ c` produces a locally constant `u : G → A` with `f (u σ) = sect (c σ) - w σ`,
  and then `δ¹ c = d¹u`, i.e. `connectingZ1 S c ∈ B²(G,A)`.

* Conversely, if `δ¹ x = 0` is represented by a cocycle `c : G → C`, then `δ¹c = d¹u` for a
  locally constant `u : G → A`, and `b σ := sect (c σ) - f (u σ)` is a *crossed homomorphism*
  `G → B` lifting `c` (`g (b σ) = c σ`): indeed `d¹(sect ∘ c) = f (d¹u)` by the definition of
  `δ¹`, whence `d¹b = 0`.  Its class in `H¹(G,B)` maps to the class of `c`, i.e. to `x`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Helpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-- The chosen set-theoretic inverse `invFun` of the injection `f` really inverts `f` on the
elements of `B` whose `g`-image vanishes. -/
private lemma f_invFun_eq_of_g_eq_zero (S : CoeffSES G A B C) {b : B} (h : S.g b = 0) :
    S.f (S.invFun b) = b :=
  f_invFun_eq_self S ((S.exact b).mp h)

/-- The composite `g ∘ f` vanishes, which is one half of the exactness of `0 → A → B → C → 0`. -/
private lemma g_f_eq_zero (S : CoeffSES G A B C) (a : A) : S.g (S.f a) = 0 :=
  (S.exact (S.f a)).mpr ⟨a, rfl⟩

/-- Let `b : G → B` be a `1`-cocycle and let `u : G → A` satisfy
`f (u ν) = sect (g (b ν)) - b ν` for all `ν` (so that `u` measures the difference between the
chosen section `sect` of `g` and the canonical section `b` of `g ∘ b` on `A`-level). Then the raw
connecting cochain of the `C`-valued cocycle `g ∘ b` is exactly the coboundary `d¹u`.

This is the computation that makes `connecting1 S (H1Map S.g y) = 0`. -/
private lemma delta1Fun_comp_eq_d1Fun (S : CoeffSES G A B C) (b : Cochain1 G B)
    (hb : IsCocycle1 (b : G → B)) (u : G → A)
    (hu : ∀ ν : G, S.f (u ν) = S.sect (S.g (b ν)) - b ν) :
    S.delta1Fun (fun σ => S.g (b σ)) = d1Fun (G := G) u := by
  funext p
  obtain ⟨σ, τ⟩ := p
  show S.delta1Fun (fun σ => S.g (b σ)) (σ, τ) = d1Fun u (σ, τ)
  rw [CoeffSES.delta1Fun_apply, d1Fun_apply]
  apply S.injective_f
  have hg : S.g (σ • S.sect (S.g (b τ)) - S.sect (S.g (b (σ * τ))) + S.sect (S.g (b σ))) = 0 := by
    simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
    rw [hb σ τ]
    simp only [EqHom.map_add, EqHom.map_smul]
    abel
  rw [f_invFun_eq_of_g_eq_zero S hg]
  simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, hu]
  rw [smul_sub, hb σ τ]
  abel

/-- The connecting homomorphism kills the image of `H¹(G,B)`: for every class `y` in `H¹(G,B)`,
`connecting1 S (H1Map S.g y) = 0`. -/
private lemma connecting1_H1Map_g_eq_zero (S : CoeffSES G A B C) (y : H1 G B) :
    connecting1 S (H1Map S.g y) = 0 := by
  refine QuotientAddGroup.induction_on y ?_
  intro w
  change connecting1 S (H1.mk (Z1Map S.g w)) = 0
  rw [connecting1_mk, H2.mk_eq_zero_iff, mem_B2', mem_B2]
  let uFun : G → A :=
    fun ν => S.invFun (S.sect (S.g ((w : Cochain1 G B) ν)) - (w : Cochain1 G B) ν)
  have huFun : ∀ ν : G,
      S.f (uFun ν) = S.sect (S.g ((w : Cochain1 G B) ν)) - (w : Cochain1 G B) ν := by
    intro ν
    apply f_invFun_eq_of_g_eq_zero
    simp only [EqHom.map_sub, CoeffSES.g_sect, sub_self]
  have hlc : IsLocallyConstant uFun := by
    have h1 : IsLocallyConstant fun ν : G => S.sect (S.g ((w : Cochain1 G B) ν)) := by
      simpa only [Z1Map_coe, cochain1Map_apply] using
        isLocallyConstant_sect_comp S ((Z1Map S.g w : Z1 G C) : Cochain1 G C)
    have h2 : IsLocallyConstant fun ν : G => (w : Cochain1 G B) ν :=
      ((w : Cochain1 G B)).isLocallyConstant
    exact (h1.sub h2).comp S.invFun
  refine ⟨⟨uFun, hlc⟩, ?_⟩
  have hmain := delta1Fun_comp_eq_d1Fun S (w : Cochain1 G B) (mem_Z1.mp w.2) uFun huFun
  refine LocallyConstant.ext fun p => ?_
  obtain ⟨σ, τ⟩ := p
  have hp := congrFun hmain (σ, τ)
  simp only [d1Hom_apply, connectingZ1_coe, Z1Map_coe]
  exact hp.symm

/-- An element of `H¹(G,C)` killed by the connecting homomorphism lies in the image of `H¹(G,B)`:
the cocycle representing it is modified by the `A`-valued cochain witnessing that its raw
connecting cochain is a coboundary, and the modified section is a crossed homomorphism. -/
private lemma exists_H1Map_g_eq_of_connecting1_eq_zero (S : CoeffSES G A B C) (x : H1 G C)
    (hx : connecting1 S x = 0) : ∃ y : H1 G B, H1Map S.g y = x := by
  revert hx
  refine QuotientAddGroup.induction_on x ?_
  intro z hx
  change connecting1 S (H1.mk z) = 0 at hx
  rw [connecting1_mk, H2.mk_eq_zero_iff, mem_B2', mem_B2] at hx
  obtain ⟨u, hu⟩ := hx
  -- `hu` identifies the connecting `2`-cocycle of `z` with the coboundary `d¹u`.
  have hfun : ∀ σ τ : G, S.delta1Fun (z : G → C) (σ, τ) =
      d1Fun (G := G) (u : G → A) (σ, τ) := by
    intro σ τ
    have h := congrArg (fun f : Cochain2 G A => f (σ, τ)) hu
    simp only [d1Hom_apply, connectingZ1_coe] at h
    exact h.symm
  -- Hence `f` inverts `invFun` on the argument of the connecting cochain.
  have hkey : ∀ σ τ : G, S.f (d1Fun (G := G) (u : G → A) (σ, τ)) =
      σ • S.sect ((z : G → C) τ) - S.sect ((z : G → C) (σ * τ)) +
        S.sect ((z : G → C) σ) := by
    intro σ τ
    rw [← hfun σ τ, CoeffSES.delta1Fun_apply]
    apply f_invFun_eq_of_g_eq_zero
    simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
    rw [mem_Z1.mp z.2 σ τ]
    abel
  -- The corrected section `b σ = sect (z σ) - f (u σ)` of `g` along `z`.
  let b : G → B := fun σ => S.sect ((z : G → C) σ) - S.f ((u : Cochain1 G A) σ)
  have hb_lc : IsLocallyConstant b := by
    have h1 : IsLocallyConstant fun σ : G => S.sect ((z : G → C) σ) :=
      isLocallyConstant_sect_comp S (z : Cochain1 G C)
    have h2 : IsLocallyConstant fun σ : G => S.f ((u : Cochain1 G A) σ) :=
      ((u : Cochain1 G A)).isLocallyConstant.comp (fun a : A => S.f a)
    exact h1.sub h2
  -- `b` is a crossed homomorphism: `d¹b = d¹(sect ∘ z) - f (d¹u) = 0`.
  have hb_coc : IsCocycle1 b := by
    rw [isCocycle1_iff_d1Fun]
    funext p
    obtain ⟨σ, τ⟩ := p
    have hsplit : d1Fun (G := G) b (σ, τ)
        = d1Fun (G := G) (fun ν : G => S.sect ((z : G → C) ν)) (σ, τ)
          - d1Fun (G := G) (fun ν : G => S.f ((u : Cochain1 G A) ν)) (σ, τ) := by
      rw [show b = (fun ν : G => S.sect ((z : G → C) ν))
          - (fun ν : G => S.f ((u : Cochain1 G A) ν)) from rfl]
      rw [sub_eq_add_neg, d1Fun_add, d1Fun_neg, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
    have h₂ : d1Fun (G := G) (fun ν : G => S.f ((u : Cochain1 G A) ν)) (σ, τ) =
        S.f (d1Fun (G := G) (u : G → A) (σ, τ)) := by
      rw [d1Fun_comp]
    rw [hsplit, h₂, hkey σ τ, d1Fun_apply, sub_self]
    rfl
  refine ⟨H1.mk ⟨⟨b, hb_lc⟩, mem_Z1.mpr hb_coc⟩, ?_⟩
  rw [H1Map_mk]
  congr 1
  refine Subtype.ext ?_
  refine LocallyConstant.ext fun σ => ?_
  simp only [Z1Map_coe]
  change S.g (b σ) = (z : G → C) σ
  dsimp only [b]
  simp only [EqHom.map_sub, CoeffSES.g_sect, g_f_eq_zero S (u σ), sub_zero]

end Helpers

lemma exact_H1_C {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (x : H1 G C) :
    connecting1 S x = 0 ↔ ∃ y : H1 G B, H1Map S.g y = x := by
  constructor
  · exact exists_H1Map_g_eq_of_connecting1_eq_zero S x
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact connecting1_H1Map_g_eq_zero S y

end Work.ConCohomology
