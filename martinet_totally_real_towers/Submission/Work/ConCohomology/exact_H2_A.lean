/-
Copyright: the martinet_totally_real_towers team.

# Exactness at `H²(G,A)`: the kernel of `H²(A) → H²(B)` is the image of `δ¹`

This module proves the exactness of the long exact sequence of continuous cohomology of a
topological group with discrete coefficients, at the term `H²(G,A)`:

`H¹(G,C) --δ¹--> H²(G,A) --f_*--> H²(G,B)`

i.e. a class `x ∈ H²(G,A)` dies under the coefficient map induced by `f` if and only if it is
the connecting image of a class in `H¹(G,C)`.

The two inclusions are proved separately.

* **`H2Map_connecting1`** (`im δ¹ ⊆ ker f_*`).  If `c` is a `1`-cocycle with values in `C` and
  `u σ = S.sect (c σ)` is the chosen section of the projection at `c`, then the definition of the
  connecting cochain gives
  `S.f (S.delta1Fun c (σ,τ)) = σ • u τ - u (σ*τ) + u σ`,
  so that `f_* (δ¹[c]) = [d¹u] = 0`.

* **`exists_connecting1_eq_of_H2Map_eq_zero`** (`ker f_* ⊆ im δ¹`).  Given a `2`-cocycle `z` with
  values in `A` whose image under `f` is a coboundary, say `f ∘ z = d¹u`, one puts
  `c σ = g (u σ)`; the displayed identity shows that `c` is a `1`-cocycle with values in `C`.
  The difference `u - sect ∘ c` then takes values in `im f`, and
  `v σ = S.invFun (u σ - S.sect (c σ)) ∈ A` satisfies `z - delta1Fun c = -d¹v`; hence
  `δ¹[c] = [z]`.  This is the standard diagram chase, made precise with the set-theoretic
  inverse `S.invFun` of the injection `f`.

Everything is proved on the level of cochains; the cohomological statements follow by passing to
the quotients `H¹`, `H²`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting
import Submission.Work.ConCohomology.isCocycle2_delta1Fun

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Aux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-- The `f`-image of the connecting cochain of a `1`-cocycle `c` with values in `C` is the
explicit coboundary expression `σ • s(c τ) - s(c (σ*τ)) + s(c σ)`, where `s = S.sect` is the
chosen set-theoretic section of the projection `g`. -/
lemma f_delta1Fun_eq (S : CoeffSES G A B C) (c : Cochain1 G C) (hc : IsCocycle1 (c : G → C))
    (σ τ : G) :
    S.f (S.delta1Fun (c : G → C) (σ, τ))
      = σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ) := by
  rw [CoeffSES.delta1Fun_apply]
  refine invFun_f_eq_delta1Fun_aux S ((S.exact _).mp ?_)
  simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
  rw [hc σ τ]
  abel

/-- The pointwise form of the identification `δ¹[c] = [z]`: if the `f`-image of the `2`-cocycle
`z` is the coboundary `d¹u` and `v` measures the difference of `u` from the section at
`c = g ∘ u`, then `delta1Fun c - z = -d¹v` pointwise. -/
lemma delta1Fun_sub_z_eq (S : CoeffSES G A B C) (c : Cochain1 G C) (hc : IsCocycle1 (c : G → C))
    (z : Z2 G A) (u : Cochain1 G B)
    (key : ∀ σ τ : G, σ • (u : G → B) τ - (u : G → B) (σ * τ) + (u : G → B) σ
      = S.f ((z : Cochain2 G A) (σ, τ)))
    (vFun : G → A) (hvLC : IsLocallyConstant vFun)
    (hv : ∀ σ : G, S.f (vFun σ) = (u : G → B) σ - S.sect (c σ))
    (σ τ : G) :
    (↑(connectingZ1 S (⟨c, mem_Z1.mpr hc⟩ : Z1 G C)) : Cochain2 G A) (σ, τ)
        - (z : Cochain2 G A) (σ, τ)
      = -(d1Hom G A (⟨vFun, hvLC⟩ : Cochain1 G A)) (σ, τ) := by
  show S.delta1Fun (c : G → C) (σ, τ) - (z : Cochain2 G A) (σ, τ)
      = -(d1Fun (G := G) vFun (σ, τ))
  apply S.injective_f
  rw [EqHom.map_sub, EqHom.map_neg, f_delta1Fun_eq S c hc σ τ, d1Fun_apply,
    EqHom.map_add, EqHom.map_sub, EqHom.map_smul, hv τ, hv (σ * τ), hv σ, ← key σ τ]
  simp only [smul_sub]
  abel

/-- The composite `H²(G,A) → H²(G,B)` of the coefficient map induced by `f` with the connecting
map `δ¹ : H¹(G,C) → H²(G,A)` is zero. -/
lemma H2Map_connecting1 (S : CoeffSES G A B C) (y : H1 G C) :
    H2Map S.f (connecting1 S y) = 0 := by
  refine QuotientAddGroup.induction_on y fun z => ?_
  show H2Map S.f (connecting1 S (H1.mk z)) = 0
  rw [connecting1_mk, H2Map_mk, H2.mk_eq_zero_iff]
  rw [mem_B2', mem_B2]
  refine ⟨⟨fun σ => S.sect ((z : Cochain1 G C) σ),
      (z : Cochain1 G C).isLocallyConstant.comp S.sect⟩, ?_⟩
  refine LocallyConstant.ext fun p => ?_
  obtain ⟨σ, τ⟩ := p
  rw [d1Hom_apply]
  simp only [Z2Map_coe, cochain2Map_apply, connectingZ1_coe, LocallyConstant.coe_mk]
  rw [CoeffSES.delta1Fun_apply]
  exact (invFun_f_eq_delta1Fun_aux S (by
    refine (S.exact _).mp ?_
    simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
    rw [mem_Z1.mp z.2 σ τ]
    abel)).symm

/-- The kernel of `H²(G,A) → H²(G,B)` consists of connecting classes: if the image of the class
of a `2`-cocycle `z` under `f_*` vanishes, then `[z] = δ¹[y]` for some class `y ∈ H¹(G,C)`. -/
lemma exists_connecting1_eq_of_H2Map_eq_zero (S : CoeffSES G A B C) (z : Z2 G A)
    (h : H2Map S.f (H2.mk z) = 0) :
    ∃ y : H1 G C, connecting1 S y = H2.mk z := by
  have h1 : Z2Map S.f z ∈ B2' G B :=
    (H2.mk_eq_zero_iff _).mp (by simpa [H2Map_mk] using h)
  obtain ⟨u, hu⟩ := (mem_B2 (G := G) (M := B)).mp ((mem_B2' (G := G) (M := B)).mp h1)
  -- the pointwise form of `f ∘ z = d¹u`
  have key : ∀ σ τ : G, σ • (u : G → B) τ - (u : G → B) (σ * τ) + (u : G → B) σ
      = S.f ((z : Cochain2 G A) (σ, τ)) := by
    intro σ τ
    have h := congrArg (fun w : Cochain2 G B => w (σ, τ)) hu
    simp only [d1Hom_apply, Z2Map_coe, cochain2Map_apply] at h
    exact h
  -- `c = g ∘ u` is a `1`-cocycle with values in `C`
  have hcomp : d1Fun (G := G) ((cochain1Map S.g u : Cochain1 G C) : G → C)
      = fun p : G × G => S.g (d1Fun (G := G) (u : G → B) p) := by
    rw [show ((cochain1Map S.g u : Cochain1 G C) : G → C)
          = fun σ => S.g ((u : G → B) σ) from funext fun σ => cochain1Map_apply S.g u σ]
    exact d1Fun_comp S.g (u : G → B)
  have hcCyc : IsCocycle1 ((cochain1Map S.g u : Cochain1 G C) : G → C) := by
    rw [isCocycle1_iff_d1Fun, hcomp]
    funext p
    obtain ⟨σ, τ⟩ := p
    rw [d1Fun_apply, key σ τ]
    exact (S.exact (S.f ((z : Cochain2 G A) (σ, τ)))).mpr ⟨_, rfl⟩
  -- `v` measures `u - sect ∘ c` in `A`
  set vFun : G → A :=
    fun σ : G => S.invFun ((u : G → B) σ - S.sect ((cochain1Map S.g u : Cochain1 G C) σ))
    with hvFun
  have hvLC : IsLocallyConstant vFun := by
    rw [hvFun]
    exact (u.isLocallyConstant.sub
      ((cochain1Map S.g u : Cochain1 G C).isLocallyConstant.comp S.sect)).comp S.invFun
  have hv : ∀ σ : G, S.f (vFun σ)
      = (u : G → B) σ - S.sect ((cochain1Map S.g u : Cochain1 G C) σ) := by
    intro σ
    rw [hvFun]
    refine invFun_f_eq_delta1Fun_aux S ((S.exact _).mp ?_)
    show S.g ((u : G → B) σ - S.sect ((cochain1Map S.g u : Cochain1 G C) σ)) = 0
    rw [EqHom.map_sub, CoeffSES.g_sect, ← cochain1Map_apply S.g u σ]
    abel
  have hcoe : (↑(connectingZ1 S
        (⟨(cochain1Map S.g u : Cochain1 G C), mem_Z1.mpr hcCyc⟩ : Z1 G C) - z)
        : Cochain2 G A) = -(d1Hom G A (⟨vFun, hvLC⟩ : Cochain1 G A)) := by
    rw [AddSubgroup.coe_sub]
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    rw [LocallyConstant.sub_apply, LocallyConstant.neg_apply]
    exact delta1Fun_sub_z_eq S (cochain1Map S.g u) hcCyc z u key vFun hvLC hv σ τ
  refine ⟨H1.mk ⟨(cochain1Map S.g u : Cochain1 G C), mem_Z1.mpr hcCyc⟩, ?_⟩
  rw [connecting1_mk, H2.mk_eq_mk_iff]
  rw [mem_B2', mem_B2]
  refine ⟨-(⟨vFun, hvLC⟩ : Cochain1 G A), ?_⟩
  rw [map_neg]
  exact hcoe.symm

end Aux

/-- **Exactness at `H²(G,A)`.**  For a short exact sequence `0 → A → B → C → 0` of discrete
`G`-modules, the kernel of the coefficient map `H²(G,A) → H²(G,B)` is the image of the
connecting homomorphism `δ¹ : H¹(G,C) → H²(G,A)`. -/
lemma exact_H2_A {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (x : H2 G A) :
    H2Map S.f x = 0 ↔ ∃ y : H1 G C, connecting1 S y = x := by
  constructor
  · intro h
    revert h
    refine QuotientAddGroup.induction_on x ?_
    intro z hz
    exact exists_connecting1_eq_of_H2Map_eq_zero S z hz
  · rintro ⟨y, rfl⟩
    exact H2Map_connecting1 S y

end Work.ConCohomology
