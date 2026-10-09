/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The dimension shift `Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` as a natural family

`Work.CohomologicalShrinking.shiftH2Family` produces, for every coefficient module `T` over
`𝔽_p = ZMod p`, a family of additive isomorphisms

`s m : H²(G, E(m,τ) ⊗ T) ≃+ Ĥ⁻¹(G, E(m,τ) ⊗ (T ⊗ A₂))`

which is *natural* in the level `m`: for every surjective `G`-operator homomorphism
`Φ : F(m) ⇢ F(n)` the corresponding square commutes.  This is the dimension shift
`Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ I_G^{-3})` of Schmidt–Wingberg's Proposition 6, in the form needed to
feed the shrinking statement `exists_shrinking_H2_of_shift`.

The chain is the paper's

`H²(G, X) ≅ H¹(G, X^*) ≅ Ĥ⁰(G, X^{**}) ≅ Ĥ⁻¹(G, X^{***})`

with `X^* = Coind(X)/X ≅ X ⊗ I_G^{-1}`, and the composites are natural by
`tate.dimensionShiftH2H1_natural`, `tate.dimensionShiftH1H0_natural` and
`tate.dimensionShiftCoind_natural`, transported along the coefficient isomorphisms.
-/
import Mathlib
import Submission.Work.CohomologicalShrinking.Levels
import Submission.Work.CohomologicalShrinking.Corollaries
import Submission.Work.CohomologicalShrinking.coindShiftAddEquivTensor
import Submission.Work.CohomologicalShrinking.shiftTensor.assocTripleTensorGen
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftH2H1_natural
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural
import Submission.Work.CohomologicalShrinking.tate.dimensionShiftCoind_natural
import Submission.Work.GroupCohomology.All

namespace Work.CohomologicalShrinking

open scoped TensorProduct
open scoped BigOperators

universe u v

set_option maxHeartbeats 8000000

attribute [local instance] Classical.decEq

section Helper

variable {p : ℕ}

/-! ## Functoriality of the shift `A ↦ A^* = Coind(A)/A` -/

/-- The map `A^* → B^*` induced by a `G`-equivariant additive map `φ : A →+ B`, where
`A^* = Coind(A)/A`. -/
noncomputable def coindShiftMap {G A B : Type*} [Group G] [Fintype G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (φ : A →+ B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) :
    Work.Tate.coindShift G A →+ Work.Tate.coindShift G B :=
  QuotientAddGroup.lift (Work.Tate.coindDiag G A)
    ((Work.Tate.coindProj G B).comp (Work.Tate.coindMap φ)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.Tate.coindProj_eq_zero_iff]
      rw [Work.Tate.mem_coindDiag_iff] at hx
      obtain ⟨a, rfl⟩ := hx
      exact (Work.Tate.mem_coindDiag_iff G B).mpr
        ⟨φ a, by funext y; rw [Work.Tate.coindMap_apply, hφ y a]⟩)

theorem coindShiftMap_proj {G A B : Type*} [Group G] [Fintype G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (φ : A →+ B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (f : G → A) :
    coindShiftMap φ hφ (Work.Tate.coindProj G A f)
      = Work.Tate.coindProj G B (Work.Tate.coindMap φ f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem coindShiftMap_equiv {G A B : Type*} [Group G] [Fintype G] [AddCommGroup A]
    [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (φ : A →+ B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a) (γ : G)
    (x : Work.Tate.coindShift G A) :
    coindShiftMap φ hφ (γ • x) = γ • coindShiftMap φ hφ x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change coindShiftMap φ hφ (Work.Tate.coindProj G A (γ • f))
      = γ • coindShiftMap φ hφ (Work.Tate.coindProj G A f)
  rw [coindShiftMap_proj, coindShiftMap_proj, Work.Tate.coindMap_equiv φ hφ,
    ← Work.Tate.coindProj_equiv]

/-! ## Small functoriality lemmas for `H¹`, `Ĥ⁰` and `Ĥ⁻¹` -/

theorem mapH1_congr {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] {φ φ' : A →+ B}
    (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hφ' : Work.GroupCohomology.IsEquivariant G φ') (h : φ = φ') :
    Work.GroupCohomology.mapH1 G φ hφ = Work.GroupCohomology.mapH1 G φ' hφ' := by
  subst h
  rw [Subsingleton.elim hφ hφ']

theorem H0Map_congr {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] [Fintype G] {f f' : A →+ B}
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hf' : ∀ (γ : G) (a : A), f' (γ • a) = γ • f' a) (h : f = f') :
    Work.Tate.H0Map G A B f hf = Work.Tate.H0Map G A B f' hf' := by
  subst h
  rw [Subsingleton.elim hf hf']

theorem Hm1Map_congr {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] [Fintype G] {f f' : A →+ B}
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (hf' : ∀ (γ : G) (a : A), f' (γ • a) = γ • f' a) (h : f = f') :
    Work.Tate.Hm1Map G A B f hf = Work.Tate.Hm1Map G A B f' hf' := by
  subst h
  rw [Subsingleton.elim hf hf']

theorem H0Map_comp {G A B C : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [Fintype G] (e : A →+ B) (he : ∀ (γ : G) (a : A), e (γ • a) = γ • e a)
    (f : B →+ C) (hf : ∀ (γ : G) (b : B), f (γ • b) = γ • f b)
    (hfe : ∀ (γ : G) (a : A), (f.comp e) (γ • a) = γ • (f.comp e) a) :
    Work.Tate.H0Map G A C (f.comp e) hfe
      = (Work.Tate.H0Map G B C f hf).comp (Work.Tate.H0Map G A B e he) := by
  apply AddMonoidHom.ext
  intro x
  induction x using Work.Tate.H0_induction_on with
  | h a =>
    rw [Work.Tate.H0Map_H0π, AddMonoidHom.comp_apply, Work.Tate.H0Map_H0π, Work.Tate.H0Map_H0π]
    apply congrArg (Work.Tate.H0π G C)
    apply Subtype.ext
    simp [Work.Tate.mapFixed_apply]

theorem mapH1_bijective_of_bijective {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] (e : A ≃+ B)
    (he : ∀ (γ : G) (a : A), e (γ • a) = γ • e a) :
    Function.Bijective (Work.GroupCohomology.mapH1 G e.toAddMonoidHom
      (show Work.GroupCohomology.IsEquivariant G e.toAddMonoidHom from he)) := by
  have hsym : ∀ (γ : G) (b : B), e.symm (γ • b) = γ • e.symm b := by
    intro γ b
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  have hsym' : Work.GroupCohomology.IsEquivariant G e.symm.toAddMonoidHom := hsym
  have he' : Work.GroupCohomology.IsEquivariant G e.toAddMonoidHom := he
  have hc1 : e.toAddMonoidHom.comp e.symm.toAddMonoidHom = AddMonoidHom.id B := by
    ext b; simp
  have hc2 : e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id A := by
    ext b; simp
  have hcomp1 : (Work.GroupCohomology.mapH1 G e.toAddMonoidHom he').comp
      (Work.GroupCohomology.mapH1 G e.symm.toAddMonoidHom hsym')
      = AddMonoidHom.id (Work.GroupCohomology.H1 G B) := by
    rw [← Work.GroupCohomology.mapH1_comp]
    exact (mapH1_congr (φ := e.toAddMonoidHom.comp e.symm.toAddMonoidHom)
      (φ' := AddMonoidHom.id B) _ _ hc1).trans (Work.GroupCohomology.mapH1_id (G := G) (A := B))
  have hcomp2 : (Work.GroupCohomology.mapH1 G e.symm.toAddMonoidHom hsym').comp
      (Work.GroupCohomology.mapH1 G e.toAddMonoidHom he')
      = AddMonoidHom.id (Work.GroupCohomology.H1 G A) := by
    rw [← Work.GroupCohomology.mapH1_comp]
    exact (mapH1_congr (φ := e.symm.toAddMonoidHom.comp e.toAddMonoidHom)
      (φ' := AddMonoidHom.id A) _ _ hc2).trans (Work.GroupCohomology.mapH1_id (G := G) (A := A))
  constructor
  · intro x y hxy
    have hx := DFunLike.congr_fun hcomp2 x
    have hy := DFunLike.congr_fun hcomp2 y
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hx hy
    rw [hxy] at hx
    exact hx.symm.trans hy
  · intro y
    refine ⟨(Work.GroupCohomology.mapH1 G e.symm.toAddMonoidHom hsym') y, ?_⟩
    have h := DFunLike.congr_fun hcomp1 y
    simpa using h

/-! ## Naturality of the associator for the diagonal action -/

theorem tensorAssoc_smul {G M N P : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [AddCommGroup P] [Module (ZMod p) P] [DistribMulAction G P] [SMulCommClass G (ZMod p) P]
    (γ : G) (x : (M ⊗[ZMod p] N) ⊗[ZMod p] P) :
    TensorProduct.assoc (ZMod p) M N P (γ • x)
      = γ • TensorProduct.assoc (ZMod p) M N P x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y q =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
          rw [Work.Shrinking.diagTensor_smul_tmul (p := p) (G := G) γ (m ⊗ₜ[ZMod p] n) q,
            Work.Shrinking.diagTensor_smul_tmul (p := p) (G := G) γ m n,
            TensorProduct.assoc_tmul, TensorProduct.assoc_tmul,
            Work.Shrinking.diagTensor_smul_tmul (p := p) (G := G) γ m (n ⊗ₜ[ZMod p] q),
            Work.Shrinking.diagTensor_smul_tmul (p := p) (G := G) γ n q]
      | add y1 y2 h1 h2 =>
          rw [TensorProduct.add_tmul]
          simp only [smul_add, map_add, h1, h2]
  | add x1 x2 h1 h2 =>
      simp only [smul_add, map_add, h1, h2]

theorem tensorAssoc_natural {N P : Type*} [AddCommGroup N] [Module (ZMod p) N]
    [AddCommGroup P] [Module (ZMod p) P]
    {M M' : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup M'] [Module (ZMod p) M'] (f : M →ₗ[ZMod p] M') :
    (TensorProduct.assoc (ZMod p) M' N P).toAddMonoidHom.comp
        ((f.rTensor N).rTensor P).toAddMonoidHom
      = (f.rTensor (N ⊗[ZMod p] P)).toAddMonoidHom.comp
          (TensorProduct.assoc (ZMod p) M N P).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y q =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
          show TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) ((m ⊗ₜ n) ⊗ₜ q))
            = (f.rTensor (N ⊗[ZMod p] P)) (TensorProduct.assoc (ZMod p) M N P ((m ⊗ₜ n) ⊗ₜ q))
          rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.assoc_tmul,
            TensorProduct.assoc_tmul, LinearMap.rTensor_tmul]
      | add y1 y2 h1 h2 =>
          have h1' : TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) (y1 ⊗ₜ q))
              = (f.rTensor (N ⊗[ZMod p] P))
                  (TensorProduct.assoc (ZMod p) M N P (y1 ⊗ₜ q)) := h1
          have h2' : TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) (y2 ⊗ₜ q))
              = (f.rTensor (N ⊗[ZMod p] P))
                  (TensorProduct.assoc (ZMod p) M N P (y2 ⊗ₜ q)) := h2
          show TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) ((y1 + y2) ⊗ₜ q))
            = (f.rTensor (N ⊗[ZMod p] P))
                (TensorProduct.assoc (ZMod p) M N P ((y1 + y2) ⊗ₜ q))
          simp only [TensorProduct.add_tmul, map_add, h1', h2']
  | add x1 x2 h1 h2 =>
      have h1' : TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) x1)
          = (f.rTensor (N ⊗[ZMod p] P)) (TensorProduct.assoc (ZMod p) M N P x1) := h1
      have h2' : TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) x2)
          = (f.rTensor (N ⊗[ZMod p] P)) (TensorProduct.assoc (ZMod p) M N P x2) := h2
      show TensorProduct.assoc (ZMod p) M' N P (((f.rTensor N).rTensor P) (x1 + x2))
        = (f.rTensor (N ⊗[ZMod p] P)) (TensorProduct.assoc (ZMod p) M N P (x1 + x2))
      simp only [map_add, h1', h2']

/-! ## Two pasting lemmas for commutative ladders -/

/-- Pasting of two commuting squares of additive homomorphisms. -/
theorem paste {X0 X0' Y0 Y0' X1 X1' : Type*}
    [AddCommMonoid X0] [AddCommMonoid X0'] [AddCommMonoid Y0] [AddCommMonoid Y0']
    [AddCommMonoid X1] [AddCommMonoid X1']
    (P : X0 →+ Y0) (P' : X0' →+ Y0') (c : Y0 →+ X1) (c' : Y0' →+ X1')
    (α : X0 →+ X0') (β : Y0 →+ Y0') (α' : X1 →+ X1')
    (hP : P'.comp α = β.comp P) (hc : c'.comp β = α'.comp c) :
    (c'.comp P').comp α = α'.comp (c.comp P) := by
  rw [AddMonoidHom.comp_assoc, hP, ← AddMonoidHom.comp_assoc, hc, AddMonoidHom.comp_assoc]

/-- Inverting a commuting square in which the vertical maps are equivalences. -/
theorem symm_paste {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X']
    [AddCommGroup Y] [AddCommGroup Y'] (e : X ≃+ X') (g : Y ≃+ Y') (φ : X →+ Y) (ψ : X' →+ Y')
    (h : ψ.comp e.toAddMonoidHom = g.toAddMonoidHom.comp φ) :
    g.symm.toAddMonoidHom.comp ψ = φ.comp e.symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  show g.symm (ψ z) = φ (e.symm z)
  apply g.injective
  rw [AddEquiv.apply_symm_apply]
  have hh := DFunLike.congr_fun h (e.symm z)
  simp only [AddMonoidHom.comp_apply] at hh
  simpa using hh

/-- The `IsEquivariant` form of a `∀`-formulated equivariance hypothesis. -/
theorem isEquivariant_of_forall {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B] {f : A →+ B}
    (h : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) :
    Work.GroupCohomology.IsEquivariant G f := h


/-- Equivariance of a composite of equivariant additive maps. -/
theorem IsEquivariant.comp' {G A B C : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (e : A →+ B) (he : ∀ (γ : G) (a : A), e (γ • a) = γ • e a)
    (f : B →+ C) (hf : ∀ (γ : G) (b : B), f (γ • b) = γ • f b) :
    ∀ (γ : G) (a : A), (f.comp e) (γ • a) = γ • (f.comp e) a := by
  intro γ a
  rw [AddMonoidHom.comp_apply, he, hf, AddMonoidHom.comp_apply]

theorem bijective_comp {X Y Z : Type*} [AddMonoid X] [AddMonoid Y] [AddMonoid Z]
    {f : Y →+ Z} {g : X →+ Y} (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (f.comp g) := by
  refine ⟨fun a b h => hg.1 (hf.1 ?_), fun c => ?_⟩
  · simpa only [AddMonoidHom.comp_apply] using h
  · obtain ⟨b, hb⟩ := hf.2 c
    obtain ⟨a, ha⟩ := hg.2 b
    exact ⟨a, by rw [AddMonoidHom.comp_apply, ha, hb]⟩

end Helper

section Main

/-- The dimension shift `Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` for a natural family of coefficient
isomorphisms.  This is the main body of `shiftH2Family`, with the two coefficient
isomorphisms `X^* ≅ X ⊗ I_G^{-1}` and `((X ⊗ I_G^{-1}) ⊗ I_G^{-1}) ⊗ I_G^{-1} ≅ X ⊗ A₂` taken as
explicit data. -/
theorem shiftH2Family_of_data (p : ℕ) [NeZero p] (G : Type u) [Group G] [Fintype G] {i j : ℕ}
    (T : Type v) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (L : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X], Work.Tate.coindShift G X ≃+ X ⊗[ZMod p] igDual p G)
    (L_equiv : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X] (γ : G) (x : Work.Tate.coindShift G X),
        L X (γ • x) = γ • L X x)
    (L_nat : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X]
        (Y : Type (max u v)) [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y]
        [SMulCommClass G (ZMod p) Y]
        (f : X →ₗ[ZMod p] Y) (hf : ∀ (γ : G) (a : X), f (γ • a) = γ • f a)
        (ψ : Work.Tate.coindShift G X →+ Work.Tate.coindShift G Y)
        (hψproj : ∀ x : G → X, ψ (Work.Tate.coindProj G X x)
          = Work.Tate.coindProj G Y (Work.Tate.coindMap (f.toAddMonoidHom) x)),
        (L Y).toAddMonoidHom.comp ψ
          = ((LinearMap.rTensor (igDual p G) f).toAddMonoidHom).comp (L X).toAddMonoidHom)
    (R : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X],
        ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G
          ≃+ (X ⊗[ZMod p] A2 p G))
    (R_equiv : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X] (γ : G)
        (x : ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G),
        R X (γ • x) = γ • R X x)
    (R_nat : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
        [SMulCommClass G (ZMod p) X]
        (Y : Type (max u v)) [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y]
        [SMulCommClass G (ZMod p) Y]
        (f : X →ₗ[ZMod p] Y) (hf : ∀ (γ : G) (a : X), f (γ • a) = γ • f a),
        (R Y).toAddMonoidHom.comp
            (((f.rTensor (igDual p G)).rTensor (igDual p G)).rTensor (igDual p G)).toAddMonoidHom
          = ((f.rTensor (A2 p G)).toAddMonoidHom).comp (R X).toAddMonoidHom) :
    ∃ s : ∀ m : ℕ, GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T) ≃+
        Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G)),
      ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
        ((s n).toAddMonoidHom).comp (OperatorMap.h2Map p G T Φ)
          = (OperatorMap.hm1Map p G (T ⊗[ZMod p] A2 p G) Φ).comp ((s m).toAddMonoidHom) := by
  classical
  -- ### the seven stages of the chain `X ↦ Ĥ⁻¹(G, X ⊗ A₂)`
  let c0 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      GroupCohomology.H2 G X →+ GroupCohomology.H1 G (Work.Tate.coindShift G X) :=
    fun X _ _ _ _ => (Work.Tate.dimensionShiftH2H1 G X).toAddMonoidHom
  let c1 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      GroupCohomology.H1 G (Work.Tate.coindShift G X) →+ GroupCohomology.H1 G (X ⊗[ZMod p] igDual p G) :=
    fun X _ _ _ _ => GroupCohomology.mapH1 G (L X).toAddMonoidHom
      (isEquivariant_of_forall (L_equiv X))
  let c2 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      GroupCohomology.H1 G (X ⊗[ZMod p] igDual p G) →+
        Work.Tate.H0 G (Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G)) :=
    fun X _ _ _ _ => (Work.Tate.dimensionShiftH1H0 G (X ⊗[ZMod p] igDual p G)).toAddMonoidHom
  let c3 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      Work.Tate.H0 G (Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G)) →+
        Work.Tate.H0 G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) :=
    fun X _ _ _ _ => Work.Tate.H0Map G (Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
      ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom
      (L_equiv (X ⊗[ZMod p] igDual p G))
  let c4 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      Work.Tate.H0 G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) →+
        Work.Tate.Hm1 G (Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) :=
    fun X _ _ _ _ => ((Work.Tate.dimensionShiftCoind G
      ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).symm).toAddMonoidHom
  let c5 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      Work.Tate.Hm1 G (Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) →+
        Work.Tate.Hm1 G (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) :=
    fun X _ _ _ _ => Work.Tate.Hm1Map G
      (Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
      (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
      (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom
      (L_equiv ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
  let c6 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X],
      Work.Tate.Hm1 G (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) →+
        Work.Tate.Hm1 G (X ⊗[ZMod p] A2 p G) :=
    fun X _ _ _ _ => Work.Tate.Hm1Map G
      (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) (X ⊗[ZMod p] A2 p G)
      (R X).toAddMonoidHom (R_equiv X)
  -- the seven-fold composite
  let cx : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X]
      [SMulCommClass G (ZMod p) X], GroupCohomology.H2 G X →+ Work.Tate.Hm1 G (X ⊗[ZMod p] A2 p G) :=
    fun X _ _ _ _ =>
      (c6 X).comp ((c5 X).comp ((c4 X).comp ((c3 X).comp ((c2 X).comp ((c1 X).comp (c0 X))))))
  -- bijectivity of the stages
  have hbij_c0 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c0 X) := by
    intro X _ _ _ _
    simp only [c0]
    exact (Work.Tate.dimensionShiftH2H1 G X).bijective
  have hbij_c1 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c1 X) := by
    intro X _ _ _ _
    simp only [c1]
    exact mapH1_bijective_of_bijective (L X) (L_equiv X)
  have hbij_c2 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c2 X) := by
    intro X _ _ _ _
    simp only [c2]
    exact (Work.Tate.dimensionShiftH1H0 G (X ⊗[ZMod p] igDual p G)).bijective
  have hbij_c3 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c3 X) := by
    intro X _ _ _ _
    simp only [c3]
    exact Work.Tate.H0Map_bijective _ (L_equiv (X ⊗[ZMod p] igDual p G))
      (L (X ⊗[ZMod p] igDual p G)).bijective
  have hbij_c4 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c4 X) := by
    intro X _ _ _ _
    simp only [c4]
    exact ((Work.Tate.dimensionShiftCoind G
      ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).symm).bijective
  have hbij_c5 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c5 X) := by
    intro X _ _ _ _
    simp only [c5]
    exact Work.Tate.Hm1Map_bijective _
      (L_equiv ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
      (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).bijective
  have hbij_c6 : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (c6 X) := by
    intro X _ _ _ _
    simp only [c6]
    exact Work.Tate.Hm1Map_bijective _ (R_equiv X) (R X).bijective
  have hbij_cx : ∀ (X : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X], Function.Bijective (cx X) := by
    intro X _ _ _ _
    simp only [cx]
    exact bijective_comp (hbij_c6 X)
      (bijective_comp (hbij_c5 X) (bijective_comp (hbij_c4 X)
        (bijective_comp (hbij_c3 X) (bijective_comp (hbij_c2 X)
          (bijective_comp (hbij_c1 X) (hbij_c0 X))))))
  -- ### naturality of the seven-fold composite
  have cx_nat : ∀ (X Y : Type (max u v)) [AddCommGroup X] [Module (ZMod p) X]
      [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
      [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y] [SMulCommClass G (ZMod p) Y]
      (f : X →ₗ[ZMod p] Y) (hf : ∀ (γ : G) (a : X), f (γ • a) = γ • f a),
      (cx Y).comp (GroupCohomology.mapH2 G f.toAddMonoidHom
          (show Work.GroupCohomology.IsEquivariant G f.toAddMonoidHom from hf))
        = (Work.Tate.Hm1Map G (X ⊗[ZMod p] A2 p G) (Y ⊗[ZMod p] A2 p G)
            (f.rTensor (A2 p G)).toAddMonoidHom
            (fun γ a => rTensor_equiv p (G := G) (f := f) hf γ a)).comp (cx X) := by
    intro X Y _ _ _ _ _ _ _ _ f hf
    -- the induced maps between the intermediate coefficients
    let ψ1 : Work.Tate.coindShift G X →+ Work.Tate.coindShift G Y :=
      coindShiftMap f.toAddMonoidHom (fun γ a => hf γ a)
    let f2 : X ⊗[ZMod p] igDual p G →ₗ[ZMod p] Y ⊗[ZMod p] igDual p G :=
      f.rTensor (igDual p G)
    have hf2 : ∀ (γ : G) (a : X ⊗[ZMod p] igDual p G), f2 (γ • a) = γ • f2 a :=
      fun γ a => rTensor_equiv p (G := G) (f := f) hf γ a
    let ψ2 : Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G) →+
        Work.Tate.coindShift G (Y ⊗[ZMod p] igDual p G) :=
      coindShiftMap f2.toAddMonoidHom (fun γ a => hf2 γ a)
    let f3 : (X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G →ₗ[ZMod p]
        (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G := f2.rTensor (igDual p G)
    have hf3 : ∀ (γ : G) (a : (X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G),
        f3 (γ • a) = γ • f3 a :=
      fun γ a => rTensor_equiv p (G := G) (f := f2) hf2 γ a
    let ψ3 : Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) →+
        Work.Tate.coindShift G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) :=
      coindShiftMap f3.toAddMonoidHom (fun γ a => hf3 γ a)
    let f4 : ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G →ₗ[ZMod p]
        ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G :=
      f3.rTensor (igDual p G)
    have hf4 : ∀ (γ : G) (a : ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
        ⊗[ZMod p] igDual p G), f4 (γ • a) = γ • f4 a :=
      fun γ a => rTensor_equiv p (G := G) (f := f3) hf3 γ a
    let f5 : X ⊗[ZMod p] A2 p G →ₗ[ZMod p] Y ⊗[ZMod p] A2 p G := f.rTensor (A2 p G)
    have hf5 : ∀ (γ : G) (a : X ⊗[ZMod p] A2 p G), f5 (γ • a) = γ • f5 a :=
      fun γ a => rTensor_equiv p (G := G) (f := f) hf γ a
    -- the level maps
    let L0 : GroupCohomology.H2 G X →+ GroupCohomology.H2 G Y :=
      GroupCohomology.mapH2 G f.toAddMonoidHom
        (show Work.GroupCohomology.IsEquivariant G f.toAddMonoidHom from hf)
    let L1 : GroupCohomology.H1 G (Work.Tate.coindShift G X) →+
        GroupCohomology.H1 G (Work.Tate.coindShift G Y) :=
      GroupCohomology.mapH1 G ψ1 (isEquivariant_of_forall (fun γ x => coindShiftMap_equiv
        f.toAddMonoidHom (fun γ a => hf γ a) γ x))
    let L2 : GroupCohomology.H1 G (X ⊗[ZMod p] igDual p G) →+
        GroupCohomology.H1 G (Y ⊗[ZMod p] igDual p G) :=
      GroupCohomology.mapH1 G f2.toAddMonoidHom (isEquivariant_of_forall (fun γ a => hf2 γ a))
    let L3 : Work.Tate.H0 G (Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G)) →+
        Work.Tate.H0 G (Work.Tate.coindShift G (Y ⊗[ZMod p] igDual p G)) :=
      Work.Tate.H0Map G (Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
        (Work.Tate.coindShift G (Y ⊗[ZMod p] igDual p G)) ψ2
        (fun γ x => coindShiftMap_equiv f2.toAddMonoidHom (fun γ a => hf2 γ a) γ x)
    let L4 : Work.Tate.H0 G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) →+
        Work.Tate.H0 G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) :=
      Work.Tate.H0Map G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
        ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) f3.toAddMonoidHom (fun γ a => hf3 γ a)
    let L5 : Work.Tate.Hm1 G (Work.Tate.coindShift G
          ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) →+
        Work.Tate.Hm1 G (Work.Tate.coindShift G
          ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) :=
      Work.Tate.Hm1Map G (Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
        (Work.Tate.coindShift G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) ψ3
        (fun γ x => coindShiftMap_equiv f3.toAddMonoidHom (fun γ a => hf3 γ a) γ x)
    let L6 : Work.Tate.Hm1 G (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          ⊗[ZMod p] igDual p G) →+
        Work.Tate.Hm1 G (((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          ⊗[ZMod p] igDual p G) :=
      Work.Tate.Hm1Map G _ _ f4.toAddMonoidHom (fun γ a => hf4 γ a)
    let L7 : Work.Tate.Hm1 G (X ⊗[ZMod p] A2 p G) →+ Work.Tate.Hm1 G (Y ⊗[ZMod p] A2 p G) :=
      Work.Tate.Hm1Map G _ _ f5.toAddMonoidHom (fun γ a => hf5 γ a)
    -- the ladder
    have h0 : (c0 Y).comp L0 = L1.comp (c0 X) := by
      simp only [c0, L0, L1, ψ1]
      exact (Work.CohomologicalShrinking.tate.dimensionShiftH2H1_natural (p := p) (G := G)
        (A := X) (B := Y) f hf (coindShiftMap f.toAddMonoidHom (fun γ a => hf γ a))
        (fun x => coindShiftMap_proj f.toAddMonoidHom (fun γ a => hf γ a) x)
        (fun γ x => coindShiftMap_equiv f.toAddMonoidHom (fun γ a => hf γ a) γ x)).symm
    have h1 : (c1 Y).comp L1 = L2.comp (c1 X) := by
      simp only [c1, L1, L2]
      exact (Work.GroupCohomology.mapH1_comp (G := G)
          (A := Work.Tate.coindShift G X) (B := Work.Tate.coindShift G Y)
          (C := Y ⊗[ZMod p] igDual p G) ψ1 (L Y).toAddMonoidHom
          (isEquivariant_of_forall (fun γ x => coindShiftMap_equiv f.toAddMonoidHom
            (fun γ a => hf γ a) γ x))
          (isEquivariant_of_forall (L_equiv Y))).symm.trans
        ((mapH1_congr (G := G) (A := Work.Tate.coindShift G X)
          (B := Y ⊗[ZMod p] igDual p G) (φ := (L Y).toAddMonoidHom.comp ψ1)
          (φ' := f2.toAddMonoidHom.comp (L X).toAddMonoidHom) _ _
          (L_nat X Y f hf ψ1
            (fun x => coindShiftMap_proj f.toAddMonoidHom (fun γ a => hf γ a) x))).trans
        (Work.GroupCohomology.mapH1_comp (G := G)
          (A := Work.Tate.coindShift G X) (B := X ⊗[ZMod p] igDual p G)
          (C := Y ⊗[ZMod p] igDual p G) (L X).toAddMonoidHom f2.toAddMonoidHom
          (isEquivariant_of_forall (L_equiv X))
          (isEquivariant_of_forall (fun γ a => hf2 γ a))))
    have h2 : (c2 Y).comp L2 = L3.comp (c2 X) := by
      simp only [c2, L2, L3, ψ2, f2, hf2]
      refine symm_paste (Work.Tate.dimensionShiftH1H0Symm G (X ⊗[ZMod p] igDual p G))
        (Work.Tate.dimensionShiftH1H0Symm G (Y ⊗[ZMod p] igDual p G))
        (Work.Tate.H0Map G _ _ ψ2 _) (GroupCohomology.mapH1 G f2.toAddMonoidHom _) ?_
      simpa only [f2] using (Work.CohomologicalShrinking.tate.dimensionShiftH1H0_natural
        (p := p) (G := G) (A := X ⊗[ZMod p] igDual p G) (B := Y ⊗[ZMod p] igDual p G)
        f2 hf2 ψ2
        (fun x => coindShiftMap_proj f2.toAddMonoidHom (fun γ a => hf2 γ a) x)
        (fun γ x => coindShiftMap_equiv f2.toAddMonoidHom (fun γ a => hf2 γ a) γ x))
    have h3 : (c3 Y).comp L3 = L4.comp (c3 X) := by
      simp only [c3, L3, L4, ψ2, f3]
      have hL3a : ∀ (γ : G) (a : Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G)),
          ((L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ2) (γ • a)
            = γ • ((L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ2) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
          (B := Work.Tate.coindShift G (Y ⊗[ZMod p] igDual p G))
          (C := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ψ2
          (fun γ x => coindShiftMap_equiv f2.toAddMonoidHom (fun γ a => hf2 γ a) γ x)
          (L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv (Y ⊗[ZMod p] igDual p G)) γ a
      have hL3b : ∀ (γ : G) (a : Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G)),
          (f3.toAddMonoidHom.comp (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom) (γ • a)
            = γ • (f3.toAddMonoidHom.comp (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
          (B := (X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv (X ⊗[ZMod p] igDual p G))
          f3.toAddMonoidHom (fun γ a => hf3 γ a) γ a
      exact (H0Map_comp (G := G)
          (A := Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
          (B := Work.Tate.coindShift G (Y ⊗[ZMod p] igDual p G))
          (C := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          ψ2 (fun γ x => coindShiftMap_equiv f2.toAddMonoidHom (fun γ a => hf2 γ a) γ x)
          (L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv (Y ⊗[ZMod p] igDual p G))
          (fun γ a => by
            show ((L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ2) (γ • a)
              = γ • ((L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ2) a
            exact hL3a γ a)).symm.trans
        ((H0Map_congr (G := G)
          (A := Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
          (B := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (f := (L (Y ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ2)
          (f' := f3.toAddMonoidHom.comp (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom)
          hL3a hL3b
          (L_nat (X ⊗[ZMod p] igDual p G) (Y ⊗[ZMod p] igDual p G) f2 hf2 ψ2
            (fun x => coindShiftMap_proj f2.toAddMonoidHom (fun γ a => hf2 γ a) x))).trans
        (H0Map_comp (G := G)
          (A := Work.Tate.coindShift G (X ⊗[ZMod p] igDual p G))
          (B := (X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv (X ⊗[ZMod p] igDual p G)) f3.toAddMonoidHom (fun γ a => hf3 γ a)
          (fun γ a => by
            show (f3.toAddMonoidHom.comp
                (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom) (γ • a)
              = γ • (f3.toAddMonoidHom.comp
                (L (X ⊗[ZMod p] igDual p G)).toAddMonoidHom) a
            exact hL3b γ a)))
    have h4 : (c4 Y).comp L4 = L5.comp (c4 X) := by
      simp only [c4, L4, L5, ψ3, f3]
      refine symm_paste
        (Work.Tate.dimensionShiftCoind G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
        (Work.Tate.dimensionShiftCoind G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
        (Work.Tate.Hm1Map G _ _ ψ3 _) (Work.Tate.H0Map G _ _ f3.toAddMonoidHom _) ?_
      simpa only [f3] using (Work.CohomologicalShrinking.tate.dimensionShiftCoind_natural
        (p := p) (G := G) (A := (X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
        (B := (Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) f3 hf3 ψ3
        (fun x => coindShiftMap_proj f3.toAddMonoidHom (fun γ a => hf3 γ a) x)
        (fun γ x => coindShiftMap_equiv f3.toAddMonoidHom (fun γ a => hf3 γ a) γ x))
    have h5 : (c5 Y).comp L5 = L6.comp (c5 X) := by
      simp only [c5, L5, L6, ψ3, f4]
      have hL5a : ∀ (γ : G) (a : Work.Tate.coindShift G
          ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)),
          ((L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ3) (γ • a)
            = γ • ((L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ3) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (B := Work.Tate.coindShift G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (C := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ψ3
          (fun γ x => coindShiftMap_equiv f3.toAddMonoidHom (fun γ a => hf3 γ a) γ x)
          (L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)) γ a
      have hL5b : ∀ (γ : G) (a : Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)),
          (f4.toAddMonoidHom.comp
              (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom) (γ • a)
            = γ • (f4.toAddMonoidHom.comp
                (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (B := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          f4.toAddMonoidHom (fun γ a => hf4 γ a) γ a
      exact (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
          (A := Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (B := Work.Tate.coindShift G ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (C := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          ψ3 (fun γ x => coindShiftMap_equiv f3.toAddMonoidHom (fun γ a => hf3 γ a) γ x)
          (L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (fun γ a => by
            show ((L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ3) (γ • a)
              = γ • ((L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ3) a
            exact hL5a γ a)).symm.trans
        ((Hm1Map_congr (G := G)
          (A := Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (B := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (f := (L ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom.comp ψ3)
          (f' := f4.toAddMonoidHom.comp
            (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom)
          hL5a hL5b
          (L_nat ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
            ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) f3 hf3 ψ3
            (fun x => coindShiftMap_proj f3.toAddMonoidHom (fun γ a => hf3 γ a) x))).trans
        (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
          (A := Work.Tate.coindShift G ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          (B := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom
          (L_equiv ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G))
          f4.toAddMonoidHom (fun γ a => hf4 γ a)
          (fun γ a => by
            show (f4.toAddMonoidHom.comp
                (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom) (γ • a)
              = γ • (f4.toAddMonoidHom.comp
                (L ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)).toAddMonoidHom) a
            exact hL5b γ a)))

    have h6 : (c6 Y).comp L6 = L7.comp (c6 X) := by
      simp only [c6, L6, L7, f4]
      have hL6a : ∀ (γ : G) (a : (((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)),
          ((R Y).toAddMonoidHom.comp f4.toAddMonoidHom) (γ • a)
            = γ • ((R Y).toAddMonoidHom.comp f4.toAddMonoidHom) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (B := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := Y ⊗[ZMod p] A2 p G)
          f4.toAddMonoidHom (fun γ a => hf4 γ a) (R Y).toAddMonoidHom (R_equiv Y) γ a
      have hL6b : ∀ (γ : G) (a : ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G),
          (f5.toAddMonoidHom.comp (R X).toAddMonoidHom) (γ • a)
            = γ • (f5.toAddMonoidHom.comp (R X).toAddMonoidHom) a :=
        fun γ a => IsEquivariant.comp' (G := G)
          (A := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (B := X ⊗[ZMod p] A2 p G)
          (C := Y ⊗[ZMod p] A2 p G)
          (R X).toAddMonoidHom (R_equiv X) f5.toAddMonoidHom (fun γ a => hf5 γ a) γ a
      exact (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
          (A := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (B := ((Y ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (C := Y ⊗[ZMod p] A2 p G)
          f4 (fun γ a => hf4 γ a)
          (R Y).toAddMonoidHom (R_equiv Y)
          (fun γ a => by
            show ((R Y).toAddMonoidHom.comp f4.toAddMonoidHom) (γ • a)
              = γ • ((R Y).toAddMonoidHom.comp f4.toAddMonoidHom) a
            exact hL6a γ a)).symm.trans
        ((Hm1Map_congr (G := G)
          (A := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (B := Y ⊗[ZMod p] A2 p G)
          (f := (R Y).toAddMonoidHom.comp f4.toAddMonoidHom)
          (f' := f5.toAddMonoidHom.comp (R X).toAddMonoidHom)
          hL6a hL6b
          (R_nat X Y f hf)).trans
        (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
          (A := ((X ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G) ⊗[ZMod p] igDual p G)
          (B := X ⊗[ZMod p] A2 p G)
          (C := Y ⊗[ZMod p] A2 p G)
          (R X).toAddMonoidHom (R_equiv X) f5.toAddMonoidHom (fun γ a => hf5 γ a)
          (fun γ a => by
            show (f5.toAddMonoidHom.comp (R X).toAddMonoidHom) (γ • a)
              = γ • (f5.toAddMonoidHom.comp (R X).toAddMonoidHom) a
            exact hL6b γ a)))

    -- pasting the ladder
    have hp1 : ((c1 Y).comp (c0 Y)).comp L0 = L2.comp ((c1 X).comp (c0 X)) := by
      rw [AddMonoidHom.comp_assoc, h0, ← AddMonoidHom.comp_assoc, h1, AddMonoidHom.comp_assoc]
    have hp2 : ((c2 Y).comp ((c1 Y).comp (c0 Y))).comp L0
        = L3.comp ((c2 X).comp ((c1 X).comp (c0 X))) := by
      rw [AddMonoidHom.comp_assoc, hp1, ← AddMonoidHom.comp_assoc, h2, AddMonoidHom.comp_assoc]
    have hp3 : ((c3 Y).comp ((c2 Y).comp ((c1 Y).comp (c0 Y)))).comp L0
        = L4.comp ((c3 X).comp ((c2 X).comp ((c1 X).comp (c0 X)))) := by
      rw [AddMonoidHom.comp_assoc, hp2, ← AddMonoidHom.comp_assoc, h3, AddMonoidHom.comp_assoc]
    have hp4 : ((c4 Y).comp ((c3 Y).comp ((c2 Y).comp ((c1 Y).comp (c0 Y))))).comp L0
        = L5.comp ((c4 X).comp ((c3 X).comp ((c2 X).comp ((c1 X).comp (c0 X))))) := by
      rw [AddMonoidHom.comp_assoc, hp3, ← AddMonoidHom.comp_assoc, h4, AddMonoidHom.comp_assoc]
    have hp5 : ((c5 Y).comp ((c4 Y).comp ((c3 Y).comp ((c2 Y).comp ((c1 Y).comp (c0 Y)))))).comp L0
        = L6.comp ((c5 X).comp ((c4 X).comp ((c3 X).comp ((c2 X).comp ((c1 X).comp (c0 X)))))) := by
      rw [AddMonoidHom.comp_assoc, hp4, ← AddMonoidHom.comp_assoc, h5, AddMonoidHom.comp_assoc]
    have hp6 : (cx Y).comp L0 = L7.comp (cx X) := by
      simp only [cx]
      rw [AddMonoidHom.comp_assoc, hp5, ← AddMonoidHom.comp_assoc, h6, AddMonoidHom.comp_assoc]
    exact hp6

  -- ### the last stage: the associator `(E(m) ⊗ T) ⊗ A₂ ≅ E(m) ⊗ (T ⊗ A₂)`
  let c7 : ∀ m : ℕ, Work.Tate.Hm1 G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G) →+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G)) :=
    fun m => Work.Tate.Hm1Map G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
      (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
      (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom
      (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x)
  let P8 : ∀ m : ℕ, GroupCohomology.H2 G (E p G m i j ⊗[ZMod p] T) →+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G)) :=
    fun m => (c7 m).comp (cx (E p G m i j ⊗[ZMod p] T))
  have hbij_c7 : ∀ m : ℕ, Function.Bijective (c7 m) := by
    intro m
    simp only [c7]
    exact Work.Tate.Hm1Map_bijective _
      (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x)
      (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).bijective
  have hbij_P8 : ∀ m : ℕ, Function.Bijective (P8 m) := by
    intro m
    simp only [P8]
    exact bijective_comp (hbij_c7 m) (hbij_cx (E p G m i j ⊗[ZMod p] T))
  refine ⟨fun m => AddEquiv.ofBijective (P8 m) (hbij_P8 m), ?_⟩
  intro m n Φ
  -- the graded operator map and its equivariance
  have hφe : ∀ (γ : G) (a : E p G m i j ⊗[ZMod p] T),
      (OperatorMap.gradedTensor p T Φ) (γ • a) = γ • (OperatorMap.gradedTensor p T Φ) a :=
    fun γ a => rTensor_equiv p (G := G)
      (f := gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a
  have hstep1 := cx_nat (E p G m i j ⊗[ZMod p] T) (E p G n i j ⊗[ZMod p] T)
    (OperatorMap.gradedTensor p T Φ) hφe
  have hstep1' : (cx (E p G n i j ⊗[ZMod p] T)).comp (OperatorMap.h2Map p G T Φ)
      = (Work.Tate.Hm1Map G _ _
          ((OperatorMap.gradedTensor p T Φ).rTensor (A2 p G)).toAddMonoidHom
          (fun γ a => rTensor_equiv p (G := G) (f := OperatorMap.gradedTensor p T Φ) hφe γ a)).comp
        (cx (E p G m i j ⊗[ZMod p] T)) := hstep1
  -- the associator step
  have hstep2 : (c7 n).comp (Work.Tate.Hm1Map G
        ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        ((E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom
        (fun γ a => rTensor_equiv p (G := G)
          (f := (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
          (fun g x => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
            (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g x) γ a))
      = (Work.Tate.Hm1Map G
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
          ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom
          (fun γ a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
            (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a)).comp
        (c7 m) := by
    simp only [c7]
    have hA : ∀ (γ : G) (a : (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G),
        ((TensorProduct.assoc (ZMod p) (E p G n i j) T (A2 p G)).toAddMonoidHom.comp
          (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom)
            (γ • a)
          = γ • ((TensorProduct.assoc (ZMod p) (E p G n i j) T (A2 p G)).toAddMonoidHom.comp
            (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom)
            a :=
      fun γ a => IsEquivariant.comp' (G := G)
        (A := (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (B := (E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (C := E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom
        (fun γ a => rTensor_equiv p (G := G)
          (f := (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
          (fun g x => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
            (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g x) γ a)
        (TensorProduct.assoc (ZMod p) (E p G n i j) T (A2 p G)).toAddMonoidHom
        (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x) γ a
    have hB : ∀ (γ : G) (a : (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G),
        (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom.comp
          (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom) (γ • a)
          = γ • (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom.comp
            (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom) a :=
      fun γ a => IsEquivariant.comp' (G := G)
        (A := (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (B := E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (C := E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom
        (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom
        (fun γ a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
          (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a) γ a
    exact (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
        (A := (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (B := (E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (C := E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom
        (fun γ a => rTensor_equiv p (G := G)
          (f := (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
          (fun g x => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
            (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) g x) γ a)
        (TensorProduct.assoc (ZMod p) (E p G n i j) T (A2 p G)).toAddMonoidHom
        (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x) hA).symm.trans
      ((Hm1Map_congr (G := G)
        (A := (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (B := E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (f := (TensorProduct.assoc (ZMod p) (E p G n i j) T (A2 p G)).toAddMonoidHom.comp
          (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (A2 p G)).toAddMonoidHom)
        (f' := ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom.comp
          (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom)
        hA hB
        (tensorAssoc_natural (p := p) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
          (N := T) (P := A2 p G))).trans
      (Work.CohomologicalShrinking.tate.Hm1Map_comp (G := G)
        (A := (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] A2 p G)
        (B := E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (C := E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
        (TensorProduct.assoc (ZMod p) (E p G m i j) T (A2 p G)).toAddMonoidHom
        (fun γ x => tensorAssoc_smul (p := p) (G := G) γ x)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom
        (fun γ a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
          (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a) hB))

  -- assembling
  have key : (P8 n).comp (OperatorMap.h2Map p G T Φ)
      = (Work.Tate.Hm1Map G
          (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
          ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom
          (fun γ a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
            (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a)).comp
        (P8 m) := by
    simp only [P8]
    rw [AddMonoidHom.comp_assoc, hstep1', ← AddMonoidHom.comp_assoc, hstep2,
      AddMonoidHom.comp_assoc]
  have e2 : (Work.Tate.Hm1Map G
      (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
      (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] A2 p G))
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] A2 p G)).toAddMonoidHom
      (fun γ a => rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
        (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x) γ a))
      = OperatorMap.hm1Map p G (T ⊗[ZMod p] A2 p G) Φ := rfl
  rw [e2] at key
  apply AddMonoidHom.ext
  intro x
  change (AddEquiv.ofBijective (P8 n) (hbij_P8 n)) (OperatorMap.h2Map p G T Φ x)
    = OperatorMap.hm1Map p G (T ⊗[ZMod p] A2 p G) Φ
        ((AddEquiv.ofBijective (P8 m) (hbij_P8 m)) x)
  rw [AddEquiv.ofBijective_apply, AddEquiv.ofBijective_apply]
  exact DFunLike.congr_fun key x

end Main

/-- **The dimension shift `Ĥ²(G, X) ≅ Ĥ⁻¹(G, X ⊗ A₂)` of Schmidt–Wingberg's Proposition 6.**

For every `𝔽_p[G]`-module `T` there is a family of additive isomorphisms
`s m : H²(G, E(m,τ) ⊗ T) ≃+ Ĥ⁻¹(G, E(m,τ) ⊗ (T ⊗ A₂))` which is natural in the level `m` with
respect to the maps induced by `G`-operator homomorphisms `Φ : F(m) ⇢ F(n)`. -/

theorem shiftH2Family (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G] {i j : ℕ}
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ s : ∀ m : ℕ, Work.GroupCohomology.H2 G
          (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T) ≃+
        Work.Tate.Hm1 G
          (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j)
            (TensorProduct (ZMod p) T (Work.CohomologicalShrinking.A2 p G))),
      ∀ ⦃m n : ℕ⦄ (Φ : Work.CohomologicalShrinking.OperatorMap G m n),
        ((s n).toAddMonoidHom).comp (Work.CohomologicalShrinking.OperatorMap.h2Map p G T Φ)
          = (Work.CohomologicalShrinking.OperatorMap.hm1Map p G
                (TensorProduct (ZMod p) T (Work.CohomologicalShrinking.A2 p G)) Φ).comp
              ((s m).toAddMonoidHom) := by
  obtain ⟨L, L_equiv, L_nat⟩ := Work.CohomologicalShrinking.coindShiftAddEquivTensor p G
  obtain ⟨R, R_equiv, R_nat⟩ :=
    Work.CohomologicalShrinking.shiftTensor.assocTripleTensorGen p G (igDual p G)
  exact shiftH2Family_of_data p G T L L_equiv L_nat R R_equiv R_nat

end Work.CohomologicalShrinking
