/-
# Auxiliary constructions for `Work.CharCore.irr_degree_dvd_card`

This file (part of the character-theory core, area A5) sets up the ingredients of the
classical proof that the degree of an irreducible character divides the order of the group:

* **class sums.**  For a conjugacy class `C` of `G` we define the class sum
  `conjClassSum C = ∑_{x ∈ C} x ∈ ℂ[G]`, we show that it is central, and that it is an algebraic
  integer over `ℤ` (it is the image of an element of the finite `ℤ`-algebra `ℤ[G]`);

* **the central character.**  For a simple `ℂ[G]`-module `N`, every central `z ∈ ℂ[G]` acts on
  `N` as a scalar; Schur's lemma (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`)
  turns this into a function `centralChar N hN : Z(ℂ[G]) → ℂ`;

* **integrality.**  `centralChar N hN (conjClassSum C)` is an algebraic integer for every conjugacy
  class `C`.  This is the "central character integrality" behind the divisibility theorem
  `irr_degree_dvd_card`: it is proved by transporting the monic polynomial over `ℤ` annihilating
  `conjClassSum C` through the action of `ℂ[G]` on `N`.
-/

import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

section ConjugacyClasses

/-- Conjugation preserves the conjugacy class. -/
theorem ConjClasses.mk_mul_conj_eq (g x : G) : ConjClasses.mk (g * x * g⁻¹) = ConjClasses.mk x :=
  (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)).symm

/-- Conjugation by the inverse preserves the conjugacy class. -/
theorem ConjClasses.mk_inv_mul_conj_eq (g x : G) :
    ConjClasses.mk (g⁻¹ * x * g) = ConjClasses.mk x :=
  (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by simp⟩)).symm

/-- Conjugation by `g`, as a permutation of a conjugacy class. -/
def conjClassEquiv (g : G) (C : ConjClasses G) : C.carrier ≃ C.carrier where
  toFun x := ⟨g * (x : G) * g⁻¹, ConjClasses.mem_carrier_iff_mk_eq.mpr
    ((ConjClasses.mk_mul_conj_eq g (x : G)).trans (ConjClasses.mem_carrier_iff_mk_eq.mp x.2))⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, ConjClasses.mem_carrier_iff_mk_eq.mpr
    ((ConjClasses.mk_inv_mul_conj_eq g (x : G)).trans (ConjClasses.mem_carrier_iff_mk_eq.mp x.2))⟩
  left_inv x := by
    apply Subtype.ext
    show g⁻¹ * (g * (x : G) * g⁻¹) * g = (x : G)
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  right_inv x := by
    apply Subtype.ext
    show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

/-- A chosen representative of a conjugacy class. -/
noncomputable def rep (C : ConjClasses G) : G := Quotient.out C

theorem mk_rep (C : ConjClasses G) : ConjClasses.mk (rep C) = C := Quotient.out_eq C

theorem rep_mem_carrier (C : ConjClasses G) : rep C ∈ C.carrier :=
  ConjClasses.mem_carrier_iff_mk_eq.mpr (mk_rep C)

/-- The canonical bijection between the disjoint union of the conjugacy classes and the group. -/
noncomputable def sigmaConjEquiv : (Σ C : ConjClasses G, C.carrier) ≃ G :=
  Equiv.ofBijective (fun p => (p.2 : G)) ⟨
    (fun p q h => by
      obtain ⟨C, x⟩ := p
      obtain ⟨D, y⟩ := q
      simp only at h
      have hC : C = D := by
        rw [← ConjClasses.mem_carrier_iff_mk_eq.mp x.2,
          ← ConjClasses.mem_carrier_iff_mk_eq.mp y.2, h]
      subst hC
      exact congrArg (Sigma.mk C) (Subtype.ext h)),
    (fun g => ⟨⟨ConjClasses.mk g, ⟨g, ConjClasses.mem_carrier_mk⟩⟩, rfl⟩)⟩

@[simp]
theorem sigmaConjEquiv_apply (C : ConjClasses G) (x : C.carrier) :
    sigmaConjEquiv ⟨C, x⟩ = (x : G) := rfl

/-- An element of a conjugacy class is conjugate to the chosen representative. -/
theorem isConj_rep_of_mem {C : ConjClasses G} {x : G} (hx : x ∈ C.carrier) :
    IsConj x (rep C) :=
  ConjClasses.mk_eq_mk_iff_isConj.mp
    ((ConjClasses.mem_carrier_iff_mk_eq.mp hx).trans (mk_rep C).symm)

/-- A class function is constant on each conjugacy class. -/
theorem IsClassFun.eq_rep {f : G → ℂ} (hf : IsClassFun f) {C : ConjClasses G} {x : G}
    (hx : x ∈ C.carrier) : f x = f (rep C) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_rep_of_mem hx)
  rw [← hc, hf]

/-- The sum of a class function over a conjugacy class. -/
theorem IsClassFun.sum_carrier {f : G → ℂ} (hf : IsClassFun f) (C : ConjClasses G) :
    ∑ x : C.carrier, f x = (Fintype.card C.carrier : ℂ) * f (rep C) := by
  rw [Finset.sum_congr rfl fun x _ => hf.eq_rep x.2, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- Decomposition of a sum over a finite group into a sum over its conjugacy classes, for a
class function. -/
theorem IsClassFun.sum_eq_sum_conjClasses {f : G → ℂ} (hf : IsClassFun f) :
    ∑ g : G, f g = ∑ C : ConjClasses G, (Fintype.card C.carrier : ℂ) * f (rep C) := by
  rw [← sigmaConjEquiv.sum_comp f, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun C _ => hf.sum_carrier C

end ConjugacyClasses

section ClassSum

/-- The class sum of a conjugacy class, as an element of `ℤ[G]`. -/
noncomputable def classSumZ (C : ConjClasses G) : MonoidAlgebra ℤ G :=
  ∑ x : C.carrier, MonoidAlgebra.single (x : G) (1 : ℤ)

/-- The class sum of a conjugacy class, as an element of `ℂ[G]`. -/
noncomputable def conjClassSum (C : ConjClasses G) : groupAlgebra G :=
  ∑ x : C.carrier, MonoidAlgebra.single (x : G) (1 : ℂ)

@[simp]
theorem classSumZ_eq (C : ConjClasses G) :
    classSumZ C = ∑ x : C.carrier, MonoidAlgebra.single (x : G) (1 : ℤ) := rfl

@[simp]
theorem classSum_eq (C : ConjClasses G) :
    conjClassSum C = ∑ x : C.carrier, MonoidAlgebra.single (x : G) (1 : ℂ) := rfl

/-- `conjClassSum` is the image of `classSumZ` under scalar extension `ℤ[G] → ℂ[G]`. -/
theorem classSum_eq_map_classSumZ (C : ConjClasses G) :
    conjClassSum C = MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) (classSumZ C) := by
  rw [classSum_eq, classSumZ_eq, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MonoidAlgebra.mapRingHom_single]
  norm_num

private lemma single_mul_classSum (g : G) (C : ConjClasses G) :
    MonoidAlgebra.single g (1 : ℂ) * conjClassSum C =
      conjClassSum C * MonoidAlgebra.single g (1 : ℂ) := by
  simp only [classSum_eq]
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [MonoidAlgebra.single_mul_single, mul_one]
  refine Fintype.sum_equiv (conjClassEquiv g C)
    (fun x : C.carrier => MonoidAlgebra.single (g * (x : G)) (1 : ℂ))
    (fun y : C.carrier => MonoidAlgebra.single ((y : G) * g) (1 : ℂ)) ?_
  intro x
  show MonoidAlgebra.single (g * (x : G)) (1 : ℂ)
      = MonoidAlgebra.single (((conjClassEquiv g C x : C.carrier) : G) * g) (1 : ℂ)
  rw [show ((conjClassEquiv g C x : C.carrier) : G) = g * (x : G) * g⁻¹ from rfl]
  congr 1
  simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Class sums are central. -/
theorem classSum_mem_center (C : ConjClasses G) :
    conjClassSum C ∈ Subalgebra.center ℂ (groupAlgebra G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of m => exact single_mul_classSum m C
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

/-- Class sums are algebraic integers. -/
theorem isIntegral_classSum (C : ConjClasses G) : IsIntegral ℤ (conjClassSum C) := by
  have h2 : IsIntegral ℤ ((MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)) (classSumZ C)) := by
    have h3 := RingHom.IsIntegralElem.map
      ((Algebra.IsIntegral.of_finite ℤ (MonoidAlgebra ℤ G)).isIntegral (classSumZ C))
      (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))
    rwa [show (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ)).comp (algebraMap ℤ (MonoidAlgebra ℤ G))
        = algebraMap ℤ (groupAlgebra G) from RingHom.ext_int _ _] at h3
  rwa [classSum_eq_map_classSumZ]

end ClassSum

section CentralCharacter

/-- Left multiplication by a central element, as a `ℂ[G]`-linear endomorphism of `N`. -/
noncomputable def smulEnd (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (z : Subalgebra.center ℂ (groupAlgebra G)) : Module.End (groupAlgebra G) N where
  toFun n := (z : groupAlgebra G) • n
  map_add' a b := smul_add _ _ _
  map_smul' a n := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    exact (Subalgebra.mem_center_iff.mp z.2 a).symm

@[simp]
theorem smulEnd_apply (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (z : Subalgebra.center ℂ (groupAlgebra G)) (n : N) :
    smulEnd N z n = (z : groupAlgebra G) • n := rfl

/-- Schur's lemma: the endomorphism ring of a simple `ℂ[G]`-module is the field of scalars. -/
noncomputable def centralCharEquiv (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) : ℂ ≃ₐ[ℂ] Module.End (groupAlgebra G) N :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ (Module.End (groupAlgebra G) N))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ)

theorem centralCharEquiv_apply (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (c : ℂ) :
    centralCharEquiv N hN c = c • (1 : Module.End (groupAlgebra G) N) := by
  show (Algebra.ofId ℂ (Module.End (groupAlgebra G) N)) c = c • 1
  rw [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]

/-- The **central character** of a simple `ℂ[G]`-module `N`: the scalar by which a central
element of `ℂ[G]` acts on `N`. -/
noncomputable def centralChar (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N)
    (z : Subalgebra.center ℂ (groupAlgebra G)) : ℂ :=
  (centralCharEquiv N hN).symm (smulEnd N z)

/-- The defining property of the central character. -/
theorem centralChar_spec (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (z : Subalgebra.center ℂ (groupAlgebra G)) (n : N) :
    (z : groupAlgebra G) • n = centralChar N hN z • n := by
  have h1 : centralCharEquiv N hN (centralChar N hN z) = smulEnd N z :=
    (centralCharEquiv N hN).apply_symm_apply (smulEnd N z)
  have h2 : centralChar N hN z • (1 : Module.End (groupAlgebra G) N) = smulEnd N z := by
    rw [← h1, centralCharEquiv_apply]
  have h3 := congrArg (fun f : Module.End (groupAlgebra G) N => f n) h2
  rw [LinearMap.smul_apply, Module.End.one_apply, smulEnd_apply] at h3
  exact h3.symm

/-- The algebra map `ℂ → End_ℂ(N)` is injective when `N` is nontrivial. -/
theorem algebraMap_end_injective (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) :
    Function.Injective (algebraMap ℂ (N →ₗ[ℂ] N)) := by
  haveI := IsSimpleModule.nontrivial (groupAlgebra G) N
  intro c d h
  have h0 : (c - d) • (1 : N →ₗ[ℂ] N) = 0 := by
    rw [← Algebra.algebraMap_eq_smul_one (A := N →ₗ[ℂ] N), map_sub, h, sub_self]
  obtain ⟨n, hn⟩ : ∃ n : N, n ≠ 0 := exists_ne 0
  have h1 : (c - d) • n = 0 := by
    have := congrArg (fun f : N →ₗ[ℂ] N => f n) h0
    simpa [Module.End.one_apply] using this
  exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hn)

/-- **Integrality of the central character of a class sum.** -/
theorem isIntegral_centralChar_classSum (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    IsIntegral ℤ (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) := by
  obtain ⟨p, hpmonic, hp⟩ := isIntegral_classSum C
  refine ⟨p, hpmonic, ?_⟩
  have hsc : (Algebra.lsmul ℂ ℂ N).toRingHom (conjClassSum C)
      = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) • (1 : N →ₗ[ℂ] N) := by
    show (Algebra.lsmul ℂ ℂ N) (conjClassSum C)
      = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) • (1 : N →ₗ[ℂ] N)
    refine LinearMap.ext fun n => ?_
    rw [Algebra.lsmul_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact centralChar_spec N hN ⟨conjClassSum C, classSum_mem_center C⟩ n
  have key : (Polynomial.aeval ((centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) •
      (1 : N →ₗ[ℂ] N))) (p.map (algebraMap ℤ ℂ)) = 0 := by
    rw [← hsc]
    rw [← Polynomial.map_aeval_eq_aeval_map (φ := algebraMap ℤ ℂ)
      (ψ := (Algebra.lsmul ℂ ℂ N).toRingHom) (RingHom.ext_int _ _) p (conjClassSum C)]
    rw [show Polynomial.aeval (conjClassSum C) p = 0 from by rw [Polynomial.aeval_def, hp], map_zero]
  rw [← Polynomial.eval_map (algebraMap ℤ ℂ)]
  apply Polynomial.isRoot_of_eval₂_map_eq_zero (algebraMap_end_injective N hN)
  rw [← Polynomial.aeval_def, Algebra.algebraMap_eq_smul_one]
  exact key

end CentralCharacter


section SimpleSubmodule

/-- A simple submodule of the regular module, viewed as a `ℂ[G]`-module, agrees with the
representation `submoduleRep` on it. -/
noncomputable def asModuleLinearEquiv (N : Submodule (groupAlgebra G) (groupAlgebra G)) :
    (submoduleRep N).asModule ≃ₗ[groupAlgebra G] N where
  toFun := (submoduleRep N).asModuleEquiv
  invFun := (submoduleRep N).asModuleEquiv.symm
  left_inv := (submoduleRep N).asModuleEquiv.left_inv
  right_inv := (submoduleRep N).asModuleEquiv.right_inv
  map_add' := (submoduleRep N).asModuleEquiv.map_add
  map_smul' := fun r x => by
    show (submoduleRep N).asModuleEquiv (r • x) = r • (submoduleRep N).asModuleEquiv x
    rw [Representation.asModuleEquiv_map_smul]
    rw [show Representation.asAlgebraHom (submoduleRep N) = Algebra.lsmul ℂ ℂ N from by
      ext a n
      simp [Representation.asAlgebraHom, submoduleRep, Representation.ofModule', Algebra.lsmul_apply]]
    rw [Algebra.lsmul_apply]

/-- A simple submodule of the regular module gives an irreducible representation. -/
theorem isIrreducible_submoduleRep (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) : (submoduleRep N).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (asModuleLinearEquiv N).isSimpleModule_iff.mpr hN

/-- The character of a simple submodule satisfies the first orthogonality relation in the
symmetric form `∑_g χ g * χ g⁻¹ = |G|`. -/
theorem sum_char_mul_char_inv_eq_card (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) :
    ∑ g : G, (submoduleRep N).character g * (submoduleRep N).character g⁻¹
      = (Nat.card G : ℂ) := by
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    have h : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast ne_of_gt h
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hc
  haveI := isIrreducible_submoduleRep N hN
  have h := Representation.char_orthonormal (ρ := submoduleRep N) (σ := submoduleRep N)
  rw [if_pos ⟨Representation.Equiv.refl _⟩] at h
  have h2 : (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ *
      ∑ g : G, (submoduleRep N).character g * (submoduleRep N).character g⁻¹)
        = (Nat.card G : ℂ) := by
    rw [h, mul_one]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h2
  exact h2

/-- The class sum acts on `N` through the central character, and the trace of this action is the
central character times the degree. -/
theorem trace_classSum_eq_centralChar_mul_finrank
    (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    LinearMap.trace ℂ N (Algebra.lsmul ℂ ℂ N (conjClassSum C))
      = centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ * (Module.finrank ℂ N : ℂ) := by
  have h : (Algebra.lsmul ℂ ℂ N) (conjClassSum C)
      = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) • (1 : N →ₗ[ℂ] N) := by
    refine LinearMap.ext fun n => ?_
    rw [Algebra.lsmul_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact centralChar_spec N hN ⟨conjClassSum C, classSum_mem_center C⟩ n
  rw [h, map_smul, LinearMap.trace_one, smul_eq_mul]

/-- The trace of the action of the class sum is the sum of the character values on the class. -/
theorem trace_classSum_eq_sum_char (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (C : ConjClasses G) :
    LinearMap.trace ℂ N (Algebra.lsmul ℂ ℂ N (conjClassSum C))
      = ∑ x : C.carrier, (submoduleRep N).character x := by
  rw [classSum_eq, map_sum, map_sum]
  rfl

/-- **The key numerical relation**: the central character of a class sum times the degree equals
the size of the class times the character value. -/
theorem centralChar_classSum_mul_finrank (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ * (Module.finrank ℂ N : ℂ)
      = (Fintype.card C.carrier : ℂ) * (submoduleRep N).character (rep C) := by
  rw [← trace_classSum_eq_centralChar_mul_finrank N hN C, trace_classSum_eq_sum_char N C]
  exact IsClassFun.sum_carrier (isClassFun_character (submoduleRep N)) C

end SimpleSubmodule


/-- The weighted sum `∑_C ω_C χ(g_C⁻¹)` of the central characters of the class sums against the
character values at the chosen representatives; this is the quantity whose integrality gives the
divisibility theorem. -/
noncomputable def omegaSum (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) : ℂ :=
  ∑ C : ConjClasses G,
    centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ *
      (submoduleRep N).character (rep C)⁻¹

end Work.CharCore
