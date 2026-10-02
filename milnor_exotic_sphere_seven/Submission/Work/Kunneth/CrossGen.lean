import Mathlib
import Submission.Work.Kunneth.HomCross
import Submission.Work.Kunneth.Algebra
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.homology_tpC_homSum

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product of chain complexes, in general

`Submission/Work/Kunneth/HomCross.lean` constructs the homology cross product of two *simplicial
sets* using the Eilenberg–Zilber shuffle chain `ezChain`.  This module does the same for two
arbitrary chain complexes of `ℤ`-modules, where the shuffle chain of a cycle `u` of `C` and a cycle
`v` of `D` is simply `u ⊗ v` in the `(p,q)`-summand of the tensor product `tpC C D` (the Koszul
differential of `tpC C D` kills it, because both factors are cycles).

The results are the section-free building blocks of the Künneth theorem in its *cross-product* form
(`Work.Kunneth.crossSumMap`, `Work.Kunneth.crossSumMap_shuffle`):

* `crossCycleMap C D n p q h` — the chain `u ⊗ v` in the `(p,q)`-summand of `tpC C D`;
* `d_crossCycleMap` — it is a cycle;
* `crossCycTens` — the same, as an element of the cycles;
* `iCycles_crossCycTens_tmul` — its underlying chain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **The shuffle chain of two cycles** of `C` and `D`, in total degree `n = p + q`: the element
`u ⊗ v` of the `(p,q)`-summand of the tensor product `tpC C D`. -/
noncomputable def crossCycleMap (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n) :
    ↥(C.cycles p ⊗ D.cycles q) →ₗ[ℤ] ↥((tpC C D).X n) :=
  (tpLof C D n ⟨(p, q), h⟩).comp
    (TensorProduct.map (C.iCycles p).hom (D.iCycles q).hom)

/-- The computation rule for `crossCycleMap` on pure tensors. -/
theorem crossCycleMap_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n)
    (u : ↥(C.cycles p)) (v : ↥(D.cycles q)) :
    crossCycleMap C D n p q h (u ⊗ₜ[ℤ] v)
      = tpLof C D n ⟨(p, q), h⟩
          (((C.iCycles p).hom u) ⊗ₜ[ℤ] ((D.iCycles q).hom v)) := by
  rw [crossCycleMap]
  show (tpLof C D n ⟨(p, q), h⟩)
      (TensorProduct.map (C.iCycles p).hom (D.iCycles q).hom (u ⊗ₜ[ℤ] v)) =
    (tpLof C D n ⟨(p, q), h⟩)
      (((C.iCycles p).hom u) ⊗ₜ[ℤ] ((D.iCycles q).hom v))
  rw [TensorProduct.map_tmul]

/-- **The shuffle chain of two cycles is a cycle.** -/
theorem d_crossCycleMap (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n)
    (u : ↥(C.cycles p)) (v : ↥(D.cycles q)) :
    ((tpC C D).d n (n - 1)).hom (crossCycleMap C D n p q h (u ⊗ₜ[ℤ] v)) = 0 := by
  rw [crossCycleMap_tmul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [show ((tpC C D).d 0 (0 - 1)) = 0 from (tpC C D).shape 0 0 (by simp [ComplexShape.down])]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    show ((tpC C D).d (m + 1) m).hom
      (tpLof C D (m + 1) ⟨(p, q), h⟩
        (((C.iCycles p).hom u) ⊗ₜ[ℤ] ((D.iCycles q).hom v))) = 0
    rw [tpC_d]
    simp only [ModuleCat.hom_ofHom]
    erw [tpD_lof_tmul]
    have h1 : ((C.d p (p - 1)).hom ((C.iCycles p).hom u)) = 0 := d_iCycles C p u
    have h2 : ((D.d q (q - 1)).hom ((D.iCycles q).hom v)) = 0 := d_iCycles D q v
    split_ifs <;> simp only [h1, h2, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      map_zero, add_zero, zero_add]
    all_goals exact smul_zero ((-1 : ℤ) ^ p)

/-- **The shuffle chain of two cycles is a cycle**, on an arbitrary element of the tensor product of
the cycle modules. -/
theorem d_crossCycleMap_gen (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n)
    (x : ↥(C.cycles p ⊗ D.cycles q)) :
    ((tpC C D).d n (n - 1)).hom (crossCycleMap C D n p q h x) = 0 := by
  refine TensorProduct.induction_on
    (motive := fun x => ((tpC C D).d n (n - 1)).hom (crossCycleMap C D n p q h x) = 0) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro u v
    exact d_crossCycleMap C D n p q h u v
  · intro a b ha hb
    rw [map_add (crossCycleMap C D n p q h), map_add, ha, hb, add_zero]

/-- The cross product of cycles is a chain map into the tensor product (the cycle condition for
`liftCycles`). -/
theorem crossCycleMap_d (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n) :
    ModuleCat.ofHom (crossCycleMap C D n p q h) ≫ (tpC C D).d n (n - 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    ModuleCat.hom_zero, LinearMap.zero_apply] using d_crossCycleMap_gen C D n p q h x

/-- **The cross product of two cycles**, as a cycle of the tensor product: the lift of the shuffle
chain through the cycles. -/
noncomputable def crossCycTens (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ)
    (h : p + q = n) :
    ↥(C.cycles p ⊗ D.cycles q) →ₗ[ℤ] ↥((tpC C D).cycles n) :=
  ModuleCat.Hom.hom ((tpC C D).liftCycles
    (ModuleCat.ofHom (crossCycleMap C D n p q h)) (n - 1) (downNext n)
    (crossCycleMap_d C D n p q h))

/-- The underlying chain of the cross product of two cycles is the shuffle chain. -/
theorem iCycles_crossCycTens (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ) (h : p + q = n)
    (x : ↥(C.cycles p ⊗ D.cycles q)) :
    ((tpC C D).iCycles n).hom (crossCycTens C D n p q h x)
      = crossCycleMap C D n p q h x := by
  have hh := iCycles_liftCycles_apply_gen (tpC C D) n
    (ModuleCat.ofHom (crossCycleMap C D n p q h)) (downNext n)
    (crossCycleMap_d C D n p q h) x
  rw [crossCycTens]
  exact hh

/-- The cross product of two cycles, on pure tensors. -/
theorem iCycles_crossCycTens_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (n p q : ℕ)
    (h : p + q = n) (u : ↥(C.cycles p)) (v : ↥(D.cycles q)) :
    ((tpC C D).iCycles n).hom (crossCycTens C D n p q h (u ⊗ₜ[ℤ] v))
      = tpLof C D n ⟨(p, q), h⟩
          (((C.iCycles p).hom u) ⊗ₜ[ℤ] ((D.iCycles q).hom v)) := by
  rw [iCycles_crossCycTens, crossCycleMap_tmul]

end

end Work.Kunneth
