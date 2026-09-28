import Mathlib
import Submission.Work.Kunneth.Chapter

/-!
# Rational homology is trivial when every cycle is a boundary up to a multiple

This file proves `Work.Serre.homologySubsingletonOfCycleTorsion`: for a chain complex `A` of
`ℤ`-modules, if in degree `j` every cycle `z` has a non-zero natural multiple `m • z` which is a
boundary, then the rationalised homology `H_j(A) ⊗[ℤ] ℚ` is trivial.

The mathematical content is the tautology `H_j(A) = Z_j / B_j` together with the fact that a
torsion group has trivial rationalisation: if `∂w = m • z` then `m • [z] = 0` in `H_j(A)`, and
`n • x = 0` with `n > 0` forces
`x ⊗ q = x ⊗ ((n : ℤ) • (q / n)) = ((n : ℤ) • x) ⊗ (q / n) = 0`.

## Implementation notes

The Künneth chapter works with the `ℤ`-module structures carried by `ModuleCat` objects, so
throughout this file the `ℤ`-module structure on the carrier of the submodule
`Work.Kunneth.cycKer A j` (and of `Work.Kunneth.homBnd A j`) has to be *the* structure coming from
the ambient `ModuleCat` object and **not** the canonical `AddCommGroup.toIntModule` structure
(which is propositionally equal, but not definitionally equal, to it).  That is why the generic
rationalisation lemma below takes the module structure as an explicit argument, and why the proof
of `homologyTorsion_of_cycleTorsion` fixes the two relevant instances with `letI`.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
open TensorProduct

set_option linter.style.haveILetI false

noncomputable section

/-- **A torsion group has trivial rationalisation.**  If every element `g` of an abelian group `G`
admits `n > 0` with `n • g = 0`, then `G ⊗[ℤ] ℚ` is a subsingleton.

Indeed `n • g = 0` gives, for each `q : ℚ`,
`g ⊗ q = g ⊗ ((n : ℤ) • (q / n)) = ((n : ℤ) • g) ⊗ (q / n) = 0`
(using `(n : ℤ) • g = n • g = 0`), and the pure tensors additively generate `G ⊗[ℤ] ℚ`. -/
theorem subsingleton_tensorRat_of_torsion_canon {G : Type*} [AddCommGroup G]
    (h : ∀ g : G, ∃ n : ℕ, 0 < n ∧ n • g = 0) :
    Subsingleton (TensorProduct ℤ G ℚ) := by
  rw [subsingleton_iff]
  intro x y
  have hzero : ∀ z : TensorProduct ℤ G ℚ, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul g q =>
        obtain ⟨n, hn, hng⟩ := h g
        have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        have hng' : (n : ℤ) • g = 0 := by simpa using hng
        have hq : q = (n : ℤ) • (q / (n : ℚ)) := by
          rw [← Int.cast_smul_eq_zsmul ℚ (n : ℤ) (q / (n : ℚ)), smul_eq_mul, Int.cast_natCast]
          rw [eq_comm, mul_comm, div_mul_cancel₀ q hn0]
        rw [hq, tmul_smul, smul_tmul', hng']
        simp
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

/-- `subsingleton_tensorRat_of_torsion_canon` with the `ℤ`-module structure on `G` given
explicitly: `M` is an arbitrary `ℤ`-module structure on the abelian group `G`.  All such
structures are propositionally equal, but the tensor product `G ⊗[ℤ] ℚ` depends on the choice up
to definitional equality only, so the structure has to be passed as an explicit argument. -/
theorem subsingleton_tensorRat_of_torsion {G : Type*} [AddCommGroup G] (M : Module ℤ G)
    (h : ∀ g : G, ∃ n : ℕ, 0 < n ∧ n • g = 0) :
    @Subsingleton (@TensorProduct ℤ _ G ℚ _ _ M _) := by
  have hM : M = AddCommGroup.toIntModule G := Subsingleton.elim _ _
  rw [hM]
  exact subsingleton_tensorRat_of_torsion_canon h

/-- **Every homology class is torsion, when every cycle is a boundary up to a multiple.**
Given `h : ∀ z ∈ Z_j, ∃ m > 0, ∃ w, ∂w = m • z`, every class `a ∈ H_j(A)` satisfies `n • a = 0`
for some `n > 0`.

Proof: the class of a cycle `z` in `H_j(A) ≅ Z_j / B_j` is the image of `z` under the quotient
map; choosing `z` representing `a` and `m`, `w` with `∂w = m • z`, the element `m • z` lies in
`B_j`, so its class `m • a` is zero. -/
theorem homologyTorsion_of_cycleTorsion (A : ChainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    (h : ∀ z : ↥(Work.Kunneth.cycKer A j),
        ∃ m : ℕ, 0 < m ∧ ∃ w : ↥(A.X (j + 1)), (A.d (j + 1) j).hom w = m • (z : ↥(A.X j))) :
    ∀ a : ↥(A.homology j), ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  intro a
  -- the `ℤ`-module structures of the Künneth chapter on the cycles and on the boundaries
  letI : Module ℤ ↥(Work.Kunneth.cycKer A j) := (Work.Kunneth.cycKer A j).module
  letI : Module ℤ ↥(Work.Kunneth.homBnd A j) := (Work.Kunneth.homBnd A j).module
  -- homology as the quotient of the cycles by the boundaries
  let e := (Work.Kunneth.homQuotIso A j).toLinearEquiv
  -- a cycle representing the class `a`
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (Work.Kunneth.homBnd A j) (e a)
  -- a non-zero multiple of that cycle is a boundary
  obtain ⟨m, hm, w, hw⟩ := h z
  refine ⟨m, hm, e.injective ?_⟩
  rw [map_nsmul, map_zero]
  rw [← hz, ← map_nsmul (Submodule.mkQ (Work.Kunneth.homBnd A j)) m z]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [Work.Kunneth.mem_homBnd_iff]
  exact ⟨w, hw⟩

end

theorem homologySubsingletonOfCycleTorsion (A : ChainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    (h : ∀ z : ↥(Work.Kunneth.cycKer A j),
        ∃ m : ℕ, 0 < m ∧ ∃ w : ↥(A.X (j + 1)), (A.d (j + 1) j).hom w = m • (z : ↥(A.X j))) :
    Subsingleton (TensorProduct ℤ ↥(A.homology j) ℚ) :=
  subsingleton_tensorRat_of_torsion (A.homology j).isModule
    (homologyTorsion_of_cycleTorsion A j h)

end Work.Serre
