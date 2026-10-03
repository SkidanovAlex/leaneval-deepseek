/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Additivity of the row-wise dimension on complementary submodules

For a von Neumann regular ring `R` with a Sylvester rank function `rk` and a pair of
complementary left submodules `P, Q ≤ R^n` (i.e. `P ⊔ Q = ⊤` and `P ⊓ Q = ⊥`), the row-wise
dimension `rdim` (see `DualityDefs.lean`) is additive:

  `rdim rk P + rdim rk Q = n`.

PROOF.  Since `P` and `Q` are complementary, `e := Submodule.projection P Q _` is an
idempotent endomorphism of `R^n` with `range e = P` and `ker e = Q` (`Submodule.projection`,
`range_projection`, `ker_projection`, `isIdempotentElem_projection`).  Let
`M := Matrix.toLinearMapRight'.symm e` be its matrix.  Then

* `rdim rk P = rk M` (the delegated `rdim_range_of_idempotent`, which identifies the dimension
  of the range of an idempotent with the rank of its matrix);
* `1 - e` is idempotent with `range (1 - e) = ker e = Q`, and its matrix is `1 - M`, so
  `rdim rk Q = rk (1 - M)`;
* `M * (1 - M) = 0` because `M * M = M`, so Sylvester's law of nullity
  (`RankAPI.rk_mul_add_le`) gives `rk M + rk (1 - M) ≤ n`;
* `M + (1 - M) = 1`, so subadditivity (`RankAPI.rk_add_le`) and `rk 1 = n`
  (`RankAPI.rk_identity_eq`) give the reverse inequality.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.DensityDuality
import Submission.Work.ORHughesFree.NaturalExtension.rdim_range_of_idempotent
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

theorem rdim_add_of_isCompl {R : Type u} [Ring R] [VonNeumannRegularRing R]
    (rk : SylvesterRank R) {n : ℕ} {P Q : Submodule R (Fin n → R)}
    (hsup : P ⊔ Q = ⊤) (hinf : P ⊓ Q = ⊥) :
    rdim rk P + rdim rk Q = (n : ℝ) := by
  classical
  -- The two hypotheses package `P` and `Q` into an `IsCompl` pair.
  have hcompl : IsCompl P Q :=
    isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  -- The projection onto `P` along `Q` and its matrix.
  set e : Module.End R (Fin n → R) := Submodule.projection P Q hcompl with hedef
  have he : e * e = e := by
    rw [hedef]
    exact Submodule.isIdempotentElem_projection hcompl
  have hrange : LinearMap.range e = P := by
    rw [hedef]; exact Submodule.range_projection hcompl
  have hker : LinearMap.ker e = Q := by
    rw [hedef]; exact Submodule.ker_projection hcompl
  set M : Matrix (Fin n) (Fin n) R := Matrix.toLinearMapRight'.symm e with hM
  have hMe : Matrix.toLinearMapRight' M = e := by
    rw [hM]; exact LinearEquiv.apply_symm_apply Matrix.toLinearMapRight' e
  have hMM : M * M = M := by
    apply Matrix.toLinearMapRight'.injective
    rw [Matrix.toLinearMapRight'_mul, hMe, ← Module.End.mul_eq_comp, he]
  -- `rdim rk P = rk M`.
  have hP : rdim rk P = rk.rk n n M := by
    rw [← hrange]
    exact rdim_range_of_idempotent rk e he
  -- `1 - e` is idempotent with range `ker e = Q` and matrix `1 - M`.
  have h1e : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he]
    abel
  have hrange1e : LinearMap.range (1 - e) = LinearMap.ker e := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, hz⟩
      have hz' : z - e z = x := by simpa using hz
      have h := map_sub e z (e z)
      rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, he, sub_self] at h
      rw [hz'] at h
      exact h
    · intro hx
      refine ⟨x, ?_⟩
      simp [hx]
  have hsymm1 : Matrix.toLinearMapRight'.symm (1 : Module.End R (Fin n → R)) =
      (1 : Matrix (Fin n) (Fin n) R) := by
    rw [LinearEquiv.symm_apply_eq, Matrix.toLinearMapRight'_one, Module.End.one_eq_id]
  have hmat : Matrix.toLinearMapRight'.symm (1 - e) = 1 - M := by
    rw [map_sub, hsymm1, ← hM]
  have hQ : rdim rk Q = rk.rk n n (1 - M) := by
    rw [← hker, ← hrange1e, rdim_range_of_idempotent rk (1 - e) h1e, hmat]
  -- The two halves of `rk M + rk (1 - M) = n`.
  have hzero : M * (1 - M) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hMM, sub_self]
  have hle : rk.rk n n M + rk.rk n n (1 - M) ≤ (n : ℝ) := by
    have h := Work.ORHughesFree.RankAPI.rk_mul_add_le rk M (1 - M)
    rw [hzero, rk.rk_zero] at h
    linarith
  have hge : (n : ℝ) ≤ rk.rk n n M + rk.rk n n (1 - M) := by
    have h := Work.ORHughesFree.RankAPI.rk_add_le rk M (1 - M)
    rw [show M + (1 - M) = (1 : Matrix (Fin n) (Fin n) R) by abel,
      Work.ORHughesFree.RankAPI.rk_identity_eq rk n] at h
    linarith
  rw [hP, hQ]
  linarith

end Work.ORHughesFree.NaturalExtension
