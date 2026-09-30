import Mathlib
import Submission.Work.BW.HilbSerreDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- The kernel of multiplication by `X x` inherits the grading, shifted by the weight `wZ N x`:
the `u`-th piece of `ker (mulX x)` is the part of `piece (u - wZ N x)` killed by `X x`.

The three axioms are inherited from `hg`:
* the internal decomposition is `Work.BW.isInternal_ker` applied to the degree-shifting
  endomorphism `mulX x` and the index bijection `u ↦ u - wZ N x`;
* multiplying by a variable `X v` shifts the grading of `M` and preserves the kernel;
* negative multidegrees stay negative after subtracting the non-negative weight `wZ N x`. -/
theorem isGrading_kerPiece {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (hg : IsGrading N piece) :
    IsGrading N (HilbSerre.kerPiece N M piece x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the pieces of `kerPiece` are internally direct, by the degree-shifting kernel lemma
    refine isInternal_ker (R := ℂ) (A := piece) hg.isInternal
      ((HilbSerre.mulX N M x).restrictScalars ℂ) (Equiv.subRight (wZ N x)) ?_
    intro u m hm
    rw [Submodule.mem_comap]
    have h := hg.smul_mem x (u - wZ N x) hm
    rw [sub_add_cancel] at h
    simpa [HilbSerre.mulX] using h
  · -- multiplication by a variable shifts the shifted grading and keeps the kernel
    intro v u m hm
    rw [HilbSerre.kerPiece, Submodule.mem_comap] at hm ⊢
    have h2 : (MvPolynomial.X v : MR N) • (m : M) ∈ piece ((u - wZ N x) + wZ N v) :=
      hg.smul_mem v (u - wZ N x) hm
    rw [sub_add_eq_add_sub] at h2
    simpa using h2
  · -- negative multidegrees still vanish, since `wZ N x` is non-negative
    intro u hu
    rw [HilbSerre.kerPiece]
    obtain ⟨i, hi⟩ := hu
    rw [hg.eq_bot_of_neg (u - wZ N x) (by
      refine ⟨i, ?_⟩
      rw [Finsupp.sub_apply, wZ, Finsupp.single_apply]
      split_ifs <;> omega), Submodule.comap_bot]
    simp

end Work.BW
