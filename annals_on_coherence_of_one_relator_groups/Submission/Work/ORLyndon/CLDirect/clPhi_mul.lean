import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_mul
import Submission.Work.ORLyndon.CLDirect.normalClosure_pow_le

namespace Work.ORLyndon.CLDirect

/-- Additivity of `φ` on the normal closure of `u^l`. Sketch: unfold with `dif_pos` (memberships in `M` come from `normalClosure_pow_le`); rewrite `D.e.symm ⟨n*n',_⟩ = D.e.symm ⟨n,_⟩ * D.e.symm ⟨n',_⟩` via `map_mul`/`Subtype.ext`; apply `clDelta_mul`; the middle factor is `clPi (of (e.symm ⟨n,_⟩)) = of (presentRho n) = 1` by `clPi_of`, `MulEquiv.apply_symm_apply`, `PresentedGroup.mk_eq_one_iff.mpr hn`; finish with `mul_one`/`add`. -/
theorem clPhi_mul {X : Type*} [DecidableEq X] {K : Type*} [Field K] {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) {n n' : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)))
    (hn' : n' ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clPhi (K := K) D l (n * n') =
      Work.ORLyndon.CLDirect.clPhi (K := K) D l n + Work.ORLyndon.CLDirect.clPhi (K := K) D l n' := by
  classical
  -- Both arguments and their product lie in `M = ⟪u⟫`, since `⟪u^l⟫ ≤ ⟪u⟫`.
  have hnM : n ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
    normalClosure_pow_le u l hn
  have hn'M : n' ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
    normalClosure_pow_le u l hn'
  have hnnM : n * n' ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) := mul_mem hnM hn'M
  -- Unfold `clPhi` using these memberships.
  rw [clPhi, dif_pos hnnM, clPhi, dif_pos hnM, clPhi, dif_pos hn'M]
  -- `e.symm` is a homomorphism.
  have hsymm : D.e.symm ⟨n * n', hnnM⟩ = D.e.symm ⟨n, hnM⟩ * D.e.symm ⟨n', hn'M⟩ := by
    rw [show (⟨n * n', hnnM⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
      ⟨n, hnM⟩ * ⟨n', hn'M⟩ from rfl, map_mul]
  rw [hsymm, clDelta_mul]
  -- The middle factor vanishes because `n` is trivial in `G = ⟨X | u^l⟩`.
  have hmid : clPi (K := K) D l (MonoidAlgebra.of K _ (D.e.symm ⟨n, hnM⟩)) = 1 := by
    rw [clPi_of, MulEquiv.apply_symm_apply]
    have h1 : presentRho (u ^ l)
        ((⟨n, hnM⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) : FreeGroup X) = 1 := by
      rw [presentRho_apply]
      exact PresentedGroup.mk_eq_one_iff.mpr hn
    rw [h1, map_one]
  rw [hmid, one_mul]

end Work.ORLyndon.CLDirect
