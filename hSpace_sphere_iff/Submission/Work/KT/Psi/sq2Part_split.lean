import Mathlib
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.swapPerm_permMatrix_sq
import Submission.Work.KT.Psi.kronMat_swap_comm
import Submission.Work.KT.Psi.proj2_orth
import Submission.Work.KT.Psi.orth_idem_split

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- On a `ℂ`-algebra `A`, the scalar action of `A` on matrices through `algebraMap` agrees with
the scalar action of `ℂ` (both are applied entrywise). -/
lemma smul_algebraMap_eq {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (c : ℂ)
    (M : Matrix (Fin m) (Fin m) A) : algebraMap ℂ A c • M = c • M := by
  ext i j
  simp [Matrix.smul_apply, Algebra.smul_def]

/-- `sq2Part 1 p` in the form used by `proj2_orth`: the idempotent `(1+ε)/2` part written with
`ℂ`-scalars. -/
lemma sq2Part_one_eq {A : Type} [Ring A] [Algebra ℂ A] (p : Mat A) :
    sq2Part 1 p = ⟨p.1 * p.1,
      kronMat p.2 p.2 * ((1 / 2 : ℂ) • (1 + (swapPerm p.1).permMatrix A))⟩ := by
  show (⟨p.1 * p.1, kronMat p.2 p.2 *
      (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A (1 : ℂ) • (swapPerm p.1).permMatrix A))⟩
        : Mat A) = _
  rw [smul_algebraMap_eq (1 : ℂ) ((swapPerm p.1).permMatrix A), one_smul,
    smul_algebraMap_eq (1 / 2 : ℂ) (1 + (swapPerm p.1).permMatrix A)]

/-- `sq2Part (-1) p` in the form used by `proj2_orth`. -/
lemma sq2Part_neg_one_eq {A : Type} [Ring A] [Algebra ℂ A] (p : Mat A) :
    sq2Part (-1) p = ⟨p.1 * p.1,
      kronMat p.2 p.2 * ((1 / 2 : ℂ) • (1 - (swapPerm p.1).permMatrix A))⟩ := by
  show (⟨p.1 * p.1, kronMat p.2 p.2 *
      (algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A (-1 : ℂ) • (swapPerm p.1).permMatrix A))⟩
        : Mat A) = _
  rw [smul_algebraMap_eq (1 / 2 : ℂ)
      (1 + algebraMap ℂ A (-1 : ℂ) • (swapPerm p.1).permMatrix A),
    smul_algebraMap_eq (-1 : ℂ) ((swapPerm p.1).permMatrix A), neg_one_smul, sub_eq_add_neg]

theorem sq2Part_split {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    {p : Mat A} (hp : p.IsIdem) :
    cls (p.kron p) = cls (sq2Part 1 p) + cls (sq2Part (-1) p) := by
  let K : Matrix (Fin (p.1 * p.1)) (Fin (p.1 * p.1)) A := kronMat p.2 p.2
  let S : Matrix (Fin (p.1 * p.1)) (Fin (p.1 * p.1)) A := (swapPerm p.1).permMatrix A
  have hK : K * K = K := Mat.isIdem_kron hA hp hp
  have hS : S * S = 1 := swapPerm_permMatrix_sq (A := A) p.1
  have hKS : K * S = S * K := kronMat_swap_comm hA p.2
  obtain ⟨hEE, hFF, hsum, hEF, hFE⟩ := proj2_orth K S hK hS hKS
  rw [sq2Part_one_eq, sq2Part_neg_one_eq]
  exact orth_idem_split hK hEE hFF hsum.symm hEF hFE

end

end Work.KT.Psi
