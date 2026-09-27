import Mathlib
import Submission.Work.KT.Basic
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.mZero_conj
import Submission.Work.KT.D2.Core
import Submission.Work.KT.D2.idem_conj_of_rank_eq
import Submission.Work.KT.D2.isUnit_of_forall_isUnit_toCM
import Submission.Work.KT.D2.toCM_injective
import Submission.Work.KT.homInv_cls_eq_of_conj

/-!
# `Work.KT.D2.Inject` — injectivity of the (rank, winding) invariants on `K₀(Kpair ℝ²)`

Two idempotent matrices of the same size over `Kpair ℝ²` of the same rank (at the boundary point)
and the same winding invariant have the same class in `K₀`.

The boundary values are first conjugated into coincidence by a constant invertible matrix (which
does not change the class, nor the winding invariant), reducing to the equal-boundary case of
`Work.KT.D2.Core`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-- The constant matrix over `Kpair ℝ²` associated with a complex matrix evaluates back to it. -/
lemma constMat_toCM_local (N : ℕ) (c : Matrix (Fin N) (Fin N) ℂ) :
    ∀ x : Ball (Euc 2), toCM N (c.map (algebraMap ℂ (Kpair (Euc 2)))) x = c := by
  intro x
  ext i j
  simp [toCM_apply, evalAt]

/-- **Reduction to equal boundary values.** Idempotent matrices of the same size with the same
rank and the same winding invariant have the same class. -/
theorem cls_eq_of_rank_eq {y0 : Ball (Euc 2)} (hy0 : y0 ∈ bdry (Euc 2)) {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) (Kpair (Euc 2)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hr : Matrix.rank (bval N y0 P) = Matrix.rank (bval N y0 Q))
    (hm : mZero y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2)))
      = mZero y0 hy0 (⟨N, Q⟩ : Mat (Kpair (Euc 2)))) :
    cls (⟨N, P⟩ : Mat (Kpair (Euc 2))) = cls (⟨N, Q⟩ : Mat (Kpair (Euc 2))) := by
  have hE : bval N y0 P * bval N y0 P = bval N y0 P := bval_idem N y0 P hP
  have hF : bval N y0 Q * bval N y0 Q = bval N y0 Q := bval_idem N y0 Q hQ
  obtain ⟨c, hcunit, hcE⟩ := idem_conj_of_rank_eq N (bval N y0 P) (bval N y0 Q) hE hF hr
  set c' : Matrix (Fin N) (Fin N) ℂ := ↑(hcunit.unit)⁻¹ with hc'def
  have hcc' : c * c' = 1 := IsUnit.mul_val_inv hcunit
  have hc'c : c' * c = 1 := IsUnit.val_inv_mul hcunit
  -- the constant matrices over `Kpair ℝ²`
  set C : Matrix (Fin N) (Fin N) (Kpair (Euc 2)) := c.map (algebraMap ℂ (Kpair (Euc 2))) with hCdef
  set C' : Matrix (Fin N) (Fin N) (Kpair (Euc 2)) := c'.map (algebraMap ℂ (Kpair (Euc 2)))
    with hC'def
  have hCtoCM : ∀ x : Ball (Euc 2), toCM N C x = c := constMat_toCM_local N c
  have hC'toCM : ∀ x : Ball (Euc 2), toCM N C' x = c' := constMat_toCM_local N c'
  have hCC' : C * C' = 1 := by
    apply toCM_injective N
    intro x
    rw [toCM_mul_apply, hCtoCM x, hC'toCM x, toCM_one_apply]
    exact hcc'
  have hC'C : C' * C = 1 := by
    apply toCM_injective N
    intro x
    rw [toCM_mul_apply, hC'toCM x, hCtoCM x, toCM_one_apply]
    exact hc'c
  have hCunit : IsUnit C := isUnit_of_forall_isUnit_toCM N C (fun x => by
    rw [hCtoCM x]
    exact hcunit)
  -- the conjugate of `P`
  have hP' : (C * P * C') * (C * P * C') = C * P * C' := by
    calc (C * P * C') * (C * P * C')
        = C * P * (C' * C) * P * C' := by noncomm_ring
      _ = C * P * 1 * P * C' := by rw [hC'C]
      _ = C * P * P * C' := by rw [Matrix.mul_one]
      _ = C * P * C' := by rw [Matrix.mul_assoc C P P, hP]
  have hbvalP' : bval N y0 (C * P * C') = bval N y0 Q := by
    have h1 : bval N y0 (C * P * C') = bval N y0 C * bval N y0 P * bval N y0 C' := by
      simp only [bval, Matrix.map_mul]
    rw [h1]
    have h2 : bval N y0 C = c := (toCM_bval N y0 C).symm.trans (hCtoCM y0)
    have h3 : bval N y0 C' = c' := (toCM_bval N y0 C').symm.trans (hC'toCM y0)
    rw [h2, h3]
    calc c * bval N y0 P * c' = (c * bval N y0 P) * c' := rfl
      _ = (bval N y0 Q * c) * c' := by rw [hcE]
      _ = bval N y0 Q := by rw [Matrix.mul_assoc, hcc', Matrix.mul_one]
  have hmP' : mZero y0 hy0 (⟨N, C * P * C'⟩ : Mat (Kpair (Euc 2)))
      = mZero y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) :=
    mZero_conj y0 hy0 N P hP C C' hCC' hC'C
  have hclsP' : cls (⟨N, C * P * C'⟩ : Mat (Kpair (Euc 2)))
      = cls (⟨N, P⟩ : Mat (Kpair (Euc 2))) := by
    have hu : ((hCunit.unit : (Matrix (Fin N) (Fin N) (Kpair (Euc 2)))ˣ) :
        Matrix (Fin N) (Fin N) (Kpair (Euc 2))) * P
        = (C * P * C') * ((hCunit.unit : (Matrix (Fin N) (Fin N) (Kpair (Euc 2)))ˣ) :
            Matrix (Fin N) (Fin N) (Kpair (Euc 2))) := by
      rw [IsUnit.unit_spec hCunit]
      calc C * P = C * P * 1 := by rw [Matrix.mul_one]
        _ = C * P * (C' * C) := by rw [hC'C]
        _ = C * P * C' * C := by noncomm_ring
    exact homInv_cls_eq_of_conj (C * P * C') P hP' hP hCunit.unit hu
  exact hclsP'.symm.trans (cls_eq_of_boundary_eq hy0 (C * P * C') Q hP' hQ hbvalP'
    (hmP'.trans hm))

end

end Work.KT.D2
