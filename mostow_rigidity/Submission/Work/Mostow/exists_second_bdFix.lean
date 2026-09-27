import Mathlib
import Submission.Work.Mostow.hlDefsAccess
import Submission.Work.Mostow.cuspTwoFixed
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.bdFixIff

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- **Second boundary fixed point.**  If `ξ ∈ Sph n` is fixed by `g : PO n 1` and the Busemann
cocycle `busemann ξ (g • 0)` is non-zero, then `g` fixes a *second* boundary point `η ≠ ξ`.

The proof reads `emat_eigen_of_bd`: `θ ξ = (ξ,1)` is an eigenvector of the lift `emat g` with a
non-zero eigenvalue `lam > 0`; `lev_emat_eigen` computes `busemann ξ (g • 0) = -log lam`, so the
hypothesis gives `lam ≠ 1`, whence `lam ^ 2 ≠ 1`.  `J`-orthogonality of `emat g` then produces a
non-zero eigenvector for the reciprocal eigenvalue `lam⁻¹` (`exists_eigen_inv`), which is null
(`mform_self_eq_zero_of_eigen`), hence is a multiple of `θ η` for some `η ∈ Sph n`
(`exists_sph_eq_smul_theta`); `η` is fixed by `bd g` and distinct from `ξ` because the two
eigenvalues differ. -/
theorem exists_second_bdFix (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hfix : Submission.Mostow.bd g ξ = ξ)
    (hc : Submission.Mostow.busemann ξ (g • (0 : Submission.Mostow.E n)) ≠ 0) :
    ∃ η : Submission.Mostow.E n, η ∈ Submission.Mostow.Sph n ∧ η ≠ ξ ∧
      Submission.Mostow.bd g η = η := by
  -- (1) the eigenvalue of the lift on `θ ξ`
  obtain ⟨lam, _hlam0, hlameig⟩ := emat_eigen_of_bd g hξ hfix
  obtain ⟨_hlev, hlampos, hbuslog⟩ := lev_emat_eigen g hξ hlameig
  have hlam1 : lam ≠ 1 := by
    intro h
    rw [h, Real.log_one, neg_zero] at hbuslog
    exact hc hbuslog
  have hlam_sq : lam ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact hlam1 h1
    · linarith
  have hlinv_sq : lam⁻¹ ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h1 | h1
    · refine hlam1 ?_
      have h3 := congrArg (fun x : ℝ => lam * x) h1
      rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_one] at h3
      exact h3.symm
    · have h3 := congrArg (fun x : ℝ => lam * x) h1
      rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_neg, mul_one] at h3
      linarith
  -- (2) the reciprocal eigenvalue and its null eigenvector `w`
  obtain ⟨w, hw0, hweig⟩ :=
    exists_eigen_inv (emat g) (emat_isJOrth g) lam ⟨theta ξ, nvec_ne_zero ξ, hlameig⟩
  have hww : mform w w = 0 :=
    mform_self_eq_zero_of_eigen (mform_emat_mink g) lam⁻¹ w hw0 hweig hlinv_sq
  -- (3) the corresponding boundary point `η`
  obtain ⟨η, hηS, ht, hwη⟩ := exists_sph_eq_smul_theta w hw0 hww
  have heta : emat g *ᵥ theta η = lam⁻¹ • theta η := by
    have h1 : emat g *ᵥ (w (Sum.inr 0) • theta η) = lam⁻¹ • (w (Sum.inr 0) • theta η) := by
      rw [← hwη]
      exact hweig
    rw [Matrix.mulVec_smul, smul_smul] at h1
    have h3 := congrArg (fun z : Fin n ⊕ Fin 1 → ℝ => (w (Sum.inr 0))⁻¹ • z) h1
    rw [smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h3
    have h4 : (w (Sum.inr 0))⁻¹ * (lam⁻¹ * w (Sum.inr 0)) = lam⁻¹ := by
      rw [mul_comm lam⁻¹ (w (Sum.inr 0)), ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    rw [h4] at h3
    exact h3
  have hηfix : bd g η = η :=
    (bdFixIff n (by omega) hA g η hηS).mpr
      ⟨lam⁻¹, inv_ne_zero (ne_of_gt hlampos), heta⟩
  -- (4) the two points differ
  have hξη : η ≠ ξ := by
    intro h
    have heta' : emat g *ᵥ theta ξ = lam⁻¹ • theta ξ := by
      rw [← h]
      exact heta
    have heq : lam • theta ξ = lam⁻¹ • theta ξ := hlameig.symm.trans heta'
    have hs : (lam - lam⁻¹) • theta ξ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact heq
    have hlam_eq : lam = lam⁻¹ := by
      rcases smul_eq_zero.mp hs with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 (nvec_ne_zero ξ)
    have : lam ^ 2 = 1 := by
      have h3 := congrArg (fun x : ℝ => lam * x) hlam_eq
      rw [mul_inv_cancel₀ (ne_of_gt hlampos)] at h3
      rw [pow_two]
      exact h3
    exact hlam_sq this
  exact ⟨η, hηS, hξη, hηfix⟩

end

end Work.Mostow
