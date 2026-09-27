import Mathlib
import Submission.Work.Mostow.cuspTwoFixed
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.eigNull
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.ematFix
import Submission.Work.Mostow.geomFiniteDefs

namespace Work.Mostow.Margulis

open Matrix

/-- If `g` fixes exactly one boundary point `ξ` (a singleton `bdFix g`), then the horospherical
level of `g • 0` at `ξ` is `1`: `g` preserves the Busemann function `β_ξ`.

Equivalently, the eigenvalue `lam` of the lift `emat g` on the null vector `θ ξ = nvec ξ` equals
`1`.  We argue by contradiction: if `lam ≠ 1`, then `lam ≠ ±1` (the eigenvalue of a null
eigenvector is positive), and `J`-orthogonality of `emat g` produces an eigenvector `w ≠ 0` for the
reciprocal eigenvalue `lam⁻¹`; such a `w` is null (`mform_self_eq_zero_of_eigen`) and therefore a
multiple of `θ η` for a boundary point `η ∈ Sph n`, which is then a second fixed boundary point —
contradiction. -/
theorem lev_eq_one_of_singleton_bdFix (n : ℕ) (hn : 1 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hF : Work.Mostow.bdFix g = ({ξ} : Set (Submission.Mostow.E n))) :
    Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)) = 1 := by
  have hξfix : Submission.Mostow.bd g ξ = ξ := by
    have hmem : ξ ∈ Work.Mostow.bdFix g := by rw [hF]; exact Set.mem_singleton_iff.mpr rfl
    exact hmem.2
  obtain ⟨lam, _hlamne, hlameig⟩ := Work.Mostow.emat_eigen_of_bd g hξ hξfix
  obtain ⟨hlev, hlampos, _⟩ := Work.Mostow.lev_emat_eigen g hξ hlameig
  have hlam1 : lam = 1 := by
    by_contra hne1
    have hlam_sq : lam ^ 2 ≠ 1 := by
      intro h
      rcases sq_eq_one_iff.mp h with h1 | h1
      · exact hne1 h1
      · linarith
    have hlinv_sq : lam⁻¹ ^ 2 ≠ 1 := by
      intro h
      rcases sq_eq_one_iff.mp h with h1 | h1
      · refine hne1 ?_
        have h3 := congrArg (fun x : ℝ => lam * x) h1
        rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_one] at h3
        exact h3.symm
      · have h3 := congrArg (fun x : ℝ => lam * x) h1
        rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_neg, mul_one] at h3
        linarith
    obtain ⟨w, hw0, hweig⟩ :=
      Work.Mostow.exists_eigen_inv (Work.Mostow.emat g) (Work.Mostow.emat_isJOrth g) lam
        ⟨Work.Mostow.theta ξ, Work.Mostow.nvec_ne_zero ξ, hlameig⟩
    have hww : Work.Mostow.mform w w = 0 :=
      Work.Mostow.mform_self_eq_zero_of_eigen (Work.Mostow.mform_emat_mink g) lam⁻¹ w hw0 hweig
        hlinv_sq
    obtain ⟨η, hηS, ht, hwη⟩ := Work.Mostow.exists_sph_eq_smul_theta w hw0 hww
    have heta : Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.theta η)
        = lam⁻¹ • Work.Mostow.theta η := by
      have h1 : Matrix.mulVec (Work.Mostow.emat g) (w (Sum.inr 0) • Work.Mostow.theta η)
          = lam⁻¹ • (w (Sum.inr 0) • Work.Mostow.theta η) := by
        rw [← hwη]; exact hweig
      rw [Matrix.mulVec_smul, smul_smul] at h1
      have h3 := congrArg (fun z : Fin n ⊕ Fin 1 → ℝ => (w (Sum.inr 0))⁻¹ • z) h1
      rw [smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h3
      have h4 : (w (Sum.inr 0))⁻¹ * (lam⁻¹ * w (Sum.inr 0)) = lam⁻¹ := by
        rw [mul_comm lam⁻¹ (w (Sum.inr 0)), ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
      rw [h4] at h3
      exact h3
    have hηfix : Submission.Mostow.bd g η = η :=
      (Work.Mostow.bdFixIff n hn hA g η hηS).mpr
        ⟨lam⁻¹, inv_ne_zero (ne_of_gt hlampos), heta⟩
    have hηmem : η ∈ Work.Mostow.bdFix g := ⟨hηS, hηfix⟩
    rw [hF] at hηmem
    have hηeq : η = ξ := Set.mem_singleton_iff.mp hηmem
    have heta' : Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.theta ξ)
        = lam⁻¹ • Work.Mostow.theta ξ := by
      simpa [hηeq] using heta
    have heq : lam • Work.Mostow.theta ξ = lam⁻¹ • Work.Mostow.theta ξ :=
      hlameig.symm.trans heta'
    have hs : (lam - lam⁻¹) • Work.Mostow.theta ξ = 0 := by
      rw [sub_smul, sub_eq_zero]; exact heq
    have hlam_eq : lam = lam⁻¹ := by
      rcases smul_eq_zero.mp hs with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 (Work.Mostow.nvec_ne_zero ξ)
    have hsq : lam ^ 2 = 1 := by
      have h3 := congrArg (fun x : ℝ => lam * x) hlam_eq
      rw [mul_inv_cancel₀ (ne_of_gt hlampos)] at h3
      rw [pow_two]; exact h3
    exact hlam_sq hsq
  rw [hlev, hlam1, inv_one]

end Work.Mostow.Margulis
