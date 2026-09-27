import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.PsiC.DepsDefs

/-!
# `Work.PsiC.Deps_idem` — `Eeps` and `Deps` are complementary orthogonal projectors

The joint projector `Eeps ε n = Π_j halfProj ε (sg_j)` of the three pair swaps and the difference
`Deps ε n = halfProj ε (sB n) - Eeps ε n` of the "product" projector and the joint projector are
both idempotent and are orthogonal to each other, and they add up to `halfProj ε (sB n)`.

This is a purely algebraic statement about three pairwise commuting involutions `x, y, z` (the
permutation matrices of `sg0 n`, `sg1 n`, `sg2 n`): writing `E = h_ε(x) h_ε(y) h_ε(z)` for the
joint projector and `H = h_ε(xyz)` for the projector of the product, the identities
`E * E = E`, `H * H = H`, `H * E = E * H = E` hold, and the algebraic content is settled once and
for all in `Work.PsiC.DepsAux.hps_package` (`Submission/Work/PsiC/DepsDefs.lean`); here it is
instantiated at the three pair swaps of `IB n = (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)`
and transported back from the abstract `hps` to `halfProj` via `hps_eq_halfProj`.
-/

namespace Work.PsiC

open Matrix
open Work.KT.PsiC

noncomputable section

/-- The abstract projector `DepsAux.hps ε x = (1/2)(1 + εx)` of a permutation matrix is the
matrix projector `halfProj ε σ`. -/
theorem hps_eq_halfProj {A : Type} [Ring A] [Algebra ℂ A] (ε : ℂ) {n : ℕ}
    (σ : Equiv.Perm (IB n)) : DepsAux.hps ε (σ.permMatrix A) = halfProj ε σ := by
  rw [DepsAux.hps, halfProj, smulA_eq_smulC, smulA_eq_smulC]

theorem Deps_idem (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (eps : ℂ) (heps : eps ^ 2 = 1) :
    (Work.KT.PsiC.Deps eps n : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) * Work.KT.PsiC.Deps eps n = Work.KT.PsiC.Deps eps n ∧
    (Work.KT.PsiC.Eeps eps n : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) * Work.KT.PsiC.Eeps eps n = Work.KT.PsiC.Eeps eps n ∧
    (Work.KT.PsiC.Deps eps n : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) * Work.KT.PsiC.Eeps eps n = 0 ∧
    (Work.KT.PsiC.Eeps eps n : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) * Work.KT.PsiC.Deps eps n = 0 ∧
    (Work.KT.PsiC.halfProj eps (Work.KT.PsiC.sB n) : Matrix (Work.KT.PsiC.IB n) (Work.KT.PsiC.IB n) A) =
      Work.KT.PsiC.Eeps eps n + Work.KT.PsiC.Deps eps n := by
  -- the three pair-swap permutation matrices are pairwise commuting involutions
  have h0 : (sg0 n).permMatrix A * (sg0 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg0_mul_self, Matrix.permMatrix_one]
  have h1 : (sg1 n).permMatrix A * (sg1 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg1_mul_self, Matrix.permMatrix_one]
  have h2 : (sg2 n).permMatrix A * (sg2 n).permMatrix A = 1 := by
    rw [← Matrix.permMatrix_mul, sg2_mul_self, Matrix.permMatrix_one]
  have k01 : (sg0 n).permMatrix A * (sg1 n).permMatrix A =
      (sg1 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm01]
  have k02 : (sg0 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg0 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm02]
  have k12 : (sg1 n).permMatrix A * (sg2 n).permMatrix A =
      (sg2 n).permMatrix A * (sg1 n).permMatrix A := by
    rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, sg_comm12]
  -- `permMatrix` is an anti-homomorphism, so `sB = sg0*sg1*sg2` gives `p2 * (p1 * p0)`
  have kB : (sB n).permMatrix A = (sg0 n).permMatrix A * (sg1 n).permMatrix A *
      (sg2 n).permMatrix A := by
    rw [sB, Matrix.permMatrix_mul, Matrix.permMatrix_mul]
    calc (sg2 n).permMatrix A * ((sg1 n).permMatrix A * (sg0 n).permMatrix A)
        = ((sg2 n).permMatrix A * (sg1 n).permMatrix A) * (sg0 n).permMatrix A := by
          noncomm_ring
      _ = ((sg1 n).permMatrix A * (sg2 n).permMatrix A) * (sg0 n).permMatrix A := by
          rw [← k12]
      _ = (sg1 n).permMatrix A * ((sg2 n).permMatrix A * (sg0 n).permMatrix A) := by
          noncomm_ring
      _ = (sg1 n).permMatrix A * ((sg0 n).permMatrix A * (sg2 n).permMatrix A) := by
          rw [← k02]
      _ = ((sg1 n).permMatrix A * (sg0 n).permMatrix A) * (sg2 n).permMatrix A := by
          noncomm_ring
      _ = ((sg0 n).permMatrix A * (sg1 n).permMatrix A) * (sg2 n).permMatrix A := by
          rw [← k01]
  obtain ⟨pEE, pHH, pHE, pEH⟩ := DepsAux.hps_package eps heps
    ((sg0 n).permMatrix A) ((sg1 n).permMatrix A) ((sg2 n).permMatrix A)
    h0 h1 h2 k01 k02 k12
  -- identify the abstract projectors with `halfProj` and `Eeps`
  have hEX : DepsAux.hps eps ((sg0 n).permMatrix A) * DepsAux.hps eps ((sg1 n).permMatrix A) *
      DepsAux.hps eps ((sg2 n).permMatrix A) = (Eeps eps n : Matrix (IB n) (IB n) A) := by
    rw [hps_eq_halfProj eps (sg0 n), hps_eq_halfProj eps (sg1 n), hps_eq_halfProj eps (sg2 n)]
    rfl
  have hHX : DepsAux.hps eps ((sg0 n).permMatrix A * (sg1 n).permMatrix A *
      (sg2 n).permMatrix A) = (halfProj eps (sB n) : Matrix (IB n) (IB n) A) := by
    rw [← kB, hps_eq_halfProj]
  have hE : (Eeps eps n : Matrix (IB n) (IB n) A) * Eeps eps n = Eeps eps n := by
    have h := pEE
    simp only [hEX] at h
    exact h
  have hH : (halfProj eps (sB n) : Matrix (IB n) (IB n) A) * halfProj eps (sB n) =
      halfProj eps (sB n) := by
    have h := pHH
    simp only [hHX] at h
    exact h
  have hHE : (halfProj eps (sB n) : Matrix (IB n) (IB n) A) * Eeps eps n = Eeps eps n := by
    have h := pHE
    simp only [hHX, hEX] at h
    exact h
  have hEH : (Eeps eps n : Matrix (IB n) (IB n) A) * halfProj eps (sB n) = Eeps eps n := by
    have h := pEH
    simp only [hHX, hEX] at h
    exact h
  obtain ⟨q1, q2, q3, q4⟩ := DepsAux.sub_facts hH hE hHE hEH
  exact ⟨q1, hE, q2, q3, q4.symm⟩

end

end Work.PsiC
