/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.isPrime_span_range_X_castLE` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P37

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.isPrime_span_range_X_castLE ====
section

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

theorem isPrime_span_range_X_castLE {n k : ℕ} (hk : k ≤ n) :
    (Ideal.span (Set.range (fun i : Fin k =>
      (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ)))).IsPrime := by
  classical
  set I : Ideal (MvPolynomial (Fin n) ℂ) :=
    Ideal.span (Set.range (fun i : Fin k =>
      (MvPolynomial.X (Fin.castLE hk i) : MvPolynomial (Fin n) ℂ))) with hI
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
    MvPolynomial.aeval (fun i : Fin n =>
      if (i : ℕ) < k then 0 else (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))
  have hφX : ∀ i : Fin n, φ (MvPolynomial.X i)
      = if (i : ℕ) < k then 0 else (MvPolynomial.X i : MvPolynomial (Fin n) ℂ) := by
    intro i
    show MvPolynomial.aeval (fun j : Fin n =>
      if (j : ℕ) < k then 0 else (MvPolynomial.X j : MvPolynomial (Fin n) ℂ))
      (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hI_le : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    change φ (MvPolynomial.X (Fin.castLE hk i)) = 0
    rw [hφX, Fin.val_castLE, if_pos i.isLt]
  have hM : ∀ p : MvPolynomial (Fin n) ℂ, p - φ p ∈ I := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have hca : φ (MvPolynomial.C a) = MvPolynomial.C a := by
        rw [MvPolynomial.C_eq_algebraMap]
        exact AlgHom.commutes φ a
      rw [hca, sub_self]
      exact Submodule.zero_mem I
    | add p q hp hq =>
      rw [map_add]
      have hd : p + q - (φ p + φ q) = (p - φ p) + (q - φ q) := by abel
      rw [hd]
      exact I.add_mem hp hq
    | mul_X p m hp =>
      rw [map_mul, hφX]
      have hd : p * MvPolynomial.X m
          - φ p * (if (m : ℕ) < k then 0 else (MvPolynomial.X m : MvPolynomial (Fin n) ℂ))
          = (p - φ p) * MvPolynomial.X m
            + φ p * (MvPolynomial.X m -
                (if (m : ℕ) < k then 0 else (MvPolynomial.X m : MvPolynomial (Fin n) ℂ))) := by
        ring
      rw [hd]
      apply I.add_mem
      · exact I.mul_mem_right _ hp
      · apply I.mul_mem_left
        by_cases hmk : (m : ℕ) < k
        · rw [if_pos hmk, sub_zero]
          apply Ideal.subset_span
          refine ⟨⟨m, hmk⟩, ?_⟩
          change MvPolynomial.X (Fin.castLE hk ⟨m, hmk⟩) = MvPolynomial.X m
          rw [show Fin.castLE hk ⟨m, hmk⟩ = m from Fin.ext (by simp)]
        · rw [if_neg hmk, sub_self]
          exact Submodule.zero_mem I
  have hker_le : RingHom.ker φ ≤ I := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h := hM x
    rwa [hx, sub_zero] at h
  have hIeq : I = RingHom.ker φ := le_antisymm hI_le hker_le
  rw [hIeq]
  exact RingHom.ker_isPrime φ

end Commons.Algebra.MvPolynomial
end


