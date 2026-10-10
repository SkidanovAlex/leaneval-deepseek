import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZElimCertA
import Submission.Work.MotAS.ASZElimCertB
import Submission.Work.MotAS.ASZElimCertC
import Submission.Work.MotAS.ASZElimCertD
import Submission.Work.MotAS.ASZElimCertE
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASZElimMem` — the eliminant of the AS residual chart lies in the chart ideal

The explicit elimination certificate for the characteristic-`5` (Artin--Schreier) residual chart of
the Lin--Shinder Crauder--Katz link: the five cofactors `ASZMem0 … ASZMem4` (in
`Submission/Work/MotAS/ASZElimCertA.lean`) and the correction polynomial `ASZMemCorr`
(in `ASZElimCertB…E.lean`) satisfy

  `Σ_k ASZMem k * zcubAS a b g k - C ((a+2b)(a²-ab-b²)) * rename Fin.succ P = 5 · ASZMemCorr`

over `ℤ[a,b,g,X₀,X₁,X₂]` (so `(a+2b)(a²−ab−b²)·rename P ∈ ZIAS a b g` in characteristic `5`), and
`(a+2b)(a²−ab−b²) ≠ 0` whenever `a²−ab−b² ≠ 0` in characteristic `5` (indeed `a = −2b` forces
`a²−ab−b² = 5b² = 0`).  Hence `rename Fin.succ (ASZElim.P a b g) ∈ ZIAS a b g`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS

open MvPolynomial

section Certs

variable {K : Type*} [Field K] [CharP K 5]

noncomputable def ASZMemCorr (a b g : K) : MvPolynomial (Fin 3) K :=
  ASZMemCorr0 a b g + 
  ASZMemCorr1 a b g + 
  ASZMemCorr2 a b g + 
  ASZMemCorr3 a b g + 
  ASZMemCorr4 a b g + 
  ASZMemCorr5 a b g + 
  ASZMemCorr6 a b g + 
  ASZMemCorr7 a b g + 
  ASZMemCorr8 a b g + 
  ASZMemCorr9 a b g + 
  ASZMemCorr10 a b g + 
  ASZMemCorr11 a b g + 
  ASZMemCorr12 a b g + 
  ASZMemCorr13 a b g + 
  ASZMemCorr14 a b g

/-- **The elimination certificate.** -/
theorem ASZMem_cert (a b g : K) :
    ASZMem0 a b g * zcubAS a b g 0 + ASZMem1 a b g * zcubAS a b g 1
      + ASZMem2 a b g * zcubAS a b g 2 + ASZMem3 a b g * zcubAS a b g 3
      + ASZMem4 a b g * zcubAS a b g 4
      - C ((a + 2 * b) * (a ^ 2 - a * b - b ^ 2)) * rename Fin.succ (ASZElim.P a b g)
    = (5 : MvPolynomial (Fin 3) K) * ASZMemCorr a b g := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [zcubAS, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    ASZMem0, ASZMem1, ASZMem2, ASZMem3, ASZMem4, ASZMemCorr,
    ASZMemCorr0, ASZMemCorr1, ASZMemCorr2, ASZMemCorr3, ASZMemCorr4, ASZMemCorr5, ASZMemCorr6, ASZMemCorr7, ASZMemCorr8, ASZMemCorr9, ASZMemCorr10, ASZMemCorr11, ASZMemCorr12, ASZMemCorr13, ASZMemCorr14,
    ASZElim.P, map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
  rw [h0, h1]
  refl_ring1

end Certs

/-- **The eliminant lies in the AS residual chart ideal.** -/
theorem ASZElimMem (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P a b g) ∈ Work.MotAS.ZIAS a b g := by
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h2b : a + 2 * b ≠ 0 := by
    intro h
    apply ha
    have hfac : a ^ 2 - a * b - b ^ 2 = (a + 2 * b) * (a - 3 * b) + 5 * b ^ 2 := by ring
    rw [h, zero_mul, zero_add, h5, zero_mul] at hfac
    exact hfac
  have hD : (a + 2 * b) * (a ^ 2 - a * b - b ^ 2) ≠ 0 := mul_ne_zero h2b ha
  have hcert := ASZMem_cert (K := K) a b g
  rw [show (5 : MvPolynomial (Fin 3) K) = 0 from CharP.cast_eq_zero _ 5, zero_mul,
    sub_eq_zero] at hcert
  have hmem : MvPolynomial.C ((a + 2 * b) * (a ^ 2 - a * b - b ^ 2))
        * MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P a b g)
      ∈ Work.MotAS.ZIAS a b g := by
    rw [← hcert]
    have h0 : zcubAS a b g 0 ∈ ZIAS a b g := Ideal.subset_span (Set.mem_range_self 0)
    have h1 : zcubAS a b g 1 ∈ ZIAS a b g := Ideal.subset_span (Set.mem_range_self 1)
    have h2 : zcubAS a b g 2 ∈ ZIAS a b g := Ideal.subset_span (Set.mem_range_self 2)
    have h3 : zcubAS a b g 3 ∈ ZIAS a b g := Ideal.subset_span (Set.mem_range_self 3)
    have h4 : zcubAS a b g 4 ∈ ZIAS a b g := Ideal.subset_span (Set.mem_range_self 4)
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.add_mem _
          (Ideal.add_mem _ (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1))
          (Ideal.mul_mem_left _ _ h2))
        (Ideal.mul_mem_left _ _ h3))
      (Ideal.mul_mem_left _ _ h4)
  have hunit : MvPolynomial.C (((a + 2 * b) * (a ^ 2 - a * b - b ^ 2))⁻¹)
        * (MvPolynomial.C ((a + 2 * b) * (a ^ 2 - a * b - b ^ 2))
          * MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P a b g))
      = MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P a b g) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hD, map_one, one_mul]
  have h2 := Ideal.mul_mem_left (Work.MotAS.ZIAS a b g)
    (MvPolynomial.C (((a + 2 * b) * (a ^ 2 - a * b - b ^ 2))⁻¹)) hmem
  rwa [hunit] at h2

end Work.MotAS
