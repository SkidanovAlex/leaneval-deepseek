import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBogFS.Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.PairIdentity` — FS `eq:BogIdentity` at FS's `b_k`

The per-pair Bogoliubov identity of FS `thm:BogHamDiag`: the pair quadratic

  `𝒜_k(n_k+n_{-k}) + ℬ_k(a_ka_{-k}+a_k†a_{-k}†) + 𝒞_k(a_k+a_k†+a_{-k}+a_{-k}†)`

equals `𝒟_k(b_k†b_k + b_{-k}†b_{-k})` minus `𝒟_kα_k²([a_k,a_k†]+[a_{-k},a_{-k}†])` and
minus the `κ`-error `2𝒞_k²/(𝒜_k+ℬ_k)`, where `b_k = a_k + α_ka_{-k}† + c_k` is FS's
squeezed annihilation operator of `eq:Defb_k` **with the shift `c_k` inside**.

Everything is a pure `Work.BoseB7.FockData` computation on the two modes `(k,−k)`:
the scalar inputs are `bog_D_mul_one_add_alpha_sq` (`𝒟(1+α²) = 𝒜`),
`bog_alpha_mul_D` (`2𝒟α = ℬ`), `fms_lin_coeff` (`𝒟c(1+α) = 𝒞`) and `fms_sq_coeff`
(`2𝒟c² = κ`).

This is the `FsBogDecomp`-free route to `thm:BogHamDiag`: the identity is local to the
pair, so no mode decomposition/second-quantisation bridge is needed.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The shift expansion of one squeezed number operator:
`(b_j+c_j)†(b_j+c_j) = b_j†b_j + c_j(b_j†+b_j) + c_j²`. -/
theorem bogBShift_mul (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (j : Mode) :
    (bogBShiftDag F E ρ j) ∘ₗ (bogBShift F E ρ j)
      = (F.bOpDag (bogAlpha E ρ) j) ∘ₗ (F.bOp (bogAlpha E ρ) j)
        + (bogGamma E ρ j) • ((F.bOpDag (bogAlpha E ρ) j) + (F.bOp (bogAlpha E ρ) j))
        + ((bogGamma E ρ j) ^ 2) • (1 : F.H →ₗ[ℝ] F.H) := by
  simp only [bogBShiftDag, bogBShift, ← Module.End.mul_eq_comp]
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, pow_two]
  module

/-- The shift expansion summed over the pair `(k,−k)` (with the shift even):
`(b_k+c)†(b_k+c) + (b_{-k}+c)†(b_{-k}+c) = (b_k†b_k+b_{-k}†b_{-k}) + c·Σ(b_j†+b_j) + 2c²`. -/
theorem bogBShift_mul_pair (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hγ : bogGamma E ρ (-k) = bogGamma E ρ k) :
    (bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)
      + (bogBShiftDag F E ρ (-k)) ∘ₗ (bogBShift F E ρ (-k))
      = ((F.bOpDag (bogAlpha E ρ) k) ∘ₗ (F.bOp (bogAlpha E ρ) k)
          + (F.bOpDag (bogAlpha E ρ) (-k)) ∘ₗ (F.bOp (bogAlpha E ρ) (-k)))
        + (bogGamma E ρ k) •
            (((F.bOpDag (bogAlpha E ρ) k) + (F.bOp (bogAlpha E ρ) k))
              + ((F.bOpDag (bogAlpha E ρ) (-k)) + (F.bOp (bogAlpha E ρ) (-k))))
        + (2 * (bogGamma E ρ k) ^ 2) • (1 : F.H →ₗ[ℝ] F.H) := by
  rw [bogBShift_mul F E ρ k, bogBShift_mul F E ρ (-k), hγ]
  module

/-- The linear part of `b_j†+b_j` summed over the pair `(k,−k)`:
`Σ_{j∈{k,−k}}(b_j†+b_j) = (1+α_k)(a_k+a_k†+a_{-k}+a_{-k}†)` when `α_{-k} = α_k`. -/
theorem bOp_lin_sum (F : FockData Mode) (α : Mode → ℝ) (k : Mode) (hα : α (-k) = α k) :
    ((F.bOpDag α k) + (F.bOp α k)) + ((F.bOpDag α (-k)) + (F.bOp α (-k)))
      = (1 + α k) • (F.aDag k + F.a k + F.aDag (-k) + F.a (-k)) := by
  simp only [FockData.bOp, FockData.bOpDag, hα, add_smul, one_smul, smul_add]
  abel

/-- **FS `eq:BogIdentity` at FS's `b_k`** (the shift `c_k` of `eq:Defb_k` included).

`𝒜_k(n_k+n_{-k}) + ℬ_k(a_ka_{-k}+a_k†a_{-k}†) + 𝒞_k(a_k+a_k†+a_{-k}+a_{-k}†)`
`= 𝒟_k(b_k†b_k + b_{-k}†b_{-k}) − (𝒟_kα_k²ccr2_k + κ_k)·1`, with `ccr2_k` the sum of the
two commutators. -/
theorem bogPairOp_eq_shifted (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < bogA E ρ k) (hB : |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : 0 < bogA E ρ k + bogB E ρ k)
    (hAe : bogA E ρ (-k) = bogA E ρ k) (hBe : bogB E ρ (-k) = bogB E ρ k)
    (hCe : bogC E ρ (-k) = bogC E ρ k) :
    bogPairOp F E ρ k
      = (bogD E ρ k) • ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k)
            + (bogBShiftDag F E ρ (-k)) ∘ₗ (bogBShift F E ρ (-k)))
        - ((bogD E ρ k * (bogAlpha E ρ k) ^ 2 * bogCcr2 F k)
            + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))
          • (1 : F.H →ₗ[ℝ] F.H) := by
  have hα : bogAlpha E ρ (-k) = bogAlpha E ρ k := by
    simp only [bogAlpha, hAe, hBe]
  have hγ : bogGamma E ρ (-k) = bogGamma E ρ k := by
    simp only [bogGamma, hAe, hBe, hCe]
  have hD : bogD E ρ (-k) = bogD E ρ k := by
    simp only [bogD, hAe, hBe]
  -- the scalar identities of the diagonalisation
  have hD1 : bogD E ρ k * (1 + bogAlpha E ρ k ^ 2) = bogA E ρ k := by
    simpa only [bogD, bogAlpha, bogA, bogB] using
      Submission.BoseGases.bog_D_mul_one_add_alpha_sq hA hB
  have hD2 : bogD E ρ k * (2 * bogAlpha E ρ k) = bogB E ρ k := by
    have h := Submission.BoseGases.bog_alpha_mul_D hA hB
    simp only [bogD, bogAlpha, bogA, bogB] at h ⊢
    linarith
  have hD3 : bogD E ρ k * (bogGamma E ρ k * (1 + bogAlpha E ρ k)) = bogC E ρ k := by
    have h := Submission.BoseGases.fms_lin_coeff (A := bogA E ρ k) (B := bogB E ρ k)
      (L := bogC E ρ k) hA hB hAB
    simp only [bogD, bogAlpha, bogGamma, bogA, bogB, bogC] at h ⊢
    linarith
  have hD4 : bogD E ρ k * (2 * bogGamma E ρ k ^ 2)
      = Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k) := by
    have h := Submission.BoseGases.fms_sq_coeff (A := bogA E ρ k) (B := bogB E ρ k)
      (L := bogC E ρ k) hA hB hAB
    simp only [bogD, bogGamma, bogA, bogB, bogC, Work.BoseB6.bogKappaErr] at h ⊢
    linarith
  have hblock := bOp_pair_expand F (bogAlpha E ρ) k hα
  have hsh := bogBShift_mul_pair F E ρ k hγ
  rw [hsh, hblock, bOp_lin_sum F (bogAlpha E ρ) k hα]
  simp only [bogPairOp, bogA, bogB, bogC, smul_add, smul_smul]
  rw [hD1, hD2, hD3, hD4]
  simp only [bogA, bogB, bogC, bogCcr2]
  module

end Work.BoseBogFS
