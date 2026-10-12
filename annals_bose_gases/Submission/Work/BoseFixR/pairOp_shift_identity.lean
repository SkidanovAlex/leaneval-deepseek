import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `pairOp_shift_identity` — the generic per-pair Bogoliubov shift identity in `FockData`
vocabulary

This is a *generic* restatement (in arbitrary coefficient functions `A B C : Mode → ℝ`) of
FS `eq:BogIdentity` at FS's shifted squeezing operator `b_k = a_k + α_k a_{-k}† + c_k`
(`eq:Defb_k`), i.e. verbatim `Work.BoseBogFS.bogPairOp_eq_shifted` with
`bogA E ρ k`/`bogB E ρ k`/`bogC E ρ k` replaced by `A k`/`B k`/`C k`.
The proofs of `Submission/Work/BoseBogFS/Pair.lean` and
`Submission/Work/BoseBogFS/PairIdentity.lean` (both in this workspace, readable,
sorry-free) are ported verbatim below, replacing the
`bogA/bogB/bogC/bogZ/bogAlpha/bogD/bogGamma/bogCcr2` vocabulary by the generic definitions
below.  The needed scalar inputs are `Submission.BoseGases.bog_D_mul_one_add_alpha_sq`
(`𝒟(1+α²) = 𝒜`), `Submission.BoseGases.bog_alpha_mul_D` (`2𝒟α = ℬ`),
`Submission.BoseGases.fms_lin_coeff` (`𝒟c(1+α) = 𝒞`) and
`Submission.BoseGases.fms_sq_coeff` (`2𝒟c² = κ`); the operator algebra uses
`F.ccr`, `F.cre_comm`, `F.ann_comm` and `Work.BoseB7.bOpDag_bp`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- FS `eq:Defb_k`'s squeezing parameter `α_k = ℬ_k/(𝒜_k+√(𝒜_k²−ℬ_k²))`. -/
noncomputable def pairAlpha {Mode : Type*} (A B : Mode → ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.bogAlpha (A k) (B k)

/-- FS `thm:BogHamDiag`'s `𝒟_k = ½(𝒜_k + √(𝒜_k²−ℬ_k²))`. -/
noncomputable def pairD {Mode : Type*} (A B : Mode → ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.bogD (A k) (B k)

/-- FS `eq:Defb_k`'s `c`-number shift `c_k = 2𝒞_k/(𝒜_k+ℬ_k+√(𝒜_k²−ℬ_k²))`. -/
noncomputable def pairGamma {Mode : Type*} (A B C : Mode → ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.fmsGamma (A k) (B k) (C k)

/-- FS `eq:Defb_k`'s shifted squeezing operator `b_k = a_k + α_ka_{-k}† + c_k`. -/
noncomputable def pairShift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (A B C : Mode → ℝ) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOp (pairAlpha A B) k + (pairGamma A B C k) • (1 : F.H →ₗ[ℝ] F.H)

/-- Its formal adjoint `b_k†` for the Fock form `bp` (the shift is real). -/
noncomputable def pairShiftDag {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (A B C : Mode → ℝ) (k : Mode) : F.H →ₗ[ℝ] F.H :=
  F.bOpDag (pairAlpha A B) k + (pairGamma A B C k) • (1 : F.H →ₗ[ℝ] F.H)

/-! ## 1. The generic pair algebra (ported from `Work.BoseBogFS.Pair` / `PairIdentity`)

The three operator identities of `Submission/Work/BoseBogFS/Pair.lean` and
`Submission/Work/BoseBogFS/PairIdentity.lean` are stated there for the fixed coefficient
family `α = bogAlpha E ρ` (resp. `bogBShift`); they are re-proved here for an *arbitrary*
`α : Mode → ℝ` (resp. `pairShift`), which is all the port needs. -/

/-- **The block expansion of the squeezed number operators** (generic `α`).
With `b_k = a_k + α_k a_{-k}†` (FS `eq:Defb_k` without the shift) and `α (-k) = α k`,

  `b_k†b_k + b_{-k}†b_{-k}
     = (1+α_k²)(n_k + n_{-k}) + 2α_k(a_k†a_{-k}† + a_ka_{-k})
       + α_k²([a_k,a_k†] + [a_{-k},a_{-k}†])`.

All that is used is FS `eq:Commutator_general` (`F.ccr`), the annihilation/creation
commutativity and `α (-k) = α k`. -/
theorem pairOp_block_expand {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (α : Mode → ℝ) (k : Mode) (hα : α (-k) = α k) :
    (F.bOpDag α k) ∘ₗ (F.bOp α k) + (F.bOpDag α (-k)) ∘ₗ (F.bOp α (-k))
      = (1 + α k ^ 2) • (F.nOp k + F.nOp (-k))
        + (2 * α k) • (F.aDag k ∘ₗ F.aDag (-k) + F.a k ∘ₗ F.a (-k))
        + (α k ^ 2 * (F.ccrK k k + F.ccrK (-k) (-k))) • (1 : F.H →ₗ[ℝ] F.H) := by
  have h1 : F.a (-k) ∘ₗ F.aDag (-k)
      = F.aDag (-k) ∘ₗ F.a (-k) + (F.ccrK (-k) (-k)) • (1 : F.H →ₗ[ℝ] F.H) :=
    F.ccr (-k) (-k)
  have h2 : F.a k ∘ₗ F.aDag k
      = F.aDag k ∘ₗ F.a k + (F.ccrK k k) • (1 : F.H →ₗ[ℝ] F.H) := F.ccr k k
  have h3 : F.aDag k ∘ₗ F.aDag (-k) = F.aDag (-k) ∘ₗ F.aDag k := F.cre_comm k (-k)
  have h4 : F.a (-k) ∘ₗ F.a k = F.a k ∘ₗ F.a (-k) := F.ann_comm (-k) k
  have hp1 : ∀ x : F.H, F.a (-k) (F.aDag (-k) x) = F.aDag (-k) (F.a (-k) x) + F.ccrK (-k) (-k) • x := by
    intro x
    have h := DFunLike.congr_fun h1 x
    simpa [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using h
  have hp2 : ∀ x : F.H, F.a k (F.aDag k x) = F.aDag k (F.a k x) + F.ccrK k k • x := by
    intro x
    have h := DFunLike.congr_fun h2 x
    simpa [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using h
  have hp3 : ∀ x : F.H, F.aDag k (F.aDag (-k) x) = F.aDag (-k) (F.aDag k x) := by
    intro x
    have h := DFunLike.congr_fun h3 x
    simpa [LinearMap.comp_apply] using h
  have hp4 : ∀ x : F.H, F.a (-k) (F.a k x) = F.a k (F.a (-k) x) := by
    intro x
    have h := DFunLike.congr_fun h4 x
    simpa [LinearMap.comp_apply] using h
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Module.End.one_apply, FockData.bOp, FockData.bOpDag, FockData.nOp, hα, neg_neg,
    map_add, map_smul]
  rw [hp1 x, hp2 x, hp3 x, hp4 x]
  module

/-- The linear part of `b_j†+b_j` summed over the pair `(k,−k)` (generic `α`):
`Σ_{j∈{k,−k}}(b_j†+b_j) = (1+α_k)(a_k+a_k†+a_{-k}+a_{-k}†)` when `α_{-k} = α_k`. -/
theorem pairOp_lin_sum {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : FockData Mode) (α : Mode → ℝ) (k : Mode) (hα : α (-k) = α k) :
    ((F.bOpDag α k) + (F.bOp α k)) + ((F.bOpDag α (-k)) + (F.bOp α (-k)))
      = (1 + α k) • (F.aDag k + F.a k + F.aDag (-k) + F.a (-k)) := by
  simp only [FockData.bOp, FockData.bOpDag, hα, add_smul, one_smul, smul_add]
  abel

/-- The shift expansion of one squeezed number operator (generic coefficients):
`(b_j+c_j)†(b_j+c_j) = b_j†b_j + c_j(b_j†+b_j) + c_j²`. -/
theorem pairShift_mul {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (A B C : Mode → ℝ) (j : Mode) :
    (pairShiftDag F A B C j) ∘ₗ (pairShift F A B C j)
      = (F.bOpDag (pairAlpha A B) j) ∘ₗ (F.bOp (pairAlpha A B) j)
        + (pairGamma A B C j) • ((F.bOpDag (pairAlpha A B) j) + (F.bOp (pairAlpha A B) j))
        + ((pairGamma A B C j) ^ 2) • (1 : F.H →ₗ[ℝ] F.H) := by
  simp only [pairShiftDag, pairShift, ← Module.End.mul_eq_comp]
  simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, pow_two]
  module

/-- The shift expansion summed over the pair `(k,−k)` (with the shift even). -/
theorem pairShift_mul_pair {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : FockData Mode) (A B C : Mode → ℝ) (k : Mode)
    (hγ : pairGamma A B C (-k) = pairGamma A B C k) :
    (pairShiftDag F A B C k) ∘ₗ (pairShift F A B C k)
      + (pairShiftDag F A B C (-k)) ∘ₗ (pairShift F A B C (-k))
      = ((F.bOpDag (pairAlpha A B) k) ∘ₗ (F.bOp (pairAlpha A B) k)
          + (F.bOpDag (pairAlpha A B) (-k)) ∘ₗ (F.bOp (pairAlpha A B) (-k)))
        + (pairGamma A B C k) •
            (((F.bOpDag (pairAlpha A B) k) + (F.bOp (pairAlpha A B) k))
              + ((F.bOpDag (pairAlpha A B) (-k)) + (F.bOp (pairAlpha A B) (-k))))
        + (2 * (pairGamma A B C k) ^ 2) • (1 : F.H →ₗ[ℝ] F.H) := by
  rw [pairShift_mul F A B C k, pairShift_mul F A B C (-k), hγ]
  module

/-! ## 2. FS `eq:BogIdentity` at the generic shifted squeezing operator -/

/-- **FS `eq:BogIdentity` at FS's `b_k`** (the shift `c_k` of `eq:Defb_k` included):
`𝒜_k(n_k+n_{-k}) + ℬ_k(a_ka_{-k}+a_k†a_{-k}†) + 𝒞_k(a_k+a_k†+a_{-k}+a_{-k}†)`
`= 𝒟_k(b_k†b_k + b_{-k}†b_{-k}) − (𝒟_kα_k²([a_k,a_k†]+[a_{-k},a_{-k}†]) + κ_k)·1`,
where `κ_k = 2𝒞_k²/(𝒜_k+ℬ_k)`. -/
theorem pairOp_shift_identity {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (A B C : Mode → ℝ) (k : Mode)
    (hA : 0 < A k) (hB : |B k| ≤ A k) (hAB : 0 < A k + B k)
    (hAe : A (-k) = A k) (hBe : B (-k) = B k) (hCe : C (-k) = C k) :
    ((A k) • (F.nOp k + F.nOp (-k))
        + (B k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
        + (C k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)))
      = (Work.BoseFixR.pairD A B k) •
          ((Work.BoseFixR.pairShiftDag F A B C k) ∘ₗ (Work.BoseFixR.pairShift F A B C k)
            + (Work.BoseFixR.pairShiftDag F A B C (-k)) ∘ₗ (Work.BoseFixR.pairShift F A B C (-k)))
        - ((Work.BoseFixR.pairD A B k * (Work.BoseFixR.pairAlpha A B k) ^ 2
              * (F.ccrK k k + F.ccrK (-k) (-k))
            + Work.BoseB6.bogKappaErr (A k) (B k) (C k)) • (1 : F.H →ₗ[ℝ] F.H)) := by
  have hα : pairAlpha A B (-k) = pairAlpha A B k := by
    simp only [pairAlpha, hAe, hBe]
  have hγ : pairGamma A B C (-k) = pairGamma A B C k := by
    simp only [pairGamma, hAe, hBe, hCe]
  -- the four scalar coefficient identities of the diagonalisation
  have hD1 : pairD A B k * (1 + pairAlpha A B k ^ 2) = A k := by
    simpa only [pairD, pairAlpha] using
      Submission.BoseGases.bog_D_mul_one_add_alpha_sq (A := A k) (B := B k) hA hB
  have hD2 : pairD A B k * (2 * pairAlpha A B k) = B k := by
    have h := Submission.BoseGases.bog_alpha_mul_D (A := A k) (B := B k) hA hB
    change Submission.BoseGases.bogD (A k) (B k)
        * (2 * Submission.BoseGases.bogAlpha (A k) (B k)) = B k
    linear_combination 2 * h
  have hD3 : pairD A B k * (pairGamma A B C k * (1 + pairAlpha A B k)) = C k := by
    have h := Submission.BoseGases.fms_lin_coeff (A := A k) (B := B k) (L := C k) hA hB hAB
    change Submission.BoseGases.bogD (A k) (B k)
        * (Submission.BoseGases.fmsGamma (A k) (B k) (C k)
            * (1 + Submission.BoseGases.bogAlpha (A k) (B k))) = C k
    rw [← mul_assoc]
    exact h
  have hD4 : pairD A B k * (2 * pairGamma A B C k ^ 2)
      = Work.BoseB6.bogKappaErr (A k) (B k) (C k) := by
    have h := Submission.BoseGases.fms_sq_coeff (A := A k) (B := B k) (L := C k) hA hB hAB
    change Submission.BoseGases.bogD (A k) (B k)
        * (2 * Submission.BoseGases.fmsGamma (A k) (B k) (C k) ^ 2)
      = 2 * (C k) ^ 2 / (A k + B k)
    linear_combination h
  -- the operator algebra
  have hblock := pairOp_block_expand F (pairAlpha A B) k hα
  have hsh := pairShift_mul_pair F A B C k hγ
  rw [hsh, hblock, pairOp_lin_sum F (pairAlpha A B) k hα]
  simp only [smul_add, smul_smul, mul_assoc]
  rw [hD1, hD2, hD3, hD4]
  module

end Work.BoseFixR
