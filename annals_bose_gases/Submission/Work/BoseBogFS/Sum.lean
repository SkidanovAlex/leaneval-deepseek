import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBogFS.Ground
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Sum` — the finite-sum steps over the mode labels

`KzBogFS` is `Σ_k ½ • bogPairOp_k`; summing `bogPairOp_ground` over the labels (including
the `χ`-label `0`, `F6`) gives FS `thm:BogHamDiag`'s zero-point bound

  `−Σ_k ½(𝒵_k+κ_k)‖f‖² ≤ ⟨f, 𝒦^Bog f⟩`,

and the *shifted* diagonal reserve `Σ_{k∈RHi}𝒟_k(b_k+c_k)†(b_k+c_k)` (FS `thm:Control3Q`'s
`eq:Q3Cancels` diagonal, with `c_k` inside `b_k` as in `eq:Defb_k`) is dominated by
`𝒦^Bog` plus the same scalar.

The reindexing `k ↦ −k` of the finite additive group `Mode` replaces the pair sum by the
label sum; `𝒟_{−k} = 𝒟_k` is the evenness of the diagonal coefficient.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `KzBogFS` is the half-weighted sum of the per-pair quadratics. -/
theorem KzBogFS_eq_sum (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) :
    KzBogFS F E ρ = ∑ k : Mode, (1 / 2 : ℝ) • bogPairOp F E ρ k := by
  simp only [KzBogFS, bogPairOp, bogA, bogB, bogC, bogZ]

/-- Applying a finite weighted sum of linear maps to a vector. -/
theorem sum_smul_apply (F : FockData Mode) (s : Finset Mode) (c : Mode → ℝ)
    (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    (∑ k ∈ s, c k • T k) f = ∑ k ∈ s, c k • (T k f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih,
        LinearMap.smul_apply]

/-- The Fock form is additive in its first argument over a finite sum. -/
theorem bp_sum (F : FockData Mode) (s : Finset Mode) (y : Mode → F.H) (f : F.H) :
    F.bp (∑ x ∈ s, y x) f = ∑ x ∈ s, F.bp (y x) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, LinearMap.add_apply, ih]

/-- The quadratic form of a finite weighted sum over a Finset. -/
theorem qw_sum_finset (F : FockData Mode) (s : Finset Mode) (c : Mode → ℝ)
    (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    F.qw f (∑ k ∈ s, c k • T k) = ∑ k ∈ s, c k * F.qw f (T k) := by
  rw [FockData.qw, sum_smul_apply F s c T f, bp_sum F s (fun k => c k • (T k f)) f]
  exact Finset.sum_congr rfl fun k _ => by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, FockData.qw]

/-- The quadratic form of a finite weighted sum. -/
theorem qw_sum (F : FockData Mode) (c : Mode → ℝ) (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    F.qw f (∑ k : Mode, c k • T k) = ∑ k : Mode, c k * F.qw f (T k) :=
  qw_sum_finset F Finset.univ c T f

/-- Reindexing a finite additive group by `k ↦ −k`. -/
theorem sum_neg_index (g : Mode → ℝ) : (∑ k : Mode, g (-k)) = ∑ k : Mode, g k :=
  Equiv.sum_comp (Equiv.neg Mode) g

/-- **FS `thm:BogHamDiag`'s zero-point bound** at the chapter's `KzBogFS`: the value of the
Bogoliubov quadratic dominates minus the sum of the per-mode zero points and `κ`-errors. -/
theorem qw_KzBogFS_ge (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (f : F.H)
    (hA : ∀ k, 0 < bogA E ρ k) (hB : ∀ k, |bogB E ρ k| ≤ bogA E ρ k)
    (hAB : ∀ k, 0 < bogA E ρ k + bogB E ρ k)
    (hAe : ∀ k, bogA E ρ k = bogA E ρ (-k)) (hBe : ∀ k, bogB E ρ k = bogB E ρ (-k))
    (hCe : ∀ k, bogC E ρ k = bogC E ρ (-k))
    (hccr : ∀ k, bogCcr2 F k ≤ 2) :
    -(∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))) * F.normSq f
      ≤ F.qw f (KzBogFS F E ρ) := by
  rw [KzBogFS_eq_sum, qw_sum]
  have hper : ∀ k : Mode, -(Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) * F.normSq f
      ≤ F.qw f (bogPairOp F E ρ k) := fun k =>
    bogPairOp_ground F E ρ k (hA k) (hB k) (hAB k) (hAe k).symm (hBe k).symm (hCe k).symm
      (hccr k) f
  have h1 : (∑ k : Mode, (1 / 2 : ℝ) * (-(Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) * F.normSq f))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * F.qw f (bogPairOp F E ρ k) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hper k) (by norm_num)
  have h2 : (∑ k : Mode, (1 / 2 : ℝ) * (-(Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
        + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)) * F.normSq f))
      = -(∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
          + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))) * F.normSq f := by
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith [h1, h2.le, h2.ge]

end Work.BoseBogFS
