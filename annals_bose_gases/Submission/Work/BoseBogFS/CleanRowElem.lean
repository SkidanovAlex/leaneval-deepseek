import ChallengeDeps
import Submission.Work.BoseBogFS.CleanRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.CleanRowElem` — the elementary steps of the clean row

Two steps of the assembly of `ZPCleanDeficitRow` that need no analysis:

* `finset_sum_le_tsum_of_nonneg_compl` — a finite sum is dominated by the `tsum` when the
  omitted terms are nonnegative (the step that lets a finite `S ⊇ zBall(Λ)` be replaced by the
  full dual lattice);
* `cleanTerm_zero_nonneg` — the label `0` contributes nonnegatively (it is the only label that
  the sign row `cleanFun_nonneg_of_large` does not cover, since that row is stated at
  `n ≠ 0`-containment only through `‖k_n‖`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **A finite sum is dominated by the `tsum` when the omitted terms are nonnegative.** -/
theorem finset_sum_le_tsum_of_nonneg_compl {f : (Fin 3 → ℤ) → ℝ} (hsum : Summable f)
    {S : Finset (Fin 3 → ℤ)} (hS : ∀ n : Fin 3 → ℤ, n ∉ S → 0 ≤ f n) :
    ∑ n ∈ S, f n ≤ ∑' n : Fin 3 → ℤ, f n := by
  have h := hsum.sum_add_tsum_compl (s := S)
  have hnn : 0 ≤ ∑' x : ↑((↑S : Set (Fin 3 → ℤ))ᶜ), f ↑x := by
    apply tsum_nonneg
    intro x
    show 0 ≤ f x
    exact hS x (by
      have hx := x.2
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hx
      exact hx)
  linarith

/-- **The label `0` contributes nonnegatively** to the clean sum: `kAt v μ 0 = 0`, so the
subtracted term is the junk `c²/(2·0) = 0` and the value is `bogZeroPoint (τ(0)+c(0)) c(0)`,
which is `2·zpTerm v h ρ μ 0 ≥ 0` by the proved `ZPTermNonnegLattice`. -/
theorem cleanTerm_zero_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ → 0 ≤ cleanTerm v h ρ μ 0 := by
  obtain ⟨ε₀, hε₀, hrow⟩ := ZPTermNonnegLattice (v := v) (h := h) (R := R)
    hR hv hvrad hv_supp hav
  refine ⟨ε₀, hε₀, fun μ hμ ρ hρ => ?_⟩
  have hk : kAt v μ (0 : Fin 3 → ℤ) = 0 := by
    have hv0 : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by
      ext i
      simp [Work.BoseB4.vec]
    rw [kAt, hv0, smul_zero]
  have hz := hrow μ hμ ρ hρ (0 : Fin 3 → ℤ)
  rw [zpTerm, hk] at hz
  have hclean : cleanTerm v h ρ μ 0
      = Work.BoseB6.bogZeroPoint (tauAt v μ 0 + cAt v h ρ μ 0) (cAt v h ρ μ 0) := by
    rw [cleanTerm, hk]
    simp
  rw [hclean]
  linarith

end Work.BoseBogFS
