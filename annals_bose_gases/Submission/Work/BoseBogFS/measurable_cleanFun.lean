import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseBogFS.CleanRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

/-!
# `Work.BoseBogFS.measurable_cleanFun`

`cleanFun v h ρ μ k = 𝒵(τ(k)+c(k), c(k)) − c(k)²/(2‖k‖²)` with `τ = tauAt`, `c = cAt = ρ·Ŵ₁(k)`
and `𝒵 = bogZeroPoint`.  Its measurability is what lets the clean row `ZPCleanDeficitRow` speak
about the *integral* `∫ cleanFun` at all.

The proof is a continuity computation.  The three ingredients are

* `tauAt v μ` is continuous in `k` (`tauSm` is a fixed linear combination of compositions of the
  continuous profile `tauProf` with `k ↦ ‖k‖`),
* `cAt v h ρ μ k = ρ·Ŵ₁(k)` is continuous in `k`, and *this is where the hypothesis
  `Integrable (W1fun v h (ell v μ))` is used*: by `continuous_chat` the `p`-convention Fourier
  transform of an `L¹` function is continuous,
* `bogZeroPoint A B = A − √(A²−B²)` is continuous in `(A,B)` (Mathlib's `Real.continuous_sqrt`).

The last term `c(k)²/(2‖k‖²)` is *not* continuous at `k = 0`, but it is manifestly measurable
(`inv` is measurable on `ℝ`), which suffices.
-/

/-- The profile `tauProf` chosen by `exists_tauProf` is continuous. -/
lemma continuous_tauProf : Continuous Work.BoseBoxFock.tauProf :=
  Work.BoseBoxFock.tauProf_spec.1.continuous

theorem measurable_cleanFun {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ ρ : ℝ}
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))) :
    Measurable (fun k : EuclideanSpace ℝ (Fin 3) => Work.BoseBogFS.cleanFun v h ρ μ k) := by
  have hτc : Continuous Work.BoseBoxFock.tauProf := continuous_tauProf
  -- `k ↦ τ(k)` is continuous
  have hτ : Continuous (fun k : ℝ³ => tauAt v μ k) := by
    unfold tauAt Work.BoseBoxFock.tauSm
    fun_prop
  -- `k ↦ c(k) = ρ·Ŵ₁(k)` is continuous: this is the one place the `L¹` hypothesis is used
  have hc : Continuous (fun k : ℝ³ => cAt v h ρ μ k) := by
    have hcc : Continuous (Work.BoseFixR.chat (W1fun v h (ell v μ))) := continuous_chat _ hW
    unfold cAt W1At
    fun_prop
  -- `𝒵(τ+c, c)` is measurable (it is in fact continuous)
  have hbog : Measurable (fun k : ℝ³ =>
      Work.BoseB6.bogZeroPoint (tauAt v μ k + cAt v h ρ μ k) (cAt v h ρ μ k)) := by
    unfold Work.BoseB6.bogZeroPoint
    fun_prop
  -- the subtraction term `c(k)²/(2‖k‖²)` is measurable (`inv` on `ℝ` is measurable)
  have h2 : Measurable (fun k : ℝ³ => (cAt v h ρ μ k) ^ 2 / (2 * ‖k‖ ^ 2)) := by
    fun_prop
  show Measurable (fun k : ℝ³ =>
    Work.BoseB6.bogZeroPoint (tauAt v μ k + cAt v h ρ μ k) (cAt v h ρ μ k)
      - (cAt v h ρ μ k) ^ 2 / (2 * ‖k‖ ^ 2))
  exact hbog.sub h2

end Work.BoseBogFS
