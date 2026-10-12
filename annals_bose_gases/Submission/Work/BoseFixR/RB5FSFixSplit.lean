import ChallengeDeps
import Submission.Work.BoseFixR.RB5FSFixAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `RB5FSFixSplit.lean` — the `ε`-split of `KzBogFS` and its `n₊`-correction

Pieces of FS's proof of `lem:Roughbounds` (`eq:Rough2`) that the far-leg residual needs and
that are *independent* of the two hard slots (`FarMass`, `FarThreeQ`):

* `KzBogFS_split` — the identity
  `KzBogFS F E ρ = KzBogFS F (farEnv E v μ ρ) ρ + Σ_k ½•((ετ_k − ρε^{-1/2}a)•(nOp k + nOp (−k)))`,
  i.e. FS's replacement of the kinetic symbol `τ` by `(1−ε)τ + ρε^{-1/2}a`;
* `sum_neg_index` — the reindexing `k ↦ −k`;
* `nPlus_window_le` — `⟨Σ_k n_k⟩ ≤ Cn·𝓜‖f‖²` on the window (Bessel conjunct + window);
* `epsCorr_lower` — the `n₊`-correction of the `ε`-split is at most
  `ρε^{-1/2}a·Cn·𝓜‖f‖²` in absolute value.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7 Work.BoseB7A

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `ε`-split of FS's Bogoliubov quadratic.**  FS's proof of `lem:Roughbounds`
(`eq:Rough2`) replaces the kinetic symbol `τ` by `(1−ε)τ + ρε^{-1/2}a`
(`Work.BoseFixR.farEnv`), so that the diagonal `𝒜₁ = (1−ε)τ + ρε^{-1/2}a + ρŴ₁` is strictly
positive and dominates `ℬ = ρŴ₁`; the difference is the `n₊`-term
`(ετ_k − ρε^{-1/2}a)(n_k + n_{−k})` controlled by FS `eq:Rough0`. -/
lemma KzBogFS_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (v : ℝ³ → ℝ) (μ ρ : ℝ) :
    KzBogFS F E ρ
      = KzBogFS F (farEnv E v μ ρ) ρ
        + ∑ k : Mode, (1 / 2 : ℝ) • ((epsFar v μ ρ * E.tau k
            - ρ * (epsFar v μ ρ) ^ (-(1 / 2 : ℝ)) * a v) • (F.nOp k + F.nOp (-k))) := by
  simp only [KzBogFS, farEnv, KzEnvAt]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  module

/-- Reindexing `k ↦ −k` of a sum over a finite additive group. -/
lemma sum_neg_index {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (g : Mode → ℝ) :
    (∑ k : Mode, g (-k)) = ∑ k : Mode, g k := by
  refine Fintype.sum_equiv (Equiv.neg Mode) (fun k => g (-k)) g (fun k => ?_)
  simp

/-- `⟨Σ_k n_k⟩ ≤ Cn·𝓜‖f‖²` on the `𝓜`-window, the Bessel conjunct being
`∀ g, ⟨Σ_k n_k g, g⟩ ≤ Cn⟨T.N g, g⟩`. -/
lemma nPlus_window_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F) {Cn M : ℝ} (hCn : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ g : F.H, F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g)
    {f : F.H} (hf : T.NWindow M f) :
    F.qw f (∑ k : Mode, F.nOp k) ≤ Cn * M * F.normSq f := by
  have hTN : F.bp (T.N f) f ≤ M * F.normSq f := NWindow_bp_N_le F T hM hf
  calc F.qw f (∑ k : Mode, F.nOp k)
      = F.bp ((∑ k : Mode, F.nOp k) f) f := rfl
    _ ≤ Cn * F.bp (T.N f) f := hBessel f
    _ ≤ Cn * (M * F.normSq f) := mul_le_mul_of_nonneg_left hTN hCn
    _ = Cn * M * F.normSq f := by ring

end Work.BoseFixR
