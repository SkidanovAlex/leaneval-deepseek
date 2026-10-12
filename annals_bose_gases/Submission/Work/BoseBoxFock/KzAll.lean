import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.bddBelow_valFS_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.KzAll` — `KzOpFS` with the χ-label-`0` row of `Q₂^ex`

`KzOpFS` (FS `eq:Kz`, `Defs.lean`) uses `F.Q2ex (KzEnvAt E ρ)`, and `F.Q2ex` sums over
`excited Mode = univ.erase 0`.  The χ-label `0` is the *vector* `Qχ_Λ`, an excited state (the
condensate is the separate ambient index `0` of `RealFock m`), so FS's `Q₂` — the image of
`a₀†a_k†a_k a₀` under the `c`-number substitution — carries a label-`0` term
`ρ_z(Ŵ₁ω(0) + Ŵ₁ω(0))·n₀` (`k = 0` in `Q2ex`'s pattern, with `n_k = n₀`).

This module adjoins that row, keeping `KzOpFS`/`model_kafz` and everything proved about them
untouched:

* `KzRow0 F E ρ` — the adjoined operator `ρ_z(Ŵ₁ω(0) + Ŵ₁ω(0))·nOp 0`;
* `KzOpFSAll F T E gHat0 ρ = KzOpFS F T E gHat0 ρ + KzRow0 F E ρ`;
* `KzValFSAll`, `KzDatum.valFSAll` — the same window infima with `KzOpFSAll`;
* `KzOpFS_qw_le_KzOpFSAll` — form monotonicity when the label-`0` coefficient is `≥ 0`;
* `KzOpFSAll_window_ge` — the window lower bound, transported from `KzOpFS_window_ge`.

The bridge to `Work.BoseRowQ2`'s `Q2exAll` (`KzOpFSAll` = `KzOpFS` with `F.Q2ex` replaced by
`F.Q2exAll`) is stated there, not here, to keep this module free of that dependency.
-/

noncomputable section
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.BoseBoxFock

open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The label-`0` coefficient of `Q₂^ex` at density `ρ`: `ρ_z(Ŵ₁ω(0) + Ŵ₁ω(0))`. -/
def kz0Coef (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) : ℝ :=
  (KzEnvAt E ρ).rho * ((KzEnvAt E ρ).W1omega 0 + (KzEnvAt E ρ).W1omega0)

/-- FS's `Q₂` **with the χ-label `0` included**: the row adjoined to `F.Q2ex`. -/
def KzRow0 (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    F.H →ₗ[ℝ] F.H :=
  (kz0Coef E ρ) • F.nOp 0

/-- **FS `eq:Kz` with the label-`0` row of `Q₂^ex`**: `KzOpFS` plus `ρ_z(Ŵ₁ω(0)+Ŵ₁ω(0))·nOp 0`
(the `k = 0` term of `Q2ex`, which the `excited Mode` sum drops). -/
def KzOpFSAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) : F.H →ₗ[ℝ] F.H :=
  KzOpFS F T E gHat0 ρ + KzRow0 F E ρ

lemma KzOpFSAll_def (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzOpFSAll F T E gHat0 ρ = KzOpFS F T E gHat0 ρ + (kz0Coef E ρ) • F.nOp 0 := rfl

/-- The quadratic form of the label-`0` row is `kz0Coef·‖a₀Ψ‖² ≥ 0` when the coefficient is
nonnegative. -/
lemma qw_KzRow0_nonneg (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ)
    (h : 0 ≤ kz0Coef E ρ) (Ψ : F.H) : 0 ≤ F.qw Ψ (KzRow0 F E ρ) := by
  have hnn : 0 ≤ F.qw Ψ (F.nOp 0) := by
    rw [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.nOp, LinearMap.comp_apply]
    rw [F.aDag_adjoint]
    exact F.bp_nonneg _
  rw [KzRow0, Work.BoseB7.FockData.qw_smul]
  exact mul_nonneg h hnn

/-- **Form monotonicity**: `KzOpFS ≤ KzOpFSAll` when the label-`0` coefficient is `≥ 0`. -/
lemma KzOpFS_qw_le_KzOpFSAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (h : 0 ≤ kz0Coef E ρ) (Ψ : F.H) :
    F.qw Ψ (KzOpFS F T E gHat0 ρ) ≤ F.qw Ψ (KzOpFSAll F T E gHat0 ρ) := by
  rw [KzOpFSAll, Work.BoseB7.FockData.qw_add]
  exact le_add_of_nonneg_right (qw_KzRow0_nonneg F E ρ h Ψ)

/-- The substituted energy with the label-`0` row. -/
def KzValFSAll (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) : ℝ :=
  ⨅ (f : {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}),
    F.qw f.1 (KzOpFSAll F T E gHat0 ρ) / F.normSq f.1

def _root_.Work.BoseFixR.KzDatum.valFSAll (D : KzDatum) (ρ : ℝ) : ℝ :=
  KzValFSAll D.F D.T D.E D.gHat0 ρ

/-- **The window lower bound for `KzOpFSAll`**, transported from `KzOpFS_window_ge`: the
adjoined label-`0` row is a nonnegative form when its coefficient is nonnegative. -/
theorem KzOpFSAll_window_ge
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 ρ M Cn KNH : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn) (hKNH : 0 ≤ KNH)
    (hcoef : 0 ≤ kz0Coef E ρ)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hNH : ∀ f : F.H, T.NWindow M f → F.bp (T.NH f) f ≤ KNH * F.normSq f)
    (hKBog : ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (KzBogFS F E ρ))
    (hQ3T : ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ F.qw g (T.Q3T (Work.BoseFixR.KzEnvAt E ρ))) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (KzOpFSAll F T E gHat0 ρ) := by
  obtain ⟨K, hK⟩ := KzOpFS_window_ge F T E gHat0 ρ M Cn KNH hM hCn0 hKNH hBessel hNH hKBog hQ3T
  exact ⟨K, fun g hg => le_trans (hK g hg) (KzOpFS_qw_le_KzOpFSAll F T E gHat0 ρ hcoef g)⟩

end Work.BoseBoxFock
