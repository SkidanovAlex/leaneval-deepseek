/-
# `Work.FTS.StrongPersist.H6Aux.Mth6_integral_bound`

The angular majorant `Mth6 α` (`L6Aux.LinMem6Aux`) of the level-six nonlocal term has a
`θ`-integral which is **bounded uniformly in `α ∈ (0,1]`**.

Route.  Two colleagues' facts are combined:

* `L6Aux.gamCoef_angBlk6` — the integrand of `Mth6 α` is dominated by `K · radAngInt α θ`
  *pointwise*, with `K` independent of `α` and
  `radAngInt α θ = sin(2θ)^{-η} + α² Γ(θ)² sin(2θ)^{-γ}`.  The factor `α²` (coming from the
  angular jets `|D_θ^i Γ| ≤ α·10⁵·Γ`) is what keeps the `γ`-singularity integrable *uniformly*
  as `α → 0⁺`;
* `L3Aux.radAngInt_bound` — `∫_{Iθ} radAngInt α ≤ 10500` for every `α ∈ (0,1]`
  (the `η`-part contributes `≤ 10000`, the `γ`-part `≤ 200`).

Integrability of `Mth6 α` (needed to apply the monotone-integral lemma) is
`L6Aux.LinMem6Aux.Mth6_integrable`.  Hence `C := max 1 (K · 10500)` works.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L6Aux.LinMem6Aux
import Submission.Work.FTS.StrongPersist.L6Aux.gamCoef_angBlk6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoef_gamCoef_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open MeasureTheory Set
open scoped Real Topology

/-- The pointwise comparison behind `Mth6_integral_bound`, stated in the `Mth6` vocabulary:
the integrand of `Mth6 α` is dominated by `K · radAngInt α θ` with a single `K` for all
`α ∈ (0,1]`.  (`L3Aux.radAngInt α θ = sin(2θ)^{-η} + α²Γ(θ)²sin(2θ)^{-γ}`.) -/
theorem Mth6_le_radAngInt : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
    Work.FTS.StrongPersist.Mth6 α θ
      ≤ K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
  obtain ⟨K, hKpos, hang⟩ := Work.FTS.StrongPersist.L6Aux.gamCoef_angBlk6
  exact ⟨K, hKpos, fun α hα θ hθ => hang α hα.1 hα.2 θ hθ⟩

theorem Mth6_integral_bound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ) ≤ C := by
  obtain ⟨K, hKpos, hpoint⟩ := Mth6_le_radAngInt
  obtain ⟨M, _hMpos, hbound⟩ := Work.FTS.StrongPersist.L3Aux.radAngInt_bound
  refine ⟨max 1 (K * M), lt_max_of_lt_left one_pos, fun α hα => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hintM : IntegrableOn (Work.FTS.StrongPersist.Mth6 α) Work.Spaces.Iθ :=
    Work.FTS.StrongPersist.Mth6_integrable hα0 hα1
  obtain ⟨hintR, hRbd⟩ := hbound α hα0 hα1
  have hintKR : IntegrableOn (fun θ => K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ)
      Work.Spaces.Iθ := hintR.const_mul K
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.Mth6 α θ)
      ≤ ∫ θ in Work.Spaces.Iθ, K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
        integral_mono_ae hintM hintKR
          (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpoint α hα θ hθ))
    _ = K * ∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
        integral_const_mul K _
    _ ≤ K * M := mul_le_mul_of_nonneg_left hRbd hKpos.le
    _ ≤ max 1 (K * M) := le_max_right _ _

end Work.FTS.StrongPersist.H6Aux
