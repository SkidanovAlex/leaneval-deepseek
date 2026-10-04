import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.Lead.J_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the dimension-free Friedrichs-mollifier bound `BNorm k (J ρ ε h) ≤ C · BNorm k h`

`Submission/Work/Diff/STE/B3/BNorm_J_le_uniform.lean` proves this estimate for a constant `C`
independent of `ε ∈ (0,1]`, but under the extra dimension hypothesis `finrank ℝ E < 2 * k`,
which enters only through the chart-transfer estimate `CSq_period_comp_arg_le_of_isOpen` (whose
proof bounds the test function in sup norm via the Sobolev embedding, available only for
`k > finrank E / 2`).  The dimension-free transfer `CSq_period_comp_arg_le_nodim_of_isOpen`
removes that restriction, and the whole argument — with the transfer estimate carried as an
explicit hypothesis — is already assembled, sorry-free, in
`Work.Diff.STE.Lead.BNorm_J_le_of_transfer`
(module `Submission.Work.Diff.STE.Lead.J_norm_le`).  This file is the resulting instantiation.

The surrounding argument (unchanged from the dimension-restricted version): `J ρ ε h` is a finite
sum `Σ_i Rstar_i (S_ε (R i h))`; each cross-chart component `R j (Rstar i (S_ε (R i h)))` is a
periodisation of `z ↦ G(z) · u (T z)` with `u := S_ε (R i h)` (`bump_expansion`), to which the
chart-transfer estimate applies, giving a bound by `CSq k (fourierCoeff u)` (after the additive
constant `+|1|` is removed by the rescaling `homog_transfer`); `S_ε` is a contraction on every
`CSq` level (`STruncR_CSq_le`) and the finite sum is handled by `CSq_sum_le`.
-/

namespace Work.Diff.STE.B3

theorem BNorm_J_le_uniform_nodim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
          D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  classical
  refine Work.Diff.STE.Lead.BNorm_J_le_of_transfer (I := I) (M := M) k ?_ D ρ hρ
  intro T f hf hfsupp hK U hU hUf hT hinj hdet
  exact CSq_period_comp_arg_le_nodim_of_isOpen k T f hf hfsupp hK U hU hUf hT hinj hdet

end Work.Diff.STE.B3
