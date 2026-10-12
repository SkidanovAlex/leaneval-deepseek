import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.chat_g0_abs_le`

    |Ŵ(g₀)(k)| ≤ 8π·(a v)   for every momentum `k`,

where `g₀ = v(1−ω)` is the corpus's scattering numerator (`Submission.BoseGases.g0`),
`Ŵ = Work.BoseFixR.chat` is the corpus's `p`-convention Fourier transform
(`chat W k = (∫ e^{−i⟪k,y⟫} W(y) dy).re`), and `a v` is the scattering length.

## Route

1. `abs_chat_le_integral_abs` (`Work.BoseB7AK.W1rows`): the Fourier transform is
   dominated by the `L¹` mass, `|Ŵ(W)(k)| ≤ ∫|W|` for every `k` and every `W`
   (no integrability hypothesis needed — when `W` is not integrable both sides of
   the `fourierIntegral` definition vanish).
2. `g₀ ≥ 0` a.e. (`Submission.BoseGases.g0_nonneg_ae`), so `|g₀| = g₀` a.e. and
   `∫|g₀| = ∫g₀`.
3. `∫g₀ = 8π·(a v)` (`Submission.BoseGases.g0_integral`) — the mass identity for
   the chosen scattering branch.

Step 3 already forces `a v ≥ 0` here, since `g₀ ≥ 0` a.e. gives
`0 ≤ ∫g₀ = 8π·(a v)`; the right-hand side of the target is therefore nonnegative
and there is no sign edge case.  The constant `8π` is sharp: at `k = 0`,
`Ŵ(g₀)(0) = ∫g₀ = 8π·(a v)`.
-/

namespace Work.BoseRowsFS

noncomputable section

open MeasureTheory

/-- **`∫|g₀| = 8π·(a v)`**: `g₀` is nonnegative a.e. and has total mass `8πa v`. -/
lemma integral_abs_g0_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v) :
    (∫ x : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h x|)
      = 8 * Real.pi * _root_.BoseGases.a v := by
  have hnn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  rw [integral_congr_ae (hnn.mono fun x hx => abs_of_nonneg hx)]
  exact Submission.BoseGases.g0_integral hR hv_supp h

theorem chat_g0_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) k|
      ≤ 8 * Real.pi * _root_.BoseGases.a v := by
  refine le_trans
    (Work.BoseB7AK.W1rows.abs_chat_le_integral_abs (W := Submission.BoseGases.g0 v h) k) ?_
  exact le_of_eq (integral_abs_g0_eq hR hv_nonneg hvrad hv_supp h)

end

end Work.BoseRowsFS
