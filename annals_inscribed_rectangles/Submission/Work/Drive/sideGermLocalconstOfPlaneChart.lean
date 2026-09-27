import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.sideGerm_parity_eq_of_close_of_separation

/-!
# The germ route's local constancy with the `hdisj` slot **gone**

`Work.Drive.sideGerm_spec` (in the germ lane's `sideGerm.lean`) takes the hypothesis
`hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)` for every `w ∈ Zc γ`, which is **not** a
consequence of `w ∈ Zc γ` and the chart's `IsPlaneChart` data (the `cap ∩ w·cap` piece is a genuine
`2`-dimensional condition, and `Zc γ` may accumulate at `0`).  This file records the same local
constancy with that hypothesis replaced by the data that *is* obtainable:

* `hγne`, `hγinj` (in the application: `IsSmoothEmbedding`), `hQ : IsPlaneChart γ hγne Q`, `hw : w ∈ Zc γ`;
* and the **Sard existence** `hA` (obligation (1) of the route: `sideGerm_good_exists`).

The proof is the *proved* assembly `Work.Drive.sideGerm_localconst_of_exists_and_parity` fed by `hA` and
by the proved parity locality `Work.Drive.sideGerm_parity_eq_of_close_of_separation`.  No hypothesis of
this theorem is an unproved statement except `hA`, which is *passed in* rather than assumed here — so the
theorem is `sorry`-free and axiom-clean, and it becomes fully unconditional (modulo `IsSmoothEmbedding`)
as soon as the Sard lands.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The germ side value is locally constant in the angle, with the `hdisj` slot discharged.** -/
theorem sideGerm_localconst_of_planeChart {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hA : ∀ w' : UnitAddCircle, ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w' t)
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  sideGerm_localconst_of_exists_and_parity Ξ Q c w hA
    (sideGerm_parity_eq_of_close_of_separation Ξ Q c hγne hγinj hQ hΞ hc hcbot w hw)

end

end Work.Drive
