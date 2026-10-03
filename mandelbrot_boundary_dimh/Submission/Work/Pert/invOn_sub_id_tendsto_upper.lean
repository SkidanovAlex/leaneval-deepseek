import Mathlib
import Submission.Work.Pert.RBlock

/-!
# PERT · `Work.Pert.invOn_sub_id_tendsto_upper`

The chosen preimage `invOn Φ Q w ∈ Q` of `w` under `Φ` (see `Work.Pert.AsmDefs`) tends to the
upper end `im → +∞` whenever `w` does, provided

* `w` eventually lies in `Φ '' Q` (`hcover`), so that `invOn` really is a preimage, and
* `Φ` does not send gate points with bounded imaginary part too high (`hproper`): the
  contrapositive says that a preimage of a point of large height must itself have large height.

Hence `invOn Φ Q w - w = -(Φ ζ - ζ)` with `ζ = invOn Φ Q w ∈ Q`, and the upper-end asymptotic
`Φ z - z → c` (`hEnd`) gives `invOn Φ Q w - w → -c`.
-/

namespace Work.Pert

open Filter Metric Set

noncomputable section

/-- A predicate is eventually true along the upper end `MandelDim.upperEnd = comap im atTop` iff it
holds for every point with sufficiently large imaginary part. -/
lemma eventually_upperEnd_iff {P : ℂ → Prop} :
    (∀ᶠ w in MandelDim.upperEnd, P w) ↔ ∃ T : ℝ, ∀ w : ℂ, T < w.im → P w := by
  rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, fun w hw => hT w.im (le_of_lt hw) w rfl⟩
  · rintro ⟨T, hT⟩
    exact ⟨T + 1, fun b hb w hwb => hT w (by rw [hwb]; linarith)⟩

theorem invOn_sub_id_tendsto_upper {Φ : ℂ → ℂ} {Ξ : ℝ} {α c : ℂ}
    (hinj : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hcover : ∀ᶠ w in MandelDim.upperEnd, w ∈ Φ '' (Work.Pert.Qm Ξ α))
    (hEnd : Filter.Tendsto (fun z => Φ z - z) MandelDim.upperEnd (nhds c))
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ Work.Pert.Qm Ξ α, ζ.im ≤ R → (Φ ζ).im ≤ N) :
    Filter.Tendsto (fun w => Work.Pert.invOn Φ (Work.Pert.Qm Ξ α) w - w)
      MandelDim.upperEnd (nhds (-c)) := by
  obtain ⟨T₁, hT₁⟩ : ∃ T : ℝ, ∀ w : ℂ, T < w.im → w ∈ Φ '' Work.Pert.Qm Ξ α :=
    eventually_upperEnd_iff.mp hcover
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_upperEnd_iff]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : ℂ, R < z.im → dist (Φ z - z) c < ε :=
    eventually_upperEnd_iff.mp ((Metric.tendsto_nhds.mp hEnd) ε hε)
  obtain ⟨N, hN⟩ := hproper R
  refine ⟨max T₁ N, fun w hw => ?_⟩
  -- `w` is large, hence lies in the image of the gate: `ζ = invOn Φ Q w` is a genuine preimage.
  obtain ⟨ζ, hζQ, hΦζ⟩ := hT₁ w (lt_of_le_of_lt (le_max_left T₁ N) hw)
  have hξ : invOn Φ (Work.Pert.Qm Ξ α) w ∈ Work.Pert.Qm Ξ α :=
    invOn_mem ⟨ζ, hζQ, hΦζ⟩
  have hspec : Φ (invOn Φ (Work.Pert.Qm Ξ α) w) = w := invOn_spec ⟨ζ, hζQ, hΦζ⟩
  -- `hproper` forces that preimage to be large as well.
  have hRim : R < (invOn Φ (Work.Pert.Qm Ξ α) w).im := by
    by_contra hcon
    have hle : (invOn Φ (Work.Pert.Qm Ξ α) w).im ≤ R := not_lt.mp hcon
    have := hN _ hξ hle
    rw [hspec] at this
    linarith [le_max_right T₁ N]
  have hdist : dist (w - invOn Φ (Work.Pert.Qm Ξ α) w) c < ε := by
    simpa only [hspec] using hR _ hRim
  have hd : dist (invOn Φ (Work.Pert.Qm Ξ α) w - w) (-c)
      = dist (w - invOn Φ (Work.Pert.Qm Ξ α) w) c := by
    rw [dist_eq_norm, dist_eq_norm,
      show invOn Φ (Work.Pert.Qm Ξ α) w - w - (-c)
        = -(w - invOn Φ (Work.Pert.Qm Ξ α) w - c) by ring, norm_neg]
  rwa [hd]

end

end Work.Pert
