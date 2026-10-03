import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.invOn_sub_id_tendsto_upper
import Submission.Work.Pert.retOf_sub_id_tendsto_upper
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

namespace Work.Pert.RBlock2

/-! NOTE (fourth revision): the strip half-width is now a PARAMETER `B`, because the reviewers
established (correctly) that the asymptotics of `Φm`/`Φp` are strip-local, so they can only be
applied at the chosen preimage once its real part is confined to a window of width `B` — and the pin
`strip_high_pin_waist` locates the preimage only in a ball of radius `4(‖Φm w - w‖ + 1)` around `w`,
so the width is a caller-supplied constant, not `2`.  (`∀ x, ε, ∃ Y', ∀ z ∈ Q, Y' < z.im →
|z.re - x| ≤ 2 → …` at a single `x` upgrades to width `B` by covering the window with
`⌈B/2⌉ + 1` windows of width `2`.)  The rest is as in the third revision, which both reviewers
verified provable: `hproper` in the orientation of `invOn_sub_id_tendsto_upper`, `hcover` a window
statement carrying the waist membership of `ζ`. -/

/-- **The end limit of the horn map `w ↦ Φp (invOn Φm (Qm) w)`.**

The whole content is the `ε/2` triangle inequality

`(Φp ζ - w - (cp - cm)) = (Φp ζ - ζ - cp) - (Φm ζ - ζ - cm)`

at the chosen preimage `ζ = invOn Φm (Qm) w` of `w`; everything else is bookkeeping of the windows:

* `hcover` gives, for `w` in `[0,1] × [Yc, ∞)`, both the membership `w ∈ Φm '' Qm` (so that `ζ` is a
  genuine preimage in `Qm`, `Φm ζ = w`) and `ζ ∈ Qp`;
* `hζre` confines `ζ.re` to the strip `|ζ.re| ≤ B`, so that the end asymptotics `hEndm`/`hEndp`
  apply at `ζ`;
* `hproper` turns the threshold `ζ.im > Y'` into the threshold `w.im > N` (contrapositive), which is
  the only way to reach the region where `hEndm`/`hEndp` are informative.

Note the two thresholds `Ym` (for `Φm`) and `Yp` (for `Φp`) are merged by taking
`N = hproper (max Ym Yp)`. -/
theorem hornmap_end_limit {Φm Φp : ℂ → ℂ} {Ξ : ℝ} {α cm cp : ℂ} {B : ℝ} (hB : 0 < B)
    (hinj : Set.InjOn Φm (Work.Pert.Qm Ξ α))
    (hcover : ∀ Y : ℝ, ∃ Yc : ℝ, ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      w ∈ Φm '' (Work.Pert.Qm Ξ α) ∧
        Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w ∈ Work.Pert.Qp Ξ α)
    (hζre : ∀ Y : ℝ, ∃ Yc : ℝ, ∀ w : ℂ, Yc ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w).re| ≤ B)
    (hproper : ∀ R : ℝ, ∃ N : ℝ, ∀ ζ ∈ Work.Pert.Qm Ξ α, ζ.im ≤ R → (Φm ζ).im ≤ N)
    (hEndm : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, Y' < z.im →
      |z.re| ≤ B → ‖Φm z - z - cm‖ < ε)
    (hEndp : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Work.Pert.Qp Ξ α, Y' < z.im →
      |z.re| ≤ B → ‖Φp z - z - cp‖ < ε) :
    ∀ ε > 0, ∃ Y : ℝ, ∀ w : ℂ, Y ≤ w.im → 0 ≤ w.re → w.re ≤ 1 →
      ‖Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) - w - (cp - cm)‖ < ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  -- the two end expansions, at accuracy `ε/2`, on the two gates
  obtain ⟨Ym, hYm⟩ := hEndm (ε / 2) hhalf
  obtain ⟨Yp, hYp⟩ := hEndp (ε / 2) hhalf
  -- `hproper` merges the two lower thresholds into a single condition on `w.im`
  obtain ⟨N, hN⟩ := hproper (max Ym Yp)
  -- the window data for the preimage
  obtain ⟨Yc, hYc⟩ := hcover 0
  obtain ⟨Yc', hYc'⟩ := hζre 0
  refine ⟨max (max Yc Yc') (N + 1), ?_⟩
  intro w hw hw0 hw1
  have hwc : Yc ≤ w.im :=
    le_trans (le_trans (le_max_left Yc Yc') (le_max_left (max Yc Yc') (N + 1))) hw
  have hwc' : Yc' ≤ w.im :=
    le_trans (le_trans (le_max_right Yc Yc') (le_max_left (max Yc Yc') (N + 1))) hw
  have hN1 : N + 1 ≤ w.im := le_trans (le_max_right (max Yc Yc') (N + 1)) hw
  have hNlt : N < w.im := lt_of_lt_of_le (lt_add_one N) hN1
  obtain ⟨hmem, hQp⟩ := hYc w hwc hw0 hw1
  have hre : |(Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w).re| ≤ B := hYc' w hwc' hw0 hw1
  -- the preimage of `w`, a genuine point of `Qm` mapping to `w`, which also lies in `Qp`
  have hQm : Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w ∈ Work.Pert.Qm Ξ α :=
    Work.Pert.invOn_mem hmem
  have hΦζ : Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) = w := Work.Pert.invOn_spec hmem
  -- its imaginary part is beyond both thresholds, by `hproper` and the window on `w.im`
  have hζim : max Ym Yp < (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w).im := by
    by_contra h
    have hle : (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w).im ≤ max Ym Yp := not_lt.mp h
    have hbad : (Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)).im ≤ N := hN _ hQm hle
    rw [hΦζ] at hbad
    exact absurd hbad (not_le.mpr hNlt)
  have hEm : ‖Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
      - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cm‖ < ε / 2 :=
    hYm _ hQm (lt_of_le_of_lt (le_max_left Ym Yp) hζim) hre
  have hEp : ‖Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
      - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cp‖ < ε / 2 :=
    hYp _ hQp (lt_of_le_of_lt (le_max_right Ym Yp) hζim) hre
  calc ‖Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) - w - (cp - cm)‖
      = ‖Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
          - Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w) - (cp - cm)‖ := by rw [hΦζ]
    _ = ‖(Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
            - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cp)
          - (Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
            - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cm)‖ := by
          congr 1
          ring
    _ ≤ ‖Φp (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
            - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cp‖
          + ‖Φm (Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w)
            - Work.Pert.invOn Φm (Work.Pert.Qm Ξ α) w - cm‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hEp hEm
    _ = ε := by ring

end Work.Pert.RBlock2
