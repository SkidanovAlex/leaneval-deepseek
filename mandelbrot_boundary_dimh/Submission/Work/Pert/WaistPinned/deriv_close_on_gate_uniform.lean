import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Pert.Setup
import Submission.Work.Pert.deriv_Phi_close_on_gate

/-!
# `Work.Pert.WaistPinned.deriv_close_on_gate_uniform`

`Φ' ≈ 1` on the gate, **uniformly in the near-translation and the Fatou coordinate**.

`Work.Pert.deriv_Phi_close_on_gate` proves, for each fixed datum `(F, Φ, α, ξ₁)` satisfying the
gate hypotheses, the existence of a radius `R₁ > 0` with `‖Φ' z - 1‖ ≤ 1/2` on every ball
`ball z R ⊆ Qm ξ₁ α` of radius `R ≥ R₁`.  Its proof in fact uses only the *universal* constants
`Rde, C₂` of Shishikura's derivative estimate `MandelDim.FatouDerivEstimate` (Lemma A.2.4(i)):

* `MandelDim.FatouDerivEstimate` is `∃ R₁ C₁ C₂, 0 < R₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧ …` — the constants do
  not depend on `F`, `Φ`, `α`, `ξ₁`;
* the only hypotheses fed to it on a ball `ball z R` are `DifferentiableOn ℂ Φ (ball z R)`,
  `Set.InjOn Φ (ball z R)` (both from `IsFatouCoordOn`), `DifferentiableOn ℂ v (ball z R)` and
  `‖v w - 1‖ < 1/4` (both from `NearTranslationL1`, with `v := F - id`), and the Abel relation
  `Φ (w + v w) = Φ w + 1` (again from `IsFatouCoordOn`);
* the two remaining numerical steps are `C₂ / R ≤ 1/64` for `R ≥ 64 C₂` and
  `‖1/v z - 1‖ ≤ 1/31` for `‖v z - 1‖ ≤ 1/32`, neither of which involves the datum.

Hence a single radius `R₂ := max Rde (64 C₂)`, depending only on `hDE`, witnesses the conclusion
for all data simultaneously.  This is the uniform form `(B)` of `NOTES_PERT_assembly.md` §I.1.
-/

namespace Work.Pert.WaistPinned

open MandelDim Complex Set Metric

theorem deriv_close_on_gate_uniform (hDE : MandelDim.FatouDerivEstimate) :
    ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ (F Φ : ℂ → ℂ) (α : ℂ) (ξ₁ : ℝ),
      MandelDim.NearTranslationL1 F (Work.Pert.Qm ξ₁ α) →
      MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm ξ₁ α) →
      ∀ z : ℂ, ∀ R : ℝ, R₂ ≤ R → Metric.ball z R ⊆ Work.Pert.Qm ξ₁ α →
        ‖deriv Φ z - 1‖ ≤ 1 / 2 := by
  obtain ⟨Rde, C₁, C₂, hRde, hC₁', hC₂, hDE'⟩ := hDE
  refine ⟨max Rde (64 * C₂), lt_max_iff.mpr (Or.inl hRde), ?_⟩
  intro F Φ α ξ₁ hNT hΦ z R hR hball
  have hRQ : Rde ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le (lt_max_iff.mpr (Or.inl hRde)) hR
  have hzball : z ∈ Metric.ball z R := by rw [Metric.mem_ball]; simpa using hRpos
  have hzQ : z ∈ Work.Pert.Qm ξ₁ α := hball hzball
  -- the vertical displacement map `v = F - id`
  set v : ℂ → ℂ := fun w => F w - w with hv
  have hvdiff : DifferentiableOn ℂ v (Metric.ball z R) := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => F w - w) (Metric.ball z R) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa [v] using h1
  have hvnear : ∀ w ∈ Metric.ball z R, ‖v w - 1‖ < 1 / 4 := by
    intro w hw
    have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hw
    have hbound : ‖v w - 1‖ ≤ 1 / 32 := by
      have heq : v w - 1 = F w - (w + 1) := by simp only [v]; ring
      rw [heq]; exact (hNT.1.2 w hwQ).1
    linarith
  have habel : ∀ w ∈ Metric.ball z R, w + v w ∈ Metric.ball z R → Φ (w + v w) = Φ w + 1 := by
    intro w hw hwv
    have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hw
    have heq : w + v w = F w := by simp only [v]; ring
    have hFQ : F w ∈ Work.Pert.Qm ξ₁ α := by rw [← heq]; exact hball hwv
    have h := hΦ.2.2 w hwQ hFQ
    rwa [heq]
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball z R) := hΦ.1.mono hball
  have hΦinj : Set.InjOn Φ (Metric.ball z R) := hΦ.2.1.mono hball
  obtain ⟨_, hb2⟩ := hDE' Φ v z R hRQ hΦdiff hΦinj hvdiff hvnear habel
  -- `C₂ / R ≤ 1/64`
  have hC2R : C₂ / R ≤ 1 / 64 := by
    rw [div_le_iff₀ hRpos]
    nlinarith [le_trans (le_max_right (Rde : ℝ) (64 * C₂)) hR]
  -- `‖1/v z - 1‖ ≤ 1/31`, since `‖v z - 1‖ ≤ 1/32`
  have hvinv : ‖1 / v z - 1‖ ≤ 1 / 31 := by
    have hvz : ‖v z - 1‖ ≤ 1 / 32 := by
      have heq : v z - 1 = F z - (z + 1) := by simp only [v]; ring
      rw [heq]; exact (hNT.1.2 z hzQ).1
    have h1a : ‖1 - v z‖ ≤ 1 / 32 := by
      rw [norm_sub_rev (1 : ℂ) (v z)]; exact hvz
    have hanorm : (31 : ℝ) / 32 ≤ ‖v z‖ := by
      have h1 : (1 : ℝ) ≤ ‖v z‖ + ‖1 - v z‖ := by
        have he : (1 : ℂ) = v z + (1 - v z) := by ring
        calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
          _ = ‖v z + (1 - v z)‖ := congrArg (fun x : ℂ => ‖x‖) he
          _ ≤ ‖v z‖ + ‖1 - v z‖ := norm_add_le _ _
      linarith
    have hne : v z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hanorm
      norm_num at hanorm
    rw [div_sub_one hne, norm_div]
    calc ‖1 - v z‖ / ‖v z‖ ≤ (1 / 32) / (31 / 32) :=
          div_le_div₀ (by norm_num) h1a (by norm_num) hanorm
      _ = 1 / 31 := by norm_num
  have htri : ‖deriv Φ z - 1‖ ≤ ‖deriv Φ z - 1 / v z‖ + ‖1 / v z - 1‖ := by
    have he : deriv Φ z - 1 = (deriv Φ z - 1 / v z) + (1 / v z - 1) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [hb2, hC2R, hvinv, htri]

end Work.Pert.WaistPinned
