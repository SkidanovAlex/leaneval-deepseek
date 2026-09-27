import Mathlib
import Submission.Work.EKLC6Core.cut_defs

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped ENNReal

/-- **Borel–Cantelli for a geometrically thinning family of thickenings.**

If the `η`-thickenings `VThick η A` of `A` satisfy the *linear* thinness estimate
`μ (VThick η A) ≤ c η`, and `T : x ↦ aDiag t • x` preserves `μ`, then for `μ₀ ∈ (0,1)`
almost every `x` has `T^n x ∉ VThick (c μ₀^n) A` for all large `n`.

Indeed, by `MeasurePreserving`, the `n`-th preimage `T^{-n} (VThick (c μ₀^n) A)` has measure at
most `c · c μ₀^n = c² μ₀^n`, a summable sequence; the first Borel–Cantelli lemma
(`MeasureTheory.ae_eventually_notMem`) concludes. -/
theorem ae_eventually_not_mem_VThick {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (A : Set Work.EKLContract.X3) {c : ℝ} (hc : 0 < c) {μ₀ : ℝ} (hμ₀0 : 0 < μ₀) (hμ₀1 : μ₀ < 1)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (Work.EKLC6Core.VThick η A) ≤ ENNReal.ofReal (c * η)) :
    ∀ᵐ x ∂μ, ∀ᶠ n : ℕ in Filter.atTop,
      ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) x
        ∉ Work.EKLC6Core.VThick (c * μ₀ ^ n) A := by
  -- The `n`-th "bad" event: the orbit hits the thinning thickening at time `n`.
  -- Each event has measure at most `c * (c * μ₀^n) = c² μ₀^n`.
  have hbound : ∀ n : ℕ,
      μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
        Work.EKLC6Core.VThick (c * μ₀ ^ n) A) ≤ ENNReal.ofReal (c * c * μ₀ ^ n) := by
    intro n
    have hη : 0 < c * μ₀ ^ n := mul_pos hc (pow_pos hμ₀0 n)
    have hthin' : μ (Work.EKLC6Core.VThick (c * μ₀ ^ n) A)
        ≤ ENNReal.ofReal (c * (c * μ₀ ^ n)) := hthin _ hη
    -- measure preservation identifies `μ (T^{-n} B)` with `μ B`
    have hle := MeasureTheory.Measure.le_map_apply (μ := μ)
      ((hmp.iterate n).measurable).aemeasurable (Work.EKLC6Core.VThick (c * μ₀ ^ n) A)
    rw [(hmp.iterate n).map_eq] at hle
    have hstep : ENNReal.ofReal (c * (c * μ₀ ^ n)) = ENNReal.ofReal (c * c * μ₀ ^ n) := by
      congr 1; ring
    exact hle.trans (hthin'.trans (le_of_eq hstep))
  -- the geometric series is summable
  have hsummable : Summable (fun n : ℕ => c * c * μ₀ ^ n) :=
    (summable_geometric_of_lt_one hμ₀0.le hμ₀1).mul_left (c * c)
  -- hence the total mass of the events is finite
  have hbdd : (∑' n : ℕ,
      μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
        Work.EKLC6Core.VThick (c * μ₀ ^ n) A))
      ≤ ENNReal.ofReal (∑' n : ℕ, c * c * μ₀ ^ n) := by
    calc (∑' n : ℕ,
          μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
            Work.EKLC6Core.VThick (c * μ₀ ^ n) A))
        ≤ ∑' n : ℕ, ENNReal.ofReal (c * c * μ₀ ^ n) := ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' n : ℕ, c * c * μ₀ ^ n) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable).symm
  have hne : (∑' n : ℕ,
      μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
        Work.EKLC6Core.VThick (c * μ₀ ^ n) A)) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hbdd ENNReal.ofReal_lt_top)
  -- first Borel–Cantelli
  filter_upwards [MeasureTheory.ae_eventually_notMem hne] with x hx
  exact hx.mono fun n hn => by simpa using hn

end Work.EKLC6Core
