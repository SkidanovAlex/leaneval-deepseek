import Mathlib
import Submission.Work.Pert.RBlock4.gate_walk_Qreg
import Submission.Work.Pert.Gates
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.pert2v2.walk_Qp_waist`

A walk of the lifted germ `F = liftF u σ α` that starts in the **waist** `Qm Ξ α ∩ Qp Ξ α`
stays inside the upper gate `Qp Ξ α` for `m` steps, where `m` is bounded by the horizontal room
`(1/α).re - (1/α).im` of the gate.

The two ingredients are purely geometric:

* `Work.Pert.Qm_inter_Qp` (with `𝓕₁ α`, i.e. `|(1/α).im| < (1/α).re`) computes the waist as
  `{|Re z| < |Im z| - Ξ}`; since `ς.im = y₀ ≥ Ξ > 0` this gives `ς.re < y₀ - Ξ`.
* For the upper gate `Qp Ξ α = Qreg (some Ξ) (some (-Ξ + 1/α))` the `b`-margin of `Qreg` at the
  starting point is
  `|(ς - b).im| - (ς - b).re ≥ (y₀ - (1/α).im) - (ς.re + Ξ - (1/α).re)
    = ((1/α).re - (1/α).im) + (y₀ - Ξ - ς.re) > (17/16) m + 1`,
  by `hm` and `ς.re < y₀ - Ξ`.  Hence the abstract walk lemma `gate_walk_Qreg` applies verbatim.

The hypothesis `himα : (1/α).im ≤ y₀ + Ξ` is not needed for this conclusion (the bound on the
margin uses `|x| ≥ x` directly).
-/

namespace Work.Pert.pert2v2

theorem walk_Qp_waist {u : ℂ → ℂ} {σ α : ℂ} {Ξ y₀ : ℝ} {ς : ℂ} {m : ℕ}
    (hΞ : 0 < Ξ) (hy₀ : Ξ ≤ y₀) (hinjα : |(1 / α).im| < (1 / α).re)
    (himα : (1 / α).im ≤ y₀ + Ξ)
    (hstep : ∀ z ∈ Work.Pert.Qp Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32)
    (hς : ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α) (him : ς.im = y₀)
    (hm : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ (1 / α).re - (1 / α).im) :
    ∀ j : ℕ, j ≤ m → (Work.Pert.liftF u σ α)^[j] ς ∈ Work.Pert.Qp Ξ α := by
  -- The waist is `{|Re z| < |Im z| - Ξ}`; since `ς.im = y₀ ≥ Ξ > 0`, this gives `ς.re < y₀ - Ξ`.
  have hwaist : |ς.re| < |ς.im| - Ξ := by
    have h := Work.Pert.Qm_inter_Qp (ξ := Ξ) (α := α) hinjα
    have hmem : ς ∈ ({z : ℂ | |z.re| < |z.im| - Ξ} : Set ℂ) := by
      rw [← h]; exact hς
    exact hmem
  have himpos : 0 < ς.im := by rw [him]; linarith
  have hre : ς.re < y₀ - Ξ := by
    have h2 := (abs_lt.mp hwaist).2
    rw [abs_of_pos himpos, him] at h2
    linarith
  -- The room of `ς` to the upper (`b`-)boundary of `Qp Ξ α` is `≥ (17/16) m + 1`.
  have hroom : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤
      |(ς - (-(Ξ : ℂ) + 1 / α)).im| - (ς - (-(Ξ : ℂ) + 1 / α)).re := by
    have him' : (ς - (-(Ξ : ℂ) + 1 / α)).im = y₀ - (1 / α).im := by
      simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]
      rw [him]; ring
    have hre' : (ς - (-(Ξ : ℂ) + 1 / α)).re = ς.re + Ξ - (1 / α).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      ring
    have hle : y₀ - (1 / α).im ≤ |(ς - (-(Ξ : ℂ) + 1 / α)).im| := by
      rw [him']; exact le_abs_self _
    rw [hre']
    linarith
  have hz : ς ∈ MandelDim.Qreg (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)) := hς.2
  have hwalk := Work.Pert.RBlock4.gate_walk_Qreg (F := Work.Pert.liftF u σ α)
    (a := (Ξ : ℂ)) (b := (-(Ξ : ℂ) + 1 / α)) (z := ς) (m := m)
    (fun w hw => hstep w (by simpa only [Work.Pert.Qp] using hw)) hz hroom
  intro j hj
  simpa only [Work.Pert.Qp] using hwalk j hj

end Work.Pert.pert2v2
