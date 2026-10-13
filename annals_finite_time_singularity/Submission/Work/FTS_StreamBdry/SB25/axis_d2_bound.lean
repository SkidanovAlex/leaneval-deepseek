import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25Aux.axisD2_ident
import Submission.Work.FTS_StreamBdry.SB25Aux2.axisTail_bound
import Submission.Work.FTS_StreamBdry.SB25Aux.axisBterm_le
import Submission.Work.FTS_StreamBdry.SB25Aux.axisDterm_le
import Submission.Work.FTS_StreamBdry.SB25Aux.axisJterm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.axis_d2_bound` — leaf B4 of the SB2/SB5 plan

The 1-D axis expansion to second order: if `V := f' - tan·f` satisfies
`|V - v₀| ≤ ε (π/2 - t)` and `|V'| ≤ ε` on `[θ₀, π/2)`, and `f` is bounded on `(0, π/2)`,
then `|f''(θ₀)| ≤ 6ε + |v₀|(π/2 - θ₀)`.

Route (the leaf plan's decomposition).  With `W := f·cos` (so that `W' = cos·V`) one has

  `f'' = V' + tan θ₀·(V - v₀) + (1 + sin²θ₀)(W + v₀(1 - sin θ₀)) / cos³θ₀
          - v₀(1 - sin θ₀)²/cos³θ₀`,

whose four terms are bounded by `ε`, `ε π/2`, `ε π³/12` and `|v₀|(π/2 - θ₀)`.  The second
bound is `tan θ₀·(π/2 - θ₀) ≤ π/2` (Jordan's inequality), the third combines the tail bound
`|W + v₀(1 - sin θ₀)| ≤ ε(sin δ - δ cos δ) ≤ ε δ³/3` with `1 + sin² ≤ 2` and
`δ/sin δ ≤ π/2`, and the fourth is `(1 - sin θ₀)²/cos³θ₀ = cos θ₀/(1 + sin θ₀)² ≤ sin δ ≤ δ`.
The total is `ε(1 + π/2 + π³/12) + |v₀|δ ≤ 6ε + |v₀|δ` since `π ≤ 3.15`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

/-- The numerical constant: `1 + π/2 + π³/12 ≤ 6`. -/
lemma pi_cubic_le : 1 + Real.pi / 2 + Real.pi ^ 3 / 12 ≤ (6 : ℝ) := by
  have h1 : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have h0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have h2 : Real.pi ^ 2 ≤ 3.15 ^ 2 := by nlinarith
  have h3 : Real.pi ^ 3 ≤ 3.15 ^ 3 := by nlinarith
  nlinarith [h3]

theorem axis_d2_bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) :
    Work.FTS_StreamBdry.SB25.AxisD2Bound f v0 B ε θ0 := by
  rw [Work.FTS_StreamBdry.SB25.AxisD2Bound]
  intro hθ0 hf2 hb hV hV'
  have hlt : θ0 < Real.pi / 2 := hθ0.2
  have hδ : 0 < Real.pi / 2 - θ0 := by linarith [hθ0.2]
  have hc : Real.cos θ0 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩)
  by_cases hε : 0 ≤ ε
  swap
  · -- if `ε < 0` the hypothesis `hV` is contradictory
    exfalso
    have h0 := hV θ0 ⟨le_rfl, hlt⟩
    have h1 : ε * (Real.pi / 2 - θ0) < 0 := mul_neg_of_neg_of_pos (by linarith) hδ
    linarith [abs_nonneg (deriv f θ0 - Real.tan θ0 * f θ0 - v0), h0, h1]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb θ0 hθ0)
  have hident := Work.FTS_StreamBdry.SB25Aux.axisD2_ident f hθ0 (hf2 θ0 hθ0).1 (hf2 θ0 hθ0).2
  have htail := Work.FTS_StreamBdry.SB25Aux2.axisTail_bound f v0 B ε θ0 hθ0 hB hε
    (fun θ hθ => (hf2 θ hθ).1) (fun θ hθ => hb θ hθ) hV
  set A := deriv (fun s => deriv f s - Real.tan s * f s) θ0 with hAdef
  set Bt := Real.tan θ0 * (deriv f θ0 - Real.tan θ0 * f θ0 - v0) with hBdef
  set Ct := (f θ0 * Real.cos θ0 + v0 * (1 - Real.sin θ0)) * (1 + Real.sin θ0 ^ 2)
    / Real.cos θ0 ^ 3 with hCdef
  set Dt := v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 with hDdef
  have hA : |A| ≤ ε := by rw [hAdef]; exact hV' θ0 ⟨le_rfl, hlt⟩
  have hw : |deriv f θ0 - Real.tan θ0 * f θ0 - v0| ≤ ε * (Real.pi / 2 - θ0) :=
    hV θ0 ⟨le_rfl, hlt⟩
  have hBnd : |Bt| ≤ ε * (Real.pi / 2) := by
    rw [hBdef]; exact Work.FTS_StreamBdry.SB25Aux.axisBterm_le θ0 _ v0 ε hθ0 hε hw
  have hDnd : |Dt| ≤ |v0| * (Real.pi / 2 - θ0) := by
    rw [hDdef]; exact Work.FTS_StreamBdry.SB25Aux.axisDterm_le θ0 v0 hθ0
  have hJnd : |Ct| ≤ ε * (Real.pi ^ 3 / 12) := by
    rw [hCdef]; exact Work.FTS_StreamBdry.SB25Aux.axisJterm_le θ0 _ ε hθ0 hε htail
  have hdecomp : deriv (deriv f) θ0 = A + Bt + Ct - Dt := by
    rw [hident, hAdef, hBdef, hCdef, hDdef]
    rw [show Real.tan θ0 = Real.sin θ0 / Real.cos θ0 from Real.tan_eq_sin_div_cos θ0]
    field_simp
    ring_nf
    linear_combination (v0 * Real.sin θ0) * Real.sin_sq_add_cos_sq θ0
  rw [hdecomp]
  have htri : |A + Bt + Ct - Dt| ≤ |A| + |Bt| + |Ct| + |Dt| := by
    have h1 : |A + Bt + Ct - Dt| = |(A + Bt + Ct) + (-Dt)| := by ring_nf
    rw [h1]
    calc |(A + Bt + Ct) + (-Dt)| ≤ |A + Bt + Ct| + |-Dt| := abs_add_le _ _
      _ = |A + Bt + Ct| + |Dt| := by rw [abs_neg]
      _ ≤ (|A| + |Bt| + |Ct|) + |Dt| := by linarith [abs_add_three A Bt Ct]
  have hnum : |A| + |Bt| + |Ct| + |Dt| ≤ 6 * ε + |v0| * (Real.pi / 2 - θ0) := by
    have hp := pi_cubic_le
    nlinarith [hA, hBnd, hJnd, hDnd, hε, hp]
  linarith [htri, hnum]

end Work.FTS_StreamBdry.SB25
