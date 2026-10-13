/-
# `Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero`

The doubly-mollified datum `zmoll G δ ε` vanishes on the angular boundary line `θ = 0`,
for **every** radial scale `δ` and every angular scale `0 < ε ≤ 1/2`.

The angular mollification
`thMoll G ε w θ = ∫ s, sKer ε (θ - s) * Qext G w s`
is the convolution of the *even* kernel `sKer ε` with the *doubly odd* extension `Qext G w`
(odd about `0` and odd about `π/2`).  At `θ = 0` the integrand
`s ↦ sKer ε (-s) * Qext G w s` is almost everywhere odd: off the support `(-ε, ε)` of the
kernel it vanishes identically, while on `(-ε, ε) ⊆ (-1/2, 1/2)` the extension is odd about
`0` (where the hypothesis `ε ≤ 1/2` is used).  Hence the integral vanishes, and so does
`zmoll`, whose `θ`-dependence is entirely through `thMoll`.

The only point at which oddness may fail is `s = 0` (`Qext G w 0 = G w 0`, whereas one would
need `-G w 0`), a null set; the integral of an a.e.-odd function is zero
(`integral_eq_zero_of_ae_odd`).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open Work.FTS.EllSol.PkgK5.K5c

/-- The integrand of the angular mollification at `θ = 0`: the even kernel `sKer ε` sampled at
`-s` against the doubly-odd extension `Qext G w`. -/
def thZero (G : ℝ → ℝ → ℝ) (ε w : ℝ) : ℝ → ℝ :=
  fun s => sKer ε (-s) * Qext G w s

/-- **The integral of an almost everywhere odd real function vanishes.** -/
theorem integral_eq_zero_of_ae_odd {g : ℝ → ℝ}
    (h : ∀ᵐ s ∂(volume : Measure ℝ), g (-s) = - g s) : ∫ s, g s = 0 := by
  have h1 : ∫ s, g s = ∫ s, - g (-s) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with s hs
    rw [hs]; ring
  have h2 : ∫ s, - g (-s) = - ∫ s, g (-s) := MeasureTheory.integral_neg _
  have h3 : ∫ s, g (-s) = ∫ s, g s := MeasureTheory.integral_neg_eq_self g volume
  have h4 : ∫ s, g s = - ∫ s, g s := by
    calc ∫ s, g s = ∫ s, - g (-s) := h1
      _ = - ∫ s, g (-s) := h2
      _ = - ∫ s, g s := by rw [h3]
  linarith

/-- Almost every real number is nonzero, `volume` being atomless. -/
theorem ae_ne_zero' : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  rw [show {a : ℝ | ¬ a ≠ 0} = ({0} : Set ℝ) by ext a; simp]
  exact MeasureTheory.NullSingletonClass.measure_singleton 0

/-- `Qext u z` is odd about `0` on `(-1/2, 1/2)` — the range met by the angular mollification
at scales `ε ≤ 1/2` — except at the origin. -/
theorem Qext_neg_eq_neg_of_abs_lt_half {u : ℝ → ℝ → ℝ} {z s : ℝ} (hs : s ≠ 0)
    (h : |s| < 1 / 2) : Qext u z (-s) = - Qext u z s := by
  have hpi : (1 : ℝ) / 2 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rcases lt_or_gt_of_ne hs with hslt | hsgt
  · have ht : 0 < -s := by linarith
    have htle : -s ≤ Real.pi / 2 := by
      have h1 : -s < 1 / 2 := by linarith [(abs_lt.mp h).1]
      linarith
    have h1 : Qext u z (-s) = u z (-s) := Qext_of_mem u z (-s) ⟨ht.le, htle⟩
    have h2 : Qext u z s = -u z (-s) := by
      have h3 := Qext_neg_of_pos u z (-s) ht
      rwa [neg_neg] at h3
    rw [h1, h2, neg_neg]
  · rw [Qext_neg_of_pos u z s hsgt,
      Qext_of_mem u z s ⟨hsgt.le, by linarith [(abs_lt.mp h).2]⟩]

/-- The `θ = 0` integrand of the angular mollification is odd off the origin. -/
theorem thZero_ae_odd (G : ℝ → ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w s : ℝ) (hs : s ≠ 0) : thZero G ε w (-s) = - thZero G ε w s := by
  unfold thZero
  by_cases hsmall : |s| < ε
  · have hhalf : |s| < 1 / 2 := lt_of_lt_of_le hsmall hε2
    rw [neg_neg, sKer_even ε s, Qext_neg_eq_neg_of_abs_lt_half hs hhalf]
    ring
  · rw [not_lt] at hsmall
    have h0 : sKer ε s = 0 := sKer_eq_zero_of_le_abs hε hsmall
    have h00 : sKer ε (-s) = 0 := sKer_eq_zero_of_le_abs hε (by simpa using hsmall)
    rw [neg_neg, h0, h00]
    simp

/-- **The angular mollification vanishes at `θ = 0`.** -/
theorem thMoll_theta_zero (G : ℝ → ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w : ℝ) : thMoll G ε w 0 = 0 := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), thZero G ε w (-s) = - thZero G ε w s := by
    filter_upwards [ae_ne_zero'] with s hs
    exact thZero_ae_odd G hε hε2 w s hs
  have h0 : ∫ s, thZero G ε w s = 0 := integral_eq_zero_of_ae_odd hae
  have h1 : thMoll G ε w 0 = ∫ s, thZero G ε w s := by
    simp only [thMoll, thZero, zero_sub]
  rw [h1, h0]

theorem zmoll_theta_zero (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (z : ℝ) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z 0 = 0 := by
  simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, thMoll_theta_zero G hε hε2]
  simp

end Work.FTS.EllSol.EllPkgAux.MollSmooth
