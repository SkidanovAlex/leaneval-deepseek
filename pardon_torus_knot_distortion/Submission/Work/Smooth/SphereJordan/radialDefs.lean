import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.BoundedSide

/-!
# Vocabulary for the two radial crosscuts of the plane annulus

This module fixes the definitions used by `Work.Smooth.SphereJordan.radialTwoCutsSpans`:

* `tp = 2π` and `per x`, the representative of `x` in `Ico 0 (2π)`, so that `per (θ' - θ) ∈ [0, 2π)`
  and `θ + per (θ' - θ) ≡ θ'` modulo `2π`;
* `cut w t u` — the point `(t + u(1-t)) • w` of the radial segment from `t • w` to `w`;
* `cArc a b u` — the point `exp (i (a + u * per (b - a)))` of the unit circle, running from
  `e^{ia}` to `e^{ib}` in the direction of increasing argument;
* `fourArc γ θ θ' w t w' t' arcs` — the closed curve obtained by concatenating the `γ`-arc from
  `γ θ` to `γ θ'`, the outward radial segment along `w'`, the circle arc `arcs` from `w'` to `w`,
  and the inward radial segment along `w`.
-/

open Set

noncomputable section

namespace Work.Smooth.SphereJordan

/-- `2π`. -/
def tp : ℝ := 2 * Real.pi

theorem tp_pos : 0 < tp := by unfold tp; positivity

theorem tp_ne_zero : tp ≠ 0 := ne_of_gt tp_pos

/-- The representative of `x` in `Ico 0 (2π)`. -/
def per (x : ℝ) : ℝ := x - ⌊x / tp⌋ * tp

theorem per_sub_self (x : ℝ) : per x = x - ⌊x / tp⌋ * tp := rfl

theorem per_mem (x : ℝ) : per x ∈ Set.Ico 0 tp := by
  have h := tp_pos
  refine ⟨?_, ?_⟩
  · have := (le_div_iff₀ h).mp (Int.floor_le (x / tp))
    rw [per_sub_self]; linarith
  · have := (div_lt_iff₀ h).mp (Int.lt_floor_add_one (x / tp))
    rw [per_sub_self]; linarith

theorem per_self {x : ℝ} (hx : x ∈ Set.Ico 0 tp) : per x = x := by
  have h : ⌊x / tp⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg hx.1 (le_of_lt tp_pos), by rw [div_lt_one tp_pos]; exact hx.2⟩
  rw [per_sub_self, h]; ring

theorem per_periodic (x : ℝ) : per (x + tp) = per x := by
  have h : ⌊(x + tp) / tp⌋ = ⌊x / tp⌋ + 1 := by
    rw [add_div, div_self tp_ne_zero]; exact Int.floor_add_one _
  rw [per_sub_self, per_sub_self, h]; push_cast; ring

theorem per_add_int_mul (x : ℝ) (k : ℤ) : per (x + k * tp) = per x := by
  have hdiv : (x + (k : ℝ) * tp) / tp = x / tp + (k : ℝ) := by
    rw [add_div, mul_div_cancel_right₀ _ tp_ne_zero]
  have hfl : ⌊x / tp + (k : ℝ)⌋ = ⌊x / tp⌋ + k := Int.floor_add_intCast _ k
  rw [per_sub_self, per_sub_self, hdiv, hfl]
  push_cast
  ring

/-- `x` differs from `per x` by an integer multiple of `2π`. -/
theorem sub_per_mem (x : ℝ) : ∃ k : ℤ, x = per x + k * tp :=
  ⟨⌊x / tp⌋, by rw [per_sub_self]; ring⟩

/-- `θ + per (θ' - θ)` and `θ'` differ by an integer multiple of `2π`. -/
theorem theta_add_per_sub (θ θ' : ℝ) :
    ∃ k : ℤ, θ + per (θ' - θ) = θ' + k * tp := by
  refine ⟨-⌊(θ' - θ) / tp⌋, ?_⟩
  rw [per_sub_self]
  push_cast
  ring

/-- `γ` at the parameter reached by the first quarter. -/
theorem gamma_theta_add (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) :
    γ.γ (θ + per (θ' - θ)) = γ.γ θ' := by
  obtain ⟨k, hk⟩ := theta_add_per_sub θ θ'
  rw [hk, tp]
  exact γ.apply_add_int_mul θ' k

/-- The outward radial segment: `cut w t u = (t + u(1-t)) • w`, so `cut w t 0 = t • w` and
`cut w t 1 = w`. -/
def cut (w : ℂ) (t : ℝ) (u : ℝ) : ℂ := (t + u * (1 - t)) • w

@[simp] theorem cut_zero (w : ℂ) (t : ℝ) : cut w t 0 = t • w := by simp [cut]

@[simp] theorem cut_one (w : ℂ) (t : ℝ) : cut w t 1 = w := by
  simp [cut]

theorem cut_continuous (w : ℂ) (t : ℝ) : Continuous (cut w t) := by
  unfold cut; fun_prop

/-- The unit-circle arc from `e^{ia}` to `e^{ib}` in the direction of increasing argument. -/
def cArc (a b : ℝ) (u : ℝ) : ℂ := Complex.exp (((a + u * per (b - a) : ℝ)) * Complex.I)

theorem cArc_zero (a b : ℝ) : cArc a b 0 = Complex.exp ((a : ℂ) * Complex.I) := by
  simp [cArc]

theorem cArc_one (a b : ℝ) : cArc a b 1 = Complex.exp ((b : ℂ) * Complex.I) := by
  have h : a + per (b - a) = b + (-⌊(b - a) / tp⌋) * tp := by
    rw [per_sub_self]; ring
  simp only [cArc, one_mul]
  rw [h]
  have hcast : ((b + (-⌊(b - a) / tp⌋) * tp : ℝ) : ℂ) * Complex.I
      = (b : ℂ) * Complex.I + (-⌊(b - a) / tp⌋ : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast [tp]; ring
  rw [hcast, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cArc_continuous (a b : ℝ) : Continuous (cArc a b) := by
  unfold cArc; fun_prop

theorem cArc_norm (a b u : ℝ) : ‖cArc a b u‖ = 1 := by
  rw [cArc, show ((a + u * per (b - a) : ℝ) : ℂ) * Complex.I
    = ((a + u * per (b - a) : ℝ) : ℂ) * Complex.I from rfl]
  exact Complex.norm_exp_ofReal_mul_I _


/-- **The four-arc curve.**  Starting at `γ θ`, run along `γ` to `γ θ'` (the parameter running
from `θ` to `θ + per (θ' - θ)`), then outward along `w'` to the unit circle, then along the given
circle arc `arcs` (which should run from `w'` to `w`), then inward along `w` back to `γ θ`. -/
def fourArc (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ) (w' : ℂ) (t' : ℝ)
    (arcs : ℝ → ℂ) (σ : ℝ) : ℂ :=
  let s := per σ
  if s ≤ Real.pi / 2 then γ.γ (θ + (s / (Real.pi / 2)) * per (θ' - θ))
  else if s ≤ Real.pi then cut w' t' ((s - Real.pi / 2) / (Real.pi / 2))
  else if s ≤ 3 * Real.pi / 2 then arcs ((s - Real.pi) / (Real.pi / 2))
  else cut w t (1 - (s - 3 * Real.pi / 2) / (Real.pi / 2))

theorem fourArc_periodic (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ)
    (w' : ℂ) (t' : ℝ) (arcs : ℝ → ℂ) :
    Function.Periodic (fourArc γ θ θ' w t w' t' arcs) tp := by
  intro σ
  simp only [fourArc]
  rw [per_periodic]

/-- The first quarter of `fourArc` lies in `γ.trace`. -/
theorem fourArc_mem_trace_of_le (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ)
    (w' : ℂ) (t' : ℝ) (arcs : ℝ → ℂ) {σ : ℝ} (h : per σ ≤ Real.pi / 2) :
    fourArc γ θ θ' w t w' t' arcs σ ∈ γ.trace := by
  have := γ.mem_trace (θ + (per σ / (Real.pi / 2)) * per (θ' - θ))
  simpa only [fourArc, if_pos h] using this

/-- The second quarter of `fourArc` lies in the ray through `w'`. -/
theorem fourArc_eq_cut_of_le (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ)
    (w' : ℂ) (t' : ℝ) (arcs : ℝ → ℂ) {σ : ℝ} (h1 : ¬ per σ ≤ Real.pi / 2)
    (h2 : per σ ≤ Real.pi) :
    fourArc γ θ θ' w t w' t' arcs σ
      = cut w' t' ((per σ - Real.pi / 2) / (Real.pi / 2)) := by
  simp only [fourArc, if_neg h1, if_pos h2]

/-- The third quarter of `fourArc` is the circle arc. -/
theorem fourArc_eq_arc_of_le (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ)
    (w' : ℂ) (t' : ℝ) (arcs : ℝ → ℂ) {σ : ℝ} (h1 : ¬ per σ ≤ Real.pi / 2)
    (h2 : ¬ per σ ≤ Real.pi) (h3 : per σ ≤ 3 * Real.pi / 2) :
    fourArc γ θ θ' w t w' t' arcs σ = arcs ((per σ - Real.pi) / (Real.pi / 2)) := by
  simp only [fourArc, if_neg h1, if_neg h2, if_pos h3]

/-- The fourth quarter of `fourArc` lies in the ray through `w`. -/
theorem fourArc_eq_cut_of_le' (γ : Work.Smooth.Jordan.PlaneCurve) (θ θ' : ℝ) (w : ℂ) (t : ℝ)
    (w' : ℂ) (t' : ℝ) (arcs : ℝ → ℂ) {σ : ℝ} (h1 : ¬ per σ ≤ Real.pi / 2)
    (h2 : ¬ per σ ≤ Real.pi) (h3 : ¬ per σ ≤ 3 * Real.pi / 2) :
    fourArc γ θ θ' w t w' t' arcs σ
      = cut w t (1 - (per σ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
  simp only [fourArc, if_neg h1, if_neg h2, if_neg h3]

/-- The forward circle arc from `e^{ia}` to `e^{ib}` (increasing argument). -/
def arcF (a b : ℝ) : ℝ → ℂ := cArc a b

/-- The backward circle arc from `e^{ia}` to `e^{ib}` (decreasing argument). -/
def arcB (a b : ℝ) : ℝ → ℂ := fun u => cArc b a (1 - u)

theorem arcF_zero (a b : ℝ) : arcF a b 0 = Complex.exp ((a : ℂ) * Complex.I) := cArc_zero a b
theorem arcF_one (a b : ℝ) : arcF a b 1 = Complex.exp ((b : ℂ) * Complex.I) := cArc_one a b
theorem arcB_zero (a b : ℝ) : arcB a b 0 = Complex.exp ((a : ℂ) * Complex.I) := by
  show cArc b a (1 - 0) = _
  rw [sub_zero, cArc_one]
theorem arcB_one (a b : ℝ) : arcB a b 1 = Complex.exp ((b : ℂ) * Complex.I) := by
  show cArc b a (1 - 1) = _
  rw [sub_self, cArc_zero]


end Work.Smooth.SphereJordan

end
