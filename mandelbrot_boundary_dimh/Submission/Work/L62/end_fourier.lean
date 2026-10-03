import Mathlib

/-!
# Exponential decay of a bounded periodic holomorphic function on a half-plane

`Work.L62.end_fourier`: if `φ` is holomorphic on the half-plane `{w | Y ≤ w.im}`, bounded there
by `B`, and periodic with period `1` there, then `φ` tends to a limit `c` at `+i∞` at the
exponential rate `exp (-2π (im w - Y - 1))`.

The proof pushes `φ` to the punctured disc by the `q`-parameter and uses the Mathlib
development of periodic holomorphic functions (`Mathlib.Analysis.Complex.Periodic`), the
Riemann removable singularity theorem and the maximum modulus principle.
-/

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

/-- The "periodic push-down": project a point of `ℂ` into the closed half-plane `{im ≥ Y}` by
replacing its imaginary part by `max Y w.im`. -/
private def push (Y : ℝ) (w : ℂ) : ℂ := w.re + (max Y w.im) * Complex.I

private lemma push_im (Y : ℝ) (w : ℂ) : (push Y w).im = max Y w.im := by
  simp [push]

private lemma push_eq_self (Y : ℝ) {w : ℂ} (h : Y ≤ w.im) : push Y w = w := by
  simp only [push, max_eq_right h, Complex.re_add_im]

private lemma push_add_one (Y : ℝ) (w : ℂ) : push Y (w + 1) = push Y w + 1 := by
  simp only [push, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  apply Complex.ext <;> simp

/-- The push-down of a function periodic on the half-plane `{im ≥ Y}` is globally periodic. -/
private lemma periodic_push {g : ℂ → ℂ} {Y : ℝ} (hper : ∀ w : ℂ, Y ≤ w.im → g (w + 1) = g w) :
    Function.Periodic (fun w : ℂ => g (push Y w)) (1 : ℝ) := by
  intro w
  show g (push Y (w + ((1 : ℝ) : ℂ))) = g (push Y w)
  have h1 : w + ((1 : ℝ) : ℂ) = w + 1 := by norm_num
  rw [h1, push_add_one, hper (push Y w)]
  rw [push_im]
  exact le_max_left Y w.im

private lemma eventually_im_ge (Y : ℝ) :
    {z : ℂ | Y ≤ z.im} ∈ Filter.comap Complex.im Filter.atTop := by
  rw [Filter.mem_comap]
  exact ⟨Set.Ici Y, Filter.Ici_mem_atTop Y, fun x hx => hx⟩

private lemma eventually_im_gt (Y : ℝ) :
    {z : ℂ | Y < z.im} ∈ Filter.comap Complex.im Filter.atTop := by
  rw [Filter.mem_comap]
  exact ⟨Set.Ioi Y, Filter.Ioi_mem_atTop Y, fun x hx => hx⟩

theorem end_fourier {φ : ℂ → ℂ} {Y B : ℝ}
    (hper : ∀ w : ℂ, Y ≤ w.im → φ (w + 1) = φ w)
    (hhol : DifferentiableOn ℂ φ {w : ℂ | Y ≤ w.im})
    (hbd : ∀ w : ℂ, Y ≤ w.im → ‖φ w‖ ≤ B) :
    ∃ c : ℂ, ∃ M : ℝ, (∀ w : ℂ, Y + 1 ≤ w.im →
      ‖φ w - c‖ ≤ M * Real.exp (-2 * Real.pi * (w.im - Y - 1))) := by
  let ψ : ℂ → ℂ := fun w => φ (push Y w)
  have hψeq : ∀ w : ℂ, Y ≤ w.im → ψ w = φ w :=
    fun w hw => by simp only [ψ, push_eq_self Y hw]
  -- differentiability of `ψ` near `+i∞`
  have hψdiff : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ ψ z := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨{z : ℂ | Y < z.im}, eventually_im_gt Y, ?_⟩
    intro z hz
    have hgt : {w : ℂ | Y < w.im} ∈ 𝓝 z :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
    have hnb : {w : ℂ | Y ≤ w.im} ∈ 𝓝 z :=
      Filter.mem_of_superset hgt (by intro w hw; exact le_of_lt (show Y < w.im from hw))
    have heq : ψ =ᶠ[𝓝 z] φ := by
      filter_upwards [hnb] with w hw
      exact hψeq w hw
    exact (hhol.differentiableAt hnb).congr_of_eventuallyEq heq
  -- boundedness of `ψ` near `+i∞`
  have hψbd : Filter.BoundedAtFilter (Filter.comap Complex.im Filter.atTop) ψ := by
    show Asymptotics.IsBigO (Filter.comap Complex.im Filter.atTop) ψ (1 : ℂ → ℝ)
    rw [Asymptotics.isBigO_iff]
    refine ⟨max B 0, ?_⟩
    refine Filter.eventually_iff_exists_mem.mpr ⟨{z : ℂ | Y ≤ z.im}, eventually_im_ge Y, ?_⟩
    intro z hz
    rw [hψeq z hz]
    have h1 : ‖(1 : ℂ → ℝ) z‖ = 1 := by simp
    rw [h1, mul_one]
    exact (hbd z hz).trans (le_max_left _ _)
  -- the Mathlib theorem: decay of a bounded periodic holomorphic function at `+i∞`
  obtain ⟨C, hCpos, hCev⟩ := Asymptotics.isBigO_iff'.mp
    (Function.Periodic.exp_decay_sub_of_bounded_at_inf (h := (1 : ℝ)) (f := ψ) one_pos
      (periodic_push hper) hψdiff hψbd)
  rw [Filter.eventually_comap] at hCev
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hCev
  have hwY0 : Y ≤ (((Y : ℂ) * Complex.I)).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hbd _ hwY0)
  set c : ℂ := Function.Periodic.cuspFunction (1 : ℝ) ψ 0
  -- the two regions: `im w ≥ max T (Y+1)` (exponential decay) and `Y+1 ≤ im w ≤ max T (Y+1)`
  have hfar : ∀ w : ℂ, max T (Y + 1) ≤ w.im →
      ‖ψ w - c‖ ≤ (C * Real.exp (-2 * Real.pi * (Y + 1))) *
        Real.exp (-2 * Real.pi * (w.im - Y - 1)) := by
    intro w hw
    have hTw : T ≤ w.im := le_trans (le_max_left T (Y + 1)) hw
    have h1 : ‖ψ w - c‖ ≤ C * Real.exp (-2 * Real.pi * w.im) := by
      have h0 := hT w.im hTw w rfl
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), div_one] at h0
      exact h0
    have hexp : Real.exp (-2 * Real.pi * w.im)
        = Real.exp (-2 * Real.pi * (w.im - Y - 1)) *
          Real.exp (-2 * Real.pi * (Y + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖ψ w - c‖ ≤ C * Real.exp (-2 * Real.pi * w.im) := h1
      _ = C * (Real.exp (-2 * Real.pi * (w.im - Y - 1)) *
            Real.exp (-2 * Real.pi * (Y + 1))) := by rw [hexp]
      _ = (C * Real.exp (-2 * Real.pi * (Y + 1))) *
            Real.exp (-2 * Real.pi * (w.im - Y - 1)) := by ring
  have hnear : ∀ w : ℂ, Y + 1 ≤ w.im → w.im ≤ max T (Y + 1) →
      ‖ψ w - c‖ ≤ ((B + ‖c‖) * Real.exp (2 * Real.pi * (max T (Y + 1) - Y - 1))) *
        Real.exp (-2 * Real.pi * (w.im - Y - 1)) := by
    intro w hw hwT
    have hb : ‖ψ w - c‖ ≤ B + ‖c‖ := by
      rw [hψeq w (by linarith)]
      exact (norm_sub_le (φ w) c).trans (add_le_add (hbd w (by linarith)) le_rfl)
    have hBnnc : 0 ≤ B + ‖c‖ := by linarith [hBnn, norm_nonneg c]
    have he : 0 ≤ 2 * Real.pi * (max T (Y + 1) - w.im) :=
      mul_nonneg (by positivity) (by linarith)
    have hone : 1 ≤ Real.exp (2 * Real.pi * (max T (Y + 1) - w.im)) := Real.one_le_exp he
    calc ‖ψ w - c‖ ≤ B + ‖c‖ := hb
      _ ≤ (B + ‖c‖) * Real.exp (2 * Real.pi * (max T (Y + 1) - w.im)) :=
          le_mul_of_one_le_right hBnnc hone
      _ = ((B + ‖c‖) * Real.exp (2 * Real.pi * (max T (Y + 1) - Y - 1))) *
            Real.exp (-2 * Real.pi * (w.im - Y - 1)) := by
          have hA : 2 * Real.pi * (max T (Y + 1) - w.im)
              = 2 * Real.pi * (max T (Y + 1) - Y - 1) + (-2 * Real.pi * (w.im - Y - 1)) := by
            ring
          rw [hA, Real.exp_add]
          ring
  refine ⟨c, max (C * Real.exp (-2 * Real.pi * (Y + 1)))
      ((B + ‖c‖) * Real.exp (2 * Real.pi * (max T (Y + 1) - Y - 1))), ?_⟩
  intro w hw
  have hwY : Y ≤ w.im := by linarith
  rw [← hψeq w hwY]
  rcases le_total (max T (Y + 1)) w.im with h | h
  · exact (hfar w h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · exact (hnear w hw h).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

end Work.L62
