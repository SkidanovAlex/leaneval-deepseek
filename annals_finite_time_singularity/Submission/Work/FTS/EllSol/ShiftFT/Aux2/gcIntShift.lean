import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set
open scoped Real Topology

noncomputable section

/-! ## Where `deriv (chi N)` vanishes

`chi N t = tk (t/N)` with `tk = Real.smoothTransition (2 - ·²)`, so `tk` is *identically* `0` on
a whole neighbourhood of every point with `2 ≤ |t|` (the threshold `√2` of `2 - t² ≤ 0` is
strictly below `2`, so the closed condition `2 ≤ |t|` gives an open neighbourhood).  Hence,
up to the endpoints: `deriv (chi N)` vanishes for `2N ≤ |s|`.  This is the (slightly sharper)
closed-endpoint version of `Trunc.deriv_chi_eq_zero_of_gt`, which only covers `2N < |s|`; the
endpoint case matters below because the integration interval is *closed* at `-2N`. -/

/-- `deriv tk` vanishes at every point with `2 ≤ |t|` (in fact `tk` is `0` near such a point). -/
theorem deriv_tk_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    deriv (Work.FTS.EllSol.Trunc.tk) t = 0 := by
  -- `2 - t² < 0`, so `tk ≡ 0` on a neighbourhood of `t`
  have hneg : 2 - t ^ 2 < 0 := by
    have h2 : (2 : ℝ) < t ^ 2 := by
      have h3 := sq_abs t
      nlinarith [abs_nonneg t, ht]
    linarith
  have hopen : IsOpen {s : ℝ | 2 - s ^ 2 < 0} :=
    isOpen_lt (f := fun s : ℝ => 2 - s ^ 2) (g := fun _ : ℝ => 0)
      (continuous_const.sub (continuous_id.pow 2)) continuous_const
  have hev : (Work.FTS.EllSol.Trunc.tk) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hneg] with s hs
    unfold Work.FTS.EllSol.Trunc.tk
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-- `deriv (chi N)` vanishes at every point with `2N ≤ |t|` (`N > 0`). -/
theorem deriv_chi_eq_zero_of_two_mul_le_abs {N t : ℝ} (hN : 0 < N) (ht : 2 * N ≤ |t|) :
    deriv (Work.FTS.EllSol.Trunc.chi N) t = 0 := by
  rw [Work.FTS.EllSol.Trunc.deriv_chi_eq]
  have h2 : (2 : ℝ) ≤ |t / N| := by
    rw [abs_div, abs_of_pos hN, le_div_iff₀ hN]
    linarith
  rw [deriv_tk_eq_zero_of_two_le_abs h2, zero_div]

/-- **The shifted integral does not see the lower limit, once that limit is left of `-2N`.**
Since `deriv (chi N)` is supported in `[-2N, 2N]`, the integrand
`s ↦ e^{-bs}·(chi N)'(s)·u(s,θ)` has support inside `(-2N, 2N]`; hence both the integral over
`[t, 2N]` (for `t ≤ -2N`) and the integral over `[-2N, 2N]` equal the integral of that same
integrand over all of `ℝ`. -/
theorem gcIntShift (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ, t ≤ -(2 * N) →
      (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
        = ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
  intro θ hθ t ht
  set f : ℝ → ℝ := fun s => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
    with hf
  -- the derivative of the cutoff vanishes on both outer regions
  have hz : ∀ x : ℝ, (x ≤ -(2 * N) ∨ 2 * N ≤ x) →
      deriv (Work.FTS.EllSol.Trunc.chi N) x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact deriv_chi_eq_zero_of_two_mul_le_abs hN
        (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact deriv_chi_eq_zero_of_two_mul_le_abs hN
        (by rw [abs_of_pos (by linarith)]; linarith)
  -- hence the integrand is supported in `(-2N, 2N]`
  have hsuppBig : Function.support f ⊆ Set.Ioc (-(2 * N)) (2 * N) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · by_contra h
      simp only [not_lt] at h
      exact hs (by rw [hf]; simp [hz s (Or.inl h)])
    · by_contra h
      simp only [not_le] at h
      exact hs (by rw [hf]; simp [hz s (Or.inr (le_of_lt h))])
  -- and a fortiori in `(t, 2N]` whenever `t ≤ -2N`
  have hsupp1 : Function.support f ⊆ Set.Ioc t (2 * N) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hsuppBig hs
    exact ⟨by linarith, h2⟩
  have h2 : (∫ s in t..(2 * N), f s) = ∫ s, f s :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupp1
  have h1 : (∫ s in (-(2 * N))..(2 * N), f s) = ∫ s, f s :=
    intervalIntegral.integral_eq_integral_of_support_subset hsuppBig
  rw [h2, h1]

end

end Work.FTS.EllSol.ShiftFT.Aux2
