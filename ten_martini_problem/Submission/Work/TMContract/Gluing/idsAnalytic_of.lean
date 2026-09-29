import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMContract.Components
import Submission.Work.TMContract.Gluing.analyticOnNhd_integral

/-!
# `N` is real-analytic on a spectral interval (`0 < λ ≤ 1`)

This is the glue statement `idsAnalytic_of` from `Submission/Work/TMPlan/ROUTE_LEAD.md` §3.2:

* C9 (`P_mAnalytic`) provides, on a spectral interval `(a,b)`, a real-analytic conjugacy
  `C` of the transfer cocycle to rotations, with a real-analytic angle `φ`, degree `0`:
  `C_E(x+α) S_E(x) = R_{φ(E,x)} C_E(x)`.
* C5 part 4 (`P_RotBasics`) with `k = 0` then gives
  `rotLift α λ E = 2 ∫₀¹ φ(E,x) dx + 2 j(E)` with `j(E) ∈ ℤ`.
* `E ↦ ∫₀¹ φ(E,x) dx` is real-analytic on `(a,b)` (`analyticOnNhd_integral`: integrate a
  jointly analytic function of two variables over a compact parameter interval).
* `rotLift = 1 - ids` is continuous in `E` (C5 part 3), so `E ↦ rotLift α λ E - 2∫φ` is a
  continuous, `2ℤ`-valued function; being continuous and integer-valued it is *locally*
  constant (`eventually_eq_of_two_mul_int_continuousAt`).  Hence near each `E₀ ∈ (a,b)`
  `rotLift` agrees with the analytic function `E ↦ 2∫₀¹ φ(E,x) dx + 2 j(E₀)`, and so does
  `ids = 1 - rotLift`.
-/

open MeasureTheory Filter Topology Set

open scoped Topology

namespace Work.TMContract.Gluing

/-- A slice of a jointly analytic function of two variables is continuous. -/
theorem continuous_slice_of_jointAnalytic {a b : ℝ} {φ : ℝ → ℝ → ℝ}
    (hφ : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ))
    {E : ℝ} (hE : E ∈ Ioo a b) : Continuous (fun x : ℝ => φ E x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (AnalyticAt.curry_right (hφ (E, x) ⟨hE, mem_univ x⟩)).continuousAt

/-- A continuous real function which takes values in `2ℤ` near `x₀` is constant near `x₀`:
it cannot jump in less than the distance `2` between two distinct elements of `2ℤ`. -/
theorem eventually_eq_of_two_mul_int_continuousAt {g : ℝ → ℝ} {x₀ : ℝ} {j₀ : ℤ}
    (hg : ContinuousAt g x₀) (h₀ : g x₀ = 2 * (j₀ : ℝ))
    (hj : ∀ᶠ E in 𝓝 x₀, ∃ j : ℤ, g E = 2 * (j : ℝ)) :
    ∀ᶠ E in 𝓝 x₀, g E = g x₀ := by
  have hball : Metric.ball (g x₀) (2 : ℝ) ∈ 𝓝 (g x₀) :=
    Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball])
  have h2 : ∀ᶠ E in 𝓝 x₀, dist (g E) (g x₀) < 2 := by
    filter_upwards [hg.tendsto.eventually hball] with E hE
    simpa [Metric.mem_ball] using hE
  filter_upwards [hj, h2] with E hE hd
  obtain ⟨j, hjE⟩ := hE
  rw [hjE, h₀] at hd
  simp only [Real.dist_eq] at hd
  have hlt : |(j : ℝ) - (j₀ : ℝ)| < 1 := by
    rw [abs_lt] at hd ⊢
    constructor <;> linarith
  have hsub : ((j - j₀ : ℤ) : ℝ) = (j : ℝ) - (j₀ : ℝ) := by push_cast; ring
  have h3 : ((j - j₀ : ℤ) : ℝ) < (1 : ℤ) := by
    rw [hsub]; norm_num; linarith [(abs_lt.mp hlt).2]
  have h4 : ((-1 : ℤ) : ℝ) < ((j - j₀ : ℤ) : ℝ) := by
    rw [hsub]; norm_num; linarith [(abs_lt.mp hlt).1]
  have h5 : j - j₀ < (1 : ℤ) := by exact_mod_cast h3
  have h6 : (-1 : ℤ) < j - j₀ := by exact_mod_cast h4
  have hjeq : j = j₀ := by omega
  rw [hjE, h₀, hjeq]

theorem idsAnalytic_of (h5 : Work.TMContract.P_RotBasics) (h9 : Work.TMContract.P_mAnalytic) :
    ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b →
      Set.Ioo a b ⊆ Work.TMContract.amoSpec α lam →
      AnalyticOnNhd ℝ (Work.TMContract.ids α lam) (Set.Ioo a b) := by
  intro α lam a b hα h0 h1 hab hsub
  obtain ⟨C, φ, _hC, hφ, hCper, hφper, hCdet, hCdeg, hconj⟩ :=
    h9 α lam a b hα h0 h1 hab hsub
  have hFanal : AnalyticOnNhd ℝ (fun E : ℝ => ∫ x in (0:ℝ)..1, φ E x) (Ioo a b) :=
    analyticOnNhd_integral hφ
  intro E₀ hE₀
  -- C5 part 4 with `k = 0`, at the single point `E₀`
  obtain ⟨j₀, hj₀⟩ := h5.2.2.2 α lam E₀ (C E₀) (φ E₀) 0 (hCdeg E₀ hE₀) (hCper E₀)
     (hCdet E₀ hE₀) (continuous_slice_of_jointAnalytic hφ hE₀) (hφper E₀) (hconj E₀ hE₀)
  have hj₀' : rotLift α lam E₀ = 2 * (∫ x in (0:ℝ)..1, φ E₀ x) + 2 * (j₀:ℝ) := by
    rw [hj₀]; push_cast; ring
  -- continuity of the relevant functions at `E₀`
  have hids_cont : ContinuousAt (fun E : ℝ => ids α lam E) E₀ := by
    have hc : Continuous (fun p : ℝ × ℝ => ids p.1 lam p.2) := h5.2.2.1 lam
    fun_prop
  have hrot_cont : ContinuousAt (fun E : ℝ => rotLift α lam E) E₀ := by
    have heq : (fun E : ℝ => rotLift α lam E) = fun E => 1 - ids α lam E := by
      funext E; simp only [ids]; ring
    rw [heq]
    exact continuousAt_const.sub hids_cont
  have hg_cont : ContinuousAt (fun E : ℝ =>
      rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x)) E₀ :=
    hrot_cont.sub ((hFanal E₀ hE₀).continuousAt.const_mul 2)
  -- the `2ℤ`-valuedness of `rotLift - 2∫φ` near `E₀`
  have hjf : ∀ᶠ E in 𝓝 E₀, ∃ j : ℤ,
      rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x) = 2 * (j:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hE₀] with E hE
    obtain ⟨j, hj⟩ := h5.2.2.2 α lam E (C E) (φ E) 0 (hCdeg E hE) (hCper E)
       (hCdet E hE) (continuous_slice_of_jointAnalytic hφ hE) (hφper E) (hconj E hE)
    refine ⟨j, ?_⟩
    rw [hj]; push_cast; ring
  have hg₀ : rotLift α lam E₀ - 2 * (∫ x in (0:ℝ)..1, φ E₀ x) = 2 * (j₀:ℝ) := by
    rw [hj₀']; ring
  have hconst : ∀ᶠ E in 𝓝 E₀,
      rotLift α lam E - 2 * (∫ x in (0:ℝ)..1, φ E x)
        = rotLift α lam E₀ - 2 * (∫ x in (0:ℝ)..1, φ E₀ x) :=
    eventually_eq_of_two_mul_int_continuousAt hg_cont hg₀ hjf
  -- hence `ids` agrees near `E₀` with an explicit real-analytic function
  have han : AnalyticAt ℝ (fun E : ℝ =>
      1 - (2 * (∫ x in (0:ℝ)..1, φ E x) + 2 * (j₀:ℝ))) E₀ := by
    have h1 : AnalyticAt ℝ (fun E : ℝ => (∫ x in (0:ℝ)..1, φ E x)) E₀ := hFanal E₀ hE₀
    fun_prop
  refine han.congr ?_
  filter_upwards [hconst] with E hE
  have hE' : rotLift α lam E = 2 * (∫ x in (0:ℝ)..1, φ E x) + 2 * (j₀:ℝ) := by linarith
  simp only [ids]
  rw [hE']

end Work.TMContract.Gluing
