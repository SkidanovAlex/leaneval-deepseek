import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.dz_tau_cont`

If `τ ↦ g z θ τ` has the primitive `R z θ τ`, i.e. `g z θ k - g z θ 0 = ∫_0^k R z θ s ds`, and
every `z`-section `x ↦ R x θ τ` is differentiable on `(0,∞)` with a derivative bounded by `Nz`
in absolute value, then the `z`-derivatives of the `τ`-slices of `g` differ by at most `Nz * τ`.

This is "differentiation under the integral sign", with the caveat that for the Bochner integral a
non-integrable integrand contributes `0` (junk value): so the argument splits according to whether
the section `s ↦ R z θ s` is interval-integrable, `intervalIntegral.integral_undef` dispensing with
the other case.  The key structural fact is that the *set of `z` whose section is integrable is
closed*: the sections are uniformly Lipschitz in `x` (hence a pointwise limit of integrable
sections is measurable) and dominated by an integrable function.

The `z`-derivative of `∫_0^τ R x θ s ds` is then bounded by rewriting the difference over two
integrable sections as the integral of the difference and applying
`intervalIntegral.norm_integral_le_of_norm_le_const`, and using the fact that `g(·,θ,τ) - g(·,θ,0)`
is differentiable.
-/

namespace Work.FTS_RegExport.RXR1

open scoped Topology
open Filter
open MeasureTheory

set_option autoImplicit false

section Helpers

variable {R : ℝ → ℝ → ℝ → ℝ} {θ Nz τ : ℝ}

/-- **Auxiliary (pointwise Lipschitz bound).**  If every section `x ↦ R x θ s` (`s ∈ [0,1]`) is
differentiable on `(0,∞)` with derivative bounded by `Nz`, then those sections are `Nz`-Lipschitz. -/
private lemma section_lip
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) {x y : ℝ}
    (hx : x ∈ Set.Ioi (0:ℝ)) (hy : y ∈ Set.Ioi (0:ℝ)) :
    |R x θ s - R y θ s| ≤ Nz * |x - y| := by
  have hdiff : ∀ w ∈ Set.Ioi (0:ℝ), DifferentiableAt ℝ (fun u => R u θ s) w :=
    fun w hw => ((hbd s hs w hw).choose_spec.1).differentiableAt
  have hbound : ∀ w ∈ Set.Ioi (0:ℝ), ‖deriv (fun u => R u θ s) w‖ ≤ Nz := by
    intro w hw
    obtain ⟨d, hd, hle⟩ := hbd s hs w hw
    rw [hd.deriv]
    simpa [Real.norm_eq_abs] using hle
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_Ioi (0:ℝ)) hy hx
  simpa [Real.norm_eq_abs] using h

/-- **Auxiliary (the integrability locus is open in its complement).**  If the section at `z' > 0`
is *not* interval-integrable on `[0,τ]`, then neither is the section at any nearby positive point:
otherwise a sequence of integrable sections would converge to the non-integrable one, contradicting
`Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto`. -/
private lemma bad_nhds (hNz : 0 ≤ Nz)
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {z' : ℝ} (hz' : z' ∈ Set.Ioi (0:ℝ))
    (hbad : ¬ IntervalIntegrable (fun s => R z' θ s) volume (0:ℝ) τ) :
    ∃ ε > 0, ∀ x ∈ Set.Ioi (0:ℝ), |x - z'| < ε →
      ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
  by_contra hcon
  push_neg at hcon
  have hsel : ∀ n : ℕ, ∃ x : ℝ, x ∈ Set.Ioi (0:ℝ) ∧ |x - z'| < 1 / ((n : ℝ) + 1) ∧
      IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose u hu using hsel
  have htu : Filter.Tendsto u Filter.atTop (𝓝 z') := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine squeeze_zero (fun n => abs_nonneg _) (fun n => le_of_lt (hu n).2.1) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact hbad (Work.FTS_RegExport.RXR1Aux.intervalIntegrable_of_tendsto
    (R := fun x s => R x θ s) hNz hτ0 hτ1
    (fun s hs x hx y hy => section_lip hbd hs hx hy) hz' htu (fun n => (hu n).1)
    (fun n => (hu n).2.2))

end Helpers

theorem dz_tau_cont {g R : ℝ → ℝ → ℝ → ℝ} {θ Nz z : ℝ}
    (hNz : 0 ≤ Nz)
    (hFTC : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ k ∈ Set.Icc (0:ℝ) 1,
      g z' θ k - g z' θ 0 = ∫ s in (0:ℝ)..k, R z' θ s)
    (hbd : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ),
      ∃ d : ℝ, HasDerivAt (fun z'' => R z'' θ τ) d z' ∧ |d| ≤ Nz)
    (hd0 : ∀ z' ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z'' => g z'' θ 0)
      (deriv (fun z'' => g z'' θ 0) z') z')
    (hdτ : ∀ τ ∈ Set.Ioc (0:ℝ) 1, ∀ z' ∈ Set.Ioi (0:ℝ), HasDerivAt (fun z'' => g z'' θ τ)
      (deriv (fun z'' => g z'' θ τ) z') z') :
    ∀ z' ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      |deriv (fun z'' => g z'' θ τ) z' - deriv (fun z'' => g z'' θ 0) z'| ≤ Nz * τ := by
  intro z' hz' τ hτ
  obtain ⟨hτ0, hτ1⟩ := hτ
  rcases eq_or_lt_of_le hτ0 with hτeq | hτpos
  · subst hτeq
    simp
  have hC0 : 0 ≤ Nz * τ := mul_nonneg hNz hτ0
  -- the difference of the two slices is the integral of `R`
  set I : ℝ → ℝ := fun x => ∫ s in (0:ℝ)..τ, R x θ s with hIdef
  have hiff : I =ᶠ[𝓝 z'] ((fun x => g x θ τ) - (fun x => g x θ 0)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with x hx
    have h := hFTC x hx τ ⟨hτ0, hτ1⟩
    rw [hIdef]
    simp only [Pi.sub_apply]
    exact h.symm
  have hd_sub : HasDerivAt ((fun x => g x θ τ) - (fun x => g x θ 0))
      (deriv (fun x => g x θ τ) z' - deriv (fun x => g x θ 0) z') z' := by
    have h1 : HasDerivAt (fun x => g x θ τ) (deriv (fun x => g x θ τ) z') z' :=
      hdτ τ ⟨hτpos, hτ1⟩ z' hz'
    have h0 : HasDerivAt (fun x => g x θ 0) (deriv (fun x => g x θ 0) z') z' := hd0 z' hz'
    exact h1.sub h0
  have hd_I : HasDerivAt I (deriv (fun x => g x θ τ) z' - deriv (fun x => g x θ 0) z') z' :=
    hd_sub.congr_of_eventuallyEq hiff
  have hset : Set.uIoc (0:ℝ) τ ⊆ Set.Icc (0:ℝ) 1 := by
    intro s hs
    have h1 : s ∈ Set.uIcc 0 τ := Set.uIoc_subset_uIcc hs
    rw [Set.uIcc_of_le hτ0] at h1
    exact ⟨h1.1, le_trans h1.2 hτ1⟩
  -- the integral of a non-integrable section is `0`
  have hzero : ∀ x, ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ → I x = 0 := by
    intro x hx
    rw [hIdef]
    simp only
    exact intervalIntegral.integral_undef hx
  -- Lipschitz bound between two integrable sections
  have hlip : ∀ x y : ℝ, x ∈ Set.Ioi (0:ℝ) → y ∈ Set.Ioi (0:ℝ) →
      IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ →
      IntervalIntegrable (fun s => R y θ s) volume (0:ℝ) τ →
      ‖I x - I y‖ ≤ Nz * τ * ‖x - y‖ := by
    intro x y hx hy hgx hgy
    have hsub := intervalIntegral.integral_sub hgx hgy
    have hIxy : I x - I y = ∫ s in (0:ℝ)..τ, (R x θ s - R y θ s) := by
      rw [hIdef]
      simp only
      exact hsub.symm
    rw [hIxy]
    have hb : ∀ s ∈ Set.uIoc (0:ℝ) τ, ‖R x θ s - R y θ s‖ ≤ Nz * |x - y| := by
      intro s hs
      have hs1 : s ∈ Set.Icc (0:ℝ) 1 := hset hs
      have h := section_lip hbd hs1 hx hy
      simpa [Real.norm_eq_abs] using h
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := τ)
      (C := Nz * |x - y|) (f := fun s => R x θ s - R y θ s) hb
    calc ‖∫ s in (0:ℝ)..τ, (R x θ s - R y θ s)‖ ≤ Nz * |x - y| * |τ - 0| := hmain
      _ = Nz * τ * ‖x - y‖ := by rw [sub_zero, abs_of_pos hτpos, Real.norm_eq_abs]; ring
  -- the eventual Lipschitz bound at `z'`
  have hEv : ∀ᶠ x in 𝓝 z', ‖I x - I z'‖ ≤ (Nz * τ) * ‖x - z'‖ := by
    by_cases hgz : IntervalIntegrable (fun s => R z' θ s) volume (0:ℝ) τ
    · by_cases hIz : I z' = 0
      · -- `z'` is integrable, but its integral vanishes
        filter_upwards [isOpen_Ioi.mem_nhds hz'] with x hx
        by_cases hgx : IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ
        · exact hlip x z' hx hz' hgx hgz
        · rw [hzero x hgx, hIz]
          simp only [sub_self, norm_zero]
          exact mul_nonneg hC0 (norm_nonneg _)
      · -- `z'` is integrable with nonzero integral: nearby points are integrable too
        have hev : ∀ᶠ x in 𝓝 z', I x ≠ 0 := hd_I.continuousAt.eventually_ne hIz
        filter_upwards [hev, isOpen_Ioi.mem_nhds hz'] with x hxne hx
        have hgx : IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
          by_contra hxb
          exact hxne (hzero x hxb)
        exact hlip x z' hx hz' hgx hgz
    · -- `z'` is not integrable: a whole neighbourhood of `z'` consists of non-integrable points
      have hIz : I z' = 0 := hzero z' hgz
      obtain ⟨ε, hεpos, hεb⟩ := bad_nhds hNz hbd hτ0 hτ1 hz' hgz
      have hev : ∀ᶠ x in 𝓝 z', ¬ IntervalIntegrable (fun s => R x θ s) volume (0:ℝ) τ := by
        rw [Metric.eventually_nhds_iff]
        refine ⟨min ε z', lt_min hεpos hz', ?_⟩
        intro x hx
        rw [Real.dist_eq] at hx
        have hxz : |x - z'| < ε := lt_of_lt_of_le hx (min_le_left _ _)
        have hxle : |x - z'| < z' := lt_of_lt_of_le hx (min_le_right _ _)
        have hxpos : 0 < x := by
          have h2 := (abs_lt.mp hxle).1
          linarith
        exact hεb x hxpos hxz
      filter_upwards [hev] with x hxb
      rw [hzero x hxb, hIz]
      simp only [sub_self, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hLip := hd_I.le_of_lip' hC0 hEv
  simpa [Real.norm_eq_abs] using hLip

end Work.FTS_RegExport.RXR1
