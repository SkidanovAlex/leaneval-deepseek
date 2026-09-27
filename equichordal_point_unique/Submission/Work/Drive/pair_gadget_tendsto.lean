import Mathlib
import Submission.Work.Drive.phaseGadget
import Submission.Work.Drive.continuousAt_gadget
import Submission.Work.Drive.tendsto_chart_transition_slope

/-!
# The limit of the product of two consecutive transfer gadgets at the shared pivot

The `i`-th transfer gadget `Work.Drive.gadget a ρ i` (see `Submission/Work/Drive/phaseGadget.lean`)
is supported in the chart ball of radius `8 ρ i` about the pivot `a i`; off its two pivots it is a
unit complex number, and in the inner ball of radius `2 ρ i` it equals the phase
`(c x - c (a i)) / (c x - c (a (i + 1)))` of the ratio of the two chart differences
(`Work.Drive.gadget_eq_phase`).

At the pivot `a j` the gadget `j - 1` (whose second pivot is `a j`) is singular and so is the gadget
`j` (whose first pivot is `a j`); individually neither has a limit, since a phase of a quantity
tending to `0` or to `∞` has no limit.  What does have a limit is their *product*: writing
`u = φ x` in the chart `φ = chartAt ℂ (a (j-1))` and `w = ψ x` in the chart `ψ = chartAt ℂ (a j)`,
the two phases multiply to

`phase (u - φ (a (j-1))) * phase ((w - ψ (a j)) / (u - φ (a j))) * conj (phase (w - ψ (a (j+1))))`,

where the "bad" factors `phase (u - φ (a j))` and `phase (w - ψ (a j))` multiplied to `1` because the
coordinate change is a local biholomorphism with **non-zero** derivative at `a j` (the hypothesis
`hT`).  Each of the three surviving factors now has a limit: `u - φ (a (j-1))` tends to a non-zero
constant, `(w - ψ (a j))/(u - φ (a j))` to the derivative of the chart transition
(`Work.Drive.tendsto_chart_transition_slope`), and `w - ψ (a (j+1))` to another non-zero constant.
The limit is therefore a product of three unit complex numbers, in particular non-zero.

This is the local input used in `Submission/Work/Drive/exists_continuous_singleZero_phase.lean`
step 2 to see that the telescoping product `∏ᵢ g i` has a removable singularity, of modulus `1`, at
every pivot `a j` with `j ≥ 1`.
-/

open scoped Manifold Topology

noncomputable section

open Filter Set Metric

namespace Work.Drive

/-! ## Elementary `phase` algebra -/

/-- The phase of a quotient is the phase of the numerator times the conjugate of the phase of the
denominator. -/
theorem phase_div_of_ne_zero {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    phase (z / w) = phase z * star (phase w) := by
  rw [div_eq_mul_inv, ← phase_mul hz (inv_ne_zero hw), phase_inv_eq_conj hw]
  rfl

/-- The key algebraic identity: on the punctured neighbourhood of `a j` the product of the two
gadgets equals `phase A * phase (C / B) * conj (phase D)`, with `A`, `B`, `C`, `D` the four chart
differences, and the two singular factors `phase B`, `phase (C / B) * phase B = phase C` having
cancelled. -/
theorem phase_ratio_mul {A B C D : ℂ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    phase (A / B) * phase (C / D) = phase A * phase (C / B) * star (phase D) := by
  rw [phase_div_of_ne_zero hA hB, phase_div_of_ne_zero hC hD, phase_div_of_ne_zero hC hB]
  ring

/-- The phase is continuous at every point where the limit is non-zero. -/
theorem tendsto_phase_of_tendsto {α : Type*} {l : Filter α} {f : α → ℂ} {L : ℂ}
    (hf : Filter.Tendsto f l (nhds L)) (hL : L ≠ 0) :
    Filter.Tendsto (fun x => phase (f x)) l (nhds (phase L)) :=
  ((continuousAt_phase hL).tendsto).comp hf

/-! ## The limit of the product of two consecutive gadgets -/

theorem pair_gadget_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {a : ℕ → X} {ρ : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hρ : ∀ i : ℕ, 0 < ρ i)
    (hinj : Function.Injective a)
    (hstep : ∀ i : ℕ, a (i + 1) ∈ {x : X | x ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (ρ i)})
    (hT : deriv ((chartAt ℂ (a (j - 1))).symm.trans (chartAt ℂ (a j)))
        ((chartAt ℂ (a (j - 1))) (a j)) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto (fun x : X =>
        Work.Drive.gadget a ρ (j - 1) x * Work.Drive.gadget a ρ j x)
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds c) := by
  classical
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  -- the consecutive-pivot hypothesis, read at `j - 1`
  have hstep_prev : a j ∈ {x : X | x ∈ (chartAt ℂ (a (j - 1))).source ∧
      (chartAt ℂ (a (j - 1))) x ∈ Metric.ball ((chartAt ℂ (a (j - 1))) (a (j - 1)))
        (ρ (j - 1))} := by
    simpa only [hj'] using hstep (j - 1)
  have hsrc_prev : a j ∈ (chartAt ℂ (a (j - 1))).source := hstep_prev.1
  have hball_prev : ‖(chartAt ℂ (a (j - 1))) (a j) - gP a (j - 1)‖ < ρ (j - 1) := by
    have h := hstep_prev.2
    rw [Metric.mem_ball, dist_eq_norm] at h
    rw [gP]
    exact h
  have hstep_j := hstep j
  have hsrc_j : a (j + 1) ∈ (chartAt ℂ (a j)).source := hstep_j.1
  have hne_j_prev : a j ≠ a (j - 1) := fun h => (by omega : j ≠ j - 1) (hinj h)
  have hne_j_next : a j ≠ a (j + 1) := fun h => (by omega : j ≠ j + 1) (hinj h)
  -- the chart value of the pivot `a j` in the chart at `a (j-1)`
  have hQ1 : gQ a (j - 1) = (chartAt ℂ (a (j - 1))) (a j) := by
    rw [gQ, hj']
  have hQ1_ne : (chartAt ℂ (a (j - 1))) (a j) ≠ gP a (j - 1) := by
    rw [gP]
    intro h
    exact hne_j_prev ((chartAt ℂ (a (j - 1))).injOn hsrc_prev (mem_chart_source ℂ (a (j - 1))) h)
  have hP2_ne_Q2 : gP a j ≠ gQ a j := by
    rw [gP, gQ]
    intro h
    exact (by omega : j ≠ j + 1) (hinj ((chartAt ℂ (a j)).injOn
      (mem_chart_source ℂ (a j)) hsrc_j h))
  -- all the eventual facts on the punctured neighbourhood of `a j`
  have h1ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ≠ a (j - 1) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_ne_nhds hne_j_prev)
  have h2ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ≠ a (j + 1) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_ne_nhds hne_j_next)
  have hsrc_prev_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ,
      x ∈ (chartAt ℂ (a (j - 1))).source :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((chartAt ℂ (a (j - 1))).open_source.mem_nhds hsrc_prev)
  have hsrc_j_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ, x ∈ (chartAt ℂ (a j)).source :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((chartAt ℂ (a j)).open_source.mem_nhds (mem_chart_source ℂ (a j)))
  have hball_prev_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ,
      ‖(chartAt ℂ (a (j - 1))) x - gP a (j - 1)‖ < 2 * ρ (j - 1) := by
    have hlt : ‖(chartAt ℂ (a (j - 1))) (a j) - gP a (j - 1)‖ < 2 * ρ (j - 1) := by
      linarith [hball_prev, hρ (j - 1)]
    have hcont : ContinuousAt (fun x : X =>
        ‖(chartAt ℂ (a (j - 1))) x - gP a (j - 1)‖) (a j) :=
      (((chartAt ℂ (a (j - 1))).continuousAt hsrc_prev).sub continuousAt_const).norm
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt))
  have hball_j_ev : ∀ᶠ x : X in nhdsWithin (a j) {(a j)}ᶜ,
      ‖(chartAt ℂ (a j)) x - gP a j‖ < 2 * ρ j := by
    have hlt : ‖(chartAt ℂ (a j)) (a j) - gP a j‖ < 2 * ρ j := by
      rw [gP, sub_self, norm_zero]
      linarith [hρ j]
    have hcont : ContinuousAt (fun x : X => ‖(chartAt ℂ (a j)) x - gP a j‖) (a j) :=
      (((chartAt ℂ (a j)).continuousAt (mem_chart_source ℂ (a j))).sub continuousAt_const).norm
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt))
  -- the three factors of the limit
  have hFst : Filter.Tendsto (fun x : X => phase ((chartAt ℂ (a (j - 1))) x - gP a (j - 1)))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase ((chartAt ℂ (a (j - 1))) (a j) - gP a (j - 1)))) := by
    refine tendsto_phase_of_tendsto ?_ (sub_ne_zero.mpr hQ1_ne)
    have hc : ContinuousAt (fun x : X => (chartAt ℂ (a (j - 1))) x) (a j) :=
      (chartAt ℂ (a (j - 1))).continuousAt hsrc_prev
    exact ((hc.sub continuousAt_const).tendsto).mono_left nhdsWithin_le_nhds
  have hmid : Filter.Tendsto (fun x : X => phase (((chartAt ℂ (a j)) x - gP a j) /
      ((chartAt ℂ (a (j - 1))) x - gQ a (j - 1))))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase (deriv ((chartAt ℂ (a (j - 1))).symm.trans (chartAt ℂ (a j)))
        ((chartAt ℂ (a (j - 1))) (a j))))) := by
    refine tendsto_phase_of_tendsto ?_ hT
    have h1 := tendsto_chart_transition_slope (x := a (j - 1)) (y := a j) hsrc_prev
    simpa only [gP, hQ1] using h1
  have hthird : Filter.Tendsto (fun x : X => star (phase ((chartAt ℂ (a j)) x - gQ a j)))
      (nhdsWithin (a j) {(a j)}ᶜ) (nhds (star (phase (gP a j - gQ a j)))) := by
    have hb : Filter.Tendsto (fun x : X => (chartAt ℂ (a j)) x - gQ a j)
        (nhdsWithin (a j) {(a j)}ᶜ) (nhds (gP a j - gQ a j)) := by
      have hc : ContinuousAt (fun x : X => (chartAt ℂ (a j)) x) (a j) :=
        (chartAt ℂ (a j)).continuousAt (mem_chart_source ℂ (a j))
      have h : Filter.Tendsto (fun x : X => (chartAt ℂ (a j)) x - gQ a j) (nhds (a j))
          (nhds (gP a j - gQ a j)) := (hc.sub continuousAt_const).tendsto
      exact h.mono_left nhdsWithin_le_nhds
    exact (tendsto_phase_of_tendsto hb (sub_ne_zero.mpr hP2_ne_Q2)).star
  have hF : Filter.Tendsto (fun x : X => phase ((chartAt ℂ (a (j - 1))) x - gP a (j - 1)) *
      phase (((chartAt ℂ (a j)) x - gP a j) / ((chartAt ℂ (a (j - 1))) x - gQ a (j - 1))) *
      star (phase ((chartAt ℂ (a j)) x - gQ a j)))
      (nhdsWithin (a j) {(a j)}ᶜ)
      (nhds (phase ((chartAt ℂ (a (j - 1))) (a j) - gP a (j - 1)) *
        phase (deriv ((chartAt ℂ (a (j - 1))).symm.trans (chartAt ℂ (a j)))
          ((chartAt ℂ (a (j - 1))) (a j))) * star (phase (gP a j - gQ a j)))) :=
    (hFst.mul hmid).mul hthird
  -- on the punctured neighbourhood the product of the two gadgets *is* that expression
  have hev : (fun x : X => gadget a ρ (j - 1) x * gadget a ρ j x)
      =ᶠ[nhdsWithin (a j) {(a j)}ᶜ]
      (fun x : X => phase ((chartAt ℂ (a (j - 1))) x - gP a (j - 1)) *
        phase (((chartAt ℂ (a j)) x - gP a j) / ((chartAt ℂ (a (j - 1))) x - gQ a (j - 1))) *
        star (phase ((chartAt ℂ (a j)) x - gQ a j))) := by
    filter_upwards [self_mem_nhdsWithin, h1ev, h2ev, hsrc_prev_ev, hball_prev_ev,
      hsrc_j_ev, hball_j_ev] with x hx hne1 hne2 hs1 hb1 hs2 hb2
    have hxA : x ≠ a j := by simpa using hx
    rw [gadget_eq_phase (a := a) (ρ := ρ) (i := j - 1) ⟨hs1, le_of_lt hb1⟩,
      gadget_eq_phase (a := a) (ρ := ρ) (i := j) ⟨hs2, le_of_lt hb2⟩]
    have h1 : (chartAt ℂ (a (j - 1))) x - gP a (j - 1) ≠ 0 := by
      rw [gP]
      exact sub_ne_zero.mpr (fun h => hne1
        ((chartAt ℂ (a (j - 1))).injOn hs1 (mem_chart_source ℂ (a (j - 1))) h))
    have h2 : (chartAt ℂ (a (j - 1))) x - gQ a (j - 1) ≠ 0 := by
      rw [gQ, hj']
      exact sub_ne_zero.mpr (fun h => hxA ((chartAt ℂ (a (j - 1))).injOn hs1 hsrc_prev h))
    have h3 : (chartAt ℂ (a j)) x - gP a j ≠ 0 := by
      rw [gP]
      exact sub_ne_zero.mpr (fun h => hxA
        ((chartAt ℂ (a j)).injOn hs2 (mem_chart_source ℂ (a j)) h))
    have h4 : (chartAt ℂ (a j)) x - gQ a j ≠ 0 := by
      rw [gQ]
      exact sub_ne_zero.mpr (fun h => hne2 ((chartAt ℂ (a j)).injOn hs2 hsrc_j h))
    exact phase_ratio_mul h1 h2 h3 h4
  refine ⟨phase ((chartAt ℂ (a (j - 1))) (a j) - gP a (j - 1)) *
      phase (deriv ((chartAt ℂ (a (j - 1))).symm.trans (chartAt ℂ (a j)))
        ((chartAt ℂ (a (j - 1))) (a j))) * star (phase (gP a j - gQ a j)), ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (phase_ne_zero (sub_ne_zero.mpr hQ1_ne))
      (phase_ne_zero hT)) (star_ne_zero.mpr (phase_ne_zero (sub_ne_zero.mpr hP2_ne_Q2)))
  · exact hF.congr' hev.symm

end Work.Drive
