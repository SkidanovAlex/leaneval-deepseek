import Mathlib
import Submission.Work.Anchor.anchor_data
import Submission.Work.OddVolterra.Window.window_tail_glue
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.glue_local_solutions
import Submission.Work.OddVolterra.Existence.data_eq_zero_of_eventuallyEq_zero
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# From the windowed solution to the state-level anchor

`Work.Anchor.engine_solution` produces, for every admissible bump `h`, a state curve `Z` on the
window `[1/2, 19/20] = [wl, wr]` solving the *modified* system, `1/100`-close to `baseState`.
Here we convert it into the statement of `Work.Anchor.state_solution`:

* the modified data agrees with the paper's data along the solution, so `Z` solves the paper's
  system on `(1/2, 19/20]` (the transfer);
* uniqueness of the odd transition-slope system on the right half-window forces `Z = baseState` on
  `[9/10, 19/20]`, so the extension `Ẑ = Z` on `[1/2, 9/10]`, `Ẑ = baseState` past `9/10` is
  `C^∞` and solves the paper's system on `(1/2, 1)`;
* the tail condition `Ẑ = baseState` for `s ≥ 9/10` and the `1/100`-closeness are immediate.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.Anchor

open Work.OddVolterra

noncomputable section

/-- A bump supported in `[1 - 2τ, 1 - τ]` vanishes on the whole tail `[1 - τ, ∞)`: off the
support window, and at the endpoint by continuity. -/
lemma h_eq_zero_of_tau_le {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    {s : ℝ} (hs : 1 - Work.OddVolterra.tau ≤ s) : h s = 0 := by
  have htau : 1 - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
  rcases lt_or_eq_of_le hs with hlt | heq
  · by_contra hne
    have hmem := hsupp hne
    rw [htau] at hmem hlt
    exact absurd hmem.2 (not_le.mpr hlt)
  · subst heq
    have hzero : ∀ u : ℝ, (1 : ℝ) - Work.OddVolterra.tau < u → h u = 0 := by
      intro u hu
      by_contra hne
      have hmem := hsupp hne
      rw [htau] at hmem hu
      exact absurd hmem.2 (not_le.mpr hu)
    have hcont : ContinuousAt h (1 - Work.OddVolterra.tau) := hh.continuous.continuousAt
    have hleft : Filter.Tendsto h (𝓝[Set.Ioi (1 - Work.OddVolterra.tau)]
        (1 - Work.OddVolterra.tau)) (𝓝 (h (1 - Work.OddVolterra.tau))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hright : Filter.Tendsto h (𝓝[Set.Ioi (1 - Work.OddVolterra.tau)]
        (1 - Work.OddVolterra.tau)) (𝓝 0) := by
      apply Filter.Tendsto.congr'
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact (hzero u hu).symm
      · exact tendsto_const_nhds
    exact tendsto_nhds_unique hleft hright

/-- `profileX s = 1/√(1+s²)` exceeds `7/10` for `0 ≤ s ≤ 1`. -/
lemma seven_tenths_le_profileX {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 10 / 7 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (7 : ℝ) / 10 ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ hpos2]; nlinarith
  have h3 : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + s ^ 2) := one_div_le_one_div_of_le hpos hsqrt
  have hprof : Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) := rfl
  rw [hprof]; linarith

/-- The two `profileX`'s of the workspace are the same function. -/
lemma profileX_eq_OddEnvelope : Commons.Geometry.Ulam.profileX = Work.OddEnvelope.profileX := rfl

/-- A state within `1/100` of `baseState σ` has its first two components at least `1/5` in
absolute value. -/
lemma abs_coord_ge_of_close {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {z : St}
    (hz : ‖z - baseState σ‖ ≤ 1 / 100) : 1 / 5 ≤ |z 0| ∧ 1 / 5 ≤ |z 1| := by
  have hcoord : ∀ i : Fin 4, |z i - baseState σ i| ≤ 1 / 100 := by
    intro i
    have h := norm_le_pi_norm (z - baseState σ) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    linarith [hz]
  have hpx : (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX σ := seven_tenths_le_profileX hσ0 hσ1
  have h0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
  have h1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
  constructor
  · have h := hcoord 0
    rw [h0, abs_le] at h
    have hge : (1 : ℝ) / 5 ≤ z 0 := by linarith [h.1, hpx]
    exact le_trans hge (le_abs_self _)
  · have h := hcoord 1
    rw [h1, abs_le] at h
    have hge : (1 : ℝ) / 5 ≤ z 1 := by linarith [h.1, hpx]
    exact le_trans hge (le_abs_self _)

/-- `baseState` is `C^∞`. -/
lemma contDiff_baseState : ContDiff ℝ (⊤ : ℕ∞) (baseState : ℝ → St) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s) :=
    Work.OddVolterra.Existence.contDiff_profileX
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s) := by
    have h := hp.deriv' (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    simpa using h
  rw [show (baseState : ℝ → St) = fun s : ℝ => ![
      Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s] from rfl]
  refine (contDiff_pi).mpr fun i => ?_
  fin_cases i
  · simpa using hp
  · simpa using hp
  · simpa using hd
  · simpa using hd

end

end Work.Anchor

namespace Work.Anchor

open Work.OddVolterra
open scoped Topology ContDiff Interval

noncomputable section

/-- The cut-offs are `1` on the states of a solution that is `1/100`-close to `baseState`, and
the manifest `Θ` agrees with the paper's `Θ` there. -/
lemma Thf_eq_Theta_of_close {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : s ∈ Set.Icc wl wr) (hsσ : s < σ) (hσw : σ ≤ wr) {z : St}
    (hz : ‖z - baseState σ‖ ≤ 1 / 100) :
    Thf n h s σ z = Theta n h s σ z := by
  have hs0 : 0 < s := by linarith [hs.1, wl_pos]
  have hσ1 : σ ≤ 1 := by linarith [hσw, wr_lt_one]
  have hσ0 : 0 ≤ σ := by linarith [hs0, hsσ]
  obtain ⟨hz0, hz1⟩ := abs_coord_ge_of_close hσ0 hσ1 hz
  -- the state cut-off is `1`
  have hchi : chiT s σ z = 1 := by
    refine chiT_eq_one_of_close (s := s) (σ := σ) hs ⟨by linarith [hsσ.le, hs.1], hσw⟩ ?_
    linarith [hz]
  -- the manifest `Θ` equals the paper's `Θ`
  have hman : Work.OddVolterra.KernelExt.ThetaM n h s σ z = Theta n h s σ z := by
    set δ : ℝ := s / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hδs : δ < s := by rw [hδ]; linarith
    refine Work.OddVolterra.Window.ThetaM_eq_Theta n hn hh hsσ hδpos z ?_ ?_ <;> intro a ha
    · have h1 : δ ≤ a := by linarith [ha.1, hδs]
      refine Work.OddVolterra.Existence.krad_pos_state_region hsupp
        (fun k hk x => hsm1 k hk x) (b := δ) (a := a) (σ := σ) (t := -(z 0)) hδpos h1 ha.2 hσ1 ?_
      rw [abs_neg]
      exact hz0
    · have h1 : δ ≤ a := by linarith [ha.1, hδs]
      refine Work.OddVolterra.Existence.krad_pos_state_region hsupp
        (fun k hk x => hsm1 k hk x) (b := δ) (a := a) (σ := σ) (t := z 1) hδpos h1 ha.2 hσ1 ?_
      exact hz1
  rw [Thf, hchi, one_smul]
  exact hman

end

end Work.Anchor
