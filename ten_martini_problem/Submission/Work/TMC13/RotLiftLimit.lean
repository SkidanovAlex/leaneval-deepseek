import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RotBasics.PSIter

/-!
# Existence of the Prüfer rotation number (`rotLift`)

`rotLift α lam E` is *defined* as `limUnder` of the averages of the Prüfer iterates.  This
module proves that the averages really converge (C5 part 1), using only the elementary
Prüfer calculus of `Submission.Work.TMComp.RotBasics.PSIter` and `…PS`:

* `pruferIter_cocycle`, `pruferIter_bound` (displacement bound), `pruferIter_periodic_x`,
  `pruferIter_continuous`, `pruferStep_cell`.

The convergence is Fekete's lemma applied to the almost-subadditive sequence
`n ↦ ∫₀¹ pruferIter n x 0 dx`.
-/

noncomputable section

namespace Work.TMC13

open MeasureTheory Filter
open scoped Topology

/-- The `n`-th Prüfer iterate is continuous in the phase. -/
lemma continuous_pruferIter_phase (α lam E : ℝ) (n : ℕ) :
    Continuous (fun x : ℝ => Work.TMContract.pruferIter α lam E n x 0) :=
  (Work.TMComp.RotBasics.pruferIter_continuous lam n).comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))

/-- One Prüfer step moves the angle by at least `-1/2`. -/
lemma pruferStep_lower (a t : ℝ) : t - 1 / 2 ≤ Work.TMContract.pruferStep a t := by
  have h1 := (Work.TMComp.RotBasics.pruferStep_cell a t).1
  have h2 : t - 1 / 2 < ((⌊t + 1 / 2⌋ : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (t + 1 / 2)
    push_cast at this
    linarith
  linarith

/-- The `n`-th Prüfer iterate is bounded below by `-n/2`. -/
lemma pruferIter_lower (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    -((n : ℝ) / 2) ≤ Work.TMContract.pruferIter α lam E n x 0 := by
  induction n with
  | zero => simp [Work.TMContract.pruferIter]
  | succ k ih =>
    have hstep : Work.TMContract.pruferIter α lam E (k + 1) x 0
        = Work.TMContract.pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (k : ℝ) * α)))
            (Work.TMContract.pruferIter α lam E k x 0) := rfl
    rw [hstep]
    have hlow := pruferStep_lower (E - 2 * lam * Real.cos (2 * Real.pi * (x + (k : ℝ) * α)))
      (Work.TMContract.pruferIter α lam E k x 0)
    push_cast
    linarith

/-- **C5 part 1.**  The averages of the Prüfer iterates converge to `rotLift`. -/
theorem prufer_rotLift_tendsto (α lam E : ℝ) :
    Tendsto (fun n : ℕ =>
        (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0) / (n : ℝ))
      atTop (𝓝 (Work.TMContract.rotLift α lam E)) := by
  set U : ℕ → ℝ := fun n => ∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0
    with hU
  have hInt : ∀ n : ℕ, IntervalIntegrable
      (fun x : ℝ => Work.TMContract.pruferIter α lam E n x 0) volume (0 : ℝ) 1 :=
    fun n => (continuous_pruferIter_phase α lam E n).intervalIntegrable 0 1
  -- pointwise almost-subadditivity
  have hpt : ∀ n m : ℕ, ∀ x : ℝ,
      Work.TMContract.pruferIter α lam E (n + m) x 0
        ≤ Work.TMContract.pruferIter α lam E n x 0
          + Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0 + 1 := by
    intro n m x
    rw [Work.TMComp.RotBasics.pruferIter_cocycle]
    have hb := Work.TMComp.RotBasics.pruferIter_bound α lam E m (x + (n : ℝ) * α)
      (Work.TMContract.pruferIter α lam E n x 0)
    rw [abs_le] at hb
    linarith [hb.2]
  -- the average of the shifted factor is the same
  have hshift : ∀ n m : ℕ,
      (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0) = U m := by
    intro n m
    have h1 : (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0)
        = ∫ x in (n : ℝ) * α..1 + (n : ℝ) * α,
            Work.TMContract.pruferIter α lam E m x 0 := by
      have := intervalIntegral.integral_comp_add_right
        (f := fun y : ℝ => Work.TMContract.pruferIter α lam E m y 0) (a := (0 : ℝ)) (b := 1)
        (d := (n : ℝ) * α)
      simpa using this
    rw [h1]
    have h1' : (1 : ℝ) + (n : ℝ) * α = (n : ℝ) * α + 1 := by ring
    rw [h1']
    have hper : Function.Periodic (fun y : ℝ => Work.TMContract.pruferIter α lam E m y 0) 1 :=
      fun x => Work.TMComp.RotBasics.pruferIter_periodic_x α lam E m x 0
    have h2 := Function.Periodic.intervalIntegral_add_eq hper ((n : ℝ) * α) 0
    simpa [hU] using h2
  have hsub : ∀ n m : ℕ, U (n + m) ≤ U n + U m + 1 := by
    intro n m
    have hIm : IntervalIntegrable
        (fun x : ℝ => Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0)
        volume (0 : ℝ) 1 :=
      ((continuous_pruferIter_phase α lam E m).comp
        (continuous_id.add continuous_const)).intervalIntegrable 0 1
    have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
      (hInt (n + m)) (((hInt n).add hIm).add intervalIntegrable_const)
      (fun x _ => hpt n m x)
    have hlin : (∫ x in (0 : ℝ)..1, (Work.TMContract.pruferIter α lam E n x 0
          + Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0 + 1))
        = U n + U m + 1 := by
      rw [intervalIntegral.integral_add ((hInt n).add hIm) intervalIntegrable_const,
        intervalIntegral.integral_add (hInt n) hIm, intervalIntegral.integral_const,
        hshift n m]
      ring
    rw [hlin] at hmono
    exact hmono
  -- lower bound
  have hUlow : ∀ n : ℕ, -((n : ℝ) / 2) ≤ U n := by
    intro n
    have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
      intervalIntegrable_const (hInt n) (fun x _ => pruferIter_lower α lam E n x)
    rw [intervalIntegral.integral_const] at h
    simpa using h
  -- Fekete
  have hbdd : BddBelow (Set.range fun n : ℕ => (U n + 1) / (n : ℝ)) := by
    refine ⟨-(1 / 2 : ℝ), ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : (-(1 / 2 : ℝ)) * (n : ℝ) ≤ U n + 1 := by
        have := hUlow n
        linarith
      rw [le_div_iff₀ hnpos]
      linarith [h1]
  have hsubb : Subadditive fun n : ℕ => U n + 1 := by
    intro n m
    have h := hsub n m
    linarith
  have hlim := hsubb.tendsto_lim hbdd
  have hzero : Tendsto (fun n : ℕ => (U n + 1) / (n : ℝ) - U n / (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
    ring
  have hUlim : Tendsto (fun n : ℕ => U n / (n : ℝ)) atTop (𝓝 hsubb.lim) := by
    have := hlim.sub hzero
    simpa using this
  have hrot : Work.TMContract.rotLift α lam E = hsubb.lim := by
    unfold Work.TMContract.rotLift
    exact Filter.Tendsto.limUnder_eq (g := fun n : ℕ => U n / (n : ℝ)) hUlim
  rw [hrot]
  simpa [hU] using hUlim

end Work.TMC13
