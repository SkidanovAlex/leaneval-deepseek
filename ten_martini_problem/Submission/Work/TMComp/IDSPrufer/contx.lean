import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.RotBasics.PS
import Submission.Work.TMPuig.pruferStep_basic

/-!
# `contx`: the `n`-th Prüfer angle is continuous in the phase

For fixed `α`, `lam`, `n` the map `x ↦ pruferIter α lam E n x 0` is continuous.  This is a
two-step argument.

* `pruferStep` is continuous as a function of `(a, t) ∈ ℝ × ℝ` jointly.  Continuity in `t`
  for fixed `a` is `Work.TMPuig.pruferStep_continuous_aux`; continuity in `a` for fixed `t`
  is elementary: on the non-exceptional branch `pruferStep a t` equals
  `⌊t+1/2⌋ + 1/2 + arctan (tan (π (t - ⌊t+1/2⌋)) - a)/π` and on the exceptional branch it is
  the locally constant floor.  Joint continuity then follows from monotonicity in `a`
  (`pruferStep_antitone`): on `a ∈ [a₀-δ, a₀+δ]` the value is pinched between the two
  functions `t ↦ pruferStep (a₀∓δ) t`, which are continuous in `t`, and whose values at the
  origin tend to `pruferStep a₀ t₀` as `δ → 0⁺`.
* the recursion
  `pruferIter α lam E (n+1) x t = pruferStep (E - 2λ cos (2π (x + nα))) (pruferIter α lam E n x t)`
  preserves continuity, because `x ↦ (E - 2λ cos (2π (x + nα)), pruferIter α lam E n x t)` is
  continuous by the induction hypothesis.
-/

noncomputable section

open Filter
open scoped Topology

namespace Work.TMComp.IDSPrufer

open Work.TMContract

/-- For fixed angle `t`, the Prüfer step is continuous in the potential value `a`. -/
theorem pruferStep_continuous_a (t : ℝ) :
    Continuous (fun a : ℝ => Work.TMContract.pruferStep a t) := by
  by_cases h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · -- exceptional branch: the value is the floor, independent of `a`
    refine (continuous_const : Continuous fun _ : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ)).congr ?_
    intro a
    exact (Work.TMComp.RotBasics.pruferStep_eq_of_floor_special (a := a) rfl h).symm
  · -- generic branch: an `arctan` of a continuous function of `a`
    have h2 : Continuous (fun a : ℝ => ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 +
        Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a) / Real.pi) := by
      fun_prop
    refine h2.congr ?_
    intro a
    exact (Work.TMComp.RotBasics.pruferStep_eq_of_floor (a := a) rfl h).symm

/-- The Prüfer step is jointly continuous in `(a, t)`. -/
theorem pruferStep_pair_cont :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, t₀⟩
  show Filter.Tendsto (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2)
    (𝓝 (a₀, t₀)) (𝓝 (Work.TMContract.pruferStep a₀ t₀))
  rw [tendsto_order]
  constructor
  · -- lower estimate: for `b < pruferStep a₀ t₀` the value is eventually above `b`
    intro b hb
    obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, dist a a₀ < δ →
        dist (Work.TMContract.pruferStep a t₀) (Work.TMContract.pruferStep a₀ t₀)
          < Work.TMContract.pruferStep a₀ t₀ - b := by
      have hcont : ContinuousAt (fun a : ℝ => Work.TMContract.pruferStep a t₀) a₀ :=
        (pruferStep_continuous_a t₀).continuousAt
      rw [Metric.continuousAt_iff] at hcont
      exact hcont _ (by linarith)
    set c : ℝ := a₀ + δ / 2 with hc
    have hca : dist c a₀ < δ := by
      rw [Real.dist_eq, show c - a₀ = δ / 2 by rw [hc]; ring, abs_of_pos (by linarith)]
      linarith
    have hcv : b < Work.TMContract.pruferStep c t₀ := by
      have h := hδ' c hca
      rw [Real.dist_eq] at h
      linarith [(abs_lt.mp h).1]
    have h1 : (fun p : ℝ × ℝ => p.1) ⁻¹' (Set.Iio c) ∈ 𝓝 (a₀, t₀) := by
      refine continuous_fst.continuousAt.preimage_mem_nhds ?_
      exact isOpen_Iio.mem_nhds (Set.mem_Iio.mpr (by rw [hc]; linarith))
    have h2 : (fun p : ℝ × ℝ => Work.TMContract.pruferStep c p.2) ⁻¹' (Set.Ioi b)
        ∈ 𝓝 (a₀, t₀) := by
      refine ((Work.TMPuig.pruferStep_continuous_aux c).comp continuous_snd).continuousAt
        |>.preimage_mem_nhds ?_
      exact isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hcv)
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Set.mem_preimage] at hp1 hp2
    exact lt_of_lt_of_le (Set.mem_Ioi.mp hp2)
      (Work.TMComp.RotBasics.pruferStep_antitone p.2 (le_of_lt (Set.mem_Iio.mp hp1)))
  · -- upper estimate: for `b > pruferStep a₀ t₀` the value is eventually below `b`
    intro b hb
    obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, dist a a₀ < δ →
        dist (Work.TMContract.pruferStep a t₀) (Work.TMContract.pruferStep a₀ t₀)
          < b - Work.TMContract.pruferStep a₀ t₀ := by
      have hcont : ContinuousAt (fun a : ℝ => Work.TMContract.pruferStep a t₀) a₀ :=
        (pruferStep_continuous_a t₀).continuousAt
      rw [Metric.continuousAt_iff] at hcont
      exact hcont _ (by linarith)
    set c : ℝ := a₀ - δ / 2 with hc
    have hca : dist c a₀ < δ := by
      rw [Real.dist_eq, show c - a₀ = -(δ / 2) by rw [hc]; ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    have hcv : Work.TMContract.pruferStep c t₀ < b := by
      have h := hδ' c hca
      rw [Real.dist_eq] at h
      linarith [(abs_lt.mp h).2]
    have h1 : (fun p : ℝ × ℝ => p.1) ⁻¹' (Set.Ioi c) ∈ 𝓝 (a₀, t₀) := by
      refine continuous_fst.continuousAt.preimage_mem_nhds ?_
      exact isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by rw [hc]; linarith))
    have h2 : (fun p : ℝ × ℝ => Work.TMContract.pruferStep c p.2) ⁻¹' (Set.Iio b)
        ∈ 𝓝 (a₀, t₀) := by
      refine ((Work.TMPuig.pruferStep_continuous_aux c).comp continuous_snd).continuousAt
        |>.preimage_mem_nhds ?_
      exact isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hcv)
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Set.mem_preimage] at hp1 hp2
    exact lt_of_le_of_lt
      (Work.TMComp.RotBasics.pruferStep_antitone p.2 (le_of_lt (Set.mem_Ioi.mp hp1)))
      (Set.mem_Iio.mp hp2)

/-- The `n`-th Prüfer angle is continuous in the phase `x`, for every starting angle. -/
theorem pruferIter_continuous_x (α lam X : ℝ) (n : ℕ) (t : ℝ) :
    Continuous (fun x : ℝ => Work.TMContract.pruferIter α lam X n x t) := by
  induction n with
  | zero =>
    refine (continuous_const : Continuous fun _ : ℝ => t).congr ?_
    intro x
    simp [Work.TMContract.pruferIter]
  | succ n ih =>
    have hstep : (fun x : ℝ => Work.TMContract.pruferIter α lam X (n + 1) x t) =
        fun x : ℝ => Work.TMContract.pruferStep
          (X - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
          (Work.TMContract.pruferIter α lam X n x t) := by
      funext x
      rw [Work.TMContract.pruferIter]
    rw [hstep]
    exact pruferStep_pair_cont.comp (Continuous.prodMk (by fun_prop) ih)

theorem contx (α lam X : ℝ) (n : ℕ) :
    Continuous (fun x : ℝ => Work.TMContract.pruferIter α lam X n x 0) :=
  pruferIter_continuous_x α lam X n 0

end Work.TMComp.IDSPrufer

end
