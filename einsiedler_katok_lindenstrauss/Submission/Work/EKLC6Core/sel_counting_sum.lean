import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2

/-!
# `Work.EKLC6Core.sel_counting_sum` — finiteness of the total mass of the counting balls

Fix a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and the greedy separated subfamily
`sel y ⊆ ℕ` of a dense sequence `y : ℕ → X₃` (`Work.EKLC6Core.sel`).  The *counting ball* of an
index `n ∈ sel y` is

`countBall μ y n = Vball (2 * cellHi (y n)) (y n) = Vball (injCap (y n) / 1024) (y n)`,

a `V`-ball whose radius is `injCap (y n)/1024`, i.e. a fixed small fraction of the injectivity
radius of its centre.  This file proves that the total mass of the counting balls is finite:

`∑' n, μ (countBall μ y n) ≤ ofReal M` for a constant `M > 0`.

## The argument

The sum of the masses is the integral of the multiplicity function
`x ↦ #{n : x ∈ countBall μ y n}`, so it suffices to bound that multiplicity uniformly in the point
(`Work.EKLC6Core.tsum_measure_le_of_card_bound`).

Fix `x : X₃` and let `A = {n : x ∈ countBall μ y n}`.  Every `n ∈ A` is selected, and
`x = u • y n` with `u ∈ V (injCap (y n)/1024)`.  That displacement is `1/1024` of the injectivity
radius of `y n`, comfortably below the admissible fraction `1/8`, so both
`Work.EKLC6Core.injCap_mem_V_le` (lower semicontinuity) and `Work.EKLC6Core.injCap_smul_le` (upper
semicontinuity) apply at `y n` and give the two-sided comparison

`injCap (y n)/16 ≤ injCap x ≤ 4 * injCap (y n)`   (`injCap_bounds_of_mem_countBall`).

With `sep := injCap x / 2^24`:

* `y n = u⁻¹ • x` with `u⁻¹ ∈ V (10 * injCap (y n)/1024) ⊆ V (5 * 2^19 * sep)`, using
  `injCap (y n) ≤ 16 injCap x` and `10 * 16/1024 = 5 * 2^19/2^24`
  (`mem_fatVball_of_mem_countBall`): all the centres `y n`, `n ∈ A`, lie in the *single* fat ball
  `Vball (5 * 2^19 * sep) x`, whose radius is `5/32 * injCap x ≤ injCap x/2`.
* `sep ≤ sepRad (y n) = injCap (y n)/2^20`, since `injCap x ≤ 4 injCap (y n)`
  (`countBall_sep`): a displacement in `V sep` carrying `y n` to `y m` would in particular lie in
  `V (sepRad (y n))`, contradicting the separation of the greedy family
  (`Work.EKLC6Core.sel_sep`).

So `{y n : n ∈ A}` is a `sep`-separated subset of `Vball (5 * 2^19 * sep) x` to which
`Work.EKLC6Core.vball_packing_uniform` (at the constant `c = 5 * 2^19`) applies, and its
cardinality is bounded by a constant `M` independent of `x` and of `sep`.  Since `n ↦ y n` is
injective on `sel y` (`Work.EKLC6Core.sel_inj`), `#A ≤ M`; summing the measures gives
`∑' n, μ (countBall μ y n) ≤ ofReal M * μ univ = ofReal M`.
-/

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open MeasureTheory
open Work.EKLContract

noncomputable section

/-- The counting ball of a selected index, written at the level of the injectivity radius. -/
theorem countBall_eq_vball_injCap {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} (hn : n ∈ sel y) :
    countBall μ y n = Work.EKLComp.Vball (injCap (y n) / 1024) (y n) := by
  rw [countBall_eq hn]
  congr 1
  rw [cellHi]
  ring

/-- A non-trivial counting ball forces its index to be selected. -/
theorem mem_sel_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) : n ∈ sel y := by
  by_contra hn
  rw [countBall_eq_empty hn] at hx
  exact Set.notMem_empty x hx

/-- **The two-sided scale of a counting ball.** -/
theorem injCap_bounds_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) :
    injCap (y n) / 16 ≤ injCap x ∧ injCap x ≤ 4 * injCap (y n) := by
  have hn := mem_sel_of_mem_countBall hx
  rw [countBall_eq_vball_injCap hn] at hx
  obtain ⟨u, hu, hueq⟩ := Work.EKLComp.mem_Vball.mp hx
  set a : ℝ := injCap (y n) / 1024 with ha
  have hapos : 0 < a := by rw [ha]; exact div_pos (injCap_pos _) (by norm_num)
  have hahalf : a ≤ 1 / 2 := by
    rw [ha]
    have := injCap_le_half (y n)
    linarith
  have ha8 : a ≤ injCap (y n) / 8 := by rw [ha]; linarith
  refine ⟨?_, ?_⟩
  · have h := injCap_mem_V_le (x := y n) (a := a) hapos hahalf ha8 hu
    rwa [hueq] at h
  · have h := injCap_smul_le (x := y n) (a := a) hapos hahalf ha8 hu
    rwa [hueq] at h

/-- The centre of a counting ball containing `x` lies in the fat ball of `x` at the uniform
scale `5 * 2^19 * (injCap x / 2^24)`. -/
theorem mem_fatVball_of_mem_countBall {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {n : ℕ} {x : X3} (hx : x ∈ countBall μ y n) :
    y n ∈ Work.EKLComp.Vball (5 * 2 ^ 19 * (injCap x / 2 ^ 24)) x := by
  have hb := injCap_bounds_of_mem_countBall hx
  have hle16 : injCap (y n) ≤ 16 * injCap x := by linarith [hb.1]
  have hn := mem_sel_of_mem_countBall hx
  rw [countBall_eq_vball_injCap hn] at hx
  obtain ⟨u, hu, hueq⟩ := Work.EKLComp.mem_Vball.mp hx
  have ha1 : injCap (y n) / 1024 ≤ 1 := by
    have := injCap_le_half (y n)
    linarith
  have hinv : u⁻¹ ∈ V (10 * (injCap (y n) / 1024)) :=
    Work.EKLComp.inv_mem_V (div_pos (injCap_pos _) (by norm_num)) ha1 hu
  refine Work.EKLComp.mem_Vball.mpr ⟨u⁻¹, Work.Misiurewicz.V_mono ?_ hinv, ?_⟩
  · rw [show 5 * 2 ^ 19 * (injCap x / 2 ^ 24) = 5 / 32 * injCap x by ring]
    rw [show 10 * (injCap (y n) / 1024) = 5 / 512 * injCap (y n) by ring]
    linarith
  · show u⁻¹ • x = y n
    rw [← hueq, ← mul_smul, inv_mul_cancel, one_smul]

/-- **Separation of the centres of two counting balls through `x`.** -/
theorem countBall_sep {μ : Measure X3} [IsFiniteMeasure μ]
    {y : ℕ → X3} {x : X3} {n m : ℕ}
    (hn : x ∈ countBall μ y n) (hm : x ∈ countBall μ y m) (hne : n ≠ m) {w : SL3}
    (hw : w ∈ V (injCap x / 2 ^ 24)) : w • y n ≠ y m := by
  have hns := mem_sel_of_mem_countBall hn
  have hms := mem_sel_of_mem_countBall hm
  have hb := injCap_bounds_of_mem_countBall hn
  have hsep : injCap x / 2 ^ 24 ≤ sepRad (y n) := by
    rw [sepRad]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2 ^ 24)]
    nlinarith [hb.2, injCap_pos (y n)]
  intro heq
  exact (sel_sep y hns hms hne).1
    (Work.EKLComp.mem_Vball.mpr ⟨w, Work.Misiurewicz.V_mono hsep hw, heq⟩)

/-- **The counting balls of the greedy family have finite total mass.**  For a probability measure
`μ` on `X₃` and a dense sequence `y`, there is `M > 0` with
`∑' n, μ (countBall μ y n) ≤ ofReal M`: the multiplicities of the counting balls are bounded
uniformly in the point, by the packing bound of `Work.EKLC6Core.vball_packing_uniform` and the
separation of the selected centres. -/
theorem sel_counting_sum (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hy : Dense (Set.range y)) :
    ∃ M : ℝ, 0 < M ∧ ∑' n : ℕ, μ (Work.EKLC6Core.countBall μ y n) ≤ ENNReal.ofReal M := by
  classical
  obtain ⟨M, hMpos, hM⟩ := vball_packing_uniform (c := 5 * 2 ^ 19) (by norm_num)
  refine ⟨M, hMpos, ?_⟩
  have hcard : ∀ (F : Finset ℕ) (x : X3),
      ((F.filter (fun n => x ∈ countBall μ y n)).card : ℝ) ≤ M := by
    intro F x
    have hSel : ∀ n ∈ F.filter (fun n => x ∈ countBall μ y n), n ∈ sel y :=
      fun n hn => mem_sel_of_mem_countBall (Finset.mem_filter.mp hn).2
    have hcard_eq : ((F.filter (fun n => x ∈ countBall μ y n)).image y).card
        = (F.filter (fun n => x ∈ countBall μ y n)).card :=
      Finset.card_image_of_injOn fun a ha b hb h => sel_inj y (hSel a ha) (hSel b hb) h
    rw [← hcard_eq]
    refine hM (injCap x / 2 ^ 24) (div_pos (injCap_pos x) (by norm_num)) x
      ((F.filter (fun n => x ∈ countBall μ y n)).image y) ?_ ?_ ?_
    · rw [show 5 * 2 ^ 19 * (injCap x / 2 ^ 24) = 5 / 32 * injCap x by ring]
      linarith [injCap_pos x]
    · intro s hs
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
      exact mem_fatVball_of_mem_countBall (Finset.mem_filter.mp hn).2
    · intro s hs s' hs' hne w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨m, hm, hmeq⟩ := Finset.mem_image.mp hs'
      have hnm : n ≠ m := fun h => hne (by rw [h, hmeq])
      rw [← hmeq]
      exact countBall_sep (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 hnm hw
  have hmain := tsum_measure_le_of_card_bound μ (fun n => countBall μ y n)
    (fun n => countBall_measurable μ y n) (le_of_lt hMpos) hcard
  rwa [measure_univ, mul_one] at hmain

end

end Work.EKLC6Core
