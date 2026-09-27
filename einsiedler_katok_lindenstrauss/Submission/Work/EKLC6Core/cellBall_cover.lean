import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2
import Submission.Work.EKLC6Core.cellBall_cover_arith_sel
import Submission.Work.EKLC6Core.cellBall_cover_arith_A
import Submission.Work.EKLC6Core.cellBall_cover_arith_B

/-!
# `Work.EKLC6Core.cellBall_cover`

The cells `cellBall μ y n` of the greedy separated subfamily `sel y ⊆ ℕ` of a dense sequence
`y : ℕ → X₃` **cover** `X₃`: for every `z : X₃` there is a *selected* index `n ∈ sel y` with
`z ∈ cellBall μ y n = Vball (cellRad μ y n) (y n)`.

## The argument

Fix `z` and put `a := injCap z / 2^80`, so that `a > 0`, `a ≤ 1/2` and `a ≤ injCap z / 8`.  The
ball `Vball a z` is a nonempty open set, so by density of `y` there are `n` and `u ∈ V a` with
`u • z = y n`; then `z = u⁻¹ • y n` with `u⁻¹ ∈ V (10 a)`.  Quantitative lower semicontinuity of
the injectivity radius (`Work.EKLC6Core.injCap_mem_V_le`) gives `injCap z / 16 ≤ injCap (y n)`.

* If `n ∈ sel y` we are done: `10 a ≤ injCap (y n)/4096 = cellLo (y n) ≤ cellRad μ y n`.
* If `n ∉ sel y`, the maximality of the greedy selection (`Work.EKLC6Core.exists_sel_witness`)
  provides `j < n` with `j ∈ sel y` and one of the two separation conditions.  Writing
  `P := injCap z`, `Q := injCap (y n)`, `R := injCap (y j)`:
  - if `y n = w • y j` with `w ∈ V (sepRad (y j))`, then `z = (u⁻¹ w) • y j` with
    `u⁻¹ w ∈ V (10 a + sepRad (y j) + 3 (10 a) sepRad (y j))`, and
    `Q ≤ 2^19 R` (`Work.EKLC6Core.injCap_le_mul_of_mem_Vball`), so the exponent is at most
    `R/4096 = cellLo (y j) ≤ cellRad μ y j`;
  - if `y j = w • y n` with `w ∈ V (sepRad (y n))`, then `z = (u⁻¹ w⁻¹) • y j` with
    `u⁻¹ w⁻¹ ∈ V (10 a + 10 sepRad (y n) + 3 (10 a)(10 sepRad (y n)))`, and
    `Q ≤ 16 R` (`Work.EKLC6Core.injCap_mem_V_le` at `y n`), so again the exponent is at most
    `R/4096`.

All the numerical estimates are isolated in the three arithmetic lemmas
`Work.EKLC6Core.cellBall_cover_arith_sel`, `Work.EKLC6Core.cellBall_cover_arith_A` and
`Work.EKLC6Core.cellBall_cover_arith_B`, proved in their own modules and imported here.
-/

open MeasureTheory Filter Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The cover -/

theorem cellBall_cover (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] (y : ℕ → Work.EKLContract.X3)
    (hy : Dense (Set.range y)) (z : Work.EKLContract.X3) :
    ∃ n : ℕ, n ∈ Work.EKLC6Core.sel y ∧ z ∈ Work.EKLC6Core.cellBall μ y n := by
  classical
  -- the tiny displacement radius, small compared with the injectivity radius of `z`
  set a : ℝ := injCap z / 2 ^ 80 with ha
  have hapos : 0 < a := by rw [ha]; exact div_pos (injCap_pos z) (by norm_num)
  have hahalf : a ≤ 1 / 2 := by
    rw [ha]
    have h1 : injCap z / 2 ^ 80 ≤ (1 / 2) / 2 ^ 80 :=
      div_le_div_of_nonneg_right (injCap_le_half z) (by norm_num)
    have h2 : ((1 : ℝ) / 2) / 2 ^ 80 ≤ 1 / 2 := by norm_num
    linarith
  have ha1 : a ≤ 1 := by linarith
  have ha8 : a ≤ injCap z / 8 := by
    rw [ha]
    exact div_le_div_of_nonneg_left (le_of_lt (injCap_pos z)) (by norm_num)
      (show (8 : ℝ) ≤ 2 ^ 80 by norm_num)
  -- density: some point of the sequence lies in the tiny ball around `z`
  have hUopen : IsOpen (Work.EKLComp.Vball a z) := Work.Misiurewicz.isOpen_Vball z hapos
  have hUne : (Work.EKLComp.Vball a z).Nonempty :=
    ⟨z, ⟨1, (Work.EKLContract.Lemmas.V_open_one a hapos).2, by simp⟩⟩
  obtain ⟨zz, hzz, hU⟩ := hy.exists_mem_open hUopen hUne
  obtain ⟨n, rfl⟩ := hzz
  obtain ⟨u, hu, huz⟩ := Work.EKLComp.mem_Vball.mp hU
  -- lower semicontinuity of the injectivity radius at `z`
  have hlsc : injCap z / 16 ≤ injCap (y n) := by
    have h := injCap_mem_V_le (x := z) hapos hahalf ha8 hu
    rwa [huz] at h
  have hP16 : injCap z ≤ 16 * injCap (y n) := by linarith
  have hu10 : u⁻¹ ∈ V (10 * a) := Work.EKLComp.inv_mem_V hapos ha1 hu
  by_cases hn : n ∈ sel y
  · -- the dense point is itself selected
    refine ⟨n, hn, ?_⟩
    rw [cellBall_eq hn]
    have h10a : (10 : ℝ) * a ≤ cellRad μ y n := by
      have hstep : (10 : ℝ) * a ≤ cellLo (y n) := by
        rw [ha, cellLo]
        exact cellBall_cover_arith_sel (le_of_lt (injCap_pos (y n))) hP16
      exact le_trans hstep (cellRad_spec hn).1
    refine ⟨u⁻¹, Work.Misiurewicz.V_mono h10a hu10, ?_⟩
    show u⁻¹ • y n = z
    rw [← huz, ← mul_smul, inv_mul_cancel, one_smul]
  · -- otherwise the greedy maximality provides an earlier selected witness
    obtain ⟨j, hjn, hjs, hcase⟩ := exists_sel_witness y hn
    refine ⟨j, hjs, ?_⟩
    rw [cellBall_eq hjs]
    rcases hcase with hA | hB
    · -- `y n` lies in the separation ball of `y j`
      obtain ⟨w, hw, hwy⟩ := Work.EKLComp.mem_Vball.mp hA
      have hmem : u⁻¹ * w ∈ V (10 * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)) :=
        V_mul_subset_V (by linarith [hapos]) (le_of_lt (sepRad_pos (y j))) hu10 hw
      have hbound : (10 : ℝ) * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)
          ≤ cellRad μ y j := by
        have hsr8 : sepRad (y j) ≤ injCap (y j) / 8 := by
          rw [sepRad]
          exact div_le_div_of_nonneg_left (a := injCap (y j)) (b := 1048576) (c := 8)
            (le_of_lt (injCap_pos (y j))) (by norm_num) (by norm_num : (8 : ℝ) ≤ 1048576)
        have hQR : injCap (y n) ≤ 2 ^ 19 * injCap (y j) :=
          injCap_le_mul_of_mem_Vball (le_of_lt (sepRad_pos (y j))) hsr8 hA
        have harith := cellBall_cover_arith_A (P := injCap z) (Q := injCap (y n))
          (R := injCap (y j)) (le_of_lt (injCap_pos (y j))) (injCap_le_half (y j)) hP16 hQR
        have hsep : sepRad (y j) = injCap (y j) / 2 ^ 20 := by rw [sepRad]; norm_num
        have hgoal : (10 : ℝ) * a + sepRad (y j) + 3 * (10 * a) * sepRad (y j)
            ≤ cellLo (y j) := by
          rw [ha, hsep, cellLo]
          exact harith
        exact le_trans hgoal (cellRad_spec hjs).1
      refine ⟨u⁻¹ * w, Work.Misiurewicz.V_mono hbound hmem, ?_⟩
      show (u⁻¹ * w) • y j = z
      rw [mul_smul, hwy, ← huz, ← mul_smul, inv_mul_cancel, one_smul]
    · -- `y j` lies in the separation ball of `y n`
      obtain ⟨w, hw, hwy⟩ := Work.EKLComp.mem_Vball.mp hB
      have hwinv : w⁻¹ ∈ V (10 * sepRad (y n)) :=
        Work.EKLComp.inv_mem_V (sepRad_pos (y n)) (sepRad_le_one (y n)) hw
      have hmem : u⁻¹ * w⁻¹ ∈
          V (10 * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))) :=
        V_mul_subset_V (by linarith [hapos]) (by linarith [sepRad_pos (y n)]) hu10 hwinv
      have hbound : (10 : ℝ) * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))
          ≤ cellRad μ y j := by
        have hsn_half : sepRad (y n) ≤ 1 / 2 := by
          rw [sepRad]
          have h1 : injCap (y n) / 1048576 ≤ (1 / 2) / 1048576 :=
            div_le_div_of_nonneg_right (injCap_le_half (y n)) (by norm_num)
          have h2 : ((1 : ℝ) / 2) / 1048576 ≤ 1 / 2 := by norm_num
          linarith
        have hsn8 : sepRad (y n) ≤ injCap (y n) / 8 := by
          rw [sepRad]
          exact div_le_div_of_nonneg_left (a := injCap (y n)) (b := 1048576) (c := 8)
            (le_of_lt (injCap_pos (y n))) (by norm_num) (by norm_num : (8 : ℝ) ≤ 1048576)
        have hQR : injCap (y n) ≤ 16 * injCap (y j) := by
          have h := injCap_mem_V_le (x := y n) (a := sepRad (y n)) (sepRad_pos (y n))
            hsn_half hsn8 hw
          rw [hwy] at h
          linarith
        have harith := cellBall_cover_arith_B (P := injCap z) (Q := injCap (y n))
          (R := injCap (y j)) (le_of_lt (injCap_pos z)) (le_of_lt (injCap_pos (y n)))
          (le_of_lt (injCap_pos (y j))) (injCap_le_half (y j)) hP16 hQR
        have hsep : sepRad (y n) = injCap (y n) / 2 ^ 20 := by rw [sepRad]; norm_num
        have hgoal : (10 : ℝ) * a + 10 * sepRad (y n) + 3 * (10 * a) * (10 * sepRad (y n))
            ≤ cellLo (y j) := by
          rw [ha, hsep, cellLo]
          exact harith
        exact le_trans hgoal (cellRad_spec hjs).1
      refine ⟨u⁻¹ * w⁻¹, Work.Misiurewicz.V_mono hbound hmem, ?_⟩
      show (u⁻¹ * w⁻¹) • y j = z
      have hw1 : w⁻¹ • y j = y n := by rw [← hwy, ← mul_smul, inv_mul_cancel, one_smul]
      rw [mul_smul, hw1, ← huz, ← mul_smul, inv_mul_cancel, one_smul]

end Work.EKLC6Core
