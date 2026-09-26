import Mathlib
import Submission.Work.Drive.qwDefs

namespace Work.Drive

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The window box is compact** (strict form).

`qBox k` is the set of windows `τ = (a,z,w,b)` with `a ∈ [0, 2π]`, the three gaps `z - a`, `w - z`,
`b - w` at least `1/(k+1)`, and the total length `b - a` at most `2π - 1/(k+1)`.  (This replaces an
earlier version with the weaker bound `b - a ≤ 2π`, which admitted the degenerate face
`b = a + period`, where the four points are not distinct and the bad-set argument fails.)  Each
coordinate is squeezed between `0` and `4π`, and the defining conditions are closed, so `qBox k` is a
closed subset of a compact coordinate box, hence compact. -/
theorem qBox_compact (k : ℕ) : IsCompact (qBox k) := by
  -- The compact coordinate box `[0, 4π]⁴`, transported to `QP` along the coordinate equivalence.
  have hK : IsCompact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm ''
      Set.Icc (0 : Fin 4 → ℝ) (fun _ => 4 * Real.pi)) :=
    isCompact_Icc.image (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.continuous
  refine IsCompact.of_isClosed_subset hK ?_ ?_
  · -- `qBox k` is closed: an intersection of five preimages of closed intervals under the
    -- continuous coordinate-and-gap maps.
    have h1 : IsClosed {τ : QP | qA τ ∈ Set.Icc (0:ℝ) (2*Real.pi)} :=
      isClosed_Icc.preimage contDiff_qA.continuous
    have h2 : IsClosed {τ : QP | (1:ℝ)/(k+1) ≤ qZ τ - qA τ} :=
      isClosed_Ici.preimage (contDiff_qZ.continuous.sub contDiff_qA.continuous)
    have h3 : IsClosed {τ : QP | (1:ℝ)/(k+1) ≤ qW τ - qZ τ} :=
      isClosed_Ici.preimage (contDiff_qW.continuous.sub contDiff_qZ.continuous)
    have h4 : IsClosed {τ : QP | (1:ℝ)/(k+1) ≤ qB τ - qW τ} :=
      isClosed_Ici.preimage (contDiff_qB.continuous.sub contDiff_qW.continuous)
    have h5 : IsClosed {τ : QP | qB τ - qA τ ≤ 2*Real.pi - (1:ℝ)/(k+1)} :=
      isClosed_Iic.preimage (contDiff_qB.continuous.sub contDiff_qA.continuous)
    have heq : qBox k = {τ : QP | qA τ ∈ Set.Icc (0:ℝ) (2*Real.pi)} ∩
        ({τ : QP | (1:ℝ)/(k+1) ≤ qZ τ - qA τ} ∩
        ({τ : QP | (1:ℝ)/(k+1) ≤ qW τ - qZ τ} ∩
        ({τ : QP | (1:ℝ)/(k+1) ≤ qB τ - qW τ} ∩
         {τ : QP | qB τ - qA τ ≤ 2*Real.pi - (1:ℝ)/(k+1)}))) := rfl
    rw [heq]
    exact h1.inter (h2.inter (h3.inter (h4.inter h5)))
  · -- `qBox k` sits inside the coordinate box: the gaps push every coordinate above `0`, and the
    -- total-length bound (with `a ≤ 2π`) pushes them below `4π`.
    intro τ hτ
    refine ⟨PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ) τ, ?_, ?_⟩
    · rw [Set.mem_Icc]
      unfold qBox at hτ
      obtain ⟨ha, hz, hw, hb, htot⟩ := hτ
      have hc : (0:ℝ) < 1/(↑k+1) := by positivity
      constructor
      · intro i
        fin_cases i
        · show (0:ℝ) ≤ qA τ
          linarith [ha.1]
        · show (0:ℝ) ≤ qZ τ
          linarith [ha.1, hc, hz]
        · show (0:ℝ) ≤ qW τ
          linarith [ha.1, hc, hz, hw]
        · show (0:ℝ) ≤ qB τ
          linarith [ha.1, hc, hz, hw, hb]
      · intro i
        fin_cases i
        · show qA τ ≤ 4 * Real.pi
          linarith [ha.2, Real.pi_pos]
        · show qZ τ ≤ 4 * Real.pi
          linarith [ha.1, ha.2, hc, hz, hw, hb, htot, Real.pi_pos]
        · show qW τ ≤ 4 * Real.pi
          linarith [ha.1, ha.2, hc, hz, hw, hb, htot, Real.pi_pos]
        · show qB τ ≤ 4 * Real.pi
          linarith [ha.1, ha.2, hc, hz, hw, hb, htot, Real.pi_pos]
    · simp

end Work.Drive
