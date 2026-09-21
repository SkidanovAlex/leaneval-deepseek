import Mathlib
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.Existence.window_C1_state

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The `i`-th coordinate of `deriv Z s` is the derivative of the `i`-th coordinate function. -/
lemma deriv_apply_coord {Z : ℝ → Work.OddVolterra.St} {s : ℝ} (hZ : DifferentiableAt ℝ Z s)
    (i : Fin 4) : deriv Z s i = deriv (fun u : ℝ => Z u i) s := by
  have h := fderiv_apply (𝕜 := ℝ) hZ i
  simp only [deriv]
  rw [h]
  rfl

/-- The unperturbed state is smooth. -/
lemma contDiff_baseState :
    ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX.iterate_deriv 1
  · show ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s)
    exact Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX.iterate_deriv 1

lemma differentiableAt_baseState (s : ℝ) :
    DifferentiableAt ℝ (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s :=
  (contDiff_baseState.differentiable (by simp)).differentiableAt

/-- The `2`-component of the derivative of the ball's state is the second derivative of
`profileX`. -/
lemma deriv_baseState_two (s : ℝ) :
    deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 2 =
      deriv (deriv Commons.Geometry.Ulam.profileX) s := by
  rw [deriv_apply_coord (differentiableAt_baseState s) 2]
  rfl

lemma deriv_baseState_three (s : ℝ) :
    deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 3 =
      deriv (deriv Commons.Geometry.Ulam.profileX) s := by
  rw [deriv_apply_coord (differentiableAt_baseState s) 3]
  rfl

/-- **The state-level window solution of Step 2, at class `C^{n+3}`.**

This is `Work.OddVolterra.Existence.window_C1_state` (the `C¹`-close state solution of the
paper's system on the transition window) specialised to the six componentwise `1/1000`-bounds
that `WindowSolutionThree` asks for: the `dist`-bounds on the state and on its derivative give
respectively the four `0,1,2,3`-bounds and the two second-order bounds on the derivatives of
the components `2,3` (which are the derivatives of the components `0,1`). -/
theorem window_solution_three (n : ℕ) (hn : 1 ≤ n) :
    Work.OddVolterra.Existence.WindowSolutionThree n := by
  obtain ⟨ε, hε, H⟩ := window_C1_state n hn
  refine ⟨ε, hε, ?_⟩
  intro h hb h0 hne
  obtain ⟨Z, hsm, hsys, htail, hclose, hder, hsign⟩ := H h hb h0 hne
  refine ⟨Z, hsm, hsys, htail, ?_, hder, hsign⟩
  intro s hs
  obtain ⟨hcd, hdd⟩ := hclose s hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hZs : DifferentiableAt ℝ Z s :=
    (hsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hs0)
  have hbnd : ∀ i : Fin 4, |Z s i - Work.OddVolterra.baseState s i| ≤ 1 / 1000 := by
    intro i
    have h1 : ‖(Z s - Work.OddVolterra.baseState s) i‖ ≤ ‖Z s - Work.OddVolterra.baseState s‖ :=
      norm_le_pi_norm _ i
    have h3 : (Z s - Work.OddVolterra.baseState s) i =
        Z s i - Work.OddVolterra.baseState s i := rfl
    rw [h3, Real.norm_eq_abs] at h1
    have h2 : ‖Z s - Work.OddVolterra.baseState s‖ ≤ 1 / 2000 := by
      simpa [dist_eq_norm] using hcd
    linarith
  have hbnd2 : ∀ i : Fin 4,
      |deriv Z s i - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s i|
        ≤ 1 / 1000 := by
    intro i
    have h1 : ‖(deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) i‖
        ≤ ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖ :=
      norm_le_pi_norm _ i
    have h3 : (deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s) i =
        deriv Z s i - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s i := rfl
    rw [h3, Real.norm_eq_abs] at h1
    have h2 : ‖deriv Z s - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s‖
        ≤ 1 / 2000 := by
      simpa [dist_eq_norm] using hdd
    linarith
  have hb0 : Work.OddVolterra.baseState s 0 = Commons.Geometry.Ulam.profileX s := rfl
  have hb1 : Work.OddVolterra.baseState s 1 = Commons.Geometry.Ulam.profileX s := rfl
  have hb2 : Work.OddVolterra.baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := rfl
  have hb3 : Work.OddVolterra.baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := rfl
  have hd2 : deriv (fun u : ℝ => Z u 2) s - deriv (deriv Commons.Geometry.Ulam.profileX) s
      = deriv Z s 2 - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 2 := by
    rw [deriv_apply_coord hZs 2, deriv_baseState_two]
  have hd3 : deriv (fun u : ℝ => Z u 3) s - deriv (deriv Commons.Geometry.Ulam.profileX) s
      = deriv Z s 3 - deriv (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) s 3 := by
    rw [deriv_apply_coord hZs 3, deriv_baseState_three]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hbnd 0; rw [hb0] at this; linarith
  · have := hbnd 2; rw [hb2] at this; linarith
  · rw [hd2]; exact hbnd2 2
  · have := hbnd 1; rw [hb1] at this; linarith
  · have := hbnd 3; rw [hb3] at this; linarith
  · rw [hd3]; exact hbnd2 3

end

end Work.OddVolterra.Existence
