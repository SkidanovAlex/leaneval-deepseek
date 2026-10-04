import Mathlib
import Submission.Work.Diff.EXT.FlatPre

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Asymptotics
open scoped Topology

namespace Work.Diff.EXT

/-- Pointwise, the Heaviside cut `stepFun T γ` is bounded by `γ` in norm: it either vanishes or
agrees with `γ`. -/
theorem norm_stepFun_le {n : ℕ} {T : ℝ} {F : Type*} [NormedAddCommGroup F]
    (γ : ℝ × (Fin n → ℝ) → F) (p : ℝ × (Fin n → ℝ)) :
    ‖stepFun T γ p‖ ≤ ‖γ p‖ := by
  rw [stepFun_apply]; split_ifs with h
  · simp
  · exact le_rfl

/-- If `γ` is `C^1` on an open set `u` and its iterated derivatives all vanish at the points of the
hyperplane `{t = T}` lying in `u`, then its Heaviside cut `stepFun T γ` is differentiable on `u`,
with derivative the Heaviside cut of `fderiv γ` (so the derivative is `0` at the points of the
hyperplane). -/
theorem hasFDerivAt_stepFun
    {n : ℕ} {T : ℝ} {u : Set (ℝ × (Fin n → ℝ))}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ × (Fin n → ℝ) → F}
    (hu : IsOpen u) (hγ : ContDiffOn ℝ 1 γ u)
    (hflat : ∀ p ∈ u, p.1 = T → ∀ j : ℕ, iteratedFDeriv ℝ j γ p = 0) :
    ∀ y ∈ u, HasFDerivAt (stepFun T γ) (stepFun T (fderiv ℝ γ) y) y := by
  intro y hy
  have hyc : ContDiffAt ℝ 1 γ y := hγ.contDiffAt (hu.mem_nhds hy)
  have hdiff : DifferentiableAt ℝ γ y := hyc.differentiableAt (by norm_num)
  have hγat : HasFDerivAt γ (fderiv ℝ γ y) y := hdiff.hasFDerivAt
  rcases lt_trichotomy y.1 T with hlt | heq | hgt
  · -- `y.1 < T`: the cut agrees with `0` near `y` and its derivative is `0`.
    have hU : {p : ℝ × (Fin n → ℝ) | p.1 < T} ∈ 𝓝 y :=
      IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const) hlt
    have hstep : stepFun T γ =ᶠ[𝓝 y] (fun _ => (0 : F)) := by
      filter_upwards [hU] with p hp
      rw [stepFun_apply, ite_eq_left (le_of_lt hp)]
    have hder : stepFun T (fderiv ℝ γ) y = 0 := by
      rw [stepFun_apply, ite_eq_left (le_of_lt hlt)]
    rw [hder]
    exact hstep.hasFDerivAt_iff.mpr (hasFDerivAt_const 0 y)
  · -- `y.1 = T`: flatness gives `γ y = 0` and `fderiv γ y = 0`, and the cut is `o(‖· - y‖)`.
    have hγy : γ y = 0 := by
      have hmem := iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := γ) (x := y) (fun i : Fin 0 => i.elim0)
      rw [hflat y hy heq 0] at hmem
      simpa using hmem.symm
    have hfdy : fderiv ℝ γ y = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have hmem := iteratedFDeriv_one_apply (𝕜 := ℝ) (f := γ) (x := y) (m := fun _ : Fin 1 => v)
      rw [hflat y hy heq 1] at hmem
      simpa using hmem.symm
    have hγat0 : HasFDerivAt γ (0 : (ℝ × (Fin n → ℝ)) →L[ℝ] F) y := by
      simpa [hfdy] using hγat
    have hder : stepFun T (fderiv ℝ γ) y = 0 := by
      rw [stepFun_apply, ite_eq_left (le_of_eq heq)]
    rw [hder]
    have hγo : (fun p : ℝ × (Fin n → ℝ) => γ p) =o[𝓝 y] (fun p => p - y) := by
      have h := hγat0.isLittleO
      simpa [hγy] using h
    have hstep : (fun p : ℝ × (Fin n → ℝ) => stepFun T γ p) =o[𝓝 y] (fun p => p - y) := by
      rw [isLittleO_iff] at hγo ⊢
      intro c hc
      filter_upwards [hγo hc] with p hp
      calc ‖stepFun T γ p‖ ≤ ‖γ p‖ := norm_stepFun_le γ p
        _ ≤ c * ‖p - y‖ := hp
    have hsy2 : (if y.1 ≤ T then (0 : F) else γ y) = 0 := by
      rw [ite_eq_left (le_of_eq heq)]
    refine HasFDerivAt.of_isLittleO ?_
    simpa [hsy2] using hstep
  · -- `T < y.1`: the cut agrees with `γ` near `y`.
    have hU : {p : ℝ × (Fin n → ℝ) | T < p.1} ∈ 𝓝 y :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) hgt
    have hstep : stepFun T γ =ᶠ[𝓝 y] γ := by
      filter_upwards [hU] with p hp
      rw [stepFun_apply, ite_eq_right (not_le.mpr hp)]
    have hder : stepFun T (fderiv ℝ γ) y = fderiv ℝ γ y := by
      rw [stepFun_apply, ite_eq_right (not_le.mpr hgt)]
    rw [hder]
    exact hstep.hasFDerivAt_iff.mpr hγat

end Work.Diff.EXT
