import Mathlib
import Submission.Work.Drive.shiftedNeedleChart
import Submission.Work.Drive.needleShiftCore
import Submission.Work.Drive.crossv_expansion

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

theorem flatteningCore_of_chartData {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ}
    (hsm : ContDiff ℝ Work.Drive.cInfT (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε))
    (h : Work.Drive.ShiftedNeedleChartData r D lam δ₁ δ₂ ε) :
    Work.Drive.FlatteningCore (Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε) := by
  obtain ⟨e, v, y₀, he, hv, hev, -, -, hypos, -, hray, hang⟩ := h
  set w : Space := crossv e v with hwdef
  set c' : Space := chordEndA r D δ₂ ε + (nHeight r D lam δ₁ δ₂ ε e 0 - y₀) • e
      + (nCoord r D lam δ₁ δ₂ ε v 0) • v with hc'def
  -- basic orthogonality facts
  have hEe : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hVv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hve : inner ℝ v e = 0 := by rw [real_inner_comm]; exact hev
  have hwe : inner ℝ w e = 0 := by rw [hwdef]; exact inner_crossv_self e v
  have hwv : inner ℝ w v = 0 := by rw [hwdef]; exact inner_crossv_right e v
  have hew : inner ℝ e w = 0 := by rw [real_inner_comm]; exact hwe
  have hvw : inner ℝ v w = 0 := by rw [real_inner_comm]; exact hwv
  have hw1 : ‖w‖ = 1 := by rw [hwdef]; exact norm_crossv_of_orthonormal he hv hev
  -- the offset `c' - A` lies in the span of `(e, v)`
  have hcs : c' - chordEndA r D δ₂ ε
      = (nHeight r D lam δ₁ δ₂ ε e 0 - y₀) • e + nCoord r D lam δ₁ δ₂ ε v 0 • v := by
    rw [hc'def]; abel
  have hcw : inner ℝ (c' - chordEndA r D δ₂ ε) w = 0 := by
    rw [hcs, inner_add_left, real_inner_smul_left, real_inner_smul_left, hew, hvw, mul_zero,
      mul_zero, add_zero]
  have hce : inner ℝ (c' - chordEndA r D δ₂ ε) e = nHeight r D lam δ₁ δ₂ ε e 0 - y₀ := by
    rw [hcs, inner_add_left, real_inner_smul_left, real_inner_smul_left, hEe, hve, mul_one,
      mul_zero, add_zero]
  have hcv : inner ℝ (c' - chordEndA r D δ₂ ε) v = nCoord r D lam δ₁ δ₂ ε v 0 := by
    rw [hcs, inner_add_left, real_inner_smul_left, real_inner_smul_left, hev, hVv, mul_zero,
      mul_one, zero_add]
  -- coordinates of `N s - c'` in the frame `(e, v)`
  have hPe : ∀ s : ℝ, inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - c') e
      = nHeight r D lam δ₁ δ₂ ε e s - nHeight r D lam δ₁ δ₂ ε e 0 + y₀ := by
    intro s
    have hsplit : shiftedNeedle r D lam δ₁ δ₂ ε s - c'
        = (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε)
          - (c' - chordEndA r D δ₂ ε) := by abel
    rw [hsplit, inner_sub_left, hce]
    simp only [nHeight]
    ring
  have hPv : ∀ s : ℝ, inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - c') v
      = nCoord r D lam δ₁ δ₂ ε v s - nCoord r D lam δ₁ δ₂ ε v 0 := by
    intro s
    have hsplit : shiftedNeedle r D lam δ₁ δ₂ ε s - c'
        = (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε)
          - (c' - chordEndA r D δ₂ ε) := by abel
    rw [hsplit, inner_sub_left, hcv]
    simp only [nCoord]
  have hNw : ∀ s : ℝ, inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε) w
      = inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - c') w := by
    intro s
    have hsplit : shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε
        = (shiftedNeedle r D lam δ₁ δ₂ ε s - c') + (c' - chordEndA r D δ₂ ε) := by abel
    rw [hsplit, inner_add_left, hcw, add_zero]
  -- the fundamental chart identity for the projected needle
  have hkey : ∀ s : ℝ,
      projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) s - c'
        = (nHeight r D lam δ₁ δ₂ ε e s - nHeight r D lam δ₁ δ₂ ε e 0 + y₀) • e
          + (nCoord r D lam δ₁ δ₂ ε v s - nCoord r D lam δ₁ δ₂ ε v 0) • v := by
    intro s
    let P : Space := shiftedNeedle r D lam δ₁ δ₂ ε s - c'
    have hexpP : P = inner ℝ P e • e + inner ℝ P v • v + inner ℝ P w • w := by
      have h := crossv_expansion he hv hev (x := P)
      rw [← hwdef] at h
      exact h
    have hproj : projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) s - c'
        = (shiftedNeedle r D lam δ₁ δ₂ ε s - c')
          - inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - c') w • w := by
      rw [projectAlong, hNw s]
      abel
    have hPeP : inner ℝ P e = nHeight r D lam δ₁ δ₂ ε e s - nHeight r D lam δ₁ δ₂ ε e 0 + y₀ :=
      hPe s
    have hPvP : inner ℝ P v = nCoord r D lam δ₁ δ₂ ε v s - nCoord r D lam δ₁ δ₂ ε v 0 :=
      hPv s
    calc projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) s - c'
        = P - inner ℝ P w • w := hproj
      _ = (inner ℝ P e • e + inner ℝ P v • v + inner ℝ P w • w) - inner ℝ P w • w := by
            rw [← hexpP]
      _ = inner ℝ P e • e + inner ℝ P v • v := by abel
      _ = (nHeight r D lam δ₁ δ₂ ε e s - nHeight r D lam δ₁ δ₂ ε e 0 + y₀) • e
          + (nCoord r D lam δ₁ δ₂ ε v s - nCoord r D lam δ₁ δ₂ ε v 0) • v := by
            rw [hPeP, hPvP]
  have hpe : ∀ t : ℝ, inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε) t - c') e
      = nHeight r D lam δ₁ δ₂ ε e t - nHeight r D lam δ₁ δ₂ ε e 0 + y₀ := by
    intro t
    have h := congrArg (fun x : Space => inner ℝ x e) (hkey t)
    rw [h, inner_add_left, real_inner_smul_left, real_inner_smul_left, hEe, hve, mul_one,
      mul_zero, add_zero]
  have hpv : ∀ t : ℝ, inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε) t - c') v
      = nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0 := by
    intro t
    have h := congrArg (fun x : Space => inner ℝ x v) (hkey t)
    rw [h, inner_add_left, real_inner_smul_left, real_inner_smul_left, hev, hVv, mul_one,
      mul_zero, zero_add]
  have hne : ∀ t : ℝ, projectAlong w (chordEndA r D δ₂ ε)
      (shiftedNeedle r D lam δ₁ δ₂ ε) t ≠ c' := by
    intro t hEq
    have h1 : nHeight r D lam δ₁ δ₂ ε e t - nHeight r D lam δ₁ δ₂ ε e 0 + y₀ = 0 := by
      have hh := hpe t
      rw [hEq, sub_self] at hh
      simpa using hh.symm
    have h2 : nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0 = 0 := by
      have hh := hpv t
      rw [hEq, sub_self] at hh
      simpa using hh.symm
    have h3 := hang t
    rw [h1, h2] at h3
    simp only [zero_mul, sub_zero] at h3
    exact absurd h3 (lt_irrefl 0)
  have hMd : ∀ t : ℝ, DifferentiableAt ℝ (projectAlong w (chordEndA r D δ₂ ε)
      (shiftedNeedle r D lam δ₁ δ₂ ε)) t := fun t =>
    ((projectAlong_smooth hsm w (chordEndA r D δ₂ ε)).differentiable cInfT_ne_zero).differentiableAt
  have hde : ∀ t : ℝ, inner ℝ (deriv (projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε)) t) e = deriv (nHeight r D lam δ₁ δ₂ ε e) t := by
    intro t
    have hfun : (fun s : ℝ => inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε) e)
        = nHeight r D lam δ₁ δ₂ ε e := by
      funext s
      have hsub : projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) s
            - chordEndA r D δ₂ ε
          = (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε)
            - inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε) w • w := by
        rw [projectAlong]
        abel
      rw [hsub, inner_sub_left, real_inner_smul_left, hwe, mul_zero, sub_zero]
      simp only [nHeight]
    have hlin : deriv (fun s : ℝ => inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε) e) t
        = inner ℝ (deriv (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε)) t) e := by
      rw [deriv_inner_apply ℝ (f := fun s : ℝ => projectAlong w (chordEndA r D δ₂ ε)
            (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε)
          (g := fun _ : ℝ => e) ((hMd t).sub_const (chordEndA r D δ₂ ε))
          (differentiableAt_const e)]
      simp [deriv_const, deriv_sub_const]
    rw [← hlin, hfun]
  have hdv : ∀ t : ℝ, inner ℝ (deriv (projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε)) t) v = deriv (nCoord r D lam δ₁ δ₂ ε v) t := by
    intro t
    have hfun : (fun s : ℝ => inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε) v)
        = nCoord r D lam δ₁ δ₂ ε v := by
      funext s
      have hsub : projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) s
            - chordEndA r D δ₂ ε
          = (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε)
            - inner ℝ (shiftedNeedle r D lam δ₁ δ₂ ε s - chordEndA r D δ₂ ε) w • w := by
        rw [projectAlong]
        abel
      rw [hsub, inner_sub_left, real_inner_smul_left, hwv, mul_zero, sub_zero]
      simp only [nCoord]
    have hlin : deriv (fun s : ℝ => inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε) v) t
        = inner ℝ (deriv (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε)) t) v := by
      rw [deriv_inner_apply ℝ (f := fun s : ℝ => projectAlong w (chordEndA r D δ₂ ε)
            (shiftedNeedle r D lam δ₁ δ₂ ε) s - chordEndA r D δ₂ ε)
          (g := fun _ : ℝ => v) ((hMd t).sub_const (chordEndA r D δ₂ ε))
          (differentiableAt_const v)]
      simp [deriv_const, deriv_sub_const]
    rw [← hlin, hfun]
  refine ⟨w, chordEndA r D δ₂ ε, c', e, v, hw1, he, hv, hev, ?_, hne, ?_, ?_, ?_⟩
  · intro t
    rw [hpe t, hpv t]
    exact hkey t
  · -- the base point maps to the direction `(1, 0)`
    simp only [polarDir, polarCoord]
    have hM0 : projectAlong w (chordEndA r D δ₂ ε) (shiftedNeedle r D lam δ₁ δ₂ ε) 0 - c'
        = y₀ • e := by
      rw [hkey 0]
      simp
    have hnorm : ‖y₀ • e‖ = y₀ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hypos, he, mul_one]
    rw [hM0, hnorm, real_inner_smul_left, real_inner_smul_left, hEe, hev, mul_one, mul_zero,
      zero_div, div_self (ne_of_gt hypos)]
  · -- the single-ray condition
    intro t ht0 htp hDir
    have hnormne : ‖projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε) t - c'‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne t))
    have hC0 : nCoord r D lam δ₁ δ₂ ε v t - nCoord r D lam δ₁ δ₂ ε v 0 = 0 := by
      have h2 : polarCoord (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε)) c' v t = 0 := by
        have hh := congrArg Prod.snd hDir
        simpa [polarDir] using hh
      rw [polarCoord] at h2
      have h2' : inner ℝ (projectAlong w (chordEndA r D δ₂ ε)
            (shiftedNeedle r D lam δ₁ δ₂ ε) t - c') v = 0 := by
        rcases div_eq_zero_iff.mp h2 with hh | hh
        · exact hh
        · exact absurd hh hnormne
      rw [hpv t] at h2'
      exact h2'
    have hEeq : nHeight r D lam δ₁ δ₂ ε e t - nHeight r D lam δ₁ δ₂ ε e 0 + y₀
        = ‖projectAlong w (chordEndA r D δ₂ ε)
            (shiftedNeedle r D lam δ₁ δ₂ ε) t - c'‖ := by
      have h1 : polarCoord (projectAlong w (chordEndA r D δ₂ ε)
          (shiftedNeedle r D lam δ₁ δ₂ ε)) c' e t = 1 := by
        have hh := congrArg Prod.fst hDir
        simpa [polarDir] using hh
      rw [polarCoord, div_eq_one_iff_eq hnormne] at h1
      rw [← h1, hpe t]
    have hle := hray t ht0 htp (sub_eq_zero.mp hC0)
    have hz : ‖projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε) t - c'‖ = 0 := by
      linarith [norm_nonneg (projectAlong w (chordEndA r D δ₂ ε)
        (shiftedNeedle r D lam δ₁ δ₂ ε) t - c')]
    exact hne t (sub_eq_zero.mp (norm_eq_zero.mp hz))
  · -- the angular velocity
    intro t
    rw [angVel_num_eq (hMd t) (hne t)]
    rw [hpe t, hpv t, hde t, hdv t]
    exact div_pos (hang t)
      (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne t))))

end Work.Drive
