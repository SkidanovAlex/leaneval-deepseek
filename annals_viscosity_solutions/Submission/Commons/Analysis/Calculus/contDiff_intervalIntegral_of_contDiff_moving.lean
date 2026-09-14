import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_upper_piece_of_continuous

namespace Commons.Analysis.Calculus

open Filter MeasureTheory
open scoped Topology Interval ContDiff

/-- The partial derivative of `fun p : ℝ × ℝ => F p.1 p.2` with respect to the first
variable is smooth when the original function is smooth. -/
lemma contDiff_fderiv_fst_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ ∞
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) p (1, 0)) := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ ∞ G := hF
  have hfd : ContDiff ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ G q) := by
    exact hG.fderiv_right (m := ∞) (by simp)
  have hvec : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))) := by
    exact contDiff_const
  have hcomp := hfd.clm_apply hvec
  simpa [G] using hcomp

/-- The derivative of `v ↦ F v t` is the partial derivative with respect to the first
variable, evaluated at `(u, t)` and the vector `(1, 0)`. -/
lemma hasDerivAt_fderiv_fst_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t)
      (fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (u, t) (1, 0)) u := by
  intro u t
  let G : ℝ × ℝ → ℝ := fun p => F p.1 p.2
  have hG : ContDiff ℝ ∞ G := hF
  have hdiff : DifferentiableAt ℝ G (u, t) := by
    exact (hG.contDiffAt (n := ∞) (x := (u, t))).differentiableAt (by norm_num)
  have hGfderiv := hdiff.hasFDerivAt
  have hγ : HasDerivAt (fun v : ℝ => (v, t)) (1, 0) u := by
    exact (hasDerivAt_id u).prodMk (hasDerivAt_const u t)
  have hcomp := hGfderiv.comp_hasDerivAt u hγ
  have hfun : (fun v : ℝ => F v t) = G ∘ (fun v : ℝ => (v, t)) := by
    funext v; rfl
  have hmain : HasDerivAt (fun v : ℝ => F v t) (fderiv ℝ G (u, t) (1, 0)) u := by
    rw [hfun]
    exact hcomp
  simpa [G] using hmain

/-- The total derivative of `(s, u) ↦ ∫ t in 0..u, F s t`, when the lower endpoint is fixed
at `0` and `F` is smooth. -/
lemma intervalIntegral_hasFDerivAt_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..p.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (p.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F p.1 p.2))) p := by
  let F' : ℝ → ℝ → ℝ := fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
  have hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := hF.continuous
  have hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
    have hF' : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F' p.1 p.2) := by
      simpa [F'] using (contDiff_fderiv_fst_of_contDiff hF)
    exact hF'.continuous
  have hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u := by
    simpa [F'] using hasDerivAt_fderiv_fst_of_contDiff hF
  have h := intervalIntegral_hasFDerivAt_upper_of_continuous'
    (a := (0:ℝ)) (b := p.2) (x₀ := p.1) (F := F) (F' := F')
    hF_cont hF'_cont hF'_isDeriv
  simpa [F'] using h

/-- Continuity of `(s, u) ↦ ∫ t in 0..u, F s t` for a smooth `F`. -/
lemma continuous_intervalIntegral_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) := by
  let f₂ : (ℝ × ℝ) → ℝ → ℝ := fun p t => F p.1 t
  have hf₂cont : Continuous (Function.uncurry f₂) := by
    have hfun : Function.uncurry f₂ = fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.2 := by
      ext q; rfl
    rw [hfun]
    exact hF.continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := f₂) (a₀ := (0:ℝ)) (μ := MeasureTheory.volume) (s := fun q : ℝ × ℝ => q.2)
    hf₂cont continuous_snd
  simpa [f₂] using hcont

/-- The `C^0` version of the fixed-lower smoothness theorem. -/
lemma contDiffAt_zero_intervalIntegral_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (p : ℝ × ℝ) :
    ContDiffAt ℝ 0 (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) p := by
  rw [contDiffAt_zero]
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  exact (continuous_intervalIntegral_fixedLower_of_contDiff hF).continuousOn

/-- Smoothness of the derivative candidate for the fixed-lower interval integral. -/
lemma contDiffAt_fderiv_intervalIntegral_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    {n : ℕ} {p : ℝ × ℝ}
    (hφD : ContDiffAt ℝ n
      (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2,
        fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)) p) :
    ContDiffAt ℝ n
      (fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2))) p := by
  have hfst : ContDiffAt ℝ n (fun _ : ℝ × ℝ => ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    contDiffAt_const
  have h1 : ContDiffAt ℝ n
      (fun q : ℝ × ℝ => (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (∫ t in (0:ℝ)..q.2,
          fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0))) p := by
    exact hfst.smulRight hφD
  have hsnd : ContDiffAt ℝ n (fun _ : ℝ × ℝ => ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    contDiffAt_const
  have hG : ContDiffAt ℝ n (fun q : ℝ × ℝ => F q.1 q.2) p := by
    have hle : (n : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
    exact (hF.contDiffAt (n := ∞) (x := p)).of_le hle
  have h2 : ContDiffAt ℝ n
      (fun q : ℝ × ℝ => (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)) p := by
    exact hsnd.smulRight hG
  exact h1.add h2

/-- Induction step for the fixed-lower smoothness theorem. -/
lemma contDiffAt_succ_intervalIntegral_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (p : ℝ × ℝ) :
    ∀ n : ℕ, ContDiffAt ℝ (n + 1)
      (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) p := by
  intro n
  induction n generalizing F with
  | zero =>
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)), ?_, ?_⟩
      · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro q hq
        exact intervalIntegral_hasFDerivAt_fixedLower_of_contDiff hF q
      · let D : ℝ → ℝ → ℝ :=
          fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
        have hDcurry : ContDiff ℝ ∞ (fun p : ℝ × ℝ => D p.1 p.2) := by
          simpa [D] using contDiff_fderiv_fst_of_contDiff hF
        exact contDiffAt_fderiv_intervalIntegral_fixedLower_of_contDiff hF
          (by simpa [D] using (contDiffAt_zero_intervalIntegral_fixedLower_of_contDiff hDcurry p))
  | succ n ih =>
      rw [contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fun q : ℝ × ℝ =>
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (∫ t in (0:ℝ)..q.2,
            fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (q.1, t) (1, 0)))
        + ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F q.1 q.2)), ?_, ?_⟩
      · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        intro q hq
        exact intervalIntegral_hasFDerivAt_fixedLower_of_contDiff hF q
      · let D : ℝ → ℝ → ℝ :=
          fun u t => fderiv ℝ (fun r : ℝ × ℝ => F r.1 r.2) (u, t) (1, 0)
        have hDcurry : ContDiff ℝ ∞ (fun p : ℝ × ℝ => D p.1 p.2) := by
          simpa [D] using contDiff_fderiv_fst_of_contDiff hF
        have hφD : ContDiffAt ℝ (n + 1)
            (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, D q.1 t) p := by
          simpa [Nat.cast_add, Nat.cast_one] using (ih hDcurry)
        exact contDiffAt_fderiv_intervalIntegral_fixedLower_of_contDiff hF
          (by simpa [D] using hφD)

/-- The fixed-lower, moving-upper interval integral
`(s, u) ↦ ∫ t in 0..u, F s t` is smooth when `F` is smooth. -/
lemma contDiff_intervalIntegral_fixedLower_of_contDiff
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2)) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, F q.1 t) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  rw [contDiffAt_infty]
  intro m
  cases m with
  | zero => exact contDiffAt_zero_intervalIntegral_fixedLower_of_contDiff hF p
  | succ k => exact contDiffAt_succ_intervalIntegral_fixedLower_of_contDiff hF p k

/-- Split an interval integral at `0`, so that both pieces have fixed lower endpoint `0`. -/
lemma intervalIntegral_eq_sub_fixedZero_of_continuous
    {F : ℝ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (a b s : ℝ) :
    (∫ t in a..b, F s t) = (∫ t in (0:ℝ)..b, F s t) - (∫ t in (0:ℝ)..a, F s t) := by
  have hcont : Continuous (fun t : ℝ => F s t) := by
    exact hF.continuous.comp
      ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (s, t)))
  have hInt0a : IntervalIntegrable (fun t : ℝ => F s t) MeasureTheory.volume (0:ℝ) a :=
    hcont.intervalIntegrable _ _
  have hIntab : IntervalIntegrable (fun t : ℝ => F s t) MeasureTheory.volume a b :=
    hcont.intervalIntegrable _ _
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (f := fun t : ℝ => F s t) (a := (0:ℝ)) (b := a) (c := b) hInt0a hIntab
  linarith

lemma contDiff_intervalIntegral_of_contDiff_moving
    {F : ℝ → ℝ → ℝ} {a b : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun s : ℝ => ∫ t in (a s)..(b s), F s t) := by
  have hφ := contDiff_intervalIntegral_fixedLower_of_contDiff hF
  have hbvec : ContDiff ℝ ∞ (fun s : ℝ => (s, b s)) := by
    exact contDiff_id.prodMk hb
  have havec : ContDiff ℝ ∞ (fun s : ℝ => (s, a s)) := by
    exact contDiff_id.prodMk ha
  have hdiff := (hφ.comp hbvec).sub (hφ.comp havec)
  rw [contDiff_iff_contDiffAt]
  intro x
  apply (hdiff.contDiffAt (x := x)).congr_of_eventuallyEq
  filter_upwards with s
  exact intervalIntegral_eq_sub_fixedZero_of_continuous hF (a s) (b s) s

end Commons.Analysis.Calculus