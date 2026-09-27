import Mathlib
import Submission.Work.KT.Dim2.log_nullhomotopic
import Submission.Work.KT.Dim2.nullhomotopic_log

/-!
# Continuous logarithms of loops in `ℂ*`

This file establishes three facts about continuous logarithms of loops in the units of `ℂ`
(the unit circle sitting inside `ℂˣ`), used in the degree-two part of the K-theoretic proof.

* `Work.KT.Dim2.log_nullhomotopic`: a map `f : S¹ → ℂˣ` admitting a continuous logarithm
  `F : S¹ → ℂ` (i.e. `exp ∘ F = f`) is null-homotopic, via the straight-line homotopy
  `(t, z) ↦ exp ((1 - t) * F z)`.
* `Work.KT.Dim2.nullhomotopic_log`: conversely, a map `S¹ → ℂˣ` homotopic to the constant `1`
  lifts through the exponential covering `exp : ℂ → ℂˣ`, hence admits a continuous logarithm.
* `zpowLogZero` / `zpowLogExists` (here): for `k : ℤ` the loop `z ↦ z ^ k` on the unit circle
  admits a continuous logarithm if and only if `k = 0` (a degree / winding-number statement).

The first two are the two halves of the classical equivalence "a loop in `ℂˣ` admits a
continuous logarithm iff it is null-homotopic"; the third identifies the degree of the loop
`z ↦ z ^ k` as `k`.  All of it rests on Mathlib's covering-space lifting theory
(`IsCoveringMap.liftHomotopy`, `IsCoveringMap.eq_of_comp_eq`) applied to
`Complex.isCoveringMap_exp`.
-/

namespace Work.KT.Dim2

open Complex Metric

noncomputable section

/-- The unit circle in `ℂ`, as a type. -/
abbrev circC : Type := Metric.sphere (0 : ℂ) 1

/-- The nonzero complex numbers, as a type. -/
abbrev nzC : Type := {z : ℂ // z ≠ 0}

/-- The exponential map `ℂ → ℂ \ {0}`, as a function into the subtype of nonzero complexes. -/
abbrev expSub : ℂ → nzC := fun w => ⟨Complex.exp w, Complex.exp_ne_zero w⟩

/-! ## The degree of `z ↦ z ^ k` -/

/-- The standard loop `t ↦ exp (2πi t)` on the unit circle, based at `1`. -/
private def stdLoop : C(unitInterval, circC) :=
  ⟨fun t => ⟨Complex.exp (2 * Real.pi * Complex.I * (t:ℂ)), by
      rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]; simp⟩,
   Continuous.subtype_mk (by fun_prop) (fun t => by
      rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]; simp)⟩

private theorem stdLoop_coe (t : unitInterval) :
    (stdLoop t : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (t:ℂ)) := rfl

private theorem stdLoop_zero : (stdLoop 0 : ℂ) = 1 := by simp [stdLoop]

private theorem stdLoop_one : (stdLoop 1 : ℂ) = 1 := by
  rw [stdLoop_coe]
  have h : Complex.exp (2 * Real.pi * Complex.I * ((1:unitInterval):ℂ))
      = Complex.exp (2 * Real.pi * Complex.I) := by simp
  rw [h]
  have h2 : Complex.exp (2 * Real.pi * Complex.I) = Complex.exp 0 := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨1, by ring⟩
  simpa using h2

private theorem stdLoop_eq : stdLoop 1 = stdLoop 0 := by
  apply Subtype.ext
  rw [stdLoop_one, stdLoop_zero]

/-- If `z ↦ z ^ k` on the unit circle admits a continuous logarithm, then `k = 0`.

Indeed a logarithm `F` of `z ↦ z ^ k` restricts along the standard loop `t ↦ exp (2πi t)` to a
lift of the path `t ↦ exp (2πi k t)`; comparing it with the explicit lift `t ↦ F 1 + 2πi k t`
(these agree at `t = 0`, and lifts of a path through a covering map that agree at one point of the
connected interval `I` agree everywhere) and evaluating at `t = 1` forces `2πi·k = 0`. -/
private theorem zpowLogZero (k : ℤ)
    (h : ∃ F : C(circC, ℂ), ∀ z, Complex.exp (F z) = (z : ℂ) ^ k) : k = 0 := by
  obtain ⟨F, hF⟩ := h
  have cov : IsCoveringMap expSub := Complex.isCoveringMap_exp
  -- the exponent of the lifted loop
  let w : C(unitInterval, ℂ) :=
    ⟨fun t => (2 * Real.pi * Complex.I) * ((k : ℂ) * (t : ℂ)), by fun_prop⟩
  -- the two lifts of `t ↦ exp (2πi k t)`
  let g₁ : C(unitInterval, ℂ) := F.comp stdLoop
  let g₂ : C(unitInterval, ℂ) := ⟨fun t => F (stdLoop 0) + w t, by fun_prop⟩
  have he : expSub ∘ g₁ = expSub ∘ g₂ := by
    funext t
    apply Subtype.ext
    show Complex.exp (F (stdLoop t)) = Complex.exp (F (stdLoop 0) + w t)
    have e2 : (Complex.exp (2 * Real.pi * Complex.I * (t:ℂ)))^k = Complex.exp (w t) := by
      rw [← Complex.exp_int_mul]
      congr 1
      simp only [w, ContinuousMap.coe_mk]
      ring
    have e3 : Complex.exp (F (stdLoop 0)) = 1 := by
      rw [hF, stdLoop_zero, one_zpow]
    calc Complex.exp (F (stdLoop t)) = (stdLoop t : ℂ) ^ k := hF (stdLoop t)
      _ = Complex.exp (w t) := by rw [stdLoop_coe]; exact e2
      _ = Complex.exp (F (stdLoop 0) + w t) := by rw [Complex.exp_add, e3, one_mul]
  have h0 : g₁ 0 = g₂ 0 := by
    show F (stdLoop 0) = F (stdLoop 0) + w 0
    simp [w]
  have hge := cov.eq_of_comp_eq g₁.continuous g₂.continuous he 0 h0
  have hg := congr_fun hge 1
  simp only [g₁, g₂, ContinuousMap.comp_apply, stdLoop_eq, w, ContinuousMap.coe_mk] at hg
  have hz : (2 * Real.pi * Complex.I) * (k : ℂ) = 0 := by
    have h' : F (stdLoop 0) = F (stdLoop 0) + (2 * Real.pi * Complex.I) * (↑k * (1:ℂ)) := hg
    have h'' := congrArg (fun y : ℂ => y - F (stdLoop 0)) h'
    simpa [mul_one] using h''.symm
  exact Int.cast_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Complex.two_pi_I_ne_zero)

/-- For `k = 0` the constant logarithm `0` realises `z ↦ z ^ k = 1`. -/
private theorem zpowLogExists (k : ℤ) (hk : k = 0) :
    ∃ F : C(circC, ℂ), ∀ z, Complex.exp (F z) = (z : ℂ) ^ k := by
  subst hk
  exact ⟨ContinuousMap.const circC 0, fun z => by simp⟩

/-- Facts about continuous logarithms of loops in `ℂ*` (the unit circle as the target). -/
theorem circle_log_facts :
    (∀ f : C(Metric.sphere (0 : ℂ) 1, ℂˣ),
      (∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = (f z : ℂ)) →
      ContinuousMap.Homotopic f (ContinuousMap.const _ 1)) ∧
    (∀ f : C(Metric.sphere (0 : ℂ) 1, ℂˣ),
      ContinuousMap.Homotopic f (ContinuousMap.const _ 1) →
      ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = (f z : ℂ)) ∧
    (∀ k : ℤ, (∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ), ∀ z, Complex.exp (F z) = (z : ℂ) ^ k) ↔ k = 0) :=
  ⟨log_nullhomotopic, nullhomotopic_log,
    fun k => ⟨zpowLogZero k, zpowLogExists k⟩⟩

end

end Work.KT.Dim2
