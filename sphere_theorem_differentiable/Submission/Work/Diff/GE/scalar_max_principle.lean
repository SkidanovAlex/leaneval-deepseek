import Mathlib
import Submission.Work.Diff.GE.smp_defs
import Submission.Work.Diff.GE.smp_aux
import Submission.Work.Diff.GE.smp_crux

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. The classical maximum principle. Let v(t,x) = e^{−C₁t}u − (max B 0) − C₂t − ε(1+t). Then v(0) < 0.
Suppose v first reaches 0 at (t₀, x₀), a spatial maximum of v(t₀,·) on compact M. There ∂ₜv ≥ 0 (one-sided in t) and
Δv ≤ 0: at a max, the gradient vanishes and hessAt is ≤ 0 on every vector, since the Hessian at a critical point is the
second derivative along any curve. The differential inequality gives a contradiction. Then let ε → 0.
The Hessian at a critical point is independent of the connection term, because mvfderiv u x = 0 there.

IMPLEMENTATION (this file).  The barrier `v = smpBarrier u C₁ C₂ (max B 0) ε` is considered on the
COMPACT box `[0,t] × M` rather than via a "first hitting time": if the barrier is positive at `(t,x)`
it attains a positive maximum `(t₀,x₀)` there with `0 < t₀ < T` (`exists_barrier_max`).  At `x₀`, the
slice `u t₀` has its maximum on `M` and is a critical point, so `laplAt (G t₀) (u t₀) x₀ ≤ 0`
(`hessAt_self_nonpos_of_isCriticalMax`, summed over the frame `onFrame` — note that no orthonormality
of that frame is needed, since every single diagonal is nonpositive).  The one-sided sign rule
`nonneg_of_hasDerivWithinAt_Ico` applied to `s ↦ smpBarrier u C₁ C₂ (max B 0) ε (s, x₀)` gives
`∂ₜv ≥ 0` at `t₀`, and the differential inequality `d t x ≤ Δu + C₁ max(u,0) + C₂` together with
`u t₀ x₀ ≥ 0` and `Δu ≤ 0` is contradictory with `ε > 0`.  Finally `ε → 0`.
-/

namespace Work.Diff.GE

set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter VectorField CovariantDerivative Metric

theorem scalar_max_principle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) :
    ScalarMaxPrinciple I M := by
  intro G T u d C₁ C₂ B hJS hC₁ hC₂ hu hineq hinit
  intro t ht x
  obtain ⟨htge, htT⟩ := mem_Ico.mp ht
  by_cases hT : T ≤ 0
  · exact absurd (lt_of_lt_of_le htT hT) (not_lt.mpr htge)
  -- it suffices to prove the bound with an extra `ε (1+t)`, and then let `ε → 0`
  suffices hmain : ∀ ε : ℝ, 0 < ε →
      u t x ≤ Real.exp (C₁ * t) * (max B 0 + C₂ * t + ε * (1 + t)) by
    have hKpos : 0 < Real.exp (C₁ * t) * (1 + t) :=
      mul_pos (Real.exp_pos _) (by linarith)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hδ' : 0 < δ / (Real.exp (C₁ * t) * (1 + t)) := div_pos hδ hKpos
    have h1 := hmain _ hδ'
    have h2 : Real.exp (C₁ * t)
          * (max B 0 + C₂ * t + δ / (Real.exp (C₁ * t) * (1 + t)) * (1 + t))
        = Real.exp (C₁ * t) * (max B 0 + C₂ * t) + δ := by
      field_simp
    rw [h2] at h1
    exact h1
  intro ε hε
  by_contra hcon
  rw [not_le] at hcon
  -- the barrier is positive at `(t,x)`
  have hVpos : 0 < smpBarrier u C₁ C₂ (max B 0) ε (t, x) := by
    simp only [smpBarrier]
    have h1 : Real.exp (-(C₁ * t)) * (Real.exp (C₁ * t) * (max B 0 + C₂ * t + ε * (1 + t)))
        < Real.exp (-(C₁ * t)) * u t x := mul_lt_mul_of_pos_left hcon (Real.exp_pos _)
    have h2 : Real.exp (-(C₁ * t)) * (Real.exp (C₁ * t) * (max B 0 + C₂ * t + ε * (1 + t)))
        = max B 0 + C₂ * t + ε * (1 + t) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [h2] at h1
    nlinarith [h1]
  -- the positive maximum of the barrier on the compact box `[0,t] × M`
  obtain ⟨t₀, x₀, ht₀pos, ht₀T, hU, hmaxu, hslice, hbar⟩ :=
    exists_barrier_max u hC₂ hε ⟨htge, htT⟩ hinit hu hVpos
  -- at `x₀` the slice `u t₀` is critical and the Laplacian is nonpositive
  have hcrit : mvfderiv I (u t₀) x₀ = 0 :=
    Smp.mvfderiv_eq_zero_of_isMax (u t₀) hslice x₀ hmaxu
  have hlapl : laplAt (G t₀) (u t₀) x₀ ≤ 0 := by
    rw [laplAt]
    refine Finset.sum_nonpos fun i _ => ?_
    exact Smp.hessAt_self_nonpos_of_isCriticalMax (G t₀) (u t₀) hslice x₀ hcrit hmaxu
      (onFrame (G t₀) x₀ i)
  -- the differential inequality at `(t₀,x₀)`
  obtain ⟨hder, hineq2⟩ := hineq t₀ ⟨le_of_lt ht₀pos, ht₀T⟩ x₀
  -- the one-sided time derivative of the barrier
  have hexp : HasDerivWithinAt (fun a : ℝ => Real.exp (-(C₁ * a)))
      (-(C₁ * Real.exp (-(C₁ * t₀)))) (Ico 0 T) t₀ :=
    (hasDerivAt_exp_neg_mul C₁ t₀).hasDerivWithinAt
  have haff : HasDerivWithinAt (fun a : ℝ => max B 0 + C₂ * a + ε * (1 + a)) (C₂ + ε)
      (Ico 0 T) t₀ :=
    (hasDerivAt_affine_barrier B C₂ ε t₀).hasDerivWithinAt
  have hprod : HasDerivWithinAt (fun a : ℝ => u a x₀ * Real.exp (-(C₁ * a)))
      ((d t₀ x₀) * Real.exp (-(C₁ * t₀)) + u t₀ x₀ * (-(C₁ * Real.exp (-(C₁ * t₀)))))
      (Ico 0 T) t₀ :=
    hasDerivWithinAt_congr_fun (hder.mul hexp) rfl (fun a => rfl)
  have hsub : HasDerivWithinAt
      (fun a : ℝ => u a x₀ * Real.exp (-(C₁ * a)) - (max B 0 + C₂ * a + ε * (1 + a)))
      ((d t₀ x₀) * Real.exp (-(C₁ * t₀)) + u t₀ x₀ * (-(C₁ * Real.exp (-(C₁ * t₀))))
        - (C₂ + ε)) (Ico 0 T) t₀ :=
    hasDerivWithinAt_congr_fun (hprod.sub haff) rfl (fun a => rfl)
  have hVder : HasDerivWithinAt (fun a : ℝ => smpBarrier u C₁ C₂ (max B 0) ε (a, x₀))
      ((d t₀ x₀) * Real.exp (-(C₁ * t₀)) + u t₀ x₀ * (-(C₁ * Real.exp (-(C₁ * t₀))))
        - (C₂ + ε)) (Ico 0 t₀) t₀ := by
    have hm : Ico 0 t₀ ⊆ Ico 0 T := fun a ha => ⟨ha.1, lt_of_lt_of_le ha.2 (le_of_lt ht₀T)⟩
    simpa only [smpBarrier] using hsub.mono hm
  -- `∂ₜ v ≥ 0` at `t₀`
  have hDnn : 0 ≤ (d t₀ x₀) * Real.exp (-(C₁ * t₀))
      + u t₀ x₀ * (-(C₁ * Real.exp (-(C₁ * t₀)))) - (C₂ + ε) :=
    nonneg_of_hasDerivWithinAt_Ico ht₀pos hVder hbar
  -- multiplying by `exp (C₁ t₀) > 0`
  have hDkey : 0 ≤ d t₀ x₀ - C₁ * u t₀ x₀ - Real.exp (C₁ * t₀) * (C₂ + ε) := by
    have h1 : 0 ≤ Real.exp (C₁ * t₀)
        * (Real.exp (-(C₁ * t₀)) * (d t₀ x₀ - C₁ * u t₀ x₀) - (C₂ + ε)) := by
      refine mul_nonneg (Real.exp_pos _).le ?_
      have hDform : (d t₀ x₀) * Real.exp (-(C₁ * t₀))
            + u t₀ x₀ * (-(C₁ * Real.exp (-(C₁ * t₀)))) - (C₂ + ε)
          = Real.exp (-(C₁ * t₀)) * (d t₀ x₀ - C₁ * u t₀ x₀) - (C₂ + ε) := by ring
      rw [← hDform]
      exact hDnn
    have h2 : Real.exp (C₁ * t₀) * Real.exp (-(C₁ * t₀)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := h1
    rw [mul_sub, ← mul_assoc, h2, one_mul] at h3
    linarith
  -- the differential inequality, using `u t₀ x₀ ≥ 0` and `Δu ≤ 0`
  have hA2 : d t₀ x₀ ≤ C₁ * u t₀ x₀ + C₂ := by
    rw [max_eq_left hU] at hineq2
    linarith
  have hE1 : 1 ≤ Real.exp (C₁ * t₀) := Real.one_le_exp (mul_nonneg hC₁ (le_of_lt ht₀pos))
  have hC2e : 0 ≤ C₂ + ε := by linarith
  have hcontra : C₂ + ε ≤ C₂ := by
    have hle : C₂ + ε ≤ Real.exp (C₁ * t₀) * (C₂ + ε) := le_mul_of_one_le_left hC2e hE1
    linarith
  linarith

end Work.Diff.GE
