/-
# The concrete contour bounds for the CKMRV kernels

The general reduction of `Work.Asymptotics.Divisor` is instantiated here with the proved
two-variable moderate growth of the cleared kernels (`Work.Asymptotics.KClear_mg2`, Theorem
4.9(4)), for the concrete logarithm data `Work.Kernels.logLambda` fixed in
`Submission/Work/Kernels/LogLambdaInstance.lean`.

## Main results

* `Work.Asymptotics.contour_bound_Kfun`, `Work.Asymptotics.contour_bound_Khat` : for `d ∈ {8,24}`
  and every `t > 0`,
  `‖K^{(d)}(τ,it)‖ · ‖Δ(τ)Δ(it)^e(j(τ)-j(it))‖ ≤ α (scale τ)^N (scale(it))^M`;
* `Work.Asymptotics.norm_Kaxis_Kfun_le` : the same with the divisor divided out, valid whenever
  `j(τ) ≠ j(it)`;
* the same two statements for `K̂^{(d)}`, which is the kernel of `F̃ = Ftgen K̂`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.ModerateGrowth2
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.Divisor

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- **The concrete contour bound for `K^{(d)}`** (Theorem 4.9(4) along the contour). -/
theorem contour_bound_Kfun (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      ‖Kaxis (Kfun ℓ d) τ t‖ * ‖growthPrefactor d τ (imagAxis t ht)‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M :=
  exists_contour_bound_Kfun hd (KClear_mg2 ℓ d hd).1

/-- **The concrete contour bound for `K̂^{(d)}`** (Theorem 4.9(4) along the contour). -/
theorem contour_bound_Khat (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ) (t : ℝ) (ht : 0 < t),
      ‖Kaxis (Khat ℓ d) τ t‖ * ‖growthPrefactor d τ (imagAxis t ht)‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M :=
  exists_contour_bound_Khat hd (KClear_mg2 ℓ d hd).2

/-- The divisor form of the contour bound for `K^{(d)}`: dividing by the divisor gives a bound
of the kernel itself, valid off the divisor. -/
theorem norm_Kaxis_Kfun_le {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24) {τ : ℍ}
    {t : ℝ} (ht : 0 < t) (hJ : jInvariantFun τ ≠ jInvariantFun (imagAxis t ht)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ‖Kaxis (Kfun ℓ d) τ t‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M
            / ‖growthPrefactor d τ (imagAxis t ht)‖ := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := contour_bound_Kfun ℓ d hd
  refine ⟨α, N, M, hα, hN, hM, ?_⟩
  have he : (if d = 8 then 1 else 2) ≠ 0 := by split <;> norm_num
  have hpos : 0 < ‖growthPrefactor d τ (imagAxis t ht)‖ := by
    rw [norm_pos_iff]
    intro hzero
    rcases mul_eq_zero.mp hzero with h2 | h3
    · rcases mul_eq_zero.mp h2 with h4 | h5
      · exact ClassicalFacts.DeltaFun_ne_zero τ h4
      · exact ClassicalFacts.DeltaFun_ne_zero (imagAxis t ht) ((pow_eq_zero_iff he).mp h5)
    · exact hJ (sub_eq_zero.mp h3)
  rw [le_div_iff₀ hpos]
  exact h τ t ht

/-- The divisor form of the contour bound for `K̂^{(d)}`. -/
theorem norm_Kaxis_Khat_le {ℓ : LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24) {τ : ℍ}
    {t : ℝ} (ht : 0 < t) (hJ : jInvariantFun τ ≠ jInvariantFun (imagAxis t ht)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ‖Kaxis (Khat ℓ d) τ t‖
        ≤ α * (scale τ) ^ N * (scale (imagAxis t ht)) ^ M
            / ‖growthPrefactor d τ (imagAxis t ht)‖ := by
  obtain ⟨α, N, M, hα, hN, hM, h⟩ := contour_bound_Khat ℓ d hd
  refine ⟨α, N, M, hα, hN, hM, ?_⟩
  have he : (if d = 8 then 1 else 2) ≠ 0 := by split <;> norm_num
  have hpos : 0 < ‖growthPrefactor d τ (imagAxis t ht)‖ := by
    rw [norm_pos_iff]
    intro hzero
    rcases mul_eq_zero.mp hzero with h2 | h3
    · rcases mul_eq_zero.mp h2 with h4 | h5
      · exact ClassicalFacts.DeltaFun_ne_zero τ h4
      · exact ClassicalFacts.DeltaFun_ne_zero (imagAxis t ht) ((pow_eq_zero_iff he).mp h5)
    · exact hJ (sub_eq_zero.mp h3)
  rw [le_div_iff₀ hpos]
  exact h τ t ht

end Work.Asymptotics
