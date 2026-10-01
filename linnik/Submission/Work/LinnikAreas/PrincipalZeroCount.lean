import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Commons.NumberTheory.Zeta.xiE_zeroCount
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

/-!
# The principal character contributes few zeros

`Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T` counts (with multiplicity) the
zeros of the completed L-function of the *principal* character mod `q` in the rectangle
`σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T`.  The principal character's primitive character is the trivial
character mod `1`, so these are exactly the zeros of the completed Riemann zeta function
`Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`, i.e. the non-trivial zeros of `ζ`, and their number is
`≪ T log(qT)` uniformly in `q` (the `q`-dependence is only logarithmic since the zeros do not
depend on `q` at all).

The bound is obtained from the entire completion `Ξ(s) = 1/2 + (1/2) s (s-1) Λ₀(s)`, whose zeros
are the non-trivial zeros of `ζ`, via the zero count
`Commons.NumberTheory.Zeta.xiE_zeroCount` for `Ξ` in a disk of radius `T + 2` (Jensen +
`xiE_circle_growth`).  The rectangle `0 ≤ Re ≤ 1`, `|Im| ≤ T` lies in that disk.
-/

open DirichletCharacter Complex Filter
open scoped Classical BigOperators Topology
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract (zeroMult)

/-- The entire completion `Ξ(s) = 1/2 + (1/2)·s·(s-1)·Λ₀(s)` of the Riemann zeta function.
Its zeros are exactly the non-trivial zeros of `ζ`. -/
def xiC (s : ℂ) : ℂ := (1 / 2 : ℂ) + (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s

lemma xiC_diff : Differentiable ℂ xiC := by
  unfold xiC
  exact (differentiable_const _).add
    ((by fun_prop : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1))).mul
      differentiable_completedZeta₀)

lemma xiC_analyticOn (U : Set ℂ) : AnalyticOnNhd ℂ xiC U := fun z _ => xiC_diff.analyticAt z

lemma xiC_zero_ne : xiC 0 ≠ 0 := by unfold xiC; norm_num

lemma xiC_one_ne : xiC 1 ≠ 0 := by unfold xiC; norm_num

/-! ### `Λ` has poles at `0` and `1` -/

/-- `Λ = completedRiemannZeta` is not analytic at `1`: it has a (simple) pole there. -/
lemma not_analyticAt_completedZeta_one : ¬ AnalyticAt ℂ completedRiemannZeta 1 := by
  intro h
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have hlim0 : Filter.Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s)
      (𝓝[≠] (1:ℂ)) (𝓝 (0:ℂ)) := by
    have := hcont.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)) (a := 1))
    simpa using this
  have h01 : (0:ℂ) = 1 := tendsto_nhds_unique hlim0 completedRiemannZeta_residue_one
  norm_num at h01

/-- `Λ` is not analytic at `0` either: `Λ(1-s) = Λ(s)` transports the pole at `1` to `0`. -/
lemma not_analyticAt_completedZeta_zero : ¬ AnalyticAt ℂ completedRiemannZeta 0 := by
  intro h
  apply not_analyticAt_completedZeta_one
  have hcomp : AnalyticAt ℂ (completedRiemannZeta ∘ fun s : ℂ => 1 - s) 1 :=
    AnalyticAt.comp (x := (1:ℂ)) (f := fun s : ℂ => 1 - s) (g := completedRiemannZeta)
      (by simpa using h) (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 - s) 1)
  have heq : (completedRiemannZeta ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 1] completedRiemannZeta := by
    filter_upwards with s
    exact completedRiemannZeta_one_sub s
  exact hcomp.congr heq

/-- `Λ` is analytic away from `0` and `1`. -/
lemma analyticAt_completedZeta_of_ne (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta ρ := by
  have hopen : IsOpen ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) := isOpen_ne.inter isOpen_ne
  have hdiffOn : DifferentiableOn ℂ completedRiemannZeta ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) := by
    intro s hs
    exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
  exact (hdiffOn.analyticOnNhd hopen) ρ ⟨h0, h1⟩

/-! ### The multiplicity of `Ξ` and of `Λ` agree -/

/-- Away from `0` and `1`, the completion `Ξ` agrees with the naive product `(1/2)s(s-1)Λ`. -/
lemma xiC_eventuallyEq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    xiC =ᶠ[𝓝 ρ] fun s : ℂ => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with s hs0 hs1
  have hΛ₀ : completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s) := by
    rw [completedRiemannZeta_eq s]; ring
  rw [xiC, hΛ₀]
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro hc; apply hs1; linear_combination -hc
  field_simp
  ring

/-- The multiplicities of `Ξ` and of `Λ` agree away from `0` and `1`. -/
lemma analyticOrderNatAt_xiC_eq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    analyticOrderNatAt xiC ρ = analyticOrderNatAt completedRiemannZeta ρ := by
  have heq := xiC_eventuallyEq ρ h0 h1
  have hΛan : AnalyticAt ℂ completedRiemannZeta ρ := analyticAt_completedZeta_of_ne ρ h0 h1
  have hpoly : AnalyticAt ℂ (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) ρ := by fun_prop
  have hpoly_ne : (1/2 : ℂ) * ρ * (ρ - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) h0) ?_
    exact sub_ne_zero.mpr h1
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr heq]
  have hmul : (fun s : ℂ => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s)
      = (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta := rfl
  rw [hmul, analyticOrderAt_mul hpoly hΛan]
  have hzero : analyticOrderAt (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hpoly_ne)
  rw [hzero]
  simp

/-- **Pointwise comparison.**  Every zero of `Λ` is a zero of `Ξ` with at least the same
multiplicity (at `0` and `1` the left-hand side is `0` because `Λ` has poles there). -/
lemma analyticOrderNatAt_zeta_le_xiC (ρ : ℂ) :
    analyticOrderNatAt completedRiemannZeta ρ ≤ analyticOrderNatAt xiC ρ := by
  by_cases h0 : ρ = 0
  · subst h0
    rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedZeta_zero]
    exact Nat.zero_le _
  · by_cases h1 : ρ = 1
    · subst h1
      rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedZeta_one]
      exact Nat.zero_le _
    · exact le_of_eq (analyticOrderNatAt_xiC_eq ρ h0 h1).symm

/-! ### The trivial character mod `1` -/

/-- The completed L-function at level `1` is the completed Riemann zeta function
(this is `DirichletCharacter.completedLFunction_modOne_eq` after transporting the level). -/
lemma completedLFunction_level_one {N : ℕ} [NeZero N] (hN : N = 1)
    (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.completedLFunction χ = completedRiemannZeta := by
  subst hN
  exact DirichletCharacter.completedLFunction_modOne_eq

/-- The multiplicity of a zero of the principal character mod `q` is the multiplicity of
the same point as a zero of `Λ`. -/
lemma zeroMult_one_eq (q : ℕ) [NeZero q] :
    (zeroMult (1 : DirichletCharacter ℂ q)) =
      fun ρ => analyticOrderNatAt completedRiemannZeta ρ := by
  funext ρ
  haveI : NeZero ((1 : DirichletCharacter ℂ q).conductor) :=
    ⟨DirichletCharacter.conductor_ne_zero (1 : DirichletCharacter ℂ q)⟩
  unfold zeroMult
  congr 1
  exact completedLFunction_level_one DirichletCharacter.conductor_one _

/-- Pointwise form of `zeroMult_one_eq`, together with the comparison with `Ξ`. -/
lemma zeroMult_one_apply (q : ℕ) [NeZero q] (ρ : ℂ) :
    (zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) ≤ (analyticOrderNatAt xiC ρ : ℝ) := by
  have h1 : zeroMult (1 : DirichletCharacter ℂ q) ρ
      = analyticOrderNatAt completedRiemannZeta ρ := congrFun (zeroMult_one_eq q) ρ
  rw [h1]
  exact_mod_cast analyticOrderNatAt_zeta_le_xiC ρ

/-! ### Geometry and arithmetic -/

/-- The rectangle `0 ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` lies in the disk of radius `T + 2`. -/
lemma norm_le_of_re_im (ρ : ℂ) {T : ℝ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1) (him : |ρ.im| ≤ T)
    (hT : 1 ≤ T) : ‖ρ‖ ≤ T + 2 := by
  have h1 : |ρ.re| = ρ.re := abs_of_nonneg hre0
  have := Complex.norm_le_abs_re_add_abs_im ρ
  rw [h1] at this
  linarith

/-- The logarithmic factor is absorbed by the `q`-dependent one. -/
lemma log_absorb (q : ℕ) (hq : 2 ≤ q) {T : ℝ} (hT : 1 ≤ T) :
    Real.log (T + 4) + 2 ≤ 2 * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT2 : (0 : ℝ) < T + 2 := by linarith
  have hprod1 : (1 : ℝ) < (q : ℝ) * (T + 2) := by nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (T + 2)) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have hlogT : Real.log (T + 4) ≤ Real.log 2 + Real.log (T + 2) := by
    have h4 : (0 : ℝ) < T + 4 := by linarith
    have hle : T + 4 ≤ 2 * (T + 2) := by linarith
    have h := Real.log_le_log h4 hle
    rw [Real.log_mul (by norm_num) (ne_of_gt hT2)] at h
    exact h
  have hT2le : Real.log (T + 2) ≤ Real.log ((q : ℝ) * (T + 2)) := by
    apply Real.log_le_log hT2
    nlinarith
  linarith

/-! ### The zero count -/

/-- `zeroCountIn` of the principal character is dominated by the divisor sum of `Ξ` over the
disk of radius `T + 2`. -/
lemma zeroCountIn_one_le_divisorSum (q : ℕ) [NeZero q] (σ T : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hT : 1 ≤ T) :
    zeroCountIn (1 : DirichletCharacter ℂ q) σ T
      ≤ ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))) u : ℤ) : ℝ) := by
  have hdiv_fin : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))) u : ℤ)) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))).finiteSupport
        (isCompact_closedBall (0:ℂ) (T + 2)))
  have hR_fin : Function.HasFiniteSupport (fun u : ℂ =>
      (((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))) u : ℤ) : ℝ)) := by
    refine hdiv_fin.subset ?_
    intro u hu
    simpa only [Function.mem_support, ne_eq, Int.cast_eq_zero] using hu
  have hL_fin : Function.HasFiniteSupport (fun ρ : ℂ =>
      if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) else 0) := by
    refine hR_fin.subset ?_
    intro ρ hρ
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hρ ⊢
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos hc] at hρ
      have hzm : zeroMult (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by
        intro hzero
        exact hρ (by simp [hzero])
      have hnat : analyticOrderNatAt xiC ρ ≠ 0 := by
        intro h0
        have hle := zeroMult_one_apply q ρ
        have hle0 : (zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) ≤ 0 := by
          rw [h0] at hle; simpa using hle
        have hzero : (zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) = 0 :=
          le_antisymm hle0 (Nat.cast_nonneg _)
        exact hzm (Nat.cast_eq_zero.mp hzero)
      have hmem : ρ ∈ Metric.closedBall (0:ℂ) (T + 2) := by
        have hnorm : ‖ρ‖ ≤ T + 2 := norm_le_of_re_im ρ (le_trans hσ0 hc.1) hc.2.1 hc.2.2 hT
        simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (xiC_analyticOn _) hmem]
      exact_mod_cast hnat
    · rw [if_neg hc] at hρ
      exact absurd rfl hρ
  rw [zeroCountIn]
  refine finsum_le_finsum' hL_fin hR_fin ?_
  intro ρ
  show (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
      then (zeroMult (1 : DirichletCharacter ℂ q) ρ : ℝ) else 0)
    ≤ ((((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))) ρ : ℤ) : ℝ))
  by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos hc]
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (T + 2) := by
      have hnorm : ‖ρ‖ ≤ T + 2 := norm_le_of_re_im ρ (le_trans hσ0 hc.1) hc.2.1 hc.2.2 hT
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (xiC_analyticOn _) hmem]
    push_cast
    exact zeroMult_one_apply q ρ
  · rw [if_neg hc]
    have hnn : (0:ℤ) ≤ MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2)) ρ :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg (xiC_analyticOn _) ρ
    exact_mod_cast hnn

theorem PrincipalZeroCount :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ σ T : ℝ,
      0 ≤ σ → σ ≤ 1 → 1 ≤ T →
        Work.LinnikAreas.zeroCountIn (1 : DirichletCharacter ℂ q) σ T
          ≤ c * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
  obtain ⟨c₁, hc₁⟩ := Commons.NumberTheory.Zeta.xiE_zeroCount
  refine ⟨2 * |c₁| + 1, by positivity, ?_⟩
  intro q hq hqne σ T hσ0 hσ1 hT
  have hT2 : (2:ℝ) ≤ T + 2 := by linarith
  have hxi : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (fun z : ℂ =>
            (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
          (Metric.closedBall 0 (T + 2))) u : ℤ) : ℝ))
      ≤ c₁ * (T + 2) * (Real.log (T + 2 + 2) + 2) := hc₁ (T + 2) hT2
  have hxi' : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor xiC (Metric.closedBall (0:ℂ) (T + 2))) u : ℤ) : ℝ))
      ≤ c₁ * (T + 2) * (Real.log (T + 4) + 2) := by
    rw [show (fun z : ℂ => (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) * completedRiemannZeta₀ z)
          = xiC from rfl,
      show T + 2 + 2 = T + 4 by ring] at hxi
    exact hxi
  have hcount := zeroCountIn_one_le_divisorSum q σ T hσ0 hσ1 hT
  have hfac_nonneg : 0 ≤ (T + 2) * (Real.log (T + 4) + 2) := by
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    positivity
  have hstep1 : c₁ * (T + 2) * (Real.log (T + 4) + 2)
      ≤ |c₁| * (T + 2) * (Real.log (T + 4) + 2) := by
    calc c₁ * (T + 2) * (Real.log (T + 4) + 2)
        = c₁ * ((T + 2) * (Real.log (T + 4) + 2)) := by ring
      _ ≤ |c₁| * ((T + 2) * (Real.log (T + 4) + 2)) :=
            mul_le_mul_of_nonneg_right (le_abs_self c₁) hfac_nonneg
      _ = |c₁| * (T + 2) * (Real.log (T + 4) + 2) := by ring
  have hstep2 : |c₁| * (T + 2) * (Real.log (T + 4) + 2)
      ≤ |c₁| * (T + 2) * (2 * (Real.log ((q : ℝ) * (T + 2)) + 2)) := by
    refine mul_le_mul_of_nonneg_left (log_absorb q hq hT) ?_
    positivity
  have hstep3 : |c₁| * (T + 2) * (2 * (Real.log ((q : ℝ) * (T + 2)) + 2))
      ≤ (2 * |c₁| + 1) * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
    have h1 : |c₁| * 2 ≤ 2 * |c₁| + 1 := by linarith [abs_nonneg c₁]
    have h2 : 0 ≤ (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by
      have : 0 ≤ Real.log ((q : ℝ) * (T + 2)) := by
        apply Real.log_nonneg
        have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
        nlinarith
      positivity
    calc |c₁| * (T + 2) * (2 * (Real.log ((q : ℝ) * (T + 2)) + 2))
        = (|c₁| * 2) * ((T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)) := by ring
      _ ≤ (2 * |c₁| + 1) * ((T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)) :=
            mul_le_mul_of_nonneg_right h1 h2
      _ = (2 * |c₁| + 1) * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2) := by ring
  exact le_trans (le_trans (le_trans hcount hxi') hstep1) (le_trans hstep2 hstep3)

end Work.LinnikAreas
