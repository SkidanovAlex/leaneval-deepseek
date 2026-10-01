import Mathlib
import Submission.Commons.NumberTheory.Zeta.xiE_partialFraction_eq

/-!
# The vanishing multiplicity of `Λ` equals that of the entire completion `Ξ = xiF`

The completed Riemann zeta function `Λ = completedRiemannZeta` has simple poles at `0` and `1`
and its zeros are exactly the non-trivial zeros of `ζ`.  The entire completion used throughout
this workspace,
`Ξ(s) = xiF s = 1/2 + (1/2) s (s-1) Λ₀(s)`, satisfies `Ξ(s) = (1/2) s (s-1) Λ(s)` away from
`s = 0, 1` (because `Λ(s) = Λ₀(s) - 1/s - 1/(1-s)`), so away from the two poles it has precisely
the zeros of `Λ` with the same multiplicities; at `s = 0, 1` the factor `(1/2)s(s-1)` vanishes but
`Ξ` does not (`Ξ(0) = Ξ(1) = 1/2`), while `Λ` is not even analytic there (junk value `0` for the
natural-valued order).  Hence the multiplicity functions agree on all of `ℂ`.
-/

open Complex Filter
open scoped Topology

noncomputable section

namespace Work.LinnikAreas

/-- `Λ = completedRiemannZeta` is not analytic at `1`: it has a (simple) pole there, whose
residue `1` is incompatible with the limit `0` of `(s-1)Λ(s)` forced by continuity. -/
private lemma not_analyticAt_completedRiemannZeta_one : ¬ AnalyticAt ℂ completedRiemannZeta 1 := by
  intro h
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul h.continuousAt
  have hlim0 : Filter.Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s)
      (𝓝[≠] (1:ℂ)) (𝓝 (0:ℂ)) := by
    have := hcont.mono_left (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℂ)) (a := 1))
    simpa using this
  have h01 : (0:ℂ) = 1 := tendsto_nhds_unique hlim0 completedRiemannZeta_residue_one
  norm_num at h01

/-- `Λ` is not analytic at `0` either: the functional equation `Λ(1-s) = Λ(s)` transports the
pole at `1` to `0`. -/
private lemma not_analyticAt_completedRiemannZeta_zero : ¬ AnalyticAt ℂ completedRiemannZeta 0 := by
  intro h
  apply not_analyticAt_completedRiemannZeta_one
  have hcomp : AnalyticAt ℂ (completedRiemannZeta ∘ fun s : ℂ => 1 - s) 1 :=
    AnalyticAt.comp (x := (1:ℂ)) (f := fun s : ℂ => 1 - s) (g := completedRiemannZeta)
      (by simpa using h) (by fun_prop : AnalyticAt ℂ (fun s : ℂ => 1 - s) 1)
  have heq : (completedRiemannZeta ∘ fun s : ℂ => 1 - s) =ᶠ[𝓝 1] completedRiemannZeta := by
    filter_upwards with s
    exact completedRiemannZeta_one_sub s
  exact hcomp.congr heq

/-- `Λ` is analytic away from `0` and `1`. -/
private lemma analyticAt_completedRiemannZeta_of_ne (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta ρ := by
  have hopen : IsOpen ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) := isOpen_ne.inter isOpen_ne
  have hdiffOn : DifferentiableOn ℂ completedRiemannZeta ({s : ℂ | s ≠ 0} ∩ {s : ℂ | s ≠ 1}) :=
    fun s hs => (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
  exact (hdiffOn.analyticOnNhd hopen) ρ ⟨h0, h1⟩

/-- The entire completion `Ξ = xiF` agrees, away from `0` and `1`, with the naive product
`(1/2) s (s-1) Λ(s)`. -/
private lemma xiF_eventuallyEq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    Commons.NumberTheory.Zeta.XiPF.xiF =ᶠ[𝓝 ρ]
      fun s : ℂ => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with s hs0 hs1
  have hΛ₀ : completedRiemannZeta₀ s = completedRiemannZeta s + 1/s + 1/(1-s) := by
    rw [completedRiemannZeta_eq s]; ring
  rw [Commons.NumberTheory.Zeta.XiPF.xiF, hΛ₀]
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro hc; exact hs1 (by linear_combination -hc)
  field_simp
  ring

/-- Away from `0` and `1` the multiplicities of `Ξ = xiF` and of `Λ` agree: the prefactor
`(1/2) s (s-1)` is analytic and non-vanishing there, hence contributes vanishing order `0`. -/
private lemma analyticOrderNatAt_xiF_eq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF ρ =
      analyticOrderNatAt completedRiemannZeta ρ := by
  have heq := xiF_eventuallyEq ρ h0 h1
  have hΛan : AnalyticAt ℂ completedRiemannZeta ρ := analyticAt_completedRiemannZeta_of_ne ρ h0 h1
  have hpoly : AnalyticAt ℂ (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) ρ := by fun_prop
  have hpoly_ne : (1/2 : ℂ) * ρ * (ρ - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1)
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr heq]
  have hmul : (fun s : ℂ => (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s)
      = (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta := rfl
  rw [hmul, analyticOrderAt_mul hpoly hΛan]
  have hzero : analyticOrderAt (fun s : ℂ => (1/2 : ℂ) * s * (s - 1)) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hpoly_ne)
  rw [hzero]
  simp

/-- If `Ξ = xiF` does not vanish at `z`, its vanishing order there is `0`. -/
private lemma xiF_orderNat_zero (z : ℂ) (hz : Commons.NumberTheory.Zeta.XiPF.xiF z ≠ 0) :
    analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF z = 0 := by
  have h : analyticOrderAt Commons.NumberTheory.Zeta.XiPF.xiF z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hz)
  simp [analyticOrderNatAt, h]

/-- `Ξ(1) = 1/2 ≠ 0`. -/
private lemma xiF_one_ne : Commons.NumberTheory.Zeta.XiPF.xiF 1 ≠ 0 := by
  have h : Commons.NumberTheory.Zeta.XiPF.xiF 1 = (1/2 : ℂ) := by
    rw [Commons.NumberTheory.Zeta.XiPF.xiF]; norm_num
  rw [h]; norm_num

/-- The vanishing multiplicity of the completed Riemann zeta function `Λ` agrees with that of
the entire completion `Ξ = xiF` at every point of `ℂ`. -/
theorem zetaOrder_eq_xiF :
    ∀ u : ℂ, analyticOrderNatAt completedRiemannZeta u =
      analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u := by
  intro u
  by_cases h0 : u = 0
  · subst h0
    rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedRiemannZeta_zero,
      xiF_orderNat_zero 0 Commons.NumberTheory.Zeta.XiPF.xiF_zero_ne]
  · by_cases h1 : u = 1
    · subst h1
      rw [analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedRiemannZeta_one,
        xiF_orderNat_zero 1 xiF_one_ne]
    · exact (analyticOrderNatAt_xiF_eq u h0 h1).symm

end Work.LinnikAreas
