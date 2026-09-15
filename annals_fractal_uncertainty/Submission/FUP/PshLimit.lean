import Submission.FUP.PSHAPI

open FractalUncertainty MeasureTheory Metric Filter Set
open scoped ENNReal BigOperators Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# Plurisubharmonicity is closed under locally uniform limits

Section 4 of Cohen's paper applies `prop:Ew_is_psh` to the *compactly supported truncations*
`ω̃_{≤n} = ∑_{k ≤ n} ω̃_k` of the modified weight, obtaining continuous plurisubharmonic
functions `u_n = Eω̃_{≤n} + C|y|`, and then passes to the limit `ω̃ = ∑_k ω̃_k`.  The passage to
the limit needs two things: `Eω̃_{≤n} → Eω̃` uniformly on compact sets (Lemma 3.1 of the paper,
`lem:Ew_conv_cpct_subsets`), and the fact that **plurisubharmonicity is closed under locally
uniform limits**, which is what this module proves.

The key point is that the sub-mean-value property survives uniform limits on compact sets because
the circle `θ ↦ z + e^{iθ}v` is compact and the circle averages converge.
-/

/-- **The circle averages converge** for a locally uniform limit. -/
theorem tendsto_circleAverage_of_tendstoUniformlyOn_compacts {u : ℕ → ℂᵈ → ℝ} {w : ℂᵈ → ℝ}
    (hcont : ∀ n, Continuous (u n))
    (hconv : ∀ K : Set ℂᵈ, IsCompact K → TendstoUniformlyOn u w atTop K)
    (z v : ℂᵈ) :
    Tendsto (fun n => ∫ θ in Set.Icc 0 (2 * π), u n (z + circlePt θ v)) atTop
      (𝓝 (∫ θ in Set.Icc 0 (2 * π), w (z + circlePt θ v))) := by
  have hlu : TendstoLocallyUniformly u w atTop :=
    tendstoLocallyUniformly_iff_forall_isCompact.mpr hconv
  have hwcont : Continuous w := hlu.continuous (Eventually.of_forall hcont).frequently
  set γ : ℝ → ℂᵈ := fun θ => z + circlePt θ v with hγ
  have hγc : Continuous γ := continuous_circlePt z v
  have hKcomp : IsCompact (γ '' Set.Icc 0 (2 * π)) := isCompact_Icc.image hγc
  have hmono : TendstoUniformlyOn (fun n θ => u n (γ θ)) (fun θ => w (γ θ)) atTop
      (Set.Icc 0 (2 * π)) :=
    ((hconv _ hKcomp).comp γ).mono (fun θ hθ => ⟨θ, hθ, rfl⟩)
  have hcontγ : ∀ n, Continuous (fun θ : ℝ => u n (γ θ)) := fun n => (hcont n).comp hγc
  have hwγ : Continuous (fun θ : ℝ => w (γ θ)) := hwcont.comp hγc
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hmono
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmono (ε / (2 * π + 2)) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hsub : (∫ θ in Set.Icc 0 (2 * π), u n (γ θ)) - (∫ θ in Set.Icc 0 (2 * π), w (γ θ))
      = ∫ θ in Set.Icc 0 (2 * π), (u n (γ θ) - w (γ θ)) := by
    rw [integral_sub]
    · exact (hcontγ n).continuousOn.integrableOn_compact isCompact_Icc
    · exact hwγ.continuousOn.integrableOn_compact isCompact_Icc
  rw [hsub]
  have hbound := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Set.Icc 0 (2 * π)) (f := fun θ : ℝ => u n (γ θ) - w (γ θ))
    (C := ε / (2 * π + 2)) (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun θ hθ => by
      have h := hN n hn θ hθ
      rw [dist_comm, dist_eq_norm] at h
      exact le_of_lt h)
  refine lt_of_le_of_lt hbound ?_
  rw [Measure.real_def, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hpos : (0 : ℝ) < 2 * π + 2 := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π + 2)]
  nlinarith [Real.pi_pos, hε]

/-- **The sub-mean-value property survives locally uniform limits.** -/
theorem SubMeanValue.of_tendstoUniformlyOn_compacts {u : ℕ → ℂᵈ → ℝ} {w : ℂᵈ → ℝ}
    (hsmv : ∀ n, SubMeanValue (u n)) (hcont : ∀ n, Continuous (u n))
    (hconv : ∀ K : Set ℂᵈ, IsCompact K → TendstoUniformlyOn u w atTop K) :
    SubMeanValue w := by
  have hlu : TendstoLocallyUniformly u w atTop :=
    tendstoLocallyUniformly_iff_forall_isCompact.mpr hconv
  intro z v
  have hz : Tendsto (fun n => u n z) atTop (𝓝 (w z)) :=
    hlu.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
  have hint := tendsto_circleAverage_of_tendstoUniformlyOn_compacts hcont hconv z v
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hiconv : ∀ g : ℂᵈ → ℝ, (∫ θ in (0 : ℝ)..(2 * π), g (z + circlePt θ v))
      = ∫ θ in Set.Icc 0 (2 * π), g (z + circlePt θ v) := by
    intro g
    rw [intervalIntegral.integral_of_le h2π.le,
      setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc' (a := (0 : ℝ)) (b := 2 * π)
        (μ := volume) (measure_singleton (0 : ℝ)))]
  have hwcont : Continuous w :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mpr hconv).continuous
      (Eventually.of_forall hcont).frequently
  rw [hiconv w]
  have h1 : ∀ n, u n z ≤ (∫ θ in Set.Icc 0 (2 * π), u n (z + circlePt θ v)) / (2 * π) := by
    intro n
    have h := hsmv n z v
    rwa [hiconv (u n)] at h
  have h2 : Tendsto (fun n => (∫ θ in Set.Icc 0 (2 * π), u n (z + circlePt θ v)) / (2 * π))
      atTop (𝓝 ((∫ θ in Set.Icc 0 (2 * π), w (z + circlePt θ v)) / (2 * π))) :=
    hint.div_const _
  exact le_of_tendsto_of_tendsto hz h2 (Eventually.of_forall h1)

/-- **Plurisubharmonicity is closed under locally uniform limits.** -/
theorem IsPSH.of_tendstoUniformlyOn_compacts {u : ℕ → ℂᵈ → ℝ} {w : ℂᵈ → ℝ}
    (hpsh : ∀ n, IsPSH (u n)) (hcont : ∀ n, Continuous (u n))
    (hconv : ∀ K : Set ℂᵈ, IsCompact K → TendstoUniformlyOn u w atTop K) :
    Continuous w ∧ IsPSH w := by
  have hlu : TendstoLocallyUniformly u w atTop :=
    tendstoLocallyUniformly_iff_forall_isCompact.mpr hconv
  have hwcont : Continuous w := hlu.continuous (Eventually.of_forall hcont).frequently
  exact ⟨hwcont, ⟨hwcont.upperSemicontinuous,
    SubMeanValue.of_tendstoUniformlyOn_compacts (fun n => (hpsh n).2) hcont hconv⟩⟩

end Submission.FUP
