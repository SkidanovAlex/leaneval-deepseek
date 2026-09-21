import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.abel_deriv_bound

/-!
# A bound for the second derivative of the Abel transform `abelF`

`abelF φ u = ∫_v u..1, φ v / √(v - u)` is the Abel transform of `φ` on the interval
`[u, 1]`.  This file proves that if `φ` is `C²` on `[c,1]`, vanishes at `1` together with
its derivative and has `|φ''| ≤ K` there, then the second derivative of `abelF φ` is bounded
by `2√(1-c) K` on every `(c, d)` with `d ≤ 1`.

The proof goes through three ingredients.

* `abelF_subst`: the substitution `v = u + (1-u)t²` expressing the Abel transform as
  `abelF φ u = 2√(1-u) ∫_t 0..1, φ (u + (1-u) t²) dt`.
* `abelIntegral_hasDerivAt`: differentiation under the integral sign for that parametric
  integral.
* `abelIntegral_ibp`: the integration by parts identity
  `∫_t 0..1, φ (u + (1-u) t²) = -2(1-u) ∫_t 0..1, φ' (u + (1-u) t²) t²`,
  which is where `φ 1 = 0` enters.

Combining the three gives the first-derivative formula `deriv (abelF φ) u = abelF φ' u`
(`deriv_abelF_eq`), which applied twice reduces the target to
`abelF (φ'') s = ∫_v s..1, φ'' v / √(v-s)`, bounded by `K ∫_v s..1 (v-s)^{-1/2} = 2K√(1-s)`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Abel

noncomputable section

/-- The substitution `v = u + (1-u) t²` expressing the Abel transform through an integral over
the fixed interval `[0,1]`. -/
lemma abelF_subst {ψ : ℝ → ℝ} {u : ℝ} (hu : u ≤ 1) :
    Work.OddVolterra.Existence.abelF ψ u
      = 2 * Real.sqrt (1 - u) * ∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2) := by
  have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (E := ℝ) (x := u) (b := 1) hu
    (fun _ σ => ψ σ)
  rw [Work.OddVolterra.Existence.abelF]
  calc ∫ v in u..1, ψ v / Real.sqrt (v - u)
      = ∫ σ in u..1, (Real.sqrt (σ - u))⁻¹ • ψ σ := by
        apply intervalIntegral.integral_congr
        intro v _
        simp [div_eq_inv_mul, smul_eq_mul, mul_comm]
    _ = (2 * Real.sqrt (1 - u)) • ∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2) := h
    _ = 2 * Real.sqrt (1 - u) * ∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2) := by
        rw [smul_eq_mul]

/-- Differentiation under the integral sign for the parametric integral
`u ↦ ∫_t 0..1, ψ (u + (1-u) t²)`. -/
theorem abelIntegral_hasDerivAt {c : ℝ} (hc : c < 1) {ψ : ℝ → ℝ}
    (hdiff : ∀ v ∈ Set.Icc c 1, DifferentiableAt ℝ ψ v)
    (hcont : ContinuousOn (deriv ψ) (Set.Icc c 1)) :
    ∀ u ∈ Set.Ioo c 1,
      HasDerivAt (fun u : ℝ => ∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2))
        (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * (1 - t ^ 2)) u := by
  intro u hu
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c ⟨le_rfl, hc.le⟩)
  have hψcont : ContinuousOn ψ (Set.Icc c 1) :=
    fun v hv => (hdiff v hv).continuousAt.continuousWithinAt
  have hpt : ∀ x ∈ Set.Ioo c 1, ∀ t ∈ Set.uIcc (0:ℝ) 1,
      x + (1 - x) * t ^ 2 ∈ Set.Icc c 1 := by
    intro x hx t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have h1 : 0 ≤ (1 - x) * t^2 := mul_nonneg (by linarith [hx.2]) (sq_nonneg t)
    have h2 : (1 - x) * t^2 ≤ (1 - x) * 1 :=
      mul_le_mul_of_nonneg_left (by nlinarith [ht.1, ht.2]) (by linarith [hx.2])
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmaps : ∀ x ∈ Set.Ioo c 1, Set.MapsTo (fun t : ℝ => x + (1 - x) * t ^ 2)
      (Set.uIcc (0:ℝ) 1) (Set.Icc c 1) := fun x hx t ht => hpt x hx t ht
  have hFcont : ∀ x ∈ Set.Ioo c 1,
      ContinuousOn (fun t : ℝ => ψ (x + (1 - x) * t ^ 2)) (Set.uIcc (0:ℝ) 1) := by
    intro x hx
    have hmap : ContinuousOn (fun t : ℝ => x + (1 - x) * t ^ 2) (Set.uIcc (0:ℝ) 1) := by fun_prop
    simpa [Function.comp_def] using hψcont.comp hmap (hmaps x hx)
  have hF'cont : ContinuousOn (fun t : ℝ => deriv ψ (u + (1 - u) * t ^ 2) * (1 - t ^ 2))
      (Set.uIcc (0:ℝ) 1) := by
    have hmap : ContinuousOn (fun t : ℝ => u + (1 - u) * t ^ 2) (Set.uIcc (0:ℝ) 1) := by fun_prop
    have h1 : ContinuousOn (fun t : ℝ => deriv ψ (u + (1 - u) * t ^ 2)) (Set.uIcc (0:ℝ) 1) := by
      simpa [Function.comp_def] using hcont.comp hmap (hmaps u hu)
    exact h1.mul (by fun_prop)
  set F : ℝ → ℝ → ℝ := fun x t => ψ (x + (1 - x) * t ^ 2) with hF
  set F' : ℝ → ℝ → ℝ := fun x t => deriv ψ (x + (1 - x) * t ^ 2) * (1 - t ^ 2) with hF'
  have hFmeas : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact ((hFcont x hx).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hFint : IntervalIntegrable (F u) volume (0:ℝ) 1 := (hFcont u hu).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (F' u) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (hF'cont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0:ℝ) 1 → ∀ x ∈ Set.Ioo c 1, ‖F' x t‖ ≤ M := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.uIcc (0:ℝ) 1 := Set.uIoc_subset_uIcc ht
    have hc01 : t ∈ Set.Icc (0:ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht'
    have hp : x + (1 - x) * t ^ 2 ∈ Set.Icc c 1 :=
      hpt x hx t (Set.uIoc_subset_uIcc ht)
    have h1 : |deriv ψ (x + (1 - x) * t ^ 2)| ≤ M := by
      simpa [Real.norm_eq_abs] using hM _ hp
    have h2 : |1 - t ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hc01.1, hc01.2]
    simp only [hF', Real.norm_eq_abs, abs_mul]
    exact le_trans (mul_le_mul h1 h2 (abs_nonneg _) hM0) (le_of_eq (mul_one M))
  have hdiff_all : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo c 1, HasDerivAt (fun x : ℝ => F x t) (F' x t) x := by
    filter_upwards with t ht x hx
    have hp : x + (1 - x) * t ^ 2 ∈ Set.Icc c 1 :=
      hpt x hx t (Set.uIoc_subset_uIcc ht)
    have hg : HasDerivAt (fun x : ℝ => x + (1 - x) * t ^ 2) (1 - t ^ 2) x := by
      have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) x := (hasDerivAt_id x).const_sub 1
      have h2 : HasDerivAt (fun x : ℝ => (1 - x) * t ^ 2) ((-1) * t ^ 2) x := h1.mul_const (t^2)
      have h3 : HasDerivAt (fun x : ℝ => x + (1 - x) * t ^ 2) (1 + (-1) * t^2) x :=
        (hasDerivAt_id x).add h2
      exact h3.congr_deriv (by ring)
    have hcomp := ((hdiff _ hp).hasDerivAt).comp x hg
    simpa only [hF, hF', Function.comp_def] using hcomp
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := 1) (bound := fun _ => M)
    (F := F) (F' := F') (x₀ := u) (s := Set.Ioo c 1)
    (isOpen_Ioo.mem_nhds hu) hFmeas hFint hF'meas hbound intervalIntegrable_const hdiff_all).2
  simpa only [hF, hF'] using hmain

/-- Integration by parts for the parametric integral: the vanishing `ψ 1 = 0` turns the
derivative `t * (d/dt) ψ(u + (1-u)t²)` into `-ψ`, giving
`∫_t 0..1, ψ (u + (1-u) t²) = -2(1-u) ∫_t 0..1, ψ' (u + (1-u) t²) t²`. -/
theorem abelIntegral_ibp {u : ℝ} (hu : u ≤ 1) {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    (hdiff : ∀ v ∈ Set.Icc u 1, DifferentiableAt ℝ ψ v)
    (hcont : ContinuousOn (deriv ψ) (Set.Icc u 1)) :
    (∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2))
      = - (2 * (1 - u)) * ∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2 := by
  have hmap : ∀ x ∈ Set.uIcc (0:ℝ) 1, u + (1 - u) * x ^ 2 ∈ Set.Icc u 1 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have h1 : 0 ≤ (1 - u) * x^2 := mul_nonneg (by linarith [hu]) (sq_nonneg x)
    have h2 : (1 - u) * x^2 ≤ (1 - u) * 1 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hx.1, hx.2]) (by linarith [hu])
    exact ⟨by linarith, by linarith⟩
  have hv_deriv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => ψ (u + (1 - u) * x ^ 2))
        (deriv ψ (u + (1 - u) * x ^ 2) * (2 * (1 - u) * x)) x := by
    intro x hx
    have hg : HasDerivAt (fun x : ℝ => u + (1 - u) * x ^ 2) (2 * (1 - u) * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow (n := 2) (x := x)
      have h2 := h1.const_mul (1 - u)
      have h3 := h2.const_add u
      exact h3.congr_deriv (by ring)
    exact ((hdiff _ (hmap x hx)).hasDerivAt).comp x hg
  have hv'_int : IntervalIntegrable
      (fun x : ℝ => deriv ψ (u + (1 - u) * x ^ 2) * (2 * (1 - u) * x)) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    have h1 : ContinuousOn (fun x : ℝ => deriv ψ (u + (1 - u) * x ^ 2)) (Set.uIcc (0:ℝ) 1) := by
      simpa [Function.comp_def] using hcont.comp (by fun_prop : ContinuousOn (fun x : ℝ => u + (1-u)*x^2) (Set.uIcc (0:ℝ) 1)) hmap
    exact h1.mul (by fun_prop)
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0:ℝ)) (b := 1)
    (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1:ℝ))
    (v := fun x : ℝ => ψ (u + (1 - u) * x ^ 2))
    (v' := fun x : ℝ => deriv ψ (u + (1 - u) * x ^ 2) * (2 * (1 - u) * x))
    (fun x _ => hasDerivAt_id x) hv_deriv intervalIntegrable_const hv'_int
  have hcongr : (∫ x in (0:ℝ)..1, x * (deriv ψ (u + (1 - u) * x ^ 2) * (2 * (1 - u) * x)))
      = 2 * (1 - u) * ∫ x in (0:ℝ)..1, deriv ψ (u + (1 - u) * x ^ 2) * x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul (μ := volume) (a := (0:ℝ)) (b := 1)
      (2 * (1 - u)) (fun x : ℝ => deriv ψ (u + (1 - u) * x ^ 2) * x ^ 2)]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have key : 2 * (1 - u) * (∫ x in (0:ℝ)..1, deriv ψ (u + (1 - u) * x ^ 2) * x ^ 2)
      = - (∫ x in (0:ℝ)..1, ψ (u + (1 - u) * x ^ 2)) := by
    rw [← hcongr, hIBP]
    have h1 : u + (1 - u) * (1:ℝ) ^ 2 = 1 := by ring
    rw [h1, hψ1]
    simp
  have hJ : (∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2))
      = - (2 * (1 - u) * (∫ x in (0:ℝ)..1, deriv ψ (u + (1 - u) * x ^ 2) * x ^ 2)) := by
    linarith [key]
  calc (∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2))
      = - (2 * (1 - u) * (∫ x in (0:ℝ)..1, deriv ψ (u + (1 - u) * x ^ 2) * x ^ 2)) := hJ
    _ = - (2 * (1 - u)) * ∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2 := by ring

/-- The first-derivative formula for the Abel transform: for `ψ` vanishing at `1`,
`(abelF ψ)' u = abelF ψ' u = ∫_v u..1, ψ' v / √(v-u)` on `(c,1)`. -/
theorem deriv_abelF_eq {c : ℝ} (hc : c < 1) {ψ : ℝ → ℝ} (hψ1 : ψ 1 = 0)
    (hdiff : ∀ v ∈ Set.Icc c 1, DifferentiableAt ℝ ψ v)
    (hcont : ContinuousOn (deriv ψ) (Set.Icc c 1)) :
    ∀ u ∈ Set.Ioo c 1,
      deriv (Work.OddVolterra.Existence.abelF ψ) u
        = Work.OddVolterra.Existence.abelF (deriv ψ) u := by
  intro u hu
  have hu1 : u ≤ 1 := le_of_lt hu.2
  have hcu : c ≤ u := le_of_lt hu.1
  have hG : Work.OddVolterra.Existence.abelF ψ =ᶠ[𝓝 u]
      fun x : ℝ => 2 * Real.sqrt (1 - x) * ∫ t in (0:ℝ)..1, ψ (x + (1 - x) * t ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact abelF_subst (le_of_lt hx.2)
  rw [hG.deriv_eq]
  have hdiff' : ∀ v ∈ Set.Icc u 1, DifferentiableAt ℝ ψ v :=
    fun v hv => hdiff v ⟨le_trans hcu hv.1, hv.2⟩
  have hcont' : ContinuousOn (deriv ψ) (Set.Icc u 1) :=
    hcont.mono (fun v hv => ⟨le_trans hcu hv.1, hv.2⟩)
  have hIBP := abelIntegral_ibp hu1 hψ1 hdiff' hcont'
  have hAderiv := abelIntegral_hasDerivAt hc hdiff hcont u hu
  have hs_pos : 0 < Real.sqrt (1 - u) := Real.sqrt_pos_of_pos (by linarith [hu.2])
  have hsqrt : HasDerivAt (fun x : ℝ => 2 * Real.sqrt (1 - x)) (-(Real.sqrt (1 - u))⁻¹) u := by
    have hne : (1:ℝ) - u ≠ 0 := by linarith [hu.2]
    have h1 : HasDerivAt (fun x : ℝ => (1:ℝ) - x) (-1) u := (hasDerivAt_id u).const_sub 1
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x)) (1 / (2 * Real.sqrt (1 - u)) * (-1)) u :=
      (Real.hasDerivAt_sqrt hne).comp u h1
    have h3 := h2.const_mul 2
    refine h3.congr_deriv ?_
    have hsne : Real.sqrt (1 - u) ≠ 0 := ne_of_gt hs_pos
    field_simp
  have hmul : HasDerivAt
      (fun x : ℝ => 2 * Real.sqrt (1 - x) * (∫ t in (0:ℝ)..1, ψ (x + (1 - x) * t ^ 2)))
      ((-(Real.sqrt (1 - u))⁻¹) * (∫ t in (0:ℝ)..1, ψ (u + (1 - u) * t ^ 2))
        + (2 * Real.sqrt (1 - u)) * (∫ t in (0:ℝ)..1,
            deriv ψ (u + (1 - u) * t ^ 2) * (1 - t ^ 2))) u :=
    hsqrt.mul hAderiv
  rw [hmul.deriv]
  rw [abelF_subst (ψ := deriv ψ) hu1]
  rw [hIBP]
  have hbase : ContinuousOn (fun t : ℝ => deriv ψ (u + (1 - u) * t ^ 2)) (Set.uIcc (0:ℝ) 1) := by
    have hmap : ∀ x ∈ Set.uIcc (0:ℝ) 1, u + (1 - u) * x ^ 2 ∈ Set.Icc c 1 := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      constructor
      · have : 0 ≤ (1 - u) * x^2 := mul_nonneg (by linarith [hu1]) (sq_nonneg x)
        linarith [hcu]
      · have h2 : (1 - u) * x^2 ≤ (1 - u) * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [hx.1, hx.2]) (by linarith [hu1])
        linarith [hu.2]
    simpa [Function.comp_def] using hcont.comp (by fun_prop : ContinuousOn (fun t : ℝ => u + (1-u)*t^2) (Set.uIcc (0:ℝ) 1)) hmap
  have hC_int : IntervalIntegrable
      (fun t : ℝ => deriv ψ (u + (1 - u) * t ^ 2) * (1 - t ^ 2)) volume (0:ℝ) 1 :=
    (hbase.mul (by fun_prop)).intervalIntegrable
  have hB_int : IntervalIntegrable
      (fun t : ℝ => deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2) volume (0:ℝ) 1 :=
    (hbase.mul (by fun_prop)).intervalIntegrable
  have hsplit : (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * (1 - t ^ 2))
      + (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2)
      = ∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) := by
    rw [← intervalIntegral.integral_add hC_int hB_int]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hsinv : (Real.sqrt (1 - u))⁻¹ * (2 * (1 - u)) = 2 * Real.sqrt (1 - u) := by
    have hsne : Real.sqrt (1 - u) ≠ 0 := ne_of_gt hs_pos
    field_simp
    rw [Real.sq_sqrt (by linarith [hu.2])]
  have hstep : -(Real.sqrt (1 - u))⁻¹
        * (-(2 * (1 - u)) * (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2))
      = 2 * Real.sqrt (1 - u) * (∫ t in (0:ℝ)..1,
          deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2) := by
    rw [show -(Real.sqrt (1 - u))⁻¹ * (-(2 * (1 - u))
          * (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2))
        = (Real.sqrt (1 - u))⁻¹ * (2 * (1 - u))
          * (∫ t in (0:ℝ)..1, deriv ψ (u + (1 - u) * t ^ 2) * t ^ 2) from by ring]
    rw [hsinv]
  rw [hstep, ← hsplit]
  ring

/-- **The second derivative of the Abel transform.**  If `φ` is `C²` on `[c,1]` with
`φ 1 = φ' 1 = 0` and `|φ''| ≤ K`, then `|(abelF φ)''| ≤ 2√(1-c) K` on `(c,d)`, `d ≤ 1`. -/
theorem abelF_deriv2_bound {c d : ℝ} (hc0 : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : ℝ → ℝ} {K : ℝ}, 0 ≤ K → φ 1 = 0 → deriv φ 1 = 0 →
      (∀ u ∈ Set.Icc c 1, DifferentiableAt ℝ φ u) →
      (∀ u ∈ Set.Icc c 1, DifferentiableAt ℝ (deriv φ) u) →
      ContinuousOn (deriv φ) (Set.Icc c 1) →
      ContinuousOn (deriv (deriv φ)) (Set.Icc c 1) →
      (∀ v ∈ Set.Ioo c 1, |deriv (deriv φ) v| ≤ K) →
      ∀ s ∈ Set.Ioo c d,
        |deriv (deriv (Work.OddVolterra.Existence.abelF φ)) s| ≤ C * K := by
  have hc1 : c < 1 := lt_of_lt_of_le hcd hd
  refine ⟨2 * Real.sqrt (1 - c), by positivity, ?_⟩
  intro φ K hK hφ1 hdφ1 hdiff hdiff2 hcont hcont2 hbnd s hs
  have hs1 : s < 1 := lt_of_lt_of_le hs.2 hd
  have hsu : s ∈ Set.Ioo c 1 := ⟨hs.1, hs1⟩
  -- step 1: the derivative of `abelF φ` is `abelF φ'` near `s`
  have hF1 : deriv (Work.OddVolterra.Existence.abelF φ) =ᶠ[𝓝 s]
      Work.OddVolterra.Existence.abelF (deriv φ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hsu] with u hu
    exact deriv_abelF_eq hc1 hφ1 hdiff hcont u hu
  have hstep1 : deriv (deriv (Work.OddVolterra.Existence.abelF φ)) s
      = deriv (Work.OddVolterra.Existence.abelF (deriv φ)) s := hF1.deriv_eq
  rw [hstep1]
  -- step 2: the derivative of `abelF φ'` at `s` is `abelF φ''`
  rw [deriv_abelF_eq hc1 hdφ1 hdiff2 hcont2 s hsu]
  -- step 3: bound the remaining Abel transform
  rw [abelF_subst (ψ := deriv (deriv φ)) (le_of_lt hs1)]
  have hmem : ∀ t ∈ Set.uIcc (0:ℝ) 1, s + (1 - s) * t ^ 2 ∈ Set.Icc c 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have h2 : (1 - s) * t^2 ≤ (1 - s) * 1 :=
      mul_le_mul_of_nonneg_left (by nlinarith [ht.1, ht.2]) (by linarith [hs1])
    have h1 : 0 ≤ (1 - s) * t^2 := mul_nonneg (by linarith [hs1]) (sq_nonneg t)
    exact ⟨by linarith [hs.1], by linarith [hs1]⟩
  have hcontg : ContinuousOn (fun t : ℝ => deriv (deriv φ) (s + (1 - s) * t ^ 2))
      (Set.uIcc (0:ℝ) 1) := by
    simpa [Function.comp_def] using hcont2.comp
      (by fun_prop : ContinuousOn (fun t : ℝ => s + (1 - s) * t ^ 2) (Set.uIcc (0:ℝ) 1)) hmem
  have hint1 : IntervalIntegrable (fun t : ℝ => |deriv (deriv φ) (s + (1 - s) * t ^ 2)|)
      volume (0:ℝ) 1 := hcontg.abs.intervalIntegrable
  have hint2 : IntervalIntegrable (fun _ : ℝ => K) volume (0:ℝ) 1 := intervalIntegrable_const
  have hI : |∫ t in (0:ℝ)..1, deriv (deriv φ) (s + (1 - s) * t ^ 2)| ≤ K := by
    calc |∫ t in (0:ℝ)..1, deriv (deriv φ) (s + (1 - s) * t ^ 2)|
        ≤ ∫ t in (0:ℝ)..1, |deriv (deriv φ) (s + (1 - s) * t ^ 2)| :=
          intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, K := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hint1 hint2 (fun t ht => ?_)
          have hpoint : s + (1 - s) * t ^ 2 ∈ Set.Ioo c 1 := by
            have h3 : 0 < (1 - s) * t^2 :=
              mul_pos (by linarith [hs1]) (pow_pos ht.1 2)
            have h4 : (1 - s) * t^2 < (1 - s) * 1 :=
              mul_lt_mul_of_pos_left (by nlinarith [ht.1, ht.2]) (by linarith [hs1])
            exact ⟨by linarith [hs.1], by linarith⟩
          exact hbnd _ hpoint
      _ = K := by simp
  calc |2 * Real.sqrt (1 - s) * (∫ t in (0:ℝ)..1, deriv (deriv φ) (s + (1 - s) * t ^ 2))|
      = 2 * Real.sqrt (1 - s)
          * |∫ t in (0:ℝ)..1, deriv (deriv φ) (s + (1 - s) * t ^ 2)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 2 * Real.sqrt (1 - s) * K := mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ 2 * Real.sqrt (1 - c) * K := by
        apply mul_le_mul_of_nonneg_right ?_ hK
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [hs.1])) (by norm_num)

end

end Work.OddVolterra.Abel
