import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The concrete bump of the `p = ∞` endpoint of Tao's `ortho-apply`(ii)

Tao's `ortho-apply`(ii) (arXiv:2008.05066, §4) is applied to a fixed smooth bump `φ` on the circle
`𝕋 = ℝ/ℤ`, supported in a ball of radius `ε`, whose Fourier coefficients decay rapidly.  This file
supplies such a bump concretely.
-/

open MeasureTheory
open scoped BigOperators ENNReal SchwartzMap FourierTransform

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The decay of the Fourier transform of a Schwartz function -/

/-- **The Fourier transform of a Schwartz function decays at least like `(1 + u²)^{-3/2}`**: the
quantity `(1 + u²)^{3/2}‖𝓕ψ u‖` is bounded by the Schwartz seminorm of `𝓕ψ` of order `(3,0)`. -/
theorem schwartz_fourier_decay (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      (1 + u ^ 2) ^ ((3:ℝ)/2) * ‖((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖ ≤ C := by
  let K : ℝ := Finset.sup (Finset.Iic ((3, 0) : ℕ × ℕ))
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 ψ)
  refine ⟨2 ^ 3 * K, by positivity, fun u => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((3, 0) : ℕ × ℕ))
      (k := 3) (n := 0) (le_refl 3) (Nat.zero_le 0) (𝓕 ψ) u
  rw [norm_iteratedFDeriv_zero] at h
  have h2 : (1 + u ^ 2) ^ ((3:ℝ)/2) ≤ (1 + ‖u‖) ^ 3 := by
    have h3 : (1 : ℝ) + u ^ 2 ≤ (1 + ‖u‖) ^ 2 := by
      rw [Real.norm_eq_abs]; nlinarith [abs_nonneg u, sq_abs u]
    calc (1 + u ^ 2) ^ ((3:ℝ)/2) ≤ ((1 + ‖u‖) ^ 2) ^ ((3:ℝ)/2) :=
          Real.rpow_le_rpow (by positivity) h3 (by norm_num)
      _ = (1 + ‖u‖) ^ (3:ℝ) := by
          rw [← Real.rpow_natCast (1 + ‖u‖) 2,
            ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 + ‖u‖)]
          norm_num
      _ = (1 + ‖u‖) ^ 3 := Real.rpow_natCast _ 3
  calc (1 + u ^ 2) ^ ((3:ℝ)/2) * ‖((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖
      ≤ (1 + ‖u‖) ^ 3 * ‖((𝓕 ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) u‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ 2 ^ 3 * K := h

/-! ## A concrete Schwartz bump -/

/-- **A concrete Schwartz bump**: a nonzero Schwartz function on `ℝ` whose support is contained in
the half-open interval `(0, 1/2]`.  It is the standard smooth bump `ContDiffBump (1/4)` with radii
`(1/16, 1/8)`, promoted to the Schwartz space (smooth with compact support), with values read in
`ℂ`. -/
theorem exists_schwartz_bump :
    ∃ ψ : 𝓢(ℝ, ℂ), Function.support (fun t : ℝ => ψ t) ⊆ Set.Ioc (0 : ℝ) (1 / 2) ∧
      ψ (1 / 4) ≠ 0 := by
  let b : ContDiffBump (1 / 4 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩
  have hcpt : HasCompactSupport (fun t : ℝ => (b t : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (b t : ℂ)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := b.contDiff
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) :=
      Complex.ofRealCLM.contDiff
    exact h2.comp h1
  refine ⟨hcpt.toSchwartzMap hcd, ?_, ?_⟩
  · intro t ht
    have ht' : (b t : ℂ) ≠ 0 := ht
    have ht'' : b t ≠ 0 := by exact_mod_cast ht'
    have hmem : t ∈ Metric.ball (1 / 4 : ℝ) (1 / 8) := by
      rw [← b.support_eq]; exact ht''
    rw [Metric.mem_ball, Real.dist_eq] at hmem
    have h1 : |t - 1 / 4| < 1 / 8 := hmem
    have h2 := abs_lt.mp h1
    rw [Set.mem_Ioc]
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · have h1 : b (1 / 4) = 1 :=
      b.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; norm_num)
    change ((b (1 / 4) : ℝ) : ℂ) ≠ 0
    rw [h1]
    norm_num

/-! ## The bump on the circle -/

/-- **The concrete bump on the circle**: `φ(ξ) = ψ(x/ε)`, where `x` is the representative of `ξ`
in `(0, 1]`. -/
def bump (ψ : ℝ → ℂ) (ε : ℝ) : Circle → ℂ :=
  AddCircle.liftIoc 1 0 (fun x => ψ (x / ε))

theorem bump_apply (ψ : ℝ → ℂ) (ε : ℝ) (ξ : Circle) :
    bump ψ ε ξ = ψ ((AddCircle.equivIoc 1 0 ξ : ℝ) / ε) := rfl

/-- **The bump is supported in the ball of radius `ε`** (Tao's `φ` supported in `B(0,ε)`). -/
theorem bump_eq_zero_of_lt_norm {ψ : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1)
    (hψ : Function.support ψ ⊆ Set.Ioc (0 : ℝ) (1 / 2)) {ξ : Circle} (hξ : ε < ‖ξ‖) :
    bump ψ ε ξ = 0 := by
  by_contra hne
  have hr : ((AddCircle.equivIoc 1 0 ξ : ℝ)) ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa using (AddCircle.equivIoc 1 0 ξ).2
  set r : ℝ := (AddCircle.equivIoc 1 0 ξ : ℝ) with hrdef
  have hrpos : 0 < r := hr.1
  have hψne : ψ (r / ε) ≠ 0 := by rwa [bump_apply] at hne
  have hmem : r / ε ∈ Set.Ioc (0 : ℝ) (1 / 2) := hψ hψne
  have h3 : r ≤ ε / 2 := by
    have h4 : r / ε ≤ 1 / 2 := hmem.2
    rw [div_le_iff₀ hε] at h4
    linarith
  have hcoe : ((r : ℝ) : Circle) = ξ := by rw [hrdef]; exact AddCircle.coe_equivIoc
  by_cases hle : r ≤ 1 / 2
  · have hnorm : ‖ξ‖ = r := by
      rw [← hcoe]
      rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
        (by rw [abs_of_pos hrpos]; linarith), abs_of_pos hrpos]
    rw [hnorm] at hξ
    linarith
  · push Not at hle
    linarith

/-- **The concrete bump is continuous** on the circle, provided `ε < 2`: the lift is continuous
because `ψ` vanishes at both `0` and `1/ε` (the latter since `1/ε > 1/2`). -/
theorem bump_continuous {ψ : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) (hψc : Continuous ψ)
    (hψ : Function.support ψ ⊆ Set.Ioc (0 : ℝ) (1 / 2)) : Continuous (bump ψ ε) := by
  have hzero : ψ 0 = 0 := by
    by_contra h
    exact absurd (hψ h).1 (lt_irrefl 0)
  have hzero' : ψ (1 / ε) = 0 := by
    by_contra h
    have h1 : 1 / ε ≤ 1 / 2 := (hψ h).2
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have hb : bump ψ ε = AddCircle.liftIoc 1 0 (fun x => ψ (x / ε)) := rfl
  rw [hb]
  refine AddCircle.liftIoc_zero_continuous ?_ ?_
  · show ψ (0 / ε) = ψ (1 / ε)
    rw [zero_div, hzero, hzero']
  · exact hψc.comp_continuousOn (continuousOn_id.div_const ε)

/-- **The concrete bump is in `L^∞` of the circle**. -/
theorem bump_memLp {ψ : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 2) (hψc : Continuous ψ)
    (hψ : Function.support ψ ⊆ Set.Ioc (0 : ℝ) (1 / 2)) {C : ℝ} (hC : ∀ t, ‖ψ t‖ ≤ C) :
    MemLp (bump ψ ε) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  refine MemLp.of_bound (bump_continuous hε hε2 hψc hψ).aestronglyMeasurable C ?_
  filter_upwards with ξ
  rw [bump_apply]
  exact hC _

/-! ## The Fourier coefficients of the concrete bump -/

/-- **The Fourier coefficients of the concrete bump, in explicit form**: with
`h t = e^{-2πiεmt}ψ(t)`, the `m`-th Fourier coefficient of `φ = bump ψ ε` is `ε ∫_ℝ h` (the change
of variables `x = ε t` in the interval integral over `(0,1]`). -/
theorem bump_fourierCoeff_exp {ψ : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hψ : Function.support ψ ⊆ Set.Ioc (0 : ℝ) (1 / 2)) (m : ℤ) :
    (∫ ξ, bump ψ ε ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = ε * ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * (ε * m)) * Complex.I) * ψ t := by
  have hstarc : ∀ z : ℂ, star z = starRingEnd ℂ z := fun z => congrFun Complex.star_def z
  set h : ℝ → ℂ := fun t => fourier (-m) ((ε * t : ℝ) : Circle) * ψ t with hh
  have step1 : (∫ ξ, bump ψ ε ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ x in (0 : ℝ)..1, fourier (-m) (x : Circle) * ψ (x / ε) := by
    rw [show (∫ ξ, bump ψ ε ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
        = fourierCoeff (bump ψ ε) m from ?_]
    · rw [fourierCoeff_eq_intervalIntegral (bump ψ ε) m 0, zero_add, div_one, one_smul]
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
      have hx' : x ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        have h1 : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
        simpa using h1
      have hlift := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := (0 : ℝ))
        (f := fun x => ψ (x / ε)) hx'
      change (fourier (-m) (x : Circle)) • (bump ψ ε (x : Circle)) = _
      rw [show bump ψ ε (x : Circle) = ψ (x / ε) from hlift, smul_eq_mul]
    · rw [fourierCoeff]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      dsimp only
      rw [hstarc, fourier_neg]
      ring
  have stepA : (∫ x in (0 : ℝ)..1, (fourier (-m) (x : Circle)) * ψ (x / ε))
      = ∫ x in (0 : ℝ)..1, h (x / ε) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x _ => ?_)
    rw [hh]
    simp only []
    rw [mul_div_cancel₀ x (ne_of_gt hε)]
  have stepB : (∫ x in (0 : ℝ)..1, h (x / ε)) = ∫ x in (0 : ℝ)..1, h (ε⁻¹ * x) := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x _ => ?_)
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  have stepC : (∫ x in (0 : ℝ)..1, h (ε⁻¹ * x)) = ε * ∫ t in (0 : ℝ)..ε⁻¹, h t := by
    have hcomp := intervalIntegral.integral_comp_mul_left (f := h) (a := (0 : ℝ)) (b := 1)
      (c := ε⁻¹) (by positivity)
    rw [mul_zero, mul_one, inv_inv] at hcomp
    rw [hcomp]
    exact Complex.real_smul
  have step3 : (∫ t in (0 : ℝ)..ε⁻¹, h t) = ∫ t : ℝ, h t := by
    have h2 : (1 : ℝ) / 2 ≤ ε⁻¹ := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hε hε2
    refine intervalIntegral.integral_eq_integral_of_support_subset ?_
    intro t ht
    have htψ : ψ t ≠ 0 := fun h0 => ht (by rw [hh]; simp only []; rw [h0, mul_zero])
    have hmem := hψ htψ
    exact ⟨hmem.1, le_trans hmem.2 h2⟩
  have step4 : (∫ t : ℝ, h t)
      = ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * (ε * m)) * Complex.I) * ψ t := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    rw [hh]
    simp only []
    rw [fourier_coe_apply]
    congr 1
    congr 1
    push_cast
    ring
  rw [step1, stepA, stepB, stepC, step3, step4]

/-- The Fourier coefficient sequence of the concrete bump `bump ψ ε` with `ψ` the Schwartz
function `Ψ`: `ε · 𝓕Ψ (ε m)`. -/
noncomputable def bumpCoeff (Ψ : 𝓢(ℝ, ℂ)) (ε : ℝ) : ℤ → ℂ :=
  fun m => ε * ((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (ε * m)

/-- **The Fourier coefficients of the concrete bump**: for a Schwartz bump `Ψ` supported in
`(0, 1/2]` and `0 < ε ≤ 2`, the `m`-th Fourier coefficient of `bump Ψ ε` is `bumpCoeff Ψ ε m`,
i.e. `ε · 𝓕Ψ (ε m)` -- the change of variables `x = ε t` in the interval integral over `(0,1]`. -/
theorem bump_fourierCoeff {Ψ : 𝓢(ℝ, ℂ)} {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hΨ : Function.support (fun t : ℝ => Ψ t) ⊆ Set.Ioc (0 : ℝ) (1 / 2)) (m : ℤ) :
    (∫ ξ, bump (fun t : ℝ => Ψ t) ε ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)))
      = bumpCoeff Ψ ε m := by
  rw [bump_fourierCoeff_exp (ψ := fun t : ℝ => Ψ t) hε hε2 hΨ m]
  unfold bumpCoeff
  congr 1
  have hcoe : ((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (fun t : ℝ => Ψ t) := rfl
  rw [hcoe, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  dsimp only
  rw [smul_eq_mul]

/-- **The decay of the Fourier coefficients of a Schwartz bump.** -/
theorem bumpCoeff_decay (Ψ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ,
      ‖bumpCoeff Ψ ε m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2) := by
  obtain ⟨C, hC0, hC⟩ := schwartz_fourier_decay Ψ
  refine ⟨C, hC0, fun m => ?_⟩
  have hpos : (0 : ℝ) < (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have h2 : ‖((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (ε * (m : ℝ))‖
      ≤ C / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2) := by
    rw [le_div_iff₀ hpos]
    simpa [mul_comm] using hC (ε * (m : ℝ))
  have hnorm : ‖((ε : ℝ) : ℂ)‖ = ε := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, abs_of_nonneg hε]
  calc ‖bumpCoeff Ψ ε m‖
      = ε * ‖((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (ε * (m : ℝ))‖ := by
        unfold bumpCoeff
        rw [norm_mul, hnorm]
    _ ≤ ε * (C / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left h2 hε
    _ = C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2) := by ring


/-- **The concrete bump of the `p = ∞` endpoint, packaged.**  For every `0 < ε ≤ 1` there is a
bump `φ` on the circle (supported in the ball of radius `ε`, nontrivial, in `L^∞`) whose Fourier
coefficients `K m = ∫ φ · conj(e^{2πim·})` decay as `C ε (1 + (εm)²)^{-3/2}`.  This is exactly the
data required by the `p = ∞` endpoint of Tao's `ortho-apply`(ii)
(`opArc_sup_torsion_family`). -/
theorem exists_bump_package {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1) :
    ∃ (φ : Circle → ℂ) (K : ℤ → ℂ) (C : ℝ), 0 ≤ C ∧
      MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)) ∧
      (∀ ξ : Circle, ε < ‖ξ‖ → φ ξ = 0) ∧
      (∃ ξ : Circle, φ ξ ≠ 0) ∧
      (∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m) ∧
      (∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3:ℝ)/2)) := by
  obtain ⟨Ψ, hΨsupp, hΨ14⟩ := exists_schwartz_bump
  obtain ⟨C, hC0, hCdecay⟩ := bumpCoeff_decay Ψ (le_of_lt hε)
  have hM : ∃ M : ℝ, ∀ t : ℝ, ‖(fun t : ℝ => Ψ t) t‖ ≤ M := by
    refine ⟨Finset.sup (Finset.Iic ((0, 0) : ℕ × ℕ))
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) Ψ, fun t => ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((0, 0) : ℕ × ℕ))
      (k := 0) (n := 0) le_rfl le_rfl Ψ t
    rw [norm_iteratedFDeriv_zero] at h
    simpa using h
  obtain ⟨M, hM⟩ := hM
  refine ⟨bump (fun t : ℝ => Ψ t) ε, bumpCoeff Ψ ε, C, hC0, ?_, ?_, ?_, ?_, ?_⟩
  · exact bump_memLp hε (by linarith) Ψ.continuous hΨsupp hM
  · intro ξ
    exact bump_eq_zero_of_lt_norm hε hε2 hΨsupp
  · refine ⟨((ε / 4 : ℝ) : Circle), ?_⟩
    rw [bump_apply]
    have hmem : ε / 4 ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
      ⟨by positivity, by linarith⟩
    have hcoe : (AddCircle.equivIoc 1 0 ((ε / 4 : ℝ) : Circle) : ℝ) = ε / 4 := by
      rw [AddCircle.equivIoc_coe_of_mem hmem]
    rw [hcoe]
    have hdiv : ε / 4 / ε = 1 / 4 := by field_simp
    rw [hdiv]
    exact hΨ14
  · intro m
    exact bump_fourierCoeff hε (by linarith) hΨsupp m
  · exact hCdecay

end

end Work.BourgainPlan.IonescuWainger
