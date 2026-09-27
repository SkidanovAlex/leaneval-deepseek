import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germCHelpers

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

/-- Near the origin (with the exceptional point `u = 0` excluded) the quantity
`R(u) = -E(u) · S(u)`, where `E(u) = a h(λ²u)/(h(λ²u) - h(λu))` (`λ = eqLam a`) and
`S(u) = (1 + h(λu)²)^{1/2}` with the principal square root, is an honest quotient
(`h(λ²u) ≠ h(λu)` there) with positive real part.  Indeed `R(u) → a·λ/(1-λ) = (1-a)/2 > 0`
as `u → 0`, since `h(w) = w · dslope h 0 w` and `dslope h 0 w → h'(0) = -1`.  This is exactly
the hypothesis `0 < R.re` of `Work.EQ.germC_step_algebra`. -/
theorem germC_R_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ → u ≠ 0 →
      h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u) ≠ 0 ∧
      0 < (-((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
              (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u))) *
            (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ)).re := by
  obtain ⟨hr, hAn, h0, hderiv, hreal, hFE⟩ := hh
  -- analyticity at `0` and the value/differentiability of `h` there
  have hAn0 : AnalyticAt ℂ h 0 := hAn 0 (by simpa using hr)
  have hd : HasDerivAt h (-1) 0 := by
    have h1 := hAn0.differentiableAt.hasDerivAt
    rwa [hderiv] at h1
  -- `dslope h 0` is continuous at `0` with value `h'(0) = -1`
  have hcontN : ContinuousAt (dslope h 0) 0 := (continuousAt_dslope_same).mpr hd.differentiableAt
  have hN0 : dslope h 0 0 = -1 := by rw [dslope_same, hderiv]
  -- `λ = eqLam a` lies in `(0,1)`, hence `λ ≠ 0` and `λ ≠ 1`
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamC_ne : (eqLam a : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]; exact ne_of_gt hl0
  have hlamC_1 : (eqLam a : ℂ) ≠ 1 := by
    intro hc
    have h2 : eqLam a = 1 := by exact_mod_cast hc
    linarith
  have h1mlam : (1 : ℂ) - (eqLam a : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlamC_1)
  -- the three building blocks: `A u = dslope h 0 (λ²u)`, `B u = dslope h 0 (λu)`,
  -- the denominator `D u = λ A u - B u`, and the square-root factor `T u = (1 + h(λu)²)^{1/2}`
  set A : ℂ → ℂ := fun u => dslope h 0 ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) with hA
  set B : ℂ → ℂ := fun u => dslope h 0 ((eqLam a : ℂ) * u) with hB
  set D : ℂ → ℂ := fun u => (eqLam a : ℂ) * A u - B u with hD
  set T : ℂ → ℂ := fun u => (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ) with hT
  have hcomp2 : ContinuousAt (fun u : ℂ => (eqLam a : ℂ) * ((eqLam a : ℂ) * u)) 0 :=
    ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const continuousAt_id)
  have hcomp1 : ContinuousAt (fun u : ℂ => (eqLam a : ℂ) * u) 0 :=
    ContinuousAt.mul continuousAt_const continuousAt_id
  have hcontA : ContinuousAt A 0 := by
    rw [hA]
    have hN' : ContinuousAt (dslope h 0) ((eqLam a : ℂ) * ((eqLam a : ℂ) * 0)) := by
      rw [mul_zero, mul_zero]; exact hcontN
    exact ContinuousAt.comp hN' hcomp2
  have hcontB : ContinuousAt B 0 := by
    rw [hB]
    have hN' : ContinuousAt (dslope h 0) ((eqLam a : ℂ) * 0) := by
      rw [mul_zero]; exact hcontN
    exact ContinuousAt.comp hN' hcomp1
  have hcontD : ContinuousAt D 0 := by
    rw [hD]
    exact (ContinuousAt.mul continuousAt_const hcontA).sub hcontB
  have hA0 : A 0 = -1 := by simp only [hA, mul_zero, hN0]
  have hB0 : B 0 = -1 := by simp only [hB, mul_zero, hN0]
  have hD0 : D 0 = 1 - (eqLam a : ℂ) := by simp only [hD, hA0, hB0]; ring
  have hDne0 : D 0 ≠ 0 := by rw [hD0]; exact h1mlam
  have hevD : ∀ᶠ u in 𝓝 (0 : ℂ), D u ≠ 0 := hcontD.eventually_ne hDne0
  have hThcont : ContinuousAt (fun u : ℂ => h ((eqLam a : ℂ) * u)) 0 := by
    have hh' : ContinuousAt h ((eqLam a : ℂ) * 0) := by rw [mul_zero]; exact hAn0.continuousAt
    exact ContinuousAt.comp hh' hcomp1
  have hcontT : ContinuousAt T 0 := by
    rw [hT]
    refine (ContinuousAt.add continuousAt_const (hThcont.pow 2)).cpow continuousAt_const ?_
    show (1 + h ((eqLam a : ℂ) * 0) ^ 2) ∈ Complex.slitPlane
    rw [mul_zero, h0]
    norm_num
  have hT0 : T 0 = 1 := by
    rw [hT]
    show (1 + h ((eqLam a : ℂ) * 0) ^ 2) ^ (1 / 2 : ℂ) = 1
    rw [mul_zero, h0]
    norm_num
  -- the limit quantity `G`, equal to `R(u)` for `u ≠ 0` near `0`
  set G : ℂ → ℂ := fun u => -((a : ℂ) * ((eqLam a : ℂ) * A u) / D u) * T u with hG
  have hcontNum : ContinuousAt (fun u : ℂ => (a : ℂ) * ((eqLam a : ℂ) * A u) / D u) 0 :=
    (ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const hcontA)).div hcontD
      hDne0
  have hcontG : ContinuousAt G 0 := by
    rw [hG]
    exact hcontNum.neg.mul hcontT
  have hG_apply : ∀ u, G u = -((a : ℂ) * ((eqLam a : ℂ) * A u) / D u) * T u := fun u => by
    simp only [hG]
  have hD_apply : ∀ u, D u = (eqLam a : ℂ) * A u - B u := fun u => by simp only [hD]
  -- `G 0 = a·λ/(1-λ) > 0`
  have hG0 : G 0 = ((a * eqLam a / (1 - eqLam a) : ℝ) : ℂ) := by
    rw [hG_apply]
    simp only [hA0, hD0, hT0]
    rw [show ((1 : ℂ) - (eqLam a : ℂ)) = ((1 - eqLam a : ℝ) : ℂ) by push_cast; ring]
    have hne : ((1 - eqLam a : ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]; linarith
    push_cast
    field_simp
  have hG0re : 0 < (G 0).re := by
    rw [hG0, Complex.ofReal_re]
    exact div_pos (mul_pos ha0 hl0) (by linarith)
  have hevG : ∀ᶠ u in 𝓝 (0 : ℂ), 0 < (G u).re :=
    hcontG.tendsto.eventually
      (IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hG0re)
  -- a single ball on which both the denominator and the real part stay positive
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hevD.and hevG)
  refine ⟨δ, hδpos, ?_⟩
  intro u hu hu0
  have hu' : dist u (0 : ℂ) < δ := by simpa [Metric.mem_ball] using hu
  obtain ⟨hDu, hGre⟩ := hδ hu'
  have hlune : (eqLam a : ℂ) * u ≠ 0 := mul_ne_zero hlamC_ne hu0
  have hDune : (eqLam a : ℂ) * A u - B u ≠ 0 := by
    rw [← hD_apply u]; exact hDu
  -- `h(w) = w · dslope h 0 w` at `w = λ²u` and `w = λu`
  have e1 : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u))
      = ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) * A u := by
    have hthis := (mul_dslope_eq (f := h) (v := (eqLam a : ℂ) * ((eqLam a : ℂ) * u)) h0).symm
    simpa [hA] using hthis
  have e2 : h ((eqLam a : ℂ) * u) = ((eqLam a : ℂ) * u) * B u := by
    have hthis := (mul_dslope_eq (f := h) (v := (eqLam a : ℂ) * u) h0).symm
    simpa [hB] using hthis
  have hdiff : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u)
      = ((eqLam a : ℂ) * u) * ((eqLam a : ℂ) * A u - B u) := by
    rw [e1, e2]; ring
  constructor
  · rw [hdiff]; exact mul_ne_zero hlune hDune
  · -- `-(a h(λ²u)/(h(λ²u) - h(λu))) · T u = G u`, whose real part is positive
    have hquot : (a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
        (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u))
        = (a : ℂ) * ((eqLam a : ℂ) * A u) / D u := by
      rw [hdiff, e1, hD_apply u]
      rw [show (a : ℂ) * (((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) * A u)
          = ((eqLam a : ℂ) * u) * ((a : ℂ) * ((eqLam a : ℂ) * A u)) by ring]
      rw [mul_div_mul_left _ _ hlune]
    have hGeq : G u = -((a : ℂ) * h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) /
          (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * u)) - h ((eqLam a : ℂ) * u))) *
        (1 + h ((eqLam a : ℂ) * u) ^ 2) ^ (1 / 2 : ℂ) := by
      simp only [hG, hT]
      rw [← hquot]
    exact hGeq ▸ hGre

end Work.EQ
