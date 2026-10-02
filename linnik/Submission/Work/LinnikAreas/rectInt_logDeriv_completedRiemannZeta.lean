import Mathlib
import Submission.Work.LinnikAreas.rectInt_logDeriv_entire_mul
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_mul_simplePole
import Submission.Commons.NumberTheory.Zeta.xi_logDeriv_re_lower_general
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_regular_bound

namespace Work.LinnikAreas

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

noncomputable section

open Commons.NumberTheory.DirichletCharacter

/-!
# Explicit formula on a rectangle for `ζ` and an entire kernel

We compute `∮_{∂R} logDeriv Λ · G ds` for `Λ = completedRiemannZeta`, `G` entire, and a
rectangle whose boundary avoids the poles and zeros of `Λ`.  The completed zeta function is
`Λ(s) = ξ(s) / ((1/2)·s·(s-1))` with `ξ = xiE_LG` entire; the argument principle applied to the
entire function `ξ` gives the sum over the zeros weighted by their order, and the two simple
poles of `Λ` at `0` and `1` contribute the correction `-G 0 - G 1`.
-/

/-- `completedRiemannZeta` is not analytic at `0` (it has a pole there). -/
private lemma not_analyticAt_completedRiemannZeta_zero :
    ¬ AnalyticAt ℂ completedRiemannZeta 0 := by
  intro h
  have hΛ₀ : AnalyticAt ℂ completedRiemannZeta₀ 0 :=
    differentiable_completedZeta₀.analyticAt 0
  have h1 : AnalyticAt ℂ ((1 : ℂ → ℂ) - id) 0 := analyticAt_const.sub analyticAt_id
  have hinv : AnalyticAt ℂ (fun s : ℂ => (1 - s)⁻¹) 0 := by
    have h1' : AnalyticAt ℂ (fun s : ℂ => (1 - s)) 0 := h1
    exact h1'.inv (by norm_num)
  have hfun : (fun s : ℂ => s⁻¹) =
      fun s : ℂ => completedRiemannZeta₀ s - (1 - s)⁻¹ - completedRiemannZeta s := by
    funext s
    rw [completedRiemannZeta_eq]
    ring
  have h2 : AnalyticAt ℂ (fun s : ℂ => s⁻¹) 0 := by
    rw [hfun]
    exact (hΛ₀.sub hinv).sub h
  have hdiff : DifferentiableAt ℂ (fun s : ℂ => s⁻¹) 0 := h2.differentiableAt
  rw [differentiableAt_inv_iff] at hdiff
  exact hdiff rfl

/-- `completedRiemannZeta` is not analytic at `1` (its residue there is `1 ≠ 0`). -/
private lemma not_analyticAt_completedRiemannZeta_one :
    ¬ AnalyticAt ℂ completedRiemannZeta 1 := by
  intro h
  have hcont : ContinuousAt (fun s : ℂ => (s - 1) * completedRiemannZeta s) 1 := by
    exact ((continuousAt_id.sub continuousAt_const).mul h.continuousAt)
  have htend : Tendsto (fun s : ℂ => (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
    have h' := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using h'
  have hz := tendsto_nhds_unique htend completedRiemannZeta_residue_one
  exact absurd hz (by norm_num)

/-- `Λ = completedRiemannZeta` is analytic at every point different from `0` and `1`. -/
private lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s :=
  DifferentiableOn.analyticAt (s := {t : ℂ | t ≠ 0 ∧ t ≠ 1})
    (fun t ht => (differentiableAt_completedZeta ht.1 ht.2).differentiableWithinAt)
    (by apply IsOpen.mem_nhds; exact isOpen_ne.inter isOpen_ne; exact ⟨h0, h1⟩)

/-- `xiE_LG` agrees with `(1/2)·s·(s-1)·Λ(s)` in a neighbourhood of any point different from
`0` and `1`. -/
private lemma xiE_LG_eventuallyEq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    Commons.NumberTheory.Zeta.xiE_LG =ᶠ[𝓝 s]
      fun t : ℂ => (1 / 2 : ℂ) * t * (t - 1) * completedRiemannZeta t := by
  have hopen : {t : ℂ | t ≠ 0 ∧ t ≠ 1} ∈ 𝓝 s := by
    apply IsOpen.mem_nhds
    · exact isOpen_ne.inter isOpen_ne
    · exact ⟨h0, h1⟩
  filter_upwards [hopen] with t ht
  rw [← Commons.NumberTheory.Zeta.xiG_LG_eq_xiE_LG_of_ne_zero_one ht.1 ht.2]
  rfl

theorem rectInt_logDeriv_completedRiemannZeta {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (hz0 : z.re < 0) (hw0 : 0 < w.re) (hz1 : z.re < 1) (hw1 : 1 < w.re)
    (hzim0 : z.im < 0) (hwim0 : 0 < w.im)
    (hnz : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      completedRiemannZeta s ≠ 0)
    (hpol : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w, s ≠ 0 ∧ s ≠ 1) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => logDeriv completedRiemannZeta s * G s) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
            then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℂ) * G ρ else 0))
          - G 1 - G 0) := by
  -- boundary points are different from `0` and `1`
  have hb0 : ∀ s ∈ rectBoundary z w, s ≠ 0 := fun s hs => (hpol s hs).1
  have hb1 : ∀ s ∈ rectBoundary z w, s ≠ 1 := fun s hs => (hpol s hs).2
  -- `0` and `1` lie strictly inside the rectangle
  have h0in : z.re < (0 : ℂ).re ∧ (0 : ℂ).re < w.re ∧ z.im < (0 : ℂ).im ∧ (0 : ℂ).im < w.im := by
    simpa using ⟨hz0, hw0, hzim0, hwim0⟩
  have h1in : z.re < (1 : ℂ).re ∧ (1 : ℂ).re < w.re ∧ z.im < (1 : ℂ).im ∧ (1 : ℂ).im < w.im := by
    refine ⟨by simpa using hz1, by simpa using hw1, by simpa using hzim0, by simpa using hwim0⟩
  have hb0' : (0 : ℂ) ∉ rectBoundary z w := fun h => (hpol 0 h).1 rfl
  have hb1' : (1 : ℂ) ∉ rectBoundary z w := fun h => (hpol 1 h).2 rfl
  -- `xiE_LG` is zero-free on the boundary
  have hξ_ne : ∀ s ∈ rectBoundary z w, Commons.NumberTheory.Zeta.xiE_LG s ≠ 0 := by
    intro s hs
    have hhead_ne : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (hb0 s hs)) (sub_ne_zero.mpr (hb1 s hs))
    have heq : Commons.NumberTheory.Zeta.xiE_LG s =
        (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
      rw [← Commons.NumberTheory.Zeta.xiG_LG_eq_xiE_LG_of_ne_zero_one (hb0 s hs) (hb1 s hs)]
      rfl
    rw [heq]
    exact mul_ne_zero hhead_ne (hnz s hs)
  -- argument principle applied to the entire function `xiE_LG`
  have harg := rectInt_logDeriv_entire_mul
      (f := Commons.NumberTheory.Zeta.xiE_LG) Commons.NumberTheory.Zeta.differentiable_xiE_LG
      hG ⟨0, by rw [Commons.NumberTheory.Zeta.xiE_LG_zero]; norm_num⟩ hzre hzim hξ_ne
  -- log-derivative identity on the boundary
  have hlogbd : ∀ s ∈ rectBoundary z w,
      logDeriv Commons.NumberTheory.Zeta.xiE_LG s =
        (1 / s + 1 / (s - 1)) + logDeriv completedRiemannZeta s := by
    intro s hs
    have hhead : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (hb0 s hs)) (sub_ne_zero.mpr (hb1 s hs))
    rw [(logDeriv_congr_nhds (xiE_LG_eventuallyEq (hb0 s hs) (hb1 s hs))).self_of_nhds]
    erw [logDeriv_mul s hhead (hnz s hs) (by fun_prop)
          (differentiableAt_completedZeta (hb0 s hs) (hb1 s hs))]
    rw [Commons.NumberTheory.Zeta.logDeriv_head s (hb0 s hs) (sub_ne_zero.mpr (hb1 s hs))]
  -- the two simple poles contribute `G 0 · 2πi + G 1 · 2πi`
  have hpole : rectInt z w (fun s => (1 / s + 1 / (s - 1)) * G s)
      = G 0 * (2 * (Real.pi : ℂ) * Complex.I) + G 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hpt : ∀ s ∈ rectBoundary z w, (1 / s + 1 / (s - 1)) * G s =
        (∑ u ∈ ({0, 1} : Finset ℂ), (1 : ℂ) * (s - u)⁻¹) * G s := by
      intro s hs
      simp only [Finset.sum_insert (by norm_num : (0 : ℂ) ∉ ({1} : Finset ℂ)),
        Finset.sum_singleton]
      rw [one_mul, one_mul]
      ring
    rw [rectInt_congr_boundary' hpt]
    have h := rectInt_finset_inv_sub_mul_entire (z := z) (w := w) hG hzre hzim
      ({0, 1} : Finset ℂ) (fun _ => (1 : ℂ))
      (by intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption)
    rw [h]
    simp only [Finset.sum_insert (by norm_num : (0 : ℂ) ∉ ({1} : Finset ℂ)),
      Finset.sum_singleton]
    rw [if_pos h0in, if_pos h1in, one_mul, one_mul]
  -- split `logDeriv Λ · G = logDeriv ξ · G - (1/s + 1/(s-1))·G` on the boundary
  have hpt' : ∀ s ∈ rectBoundary z w,
      logDeriv completedRiemannZeta s * G s + (1 / s + 1 / (s - 1)) * G s =
        logDeriv Commons.NumberTheory.Zeta.xiE_LG s * G s := by
    intro s hs
    rw [hlogbd s hs]
    ring
  have hcont1 : ∀ s ∈ rectBoundary z w,
      ContinuousAt (fun s : ℂ => logDeriv completedRiemannZeta s * G s) s := by
    intro s hs
    exact (continuousAt_logDeriv_of_analyticAt
      (analyticAt_completedRiemannZeta (hb0 s hs) (hb1 s hs)) (hnz s hs)).mul
        (hG s).continuousAt
  have hcont2 : ∀ s ∈ rectBoundary z w,
      ContinuousAt (fun s : ℂ => (1 / s + 1 / (s - 1)) * G s) s := by
    intro s hs
    refine ContinuousAt.mul ?_ (hG s).continuousAt
    exact (ContinuousAt.div continuousAt_const continuousAt_id (hb0 s hs)).add
      (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (hb1 s hs)))
  have hsplit : rectInt z w (fun s => logDeriv Commons.NumberTheory.Zeta.xiE_LG s * G s) =
      rectInt z w (fun s => logDeriv completedRiemannZeta s * G s) +
        rectInt z w (fun s => (1 / s + 1 / (s - 1)) * G s) := by
    rw [← rectInt_congr_boundary' (f := fun s =>
        logDeriv completedRiemannZeta s * G s + (1 / s + 1 / (s - 1)) * G s)
      (g := fun s => logDeriv Commons.NumberTheory.Zeta.xiE_LG s * G s)
      (fun s hs => hpt' s hs),
      rectInt_add_of_boundary_continuousAt hcont1 hcont2]
  -- identify the interior sum with the one for `Λ`
  have hsum : (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then ((analyticOrderNatAt Commons.NumberTheory.Zeta.xiE_LG ρ : ℕ) : ℂ) * G ρ else 0))
      = (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
        then ((analyticOrderNatAt completedRiemannZeta ρ : ℕ) : ℂ) * G ρ else 0)) := by
    apply finsum_congr
    intro ρ
    by_cases hIn : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
    · rw [if_pos hIn, if_pos hIn]
      have hord : analyticOrderNatAt Commons.NumberTheory.Zeta.xiE_LG ρ =
          analyticOrderNatAt completedRiemannZeta ρ := by
        by_cases h0 : ρ = 0
        · subst h0
          have hξ : analyticOrderNatAt Commons.NumberTheory.Zeta.xiE_LG 0 = 0 := by
            have h : analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG 0 = 0 :=
              analyticOrderAt_eq_zero.mpr
                (Or.inr (by rw [Commons.NumberTheory.Zeta.xiE_LG_zero]; norm_num))
            change (analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG 0).toNat = 0
            rw [h]; rfl
          rw [hξ,
            analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedRiemannZeta_zero]
        · by_cases h1 : ρ = 1
          · subst h1
            have hξ : analyticOrderNatAt Commons.NumberTheory.Zeta.xiE_LG 1 = 0 := by
              have h : analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG 1 = 0 :=
                analyticOrderAt_eq_zero.mpr
                  (Or.inr (by rw [Commons.NumberTheory.Zeta.xiE_LG_one]; norm_num))
              change (analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG 1).toNat = 0
              rw [h]; rfl
            rw [hξ,
              analyticOrderNatAt_of_not_analyticAt not_analyticAt_completedRiemannZeta_one]
          · have hhead_ne : (1 / 2 : ℂ) * ρ * (ρ - 1) ≠ 0 :=
              mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1)
            have hordE : analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG ρ =
                analyticOrderAt completedRiemannZeta ρ := by
              rw [analyticOrderAt_congr (xiE_LG_eventuallyEq h0 h1)]
              change analyticOrderAt
                ((fun t : ℂ => (1 / 2 : ℂ) * t * (t - 1)) * completedRiemannZeta) ρ = _
              rw [analyticOrderAt_mul
                ((by fun_prop :
                    ContDiffAt ℂ ⊤ (fun t : ℂ => (1 / 2 : ℂ) * t * (t - 1)) ρ).analyticAt)
                (analyticAt_completedRiemannZeta h0 h1)]
              rw [show analyticOrderAt (fun t : ℂ => (1 / 2 : ℂ) * t * (t - 1)) ρ = 0 from
                analyticOrderAt_eq_zero.mpr (Or.inr hhead_ne)]
              rw [zero_add]
            change (analyticOrderAt Commons.NumberTheory.Zeta.xiE_LG ρ).toNat =
              (analyticOrderAt completedRiemannZeta ρ).toNat
            rw [hordE]
      rw [hord]
    · rw [if_neg hIn, if_neg hIn]
  -- final assembly
  have hmain : rectInt z w (fun s => logDeriv completedRiemannZeta s * G s) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
          then ((analyticOrderNatAt Commons.NumberTheory.Zeta.xiE_LG ρ : ℕ) : ℂ) * G ρ else 0))
        - (G 0 * (2 * (Real.pi : ℂ) * Complex.I) + G 1 * (2 * (Real.pi : ℂ) * Complex.I)) := by
    have h := hsplit
    rw [harg, hpole] at h
    rw [eq_sub_iff_add_eq]
    exact h.symm
  rw [hmain, hsum]
  ring

end

end Work.LinnikAreas
