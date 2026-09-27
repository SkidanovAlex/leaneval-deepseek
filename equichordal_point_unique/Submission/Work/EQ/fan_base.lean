import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germCHelpers

/-! Base facts about the equichordal germ `germC`, the branch `invBranch` and the fan `fan`,
supporting `Work.EQ.fan_trichotomy`. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

section eqLam

theorem eqLam_pos' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

theorem eqLam_lt_one' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

theorem eqLam_ne_zero' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a ≠ 0 :=
  ne_of_gt (eqLam_pos' ha0 ha1)

theorem one_sub_eqLam {a : ℝ} (ha : a ≠ -1) : 1 - eqLam a = 2 * a / (1 + a) := by
  rw [eqLam]
  have h : (1:ℝ) + a ≠ 0 := by intro hc; apply ha; linarith
  field_simp
  ring

theorem eqLam_div_one_sub {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    eqLam a / (1 - eqLam a) = (1 - a) / (2 * a) := by
  rw [eqLam]
  have h : (1:ℝ) + a ≠ 0 := by intro hc; linarith
  have h2 : a ≠ 0 := ne_of_gt ha0
  field_simp [h2]
  ring

end eqLam

/-- `dslope h 0 = h u / u` (the numerator factor in the `y`-coordinate of `germC`). -/
def gN (h : ℂ → ℂ) : ℂ → ℂ := dslope h 0

/-- `dslope (h ∘ (λ·)) 0`. -/
def gM (a : ℝ) (h : ℂ → ℂ) : ℂ → ℂ := dslope (fun v => h ((eqLam a : ℂ) * v)) 0

/-- The denominator `dslope (h ∘ (λ·) - h) 0`. -/
def gD (a : ℝ) (h : ℂ → ℂ) : ℂ → ℂ := dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0

theorem germC_eq (a : ℝ) (h : ℂ → ℂ) (u : ℂ) :
    germC a h u = (a * gM a h u / gD a h u - a / 2,
      a * u * gN h u * gM a h u / gD a h u) := rfl

/-- Value at `0`: the germ curve passes through `A₁ = (-1/2, 0)`. -/
theorem germC_value {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) : germC a h 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  have hAn : AnalyticAt ℂ h 0 := han 0 (by simpa [Metric.mem_ball] using hr)
  have hd : HasDerivAt h (-1) 0 := by
    have := hAn.differentiableAt.hasDerivAt
    rwa [hderiv] at this
  have hc : HasDerivAt (fun v : ℂ => (eqLam a : ℂ) * v) ((eqLam a : ℂ) * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_mul (eqLam a : ℂ)
  have hcomp : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v)) ((eqLam a : ℂ) * (-1)) 0 := by
    have hcc := HasDerivAt.comp (0:ℂ)
      (show HasDerivAt h (-1) ((eqLam a : ℂ) * 0) by simpa using hd) hc
    convert hcc using 1
    · ext v; rfl
    · ring
  have hsub : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v)
      ((eqLam a : ℂ) * (-1) - (-1)) 0 := hcomp.sub hd
  have e0 : dslope h 0 0 = (-1 : ℂ) := by rw [dslope_same]; exact hderiv
  have e1 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 0 = -((eqLam a : ℝ) : ℂ) := by
    rw [dslope_same, hcomp.deriv]; ring
  have e2 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0
      = 1 - ((eqLam a : ℝ) : ℂ) := by
    rw [dslope_same, hsub.deriv]; ring
  simp only [germC, e0, e1, e2]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_div, Prod.fst_mul]
    have h1m : (1 : ℂ) - ((eqLam a : ℝ) : ℂ) = (((2 * a / (1 + a) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, eqLam]
      congr 1
      have h : (1:ℝ) + a ≠ 0 := by intro hc; linarith
      field_simp
      ring
    have hlam : ((eqLam a : ℝ) : ℂ) = (((1 - a) / (1 + a) : ℝ) : ℂ) := by rw [eqLam]
    rw [h1m, hlam]
    push_cast
    have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha0)
    have h1a : (1 + (a:ℂ)) ≠ 0 := by
      have : (0:ℝ) < 1 + a := by linarith
      exact_mod_cast (ne_of_gt this)
    field_simp
    ring
  · simp

/-- The composition formula for the fan: applying a prefix `w₁` scales the parameter by
`λ^{|w₁|}` and applies the branch product of `w₁` to the fan of `w₂`. -/
theorem fan_append {a : ℝ} {h : ℂ → ℂ} (w₁ w₂ : List Bool) (u : ℂ) :
    fan a h (w₁ ++ w₂) u = w₁.reverse.foldl (fun z s => invBranch a s z)
      (fan a h w₂ ((eqLam a : ℂ) ^ w₁.length * u)) := by
  induction w₁ generalizing u with
  | nil => simp
  | cons s t ih =>
      simp only [List.cons_append, List.length_cons, List.reverse_cons, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [fan]
      rw [ih]
      congr 1
      rw [pow_succ]
      ring

end

end Work.EQ

namespace Work.EQ
open Complex Filter _root_.Topology
noncomputable section

/-- `germC a h` is analytic near `0`. -/
theorem germC_analytic {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρ) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hfe⟩ := hh
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hd : HasDerivAt h (-1) 0 := by
    have h' := (han 0 (by simpa [Metric.mem_ball, dist_zero_right] using hr)).differentiableAt.hasDerivAt
    rwa [hderiv] at h'
  have hcomp : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v)) ((eqLam a : ℂ) * (-1)) 0 := by
    have hc : HasDerivAt (fun v : ℂ => (eqLam a : ℂ) * v) ((eqLam a : ℂ) * 1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_mul (eqLam a : ℂ)
    have hcc := HasDerivAt.comp (0:ℂ)
      (show HasDerivAt h (-1) ((eqLam a : ℂ) * 0) by simpa using hd) hc
    convert hcc using 1
    · ext v; rfl
    · ring
  have hN : AnalyticOnNhd ℂ (gN h) (Metric.ball 0 r) := fun u hu => analyticAt_dslope (han u hu)
  have hM : AnalyticOnNhd ℂ (gM a h) (Metric.ball 0 r) := by
    intro u hu
    refine analyticAt_dslope ?_
    have hlt : ‖(eqLam a : ℂ) * u‖ < r := by
      apply norm_mul_lt_of_lt hl0 hl1 hr
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact (han _ (by simpa [Metric.mem_ball, dist_zero_right] using hlt)).comp
      (analyticAt_const.mul analyticAt_id)
  have hD : AnalyticOnNhd ℂ (gD a h) (Metric.ball 0 r) := by
    intro u hu
    refine analyticAt_dslope ?_
    have hlt : ‖(eqLam a : ℂ) * u‖ < r := by
      apply norm_mul_lt_of_lt hl0 hl1 hr
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact ((han _ (by simpa [Metric.mem_ball, dist_zero_right] using hlt)).comp
      (analyticAt_const.mul analyticAt_id)).sub (han u hu)
  have hD0 : gD a h 0 ≠ 0 := by
    have hsub : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v)
        ((eqLam a : ℂ) * (-1) - (-1)) 0 := hcomp.sub hd
    rw [gD, dslope_same, hsub.deriv]
    have : (eqLam a : ℂ) * (-1) - (-1) = 1 - (eqLam a : ℂ) := by ring
    rw [this]
    have : (eqLam a : ℂ) ≠ 1 := by
      intro hc; exact absurd (Complex.ofReal_injective hc) (ne_of_lt hl1)
    exact sub_ne_zero.mpr (Ne.symm this)
  have hDcont : ContinuousOn (gD a h) (Metric.ball 0 r) :=
    fun u hu => (hD u hu).continuousAt.continuousWithinAt
  obtain ⟨ρ, hρ0, hρr, hρne⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball 0 ρ, gD a h u ≠ 0 := by
    have hmem : {u : ℂ | gD a h u ≠ 0} ∈ 𝓝 (0:ℂ) :=
      (hD 0 (by simpa [Metric.mem_ball, dist_zero_right] using hr)).continuousAt.eventually_ne hD0
    rcases Metric.mem_nhds_iff.mp hmem with ⟨ρ, hρ0, hsub⟩
    exact ⟨min ρ r, lt_min hρ0 hr, min_le_right _ _, fun u hu => hsub (by
      rw [Metric.mem_ball, dist_zero_right] at hu ⊢
      exact lt_of_lt_of_le hu (min_le_left _ _))⟩
  refine ⟨ρ, hρ0, fun u hu => ?_⟩
  have hur : u ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right] at hu ⊢; exact lt_of_lt_of_le hu hρr
  have hMu := hM u hur
  have hNu := hN u hur
  have hDu := hD u hur
  have hDne := hρne u hu
  have h1 : AnalyticAt ℂ (fun u => a * gM a h u / gD a h u - a / 2) u :=
    ((analyticAt_const.mul hMu).div hDu hDne).sub analyticAt_const
  have h2 : AnalyticAt ℂ (fun u => a * u * gN h u * gM a h u / gD a h u) u :=
    (((analyticAt_const.mul analyticAt_id).mul hNu).mul hMu).div hDu hDne
  rw [show germC a h = fun u => (a * gM a h u / gD a h u - a / 2,
      a * u * gN h u * gM a h u / gD a h u) from funext (germC_eq a h)]
  exact h1.prod h2

end
end Work.EQ
