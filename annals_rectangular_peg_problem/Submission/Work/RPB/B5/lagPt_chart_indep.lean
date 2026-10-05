import Mathlib
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.chartChain
import Submission.Work.RPB.B2.chordSurf_immersed

namespace Work.RPB.B5

/-!
# B5: the chart branch `(t,ρ) ↦ W τ t ρ` is an immersion

On the region `0 < ρ ≤ π²/4` the chart `W` of the chord annulus agrees with the chord surface
in the radius variable `r = √ρ` (`LagData.hWchord`, with `ρ = (√ρ)²`).  Hence the two tangents

* `∂_ρ W τ t ρ = (deriv √ ρ) • ∂_r chordSurf CI.c a τ t (√ρ)`,
* `∂_t W τ t ρ = ∂_t chordSurf CI.c a τ t (√ρ)`

are an invertible rescaling (in the `ρ`-direction only, by the non-zero factor `deriv √ ρ`) of the
two tangents of the chord annulus, which are linearly independent on `0 < r < π` by
`Work.RPB.B2.chordSurf_immersed`.  This is the chart-immersion fact `lagPt_chart_indep`.
-/

/-- The chart `W` at `ρ ∈ (0, π²/4]` is the chord surface at `r = √ρ`. -/
theorem chartW_eq_chordSurf_at (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioc (0 : ℝ) (Real.pi ^ 2 / 4),
      D.W τ t ρ = Work.RPB.chordSurf CI.c a τ t (Real.sqrt ρ) := by
  intro τ hτ t ρ hρ
  obtain ⟨hρpos, hρle⟩ := hρ
  have hrle : Real.sqrt ρ ≤ Real.pi / 2 := by
    have h1 : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [← h1]
    exact Real.sqrt_le_sqrt hρle
  have hh := D.hWchord τ hτ t (Real.sqrt ρ)
    ⟨Real.sqrt_pos_of_pos hρpos, hrle⟩
  rwa [Real.sq_sqrt hρpos.le] at hh

theorem lagPt_chart_indep (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioc (0 : ℝ) (Real.pi ^ 2 / 4), ∀ α β : ℝ,
      α • deriv (fun ρ' : ℝ => D.W τ t ρ') ρ
        + β • deriv (fun s : ℝ => D.W τ s ρ) t = 0 → α = 0 ∧ β = 0 := by
  intro τ hτ t ρ hρ α β h
  have hρpos : 0 < ρ := hρ.1
  have hρle : ρ ≤ Real.pi ^ 2 / 4 := hρ.2
  -- `ρ` lies in the interval on which the chart `W` is smooth
  have hρIoo : ρ ∈ Set.Ioo (-D.ρ₀) D.ρ₀ :=
    ⟨by linarith [D.hρ₀], lt_of_le_of_lt hρle D.hπρ₀⟩
  -- `r = √ρ` lies in `(0, π)`
  have hrpos : 0 < Real.sqrt ρ := Real.sqrt_pos_of_pos hρpos
  have hrle : Real.sqrt ρ ≤ Real.pi / 2 := by
    have h1 : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [← h1]
    exact Real.sqrt_le_sqrt hρle
  have hrπ : Real.sqrt ρ ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨hrpos, by linarith [hrle, Real.pi_pos]⟩
  -- ### the `t`-derivative of the chart
  have hWt : deriv (fun s : ℝ => D.W τ s ρ) t
      = deriv (fun s : ℝ => Work.RPB.chordSurf CI.c a τ s (Real.sqrt ρ)) t := by
    have hfun : (fun s : ℝ => D.W τ s ρ)
        = (fun s : ℝ => Work.RPB.chordSurf CI.c a τ s (Real.sqrt ρ)) := by
      funext s
      exact chartW_eq_chordSurf_at CI a D τ hτ s ρ hρ
    rw [hfun]
  -- ### the `ρ`-derivative of the chart
  have hf : DifferentiableAt ℝ (fun ρ' : ℝ => D.W τ t ρ') ρ :=
    differentiableAt_slice_snd (contDiffAt_W_one CI a D hτ hρIoo)
  have hFdiff : DifferentiableAt ℝ (fun rr : ℝ => Work.RPB.chordSurf CI.c a τ t rr)
      (Real.sqrt ρ) :=
    differentiableAt_slice_snd
      ((chordSurf_pair_contDiffAt CI a ha hτ hrπ).of_le (by norm_num))
  have hsqrt : DifferentiableAt ℝ Real.sqrt ρ :=
    (Real.hasDerivAt_sqrt (ne_of_gt hρpos)).differentiableAt
  have hg : DifferentiableAt ℝ
      (fun y : ℝ => Work.RPB.chordSurf CI.c a τ t (Real.sqrt y)) ρ :=
    hFdiff.comp ρ hsqrt
  have hloc : deriv (fun ρ' : ℝ => D.W τ t ρ') ρ
      = deriv (fun y : ℝ => Work.RPB.chordSurf CI.c a τ t (Real.sqrt y)) ρ := by
    refine deriv_eq_of_eqOn_Ioc _ _ hρpos hf hg ?_
    intro y hy
    have hy' : y ∈ Set.Ioc (0 : ℝ) ρ := by simpa only [sub_self] using hy
    have hypos : 0 < y := hy'.1
    have hsqle : Real.sqrt y ≤ Real.pi / 2 := by
      have h1 : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
        rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      calc Real.sqrt y ≤ Real.sqrt ρ := Real.sqrt_le_sqrt hy'.2
        _ ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hρle
        _ = Real.pi / 2 := h1
    have hh := D.hWchord τ hτ t (Real.sqrt y)
      ⟨Real.sqrt_pos_of_pos hypos, hsqle⟩
    rwa [Real.sq_sqrt hypos.le] at hh
  have hdW : deriv (fun ρ' : ℝ => D.W τ t ρ') ρ
      = deriv Real.sqrt ρ
        • deriv (fun rr : ℝ => Work.RPB.chordSurf CI.c a τ t rr) (Real.sqrt ρ) := by
    rw [hloc, deriv_comp_smul (fun rr : ℝ => Work.RPB.chordSurf CI.c a τ t rr) Real.sqrt ρ
      hFdiff hsqrt]
  -- the rescaling factor is non-zero
  have hcne : deriv Real.sqrt ρ ≠ 0 := by
    rw [(Real.hasDerivAt_sqrt (ne_of_gt hρpos)).deriv]
    exact div_ne_zero one_ne_zero
      (mul_ne_zero two_ne_zero (ne_of_gt (Real.sqrt_pos_of_pos hρpos)))
  -- rewrite the hypothesis into the form of the chord-annulus immersion
  have h' : β • deriv (fun s : ℝ => Work.RPB.chordSurf CI.c a τ s (Real.sqrt ρ)) t
      + (α * deriv Real.sqrt ρ)
        • deriv (fun rr : ℝ => Work.RPB.chordSurf CI.c a τ t rr) (Real.sqrt ρ) = 0 := by
    rw [hdW, hWt] at h
    rw [smul_smul, add_comm] at h
    exact h
  obtain ⟨hβ, hαc⟩ := Work.RPB.B2.chordSurf_immersed CI a ha τ hτ t (Real.sqrt ρ) hrπ
    β (α * deriv Real.sqrt ρ) h'
  exact ⟨(mul_eq_zero.mp hαc).resolve_right hcne, hβ⟩

end Work.RPB.B5
