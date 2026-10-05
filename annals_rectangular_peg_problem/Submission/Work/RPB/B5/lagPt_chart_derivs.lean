import Mathlib
import Submission.Work.RPB.B5.lagData_imm_aux
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs

namespace Work.RPB.B5

theorem lagPt_chart_derivs (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (hsm : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      deriv (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t) x
        = deriv (fun y : ℝ => D.rho τ y t) x • deriv (fun ρ' : ℝ => D.W τ t ρ') (D.rho τ x t)
      ∧ deriv (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s) t
        = deriv (fun s : ℝ => D.rho τ x s) t • deriv (fun ρ' : ℝ => D.W τ t ρ') (D.rho τ x t)
          + deriv (fun s : ℝ => D.W τ s (D.rho τ x t)) t := by
  intro τ hτ x hx t
  obtain ⟨hxlo, hxhi⟩ := hx
  -- `rho τ · ·` is `C¹` at `(x,t)` (slice of the global `C⁸` field `hrhosm`)
  have hrhocd : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => D.rho τ z.1 z.2) (x, t) := by
    have hg : ContDiffAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) (τ, (x, t)) :=
      D.hrhosm.contDiffAt
    have hf : ContDiffAt ℝ 8 (fun z : ℝ × ℝ => ((τ, (z.1, z.2)) : ℝ × (ℝ × ℝ))) (x, t) := by
      fun_prop
    have := hg.comp (x := (x, t)) hf
    simpa [Function.comp_def] using this.of_le (by norm_num)
  have hrho_x : DifferentiableAt ℝ (fun y : ℝ => D.rho τ y t) x :=
    differentiableAt_slice_fst hrhocd
  have hrho_t : DifferentiableAt ℝ (fun s : ℝ => D.rho τ x s) t :=
    differentiableAt_slice_snd hrhocd
  have hρmem : D.rho τ x t ∈ Set.Ioo (-D.ρ₀) D.ρ₀ :=
    D.hrhorng τ hτ x ⟨le_of_lt hxlo, hxhi⟩ t
  have hWcd : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, D.rho τ x t) :=
    contDiffAt_W_one CI a D hτ hρmem
  have hWdiff : DifferentiableAt ℝ (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, D.rho τ x t) :=
    hWcd.differentiableAt (by norm_num)
  have hFdiff : DifferentiableAt ℝ (fun ρ' : ℝ => D.W τ t ρ') (D.rho τ x t) :=
    differentiableAt_slice_snd hWcd
  constructor
  · -- the `x`-derivative: `lagPt` agrees with the chart on `Ioc (x-ε) x`, one-sided transfer
    have hf : DifferentiableAt ℝ (fun y : ℝ => lagPt D.W D.Γc D.Ac D.rho τ y t) x := by
      have h : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) (x, t) :=
        (hsm τ hτ).contDiffAt
      exact differentiableAt_slice_fst h
    have hg : DifferentiableAt ℝ (fun y : ℝ => D.W τ t (D.rho τ y t)) x :=
      hFdiff.comp x hrho_x
    have hε : 0 < (x + Real.sqrt 2) / 2 := by linarith
    have hEq : ∀ y ∈ Set.Ioc (x - (x + Real.sqrt 2) / 2) x,
        lagPt D.W D.Γc D.Ac D.rho τ y t = D.W τ t (D.rho τ y t) := by
      intro y hy
      exact lagPt_chart D.W D.Γc D.Ac D.rho (by linarith [hy.1, hxlo]) (le_trans hy.2 hxhi)
    rw [deriv_eq_of_eqOn_Ioc _ _ hε hf hg hEq]
    exact deriv_comp_smul (fun ρ' : ℝ => D.W τ t ρ') (fun y : ℝ => D.rho τ y t) x hFdiff hrho_x
  · -- the `t`-derivative: `x ≤ 0` is fixed, so `lagPt τ x · = W τ · (rho τ x ·)` everywhere
    have heqfun : (fun s : ℝ => lagPt D.W D.Γc D.Ac D.rho τ x s)
        = (fun s : ℝ => D.W τ s (D.rho τ x s)) := by
      funext s
      exact lagPt_chart D.W D.Γc D.Ac D.rho hxlo hxhi
    rw [heqfun]
    have hgraph := deriv_graph (fun z : ℝ × ℝ => D.W τ z.1 z.2)
        (fun s : ℝ => D.rho τ x s) (fderiv ℝ (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, D.rho τ x t))
        hWdiff.hasFDerivAt hrho_t.hasDerivAt
    rw [hgraph]
    have hfs := fderiv_section_fst (fun z : ℝ × ℝ => D.W τ z.1 z.2)
        (fderiv ℝ (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, D.rho τ x t)) hWdiff.hasFDerivAt
    have hss := fderiv_section_snd (fun z : ℝ × ℝ => D.W τ z.1 z.2)
        (fderiv ℝ (fun z : ℝ × ℝ => D.W τ z.1 z.2) (t, D.rho τ x t)) hWdiff.hasFDerivAt
    rw [← hfs, ← hss, add_comm]

end Work.RPB.B5
