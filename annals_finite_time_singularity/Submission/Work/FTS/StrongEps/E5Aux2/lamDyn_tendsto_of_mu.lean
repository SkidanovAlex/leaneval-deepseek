import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsWPLim.Gap
import Submission.Work.FTS.StrongEps.EpsGdotThirdH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

theorem lamDyn_tendsto_of_mu {α C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ}
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn : ∀ n : ℕ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2) :
    (|Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s| ≤ 1 / 2) ∧
    Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)) := by
  -- `muDyn` sees a family only through its `s`-slice, so `MuLamOK` — which is stated at the
  -- *constant* families built from a class-`C` profile of size `≤ C₀α²` and at time `0` — applies
  -- verbatim to each member of the sequence.
  have hbnd : ∀ n : ℕ, |Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s| ≤ 1 / 2 := by
    intro n
    obtain ⟨h1, _⟩ := hml
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n) (hXn n)
    have key : Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ =>
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ))
        (fun z θ _ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z θ) 0
        = Work.FTS.Galerkin.muDyn α
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s := rfl
    rwa [key] at h1
  -- the bound passes to the limit
  have hle : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s ≤ 1 / 2 :=
    le_of_tendsto hmu (Filter.Eventually.of_forall fun n => (abs_le.mp (hbnd n)).2)
  have hge : -(1 / 2) ≤ Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s :=
    ge_of_tendsto hmu (Filter.Eventually.of_forall fun n => (abs_le.mp (hbnd n)).1)
  refine ⟨abs_le.mpr ⟨hge, hle⟩, ?_⟩
  -- `lamfun μ = -2μ/(1+μ)` is continuous at the limit, whose distance to `-1` is `≥ 1/2`
  have hden : (1 + Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s) ≠ 0 := by
    intro h
    linarith
  have hcomp : Filter.Tendsto (fun n : ℕ => Work.Construction.lamfun
      (Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) Filter.atTop
      (nhds (Work.Construction.lamfun
        (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s))) := by
    have hcont : ContinuousAt (fun μ : ℝ => Work.Construction.lamfun μ)
        (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s) := by
      show ContinuousAt (fun μ : ℝ => -2 * μ / (1 + μ)) _
      exact (continuousAt_const.mul continuousAt_id).div
        (continuousAt_const.add continuousAt_id) hden
    exact hcont.tendsto.comp hmu
  simpa only [Work.FTS.Galerkin.lamDyn] using hcomp

end Work.FTS.StrongEps.E5Aux2
