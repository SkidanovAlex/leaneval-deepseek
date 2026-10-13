import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.StrongEps.E5G.slice_lip_ordered

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

theorem slice_lip_norm {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (h4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hb4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ B)
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'| := by
  intro τ hτ τ' hτ'
  rcases le_total τ' τ with hle | hle
  · have h := slice_lip_ordered hsol hcont hsmR h4 hb4 hslotb hτ hτ' hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h
  · have h := slice_lip_ordered hsol hcont hsmR h4 hb4 hslotb hτ' hτ hle
    have hneg : Work.Spaces.HkNorm α 4
          (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        = Work.Spaces.HkNorm α 4
          (fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ) := by
      rw [show (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
            = -(fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ)
            from by funext z θ; simp only [Pi.neg_apply]; ring,
        Work.FTS.EllipticEst.HkNorm_neg]
    show Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'|
    rw [hneg, abs_of_nonpos (sub_nonpos.mpr hle),
      show -(τ - τ') = τ' - τ from by ring]
    exact h

end Work.FTS.StrongEps.E5G
