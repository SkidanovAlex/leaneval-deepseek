/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsZero/Hadd.lean`

Additivity of the `L₁₂` zero mode over the five summands of the projected, pre-mollified
right-hand side of the `ε`-scheme.  Since

  `PgRHS α μ lam f Ψ = -μ̄·AK α + N₀ + N + N_*`,   `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)`,

and `L₁₂^K(f)(ρ) = ∫_ρ^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds` is an integral (hence additive), the
identity

  `L₁₂(PLin + PgRHS)(0) = L₁₂(PLin)(0) - μ̄ L₁₂(AK α)(0) + L₁₂(N₀)(0) + L₁₂(N)(0) + L₁₂(N_*)(0)`

holds as soon as the five summands are integrable — which is exactly the hypothesis set of the
statement (the angular slices on `Iθ` for `z > 0` and the densities on `Ioi 0`).

Everything is vocabulary of `Pieces.lean` (`rfl`-abbreviations), so the only work is (i) the
five-term split via `Work.FTS.Apriori.ZeroMode.L12_sum_zero`, (ii) the constant-multiplication
rule `Work.FM.L12_const_mul` for the `μ̄`-piece, and (iii) reassociation.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsZero.Pieces
import Submission.Work.FTS.Apriori.ZeroMode.L12_sum_zero
import Submission.Work.FTS.GalBasis.l12_linear_cc
import Submission.Work.FM.Core
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.EpsZero

theorem Hadd {α Ce Cs μ lam : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {Φs : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hLin : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PLin α f)) (Set.Ioi 0))
    (hN0 : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN0 α f)) (Set.Ioi 0))
    (hN : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f))) (Set.Ioi 0))
    (hNs : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PNs μ lam f)) (Set.Ioi 0))
    (hK : MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PK (Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) α)) (Set.Ioi 0))
    (hLinθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PLin α f z θ / z) Work.Spaces.Iθ)
    (hN0θ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN0 α f z θ / z) Work.Spaces.Iθ)
    (hNθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) z θ / z) Work.Spaces.Iθ)
    (hNsθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PNs μ lam f z θ / z) Work.Spaces.Iθ)
    (hKθ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PK (Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) α z θ / z) Work.Spaces.Iθ) :
    Work.Construction.L12 (fun z θ => Work.FTS.StrongEps.EpsZero.PLin α f z θ + Work.FTS.StrongEps.EpsZero.PgRHS α μ lam f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PLin α f) 0
        - Work.FTS.StrongEps.EpsZero.Pmubar α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) * Work.Construction.L12 (Work.Construction.AK α) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PN0 α f) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f)) 0
        + Work.Construction.L12 (Work.FTS.StrongEps.EpsZero.PNs μ lam f) 0 := by
  -- The five summands of `L₁₂(PLin + PgRHS)`: `PLin`, the `μ̄`-piece `PK μ̄ α = -μ̄·AK α`,
  -- then `N₀`, `N`, `N_*`.
  let F : Fin 5 → ℝ → ℝ → ℝ :=
    ![PLin α f, PK (Pmubar α f (PPsi E Φs f)) α, PN0 α f,
      PN α f (PPsi E Φs f), PNs μ lam f]
  -- The integrability inputs of the sum rule: the angular slices for `z > 0`,
  -- and the radial densities on `Ioi 0`.
  have hθ : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * F i z θ / z)
        Work.Spaces.Iθ := by
    intro i _ z hz
    fin_cases i
    · exact hLinθ z hz
    · exact hKθ z hz
    · exact hN0θ z hz
    · exact hNθ z hz
    · exact hNsθ z hz
  have hdens : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      MeasureTheory.IntegrableOn (fun z => Work.Construction.L12dens (F i) z)
        (Set.Ioi 0) := by
    intro i _
    fin_cases i
    · exact hLin
    · exact hK
    · exact hN0
    · exact hN
    · exact hNs
  -- Additivity of `L₁₂` over the five summands.
  have hsum := Work.FTS.Apriori.ZeroMode.L12_sum_zero (Finset.univ : Finset (Fin 5)) F hθ hdens
  -- The pointwise identity `PLin + PgRHS = ∑_i F_i`.
  have hsplit : (fun z θ : ℝ => PLin α f z θ + PgRHS α μ lam f (PPsi E Φs f) z θ)
      = fun z θ : ℝ => ∑ i ∈ (Finset.univ : Finset (Fin 5)), F i z θ := by
    funext z θ
    simp only [Fin.sum_univ_five, F, Fin.isValue, Matrix.cons_val, PgRHS, Work.Construction.gRHS, Pmubar, PK, PN0, PN,
      PNs, PLin]
    ring
  -- The `μ̄`-piece: homogeneity of `L₁₂` in a constant.
  have hKterm : Work.Construction.L12 (PK (Pmubar α f (PPsi E Φs f)) α) 0
      = -Pmubar α f (PPsi E Φs f) * Work.Construction.L12 (Work.Construction.AK α) 0 := by
    show Work.FM.L12 Work.Spaces.K
        (fun s θ => -Pmubar α f (PPsi E Φs f) * Work.Construction.AK α s θ) 0
      = -Pmubar α f (PPsi E Φs f)
        * Work.FM.L12 Work.Spaces.K (Work.Construction.AK α) 0
    exact Work.FM.L12_const_mul
  rw [hsplit, hsum, Fin.sum_univ_five]
  simp only [F, Fin.isValue, Matrix.cons_val]
  rw [hKterm]
  ring

end Work.FTS.StrongEps.EpsZero
