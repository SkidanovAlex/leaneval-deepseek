import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.rawE6_ineq_proof
import Submission.Work.FTS.StrongPersist.H6Pair_ones3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/RawE6IneqFlow.lean` — leaf **L-A over the flow class** `EpsFlowP`

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §5 step 3 + the lead's
message): the leaf L-A `rawE6_ineq`/`rawE6_ineq_ones3` (`E4R3/Apriori4Leaves/RawE6Ineq.lean`)
carries `IsEpsSolP + EpsRegP + ball`, which is *per-slice* data and does not determine the
uniform-in-`τ` `ℋ⁶`-bound `hb6` that the route needs (six children returned the leaf FALSE for
exactly this reason).  The flow class `EpsFlowP` supplies it: by
`E4R5.xn6_continuousOn_of_flow` the map `τ ↦ Xn6 α (slice g τ)` is continuous on the *compact*
`Icc 0 T`, hence bounded — which is `hb6` with a constant `B` depending on the solution.

So the present lemma is the repaired leaf, **proved** by combining

* the proved sibling `Apriori4Proofs.rawE6_ineq_uniform` (the route, with `hb6` as an explicit
  input and the S1/S5 leaves discharged), whose only remaining hypothesis is the semi-tame leaf
  S2 `epsWP_semitame` (carried here as `hS2`), and
* the proved `E4R5.xn6_continuousOn_of_flow` (`hflow : EpsFlowP`),

with the kernel symmetry `hρs` and the proved pairing estimate `StrongPersist.H6Pair_ones3`
(instantiated at `Ce`).  This is the exact shape the `ℋ⁶`-half `E4R5.SixthChapterBF` consumes.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Leaf L-A over `EpsFlowP`** — the raw level-six energy inequality with the `ε`-small
superlinear defect, for `EpsFlowP` flows.  The uniform-in-`τ` `ℋ⁶`-bound `hb6` of
`rawE6_ineq_uniform` is produced here from the flow's `ℋ⁶`-continuity. -/
theorem rawE6_ineq_flow
    (hS2 : ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
        Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
        Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
            + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) {Ce : ℝ} (hCe : 0 < Ce) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    Work.FTS.StrongEps.EpsE4Thr.E4Data α C₀ K Ce Cs ρ Φs E g₀ →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.EpsFlowP α ρ ε T Φs E g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2) →
      ∀ τ ∈ Set.Ioo 0 T,
        2 * IP6o α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by
  obtain ⟨α₂, Cp, _hCp, _hα₂, hpair⟩ := Work.FTS.StrongPersist.H6Pair_ones3 Ce hCe
  intro C₀ Cs
  obtain ⟨α₀, hα₀, h⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.rawE6_ineq_uniform (ρ := ρ) hS2 hρ hρs hpair C₀ Cs
  refine ⟨α₀, hα₀, fun α hα => ?_⟩
  obtain ⟨Λ, C₁, hΛ, hC₁, H⟩ := h α hα
  refine ⟨Λ, C₁, hΛ, hC₁, ?_⟩
  intro K Φs E g₀ hdat hstar ε hε T hT g hsol hreg hflow hball τ hτ
  -- the uniform-in-`τ` `ℋ⁶`-bound of the flow, from its continuity on the compact `[0,T]`
  have hcont : ContinuousOn (fun σ => Xn6 α (slice g σ)) (Set.Icc 0 T) :=
    Work.FTS.StrongEps.EpsE4Thr.E4R5.xn6_continuousOn_of_flow hreg hflow
  obtain ⟨B, hB⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact H hdat hstar ε hε T hT g hsol hreg hball (fun σ hσ => hB ⟨σ, hσ, rfl⟩) τ hτ

end Work.FTS.StrongEps.EpsE4Thr.E4R4
