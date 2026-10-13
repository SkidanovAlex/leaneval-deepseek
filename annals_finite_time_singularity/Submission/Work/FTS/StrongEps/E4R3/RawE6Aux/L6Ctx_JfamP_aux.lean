import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
-- The statement below is *identical* (same terms, same implicit arguments) to the one proved in
-- `E4R3/Apriori4Proofs/L6Ctx_JfamP_proof.lean`, so the proof is a direct citation of that
-- theorem.  The module is imported here so that the `RawE6Aux` name is available independently.
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.RawE6Aux

theorem L6Ctx_JfamP_aux :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀,
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
      {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn},
    Work.FTS.StrongEps.IsSmoothKernel ρ →
    (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Work.FTS.Galerkin.Fam) (τ : ℝ), 0 ≤ τ →
      Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
        (Work.FTS.StrongEps.JfamP ρ ε g) (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ :=
  Work.FTS.StrongEps.E4R3.Apriori4Proofs.L6Ctx_JfamP_proof

end Work.FTS.StrongEps.E4R3.RawE6Aux
