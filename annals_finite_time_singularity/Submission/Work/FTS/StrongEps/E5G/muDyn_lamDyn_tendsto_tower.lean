import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux2.muDyn_tendstoH
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.SB4.near0Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem muDyn_lamDyn_tendsto_tower {α C₀ Ce Cs T B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    {g : Work.FTS.Galerkin.Fam} {Maj : ℝ → ℝ} {s : ℝ}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E)
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hsmE : ContDiffOn ℝ 1 (Function.uncurry (E (Work.FTS.Galerkin.slice g s))) Work.FTS.EllipticEst.Q0)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc (0 : ℝ) 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s) (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn : ∀ n : ℕ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hXn6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ B)
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)) ∧
      (|Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s| ≤ 1 / 2) ∧
      Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.lamDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)) := by
  -- ### the level-three pinning gives the level-two law (`limApprox`'s `C²`-clause is
  -- ### `EllLimOK3`'s third conjunct, so no extra hypothesis is needed here)
  have hEll2 : Work.FTS.StrongEps.EllLimOK α E := hELL3.toEllLimOK
  -- ### the *domination* of the three densities by the majorant `Maj`, with a universal constant
  -- ### (the frozen zero-mode bound `N0_N_Transport_dens_le`, fed by `EpsDecay` + the two balls)
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongEps.E5Aux2.N0_N_Transport_dens_le
  have hdens : ∀ n : ℕ, ∀ s' ∈ Set.Ioi (0 : ℝ),
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) ∧
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) ∧
      ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) :=
    fun n s' hs' => hC1 hα (hDec n) (hC n) (hXn n) (hXn6 n) s' hs'
  -- ### the two halves of the conclusion: the convergence of `muDyn` (the `H`-stability leaf) and
  -- ### the algebraic transfer `muDyn → lamDyn` of the frozen interface
  have hmu := Work.FTS.StrongEps.E5Aux2.muDyn_tendstoH (C1 := C1) hρ hα hEll2 hEll hsmΦ hsmE
    hε hε0 hsm hconv hC hXn hXn6 hMajint hDec hl12 hC1pos hdens
  obtain ⟨hmuB, hlam⟩ := Work.FTS.StrongEps.E5Aux2.lamDyn_tendsto_of_mu hmu hml hC hXn
  exact ⟨hmu, hmuB, hlam⟩

end Work.FTS.StrongEps.E5G
