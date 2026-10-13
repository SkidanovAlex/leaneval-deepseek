import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.ConvLev0Defs
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.JepsSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem mixed_JfamP_tendsto {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α B : ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ}
    {τ : ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B
      (fun n => Work.FTS.Galerkin.slice (G n) τ) (Work.FTS.Galerkin.slice g τ))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0)
      Filter.atTop (nhds 0))
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) τ) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) := by
  -- **(1)** The slots of the *mollified* family converge: this is `E1` plus the peak estimate.
  have hJ : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) :=
    Work.FTS.StrongEps.mixed_Jeps_tendsto hρ.moll hsm hconv hεpos hε0 hp hji
  -- **(2)** The `P₀`-coefficients vanish in the limit.
  have hL : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
    have := hl12.div_const pzNorm
    simpa using this
  have hc : Filter.Tendsto
      (fun n : ℕ => (Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
        * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
      Filter.atTop (nhds 0) := by
    have := hL.mul_const (Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
    simpa using this
  -- **(3)** The slot of the projected family is the slot of the mollified profile minus the
  -- rank-one correction, pointwise in `n` (`PZeroAux.mixed_Pz`).
  have hmain : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2
        - (Work.Construction.L12
            (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
          * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) p.1 p.2)) := by
    simpa using hJ.sub hc
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hmain
  have hloc : MeasureTheory.LocallyIntegrable
      (logPull (Work.FTS.Galerkin.slice (G n) τ)) MeasureTheory.volume :=
    locallyIntegrable_logPull_of_forall_contDiffOn (fun k => hsm n k)
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
      (fun k => Jeps_contDiffOn ρ hρ (hεpos n) hloc k)
  show Work.Spaces.mixed j i
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) p.1 p.2
      - (Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) τ)) 0 / pzNorm)
        * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2
    = Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) τ) p.1 p.2
  rw [slice_JfamP]
  exact (Work.FTS.StrongEps.PZeroAux.mixed_Pz hsmJ hp.1 hp.2 j i).symm

end Work.FTS.StrongEps
