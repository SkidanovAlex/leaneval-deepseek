/-
Copyright: work module for the Elginda finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/AsmPkg.lean` — the per-horizon assembly with the decay majorant

`E5G/PkgOfHlim.lean` proves the per-horizon E5 assembly `EpsLimPkg_of_horizon_of_hlim`: every
`EpsLimPkg` row is derived, *except* that the `eqT` row consumes the pointwise identification
`hlim` of the scheme's right-hand side, which the tower's own data do **not** determine
(the chain `epsRHSP = Pz (J₀ ∘ J_ε ∘ profRHS)` passes through the *radial* zero modes
`L₁₂(·)(0)`, whose convergence needs a dominated-convergence majorant — see
`E5G/EpsLimPkg_of_horizon.lean`, whose frozen statement was returned FALSE by its prover for
exactly this reason).

The two modules of this session remove that supply clause from the interface:

* `E5G/TowerDecay.lean` (`tower_exists_decay`) produces, beside the tower, a per-horizon
  `1/z`-integrable majorant `Maj n` with `EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n)` for the whole
  horizon-`n` sequence — **as a theorem**, from `EpsUniformMem`;
* `E5G/hlim_of_tower.lean` (`hlim_of_tower`) proves the identification `hlim` from that data.

This module is the two-line consequence: the same statement as
`EpsLimPkg_of_horizon_of_hlim`, with `hlim` **removed** and the decay data put in its place.  The
remaining supply clauses of the per-horizon assembly are therefore exactly

  `hcontR`, `hWc`  (uniformity in the fake time of the limiting right-hand side),
  `hdbd`           (the `ℋ³`-bound on `∂_τ` at the limit; follows from `eqT`),
  `hapx`           (the G2 approximation clause; the `ℋ⁴`-τ-Lipschitzity chapter).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.PkgOfHlim
import Submission.Work.FTS.StrongEps.E5G.hlim_of_tower

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The per-horizon E5 assembly, with the decay majorant instead of the identification.** -/
theorem EpsLimPkg_of_horizon_of_decay {α C₀ K Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {e : ℕ → ℝ} {G : ℕ → ℕ → Fam} {K' : ℕ → ℝ} {ι : ℕ → ℕ → ℕ} {Maj : ℕ → ℝ → ℝ}
    {F : ℕ → ℝ → Fn}
    (n : ℕ) (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₀ Φs E)
    (hELL3 : EllLimOK3 α E)
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hvan : ∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hL12g₀ : Work.Construction.L12 g₀ 0 = 0)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc 0 1)
    (hε0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hTower : ∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hMaj : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0))
    (hDec : ∀ k : ℕ, n ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Tn n),
      EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n))
    (hι : StrictMono (ι n)) (hadm : ∀ k : ℕ, n ≤ ι n k)
    (hconv : ∀ τ ∈ Set.Icc 0 (Tn n),
      ConvLocUnifH6 α (K' n) (fun k => slice (G n (ι n k)) τ) (F n τ))
    (hT : 0 < T) (hTT : T ≤ Tn n)
    (hcontR : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun s : ℝ => rhsFun α Φs E (clampQ (F n) g₀) s z θ) (Set.Icc 0 T))
    (hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        rhsFun α Φs E (clampQ (F n) g₀) p.2.2 p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hdbd : ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ : ℝ, 0 < τ → τ < T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot (clampQ (F n) g₀) τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot (clampQ (F n) g₀) τ) ≤ Cd)
    (hapx : ∀ T' : ℝ, 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E (clampQ (F n) g₀)) :
    ∃ Cd' : ℝ, 0 < Cd' ∧ EpsLimPkg α C₀ K Cd' T Φs E g₀ (clampQ (F n) g₀) :=
  EpsLimPkg_of_horizon_of_hlim (n := n) (hα := hα) (hρ := hρ) (hc₁ := hc₁) (hc₂ := hc₂)
    (hEll := hEll) (hstar := hstar) (hml := hml) (hELL3 := hELL3) (hvan := hvan)
    (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0) (hTower := hTower) (hι := hι)
    (hadm := hadm) (hconv := hconv) (hT := hT) (hTT := hTT) (hcontR := hcontR)
    (hWc := hWc) (hdbd := hdbd) (hapx := hapx)
    (hlim := hlim_of_tower (n := n) (hα := hα) (hρ := hρ) (hc₁ := hc₁) (hc₂ := hc₂)
      (hEll := hEll) (hstar := hstar) (hml := hml) (hELL3 := hELL3) (hsmΦ := hsmΦ)
      (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0) (hTower := hTower) (hMaj := hMaj)
      (hDec := hDec) (hι := hι) (hadm := hadm) (hconv := hconv) (hT := hT) (hTT := hTT))

end Work.FTS.StrongEps.E5G
