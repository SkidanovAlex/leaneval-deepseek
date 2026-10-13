/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/EpsLimPkg_of_horizon_full.lean`

**The per-horizon E5 assembly with *no* supply clauses on the limit side.**

This is the frozen `E5G.EpsLimPkg_of_horizon` statement with the four limit-side clauses
`hlim`, `hcontR`, `hWc`, `hapx` **derived** from the tower data, so that only

* the tower data (`hTower`, `hconv`),
* the decay majorant (`hMaj`, `hDec`),
* the elliptic / star / modulation packages and the `c`-bounds,
* the datum clauses (`hvan`, `hL12g₀`) and the `ℋ³`-bound of `∂_τ` at the limit (`hdbd`),

remain as input.  The key point (recorded in the module header of
`E5G/EpsLimPkg_of_horizon.lean`, where the un-augmented statement was returned FALSE) is that the
`eqT` row of `EpsLimPkg` needs the pointwise identification `hlim : epsRHSP → rhsFun`, which is *not*
determined by the tower data alone, because `epsRHSP = Pz (J_ε ∘ profRHS)` passes through the
*radial* zero modes `L₁₂(·)(0)`, whose convergence needs a dominated-convergence majorant.  The
hypotheses `hMaj`/`hDec` above are exactly that majorant (`EpsDecay`), and `E5G/hlim_of_tower`
turns them into `hlim`.

The four derived clauses come from

* `E5G.hlim_of_tower`   — the pointwise identification (`hMaj` + `hDec` + the tower),
* `E5G.hcontR_of_tower` — `s`-continuity of the limiting right-hand side,
* `E5G.hWc_of_tower`    — joint continuity in `(z, θ, s)`,
* `E5G.hapx_of_tower`   — the G2 approximation clause `LimApproxOn`,

and the assembly itself is `E5G.EpsLimPkg_of_horizon_of_hlim` (in `E5G/PkgOfHlim.lean`), which
derives *all* `EpsLimPkg` rows from those data.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.AsmPkg
import Submission.Work.FTS.StrongEps.E5G.hcontR_of_tower
import Submission.Work.FTS.StrongEps.E5G.hWc_of_tower
import Submission.Work.FTS.StrongEps.E5G.hlim_of_tower
import Submission.Work.FTS.StrongEps.E5G.hapx_of_tower
import Submission.Work.FTS.StrongEps.E5G.PkgOfHlim
import Submission.Work.FTS.StrongEps.EpsLimVolterraP
import Submission.Work.FTS.StrongPersist.Clauses

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.E5G

theorem EpsLimPkg_of_horizon_full {α₂ α₄ α C₀ K Ce Cs Cs6 C3 Cpow T : ℝ} {K' : ℕ → ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {e : ℕ → ℝ} {G : ℕ → ℕ → Work.FTS.Galerkin.Fam}
    {Maj : ℕ → ℝ → ℝ} {ι : ℕ → ℕ → ℕ} {Fc : ℝ → Work.FTS.Galerkin.Fn}
    (n : ℕ) (hα₄ : 0 < α₄) (hα₄1 : α₄ ≤ 1) (hα : α ∈ Set.Ioc (0 : ℝ) α₄)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) (hα₂ : α ∈ Set.Ioc (0 : ℝ) α₂)
    (hvan : ∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hc₁ : 1 / 10 ≤ Work.Spaces.c α) (hc₂ : Work.Spaces.c α ≤ 10)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E)
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hL12g₀ : Work.Construction.L12 g₀ 0 = 0)
    (hεe : ∀ k : ℕ, e k ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto e Filter.atTop (nhds 0))
    (hTower : ∀ n k : ℕ, n ≤ k → Work.FTS.StrongEps.E5G.TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k))
    (hMaj : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0))
    (hDec : ∀ k : ℕ, n ≤ k → ∀ τ ∈ Set.Icc (0 : ℝ) (Work.FTS.StrongEps.E5G.Tn n),
      Work.FTS.StrongEps.EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n))
    (hι : StrictMono (ι n)) (hadm : ∀ k : ℕ, n ≤ ι n k)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) (Work.FTS.StrongEps.E5G.Tn n),
      Work.FTS.StrongEps.ConvLocUnifH6 α (K' n) (fun k => Work.FTS.Galerkin.slice (G n (ι n k)) τ) (Fc τ))
    (hT : 0 < T) (hTT : T ≤ Work.FTS.StrongEps.E5G.Tn n)
    (hdbd : ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ : ℝ, 0 < τ → τ < T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot (Work.FTS.StrongEps.clampQ Fc g₀) τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot (Work.FTS.StrongEps.clampQ Fc g₀) τ) ≤ Cd) :
    ∃ Cd' : ℝ, 0 < Cd' ∧
      Work.FTS.StrongEps.EpsLimPkg α C₀ K Cd' T Φs E g₀ (Work.FTS.StrongEps.clampQ Fc g₀) := by
  classical
  -- the honest parameter range of the limit-side chapters
  have hα1 : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα.1, le_trans hα.2 hα₄1⟩
  -- ## the four limit-side clauses, derived from the tower data and the decay majorant
  have hcontR := hcontR_of_tower (n := n) (hα₄ := hα₄) (hα₄1 := hα₄1) (hα := hα) (hρ := hρ)
    (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6) (hml := hml)
    (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
    (hTower := hTower) (hMaj := hMaj) (hDec := hDec) (hι := hι) (hadm := hadm)
    (hconv := hconv) (hT := hT) (hTT := hTT)
  have hWc := hWc_of_tower (n := n) (hα₄ := hα₄) (hα₄1 := hα₄1) (hα := hα) (hρ := hρ)
    (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hstar6 := hstar6) (hml := hml)
    (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
    (hTower := hTower) (hMaj := hMaj) (hDec := hDec) (hι := hι) (hadm := hadm)
    (hconv := hconv) (hT := hT) (hTT := hTT)
  have hapx := hapx_of_tower (n := n) (hα := hα1) (hρ := hρ)
    (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hml := hml)
    (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
    (hTower := hTower) (hMaj := hMaj) (hDec := hDec) (hι := hι) (hadm := hadm)
    (hconv := hconv) (hT := hT) (hTT := hTT)
  have hlim := hlim_of_tower (n := n) (hα := hα1) (hρ := hρ)
    (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar) (hml := hml)
    (hELL3 := hELL3) (hsmΦ := hsmΦ) (hL12g₀ := hL12g₀) (hεe := hεe) (hε0 := hε0)
    (hTower := hTower) (hMaj := hMaj) (hDec := hDec) (hι := hι) (hadm := hadm)
    (hconv := hconv) (hT := hT) (hTT := hTT)
  -- ## the assembly
  exact EpsLimPkg_of_horizon_of_hlim (n := n) (F := fun _ : ℕ => Fc) (K := K)
    (hα := hα1) (hρ := hρ) (hc₁ := hc₁) (hc₂ := hc₂) (hEll := hEll) (hstar := hstar)
    (hml := hml) (hELL3 := hELL3) (hvan := hvan) (hL12g₀ := hL12g₀) (hεe := hεe)
    (hε0 := hε0) (hTower := hTower) (hι := hι) (hadm := hadm) (hconv := hconv)
    (hT := hT) (hTT := hTT) (hcontR := hcontR) (hWc := hWc) (hdbd := hdbd)
    (hapx := hapx) (hlim := hlim)

end Work.FTS.StrongEps.E5G
