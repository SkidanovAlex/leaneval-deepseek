/-
# `Work.FTS_FinalLeaves.sol_fire_proved` — the (8′) feed

From a solution `hSol : FinalV2.Sol α Φs E g` of the dynamic modulated problem for the *canonical*
stream function `PsiCan Φs E g` and the Galerkin family `g`, produce the same solution statement
for the firing pair `(psiFire Φs E g, extG g)`, together with the coincidence of the modulation
constants.

**Why it is true.**  Every object appearing in `IsDynGSolWith (IsBslSolPos α)` — the elliptic law
`IsBslSolPos` (through the local operator `bslOp` and the values of `Ftau`/the slice), the linear
part `dynLin` (through `LGammaT`), the nonlinear part `dynRHS` (through `mufunS`, `N0`, `N`, `FK`,
`L12`, the pointwise operators `Rop, Uop, Vop`) and the modulation constant `muDyn` — is built from

* *pointwise data* and *one-variable derivatives* at the evaluation point `(z,θ)`, hence local;
* *integrals* over `Iθ = [0,π/2]` (with the weight `K θ = 3 sin θ cos²θ` vanishing at both
  endpoints) and over `Ioi z` with `z ≥ 0`;

and both `psiFire Φs E g` and `extG g` agree with `PsiCan Φs E g` respectively `g` on the **open
quadrant** `Qd = (0,∞) × (0,π/2)`:

* `psiFire Φs E g z θ τ = PsiCan Φs E g z θ τ` for `θ > 0` (`psiFire_of_pos`),
* `extG g z θ τ = g z θ τ` for `z > 0`, `τ ≥ 0` (`extG_of_pos`),

(the only disagreement of the two pairs is on the null sets `{θ ≤ 0}` resp. `{z ≤ 0}`).  Hence
each of those objects is unchanged when the pair `(PsiCan Φs E g, g)` is replaced by
`(psiFire Φs E g, extG g)`, and the transport of the law / of the within-derivative is bookkeeping.

The four congruence lemmas at the bottom of the dependency chain
(`Work.FTS_FinalLeaves.SolFire.LGammaT_congr_of_agreeOnQ`, `...N0_congr_of_agreeOnQ`,
`...N_congr_of_agreeOnQ`, `...isBslSolPos_psiFire_extG`) are proved in the `SolFire/` directory;
the lemmas in this file assemble them into `dynLin`, `mubar`, `gRHS`, `muDyn` and `dynRHS` and
then run the two-line transport.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.StrongGlobal.dynRHS_congr
import Submission.Work.FTS.Final.ExtG.dynOK_extG
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.Galerkin.Basic
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ
import Submission.Work.FTS.PhiStar.ZeroOffWitness
import Submission.Work.Construction.MufunS
import Submission.Work.FTS_FinalLeaves.SolFire.LGammaT_congr_of_agreeOnQ
import Submission.Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ
import Submission.Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ
import Submission.Work.FTS_FinalLeaves.SolFire.isBslSolPos_psiFire_extG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves

open scoped Real Topology

/-! ## Congruence of the differential operators on the open quadrant

The three lemmas below are the `deriv`-locality of `pth`/`Dth`/`pz` at an interior point of the
quadrant, in the form consumed by the `N0`/`N`/`gRHS` congruence chain. -/

/-- `pz` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem pz_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ := by
  simp only [Work.Spaces.pz]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact h z' θ hz' hθ hθ2

/-- `pth` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem pth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  simp only [Work.Spaces.pth]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨hθ, hθ2⟩)]
    with θ' hθ'
  exact h z θ' hz hθ'.1 hθ'.2

/-- `Dth` at an interior point of the quadrant only sees the values of the function on the
quadrant. -/
theorem Dth_congr_of_agreeOnQ {f f' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (h : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → f z' θ' = f' z' θ') :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  simp only [Work.Spaces.Dth, pth_congr_of_agreeOnQ hz hθ hθ2 h]

/-! ## Congruence of `mubar`, `Nstar`, `gRHS`, `muDyn`, `dynLin`, `dynRHS` -/

/-- `Nstar` is local: it only sees `g` and `Dz g` at the point. -/
theorem Nstar_congr_of_agreeOnQ {μ lam : ℝ} {g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ') :
    Work.Construction.Nstar μ lam g z θ = Work.Construction.Nstar μ lam g' z θ := by
  have h1 : g z θ = g' z θ := hg z θ hz hθ hθ2
  have h2 : Work.Spaces.pz g z θ = Work.Spaces.pz g' z θ := pz_congr_of_agreeOnQ hz hθ hθ2 hg
  simp only [Work.Construction.Nstar, Work.Spaces.Dz, h1, h2]

/-- The modulation average `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` only sees its data on the open
quadrant. -/
theorem mubar_congr_of_agreeOnQ {α : ℝ} {F F' Φ Φ' g g' : ℝ → ℝ → ℝ}
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      = Work.Construction.mubar (Work.Construction.N0 α F' g') (Work.Construction.N α F' Φ') := by
  have h1 : Work.Construction.L12 (Work.Construction.N0 α F g) 0
      = Work.Construction.L12 (Work.Construction.N0 α F' g') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ hz hθ hθ2 hF hg)
  have h2 : Work.Construction.L12 (Work.Construction.N α F Φ) 0
      = Work.Construction.L12 (Work.Construction.N α F' Φ') 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ hz hθ hθ2 hF hΦ)
  simp only [Work.Construction.mubar, h1, h2]

/-- `gRHS` depends on its three data only through their values on the open quadrant. -/
theorem gRHS_congr_of_agreeOnQ {α μ lam : ℝ} {F F' Φ Φ' g g' : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → F z' θ' = F' z' θ')
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → g z' θ' = g' z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → Φ z' θ' = Φ' z' θ') :
    Work.Construction.gRHS α μ lam F Φ g z θ = Work.Construction.gRHS α μ lam F' Φ' g' z θ := by
  have hmub := mubar_congr_of_agreeOnQ (α := α) hF hg hΦ
  have hN0 := Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ (α := α) hz hθ hθ2 hF hg
  have hN := Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ (α := α) hz hθ hθ2 hF hΦ
  have hNs := Nstar_congr_of_agreeOnQ (μ := μ) (lam := lam) hz hθ hθ2 hg
  simp only [Work.Construction.gRHS, hmub, hN0, hN, hNs]

/-- `muDyn` depends on the two families only through their slices on the open quadrant. -/
theorem muDyn_congr_of_agreeOnQ {α : ℝ} {Φ Φ' g g' : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hg : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z θ = Work.FTS.Galerkin.slice g' τ z θ)
    (hΦ : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice Φ τ z θ = Work.FTS.Galerkin.slice Φ' τ z θ) :
    Work.FTS.Galerkin.muDyn α Φ g τ = Work.FTS.Galerkin.muDyn α Φ' g' τ := by
  have hF : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Ftau α g τ z θ = Work.Construction.Ftau α g' τ z θ := by
    intro z θ hz hθ hθ2
    have h := hg z θ hz hθ hθ2
    simp only [Work.FTS.Galerkin.slice] at h
    simp only [Work.Construction.Ftau]
    rw [h]
  have h1 : Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice g τ)) 0
      = Work.Construction.L12
        (Work.Construction.N0 α (Work.Construction.Ftau α g' τ)
          (Work.FTS.Galerkin.slice g' τ)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N0_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hF z' θ' hz' hθ' hθ2') hg)
  have h2 : Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ)) 0
      = Work.Construction.L12
        (Work.Construction.N α (Work.Construction.Ftau α g' τ)
          (Work.FTS.Galerkin.slice Φ' τ)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 =>
        Work.FTS_FinalLeaves.SolFire.N_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hF z' θ' hz' hθ' hθ2') hΦ)
  have h3 : Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
      = Work.Construction.L12
        (fun z θ => 3 * Work.Spaces.Dth (Work.FTS.Galerkin.slice g' τ) z θ / (1 + z)) 0 :=
    Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ (le_refl (0 : ℝ))
      (fun z θ hz hθ hθ2 => by
        have hd := Dth_congr_of_agreeOnQ hz hθ hθ2
          (fun z' θ' hz' hθ' hθ2' => hg z' θ' hz' hθ' hθ2')
        simp only [hd])
  simp only [Work.FTS.Galerkin.muDyn, Work.Construction.mufunS, h1, h2, h3]

/-- `dynLin` depends on the family only through its slice on the open quadrant. -/
theorem dynLin_congr_of_agreeOnQ {α : ℝ} {g g' : Work.FTS.Galerkin.Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z' θ' = Work.FTS.Galerkin.slice g' τ z' θ') :
    Work.FTS.Galerkin.dynLin α g τ z θ = Work.FTS.Galerkin.dynLin α g' τ z θ := by
  simp only [Work.FTS.Galerkin.dynLin,
    Work.FTS_FinalLeaves.SolFire.LGammaT_congr_of_agreeOnQ (α := α) hz hθ hθ2 hg]

/-- `dynRHS` depends on the two families only through their slices on the open quadrant. -/
theorem dynRHS_congr_of_agreeOnQ {α : ℝ} {Φ Φ' g g' : Work.FTS.Galerkin.Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hg : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z' θ' = Work.FTS.Galerkin.slice g' τ z' θ')
    (hΦ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.FTS.Galerkin.slice Φ τ z' θ' = Work.FTS.Galerkin.slice Φ' τ z' θ') :
    Work.FTS.Galerkin.dynRHS α Φ g τ z θ = Work.FTS.Galerkin.dynRHS α Φ' g' τ z θ := by
  have hmu := muDyn_congr_of_agreeOnQ (α := α) (Φ := Φ) (Φ' := Φ') (g := g) (g' := g') hg hΦ
  have hF : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Work.Construction.Ftau α g τ z' θ' = Work.Construction.Ftau α g' τ z' θ' := by
    intro z' θ' hz' hθ' hθ2'
    have h := hg z' θ' hz' hθ' hθ2'
    simp only [Work.FTS.Galerkin.slice] at h
    simp only [Work.Construction.Ftau]
    rw [h]
  simp only [Work.FTS.Galerkin.dynRHS, Work.FTS.Galerkin.lamDyn, hmu]
  exact gRHS_congr_of_agreeOnQ hz hθ hθ2 hF hg hΦ

/-! ## The target -/

theorem sol_fire_proved {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hSol : Work.FTS.FinalV2.Sol α Φs E g) :
    Work.FTS.Galerkin.IsDynGSolWith (Work.FTS.Final.IsBslSolPos α) α
        (Work.FTS.FinalV2.psiFire Φs E g) (Work.FTS.RegPkgGal.extG g) ∧
      ∀ τ : ℝ, 0 ≤ τ →
        Work.FTS.Galerkin.muDyn α (Work.FTS.FinalV2.psiFire Φs E g) (Work.FTS.RegPkgGal.extG g)
            τ
          = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ := by
  -- the two pairs agree on the open quadrant
  have hgOf : ∀ (τ : ℝ), 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice g τ z θ
        = Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ z θ :=
    fun τ hτ z θ hz _ _ => by
      simp only [Work.FTS.Galerkin.slice]
      exact (Work.FTS.RegPkgGal.extG_of_pos hz hτ).symm
  have hPhiOf : ∀ (τ : ℝ), ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = Work.FTS.Galerkin.slice (Work.FTS.FinalV2.psiFire Φs E g) τ z θ :=
    fun _ z θ _ hθ _ => by
      simp only [Work.FTS.Galerkin.slice]
      exact (Work.FTS.FinalV2.psiFire_of_pos hθ).symm
  refine ⟨⟨fun τ hτ => Work.FTS_FinalLeaves.SolFire.isBslSolPos_psiFire_extG hτ (hSol.1 τ hτ),
    ?_⟩, ?_⟩
  · intro z θ τ hτ hzθ
    have hsol := hSol.2 z θ τ hτ hzθ
    obtain ⟨hz, hθ, hθ2⟩ := hzθ
    have hder : HasDerivWithinAt (fun s => Work.FTS.RegPkgGal.extG g z θ s)
        (Work.FTS.Galerkin.dynLin α g τ z θ
          + Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ z θ)
        (Set.Ici 0) τ :=
      hsol.congr (fun s hs => Work.FTS.RegPkgGal.extG_of_pos hz hs)
        (Work.FTS.RegPkgGal.extG_of_pos hz hτ)
    rw [dynLin_congr_of_agreeOnQ (α := α) hz hθ hθ2 (hgOf τ hτ),
      dynRHS_congr_of_agreeOnQ (α := α) hz hθ hθ2 (hgOf τ hτ) (hPhiOf τ)] at hder
    exact hder
  · intro τ hτ
    exact (muDyn_congr_of_agreeOnQ (α := α) (hgOf τ hτ) (hPhiOf τ)).symm

end Work.FTS_FinalLeaves
