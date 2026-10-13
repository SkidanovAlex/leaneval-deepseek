/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsZeroMode.lean` — the `L₁₂` zero mode of the scheme's RHS

The paper's `L₁₂`-zero-mode identity (`L-N5.8` of the design,
`Submission/Work/FTS/Apriori/ZeroMode.lean`)

  `L₁₂(dynLin + dynRHS)(0) = (1 - μ)·L₁₂(slice g τ)(0)`

specialised to the **projected** `ε`-scheme (`Submission/Work/FTS/StrongEps/PZeroScheme.lean`).
The scheme's right-hand side is evaluated at the projected, mollified family `JfamP ρ ε g`, whose
slice is `Pz (J_ε (slice g τ))` — hence of vanishing zero mode by construction
(`PZeroAux.Pz_l12`).  With `muDyn α Ψ G τ ≠ -1` (`MuLamOK` gives `|muDyn| ≤ 1/2`) the identity
therefore gives

  `L₁₂(epsWP α ρ ε Φs E g τ)(0) = (1 - μ)·0 = 0`,

the `h0` input of `EpsCorrTendsto.EpsCorr_tendsto_zero` (the `P₀`-half of `G4`).

## The three obligations of the zero-mode identity

In the vocabulary of `Submission/Work/FTS/StrongEps/EpsZero/Pieces.lean`, with
`f = slice (JfamP ρ ε g) τ` (a class-`C` profile vanishing off the open quadrant — `hzero` below),
`Ψ = Φs + E f`, `F = F_* + f` and `μ = muDyn … τ`:

* `hlin` — `L₁₂(-𝓛_Γ^T f)(0) = L₁₂(f)(0)`: the paper's `(L12L)` at `z = 0`
  (`EpsZero.LGammaT_zero_classC`) and `L₁₂(-h)(0) = -L₁₂(h)(0)`;
* `hstar` — `L₁₂(N_*)(0) = -μ L₁₂(f)(0)`: `μ + λ + μλ = -μ` at `λ = lamfun μ`, the elementary
  `L₁₂(D_z f)(0) = 0` and linearity (`EpsZero.Nstar_zero_classC`);
* `hadd` — additivity of `L₁₂(·)(0)` over the five summands
  `-𝓛_Γ^T f, -μ̄·AK, N₀, N, N_*` (`EpsZero.Hadd`), whose integrability certificates are
  `EpsZero.RhsDensIntegrable`.

Those three live in the sibling files of this directory (proved by colleagues); the `μ ≠ -1` side
condition and the assembly are proved here.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.Apriori.ZeroMode
import Submission.Work.FTS.StrongEps.EpsZero.Pieces
import Submission.Work.FTS.StrongEps.EpsZero.Hadd
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.EpsZero.LGammaT_zero_classC
import Submission.Work.FTS.StrongEps.EpsZero.RhsDensIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS muDyn lamDyn)
open Work.FTS.Nonlin (PsiCan)

set_option autoImplicit false

/-! ## The `μ ≠ -1` side condition of the zero-mode identity -/

/-- **`muDyn ≠ -1` at the projected family**: `muDyn` sees the two families only through their
`τ`-slices, so `MuLamOK` (which bounds `|muDyn| ≤ 1/2` at the constant families built from a
class-`C` profile of size `≤ C₀α²`) transfers to the scheme's projected family. -/
theorem muDyn_ne_neg_one {α C₀ ε τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hC : Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ))
    (hXn : Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2)
    (hML : MuLamOK α C₀ Φs E) :
    muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ ≠ -1 := by
  obtain ⟨h1, _⟩ := hML (slice (JfamP ρ ε g) τ) hC hXn
  have key : muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ
      = muDyn α (PsiCan Φs E (fun z θ _ => slice (JfamP ρ ε g) τ z θ))
          (fun z θ _ => slice (JfamP ρ ε g) τ z θ) 0 := rfl
  rw [key]
  intro hcon
  rw [hcon] at h1
  norm_num at h1

/-! ## The `μ̄` zero-mode identity, in the form its proof consumes -/

/-- The `μ̄`-zero-mode identity `L₁₂(dynLin + dynRHS)(0) = (1-μ)L₁₂(slice g τ)(0)` of
`Work.FTS.Apriori.L12_zero_rhs`, with the unused `GalClass` hypothesis dropped (the proof of
`L12_zero_rhs` consumes only the three algebra obligations `hadd`, `hlin`, `hstar`). -/
theorem L12_zero_rhs_of {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (g Φ : Fam) (τ : ℝ)
    (hadd : Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0
      = Work.Construction.L12 (dynLin α g τ) 0
        - Work.Construction.mubar
            (Work.Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
            (Work.Construction.N α (Construction.Ftau α g τ) (slice Φ τ))
          * Work.Construction.L12 (Work.Construction.AK α) 0
        + Work.Construction.L12
            (Work.Construction.N0 α (Construction.Ftau α g τ) (slice g τ)) 0
        + Work.Construction.L12
            (Work.Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) 0
        + Work.Construction.L12 (Work.Construction.Nstar (muDyn α Φ g τ)
            (Work.Construction.lamfun (muDyn α Φ g τ)) (slice g τ)) 0)
    (hlin : Work.Construction.L12 (dynLin α g τ) 0 = Work.Construction.L12 (slice g τ) 0)
    (hstar : Work.Construction.L12 (Work.Construction.Nstar (muDyn α Φ g τ)
        (Work.Construction.lamfun (muDyn α Φ g τ)) (slice g τ)) 0
      = - muDyn α Φ g τ * Work.Construction.L12 (slice g τ) 0) :
    Work.Construction.L12 (dynLin α g τ + dynRHS α Φ g τ) 0
      = (1 - muDyn α Φ g τ) * Work.Construction.L12 (slice g τ) 0 := by
  have hmubar : Work.Construction.mubar
      (Work.Construction.N0 α (Construction.Ftau α g τ) (slice g τ))
      (Work.Construction.N α (Construction.Ftau α g τ) (slice Φ τ))
      = Work.Construction.L12
          (Work.Construction.N0 α (Construction.Ftau α g τ) (slice g τ)) 0
        + Work.Construction.L12
          (Work.Construction.N α (Construction.Ftau α g τ) (slice Φ τ)) 0 := rfl
  have hAK : Work.Construction.L12 (Work.Construction.AK α) 0 = 1 :=
    Work.Construction.L12_AK_eq_one hα hα1
  rw [hadd, hlin, hstar, hmubar, hAK]
  ring

/-! ## The target -/

theorem EpsZeroMode {α C₀ Ce Cs ε τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hC : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
    (hXn : Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hML : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    Work.Construction.L12 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) 0 = 0 := by
  -- ### the projected, mollified slice vanishes off the open quadrant
  have hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) →
      slice (JfamP ρ ε g) τ z θ = 0 := by
    intro z θ h
    have hJ : Jeps ρ ε (slice g τ) z θ = 0 := Jeps_eq_zero ρ ε (slice g τ) h
    have hb : bump z θ = 0 := by
      rcases not_and_or.mp h with hz | hθ
      · have hz' : z < 1 / 2 := lt_of_le_of_lt (not_lt.mp hz) (by norm_num)
        simp only [bump, bump_zCut_eq_zero_of_lt hz', zero_mul]
      · by_cases hθ0 : θ ≤ 0
        · have h' : θ < Real.pi / 4 := lt_of_le_of_lt hθ0 (by linarith [Real.pi_pos])
          simp only [bump, bump_thCut_eq_zero_of_lt h', mul_zero]
        · have h' : 3 * Real.pi / 8 < θ := by
            have hge : Real.pi / 2 ≤ θ := by
              by_contra hc
              exact hθ ⟨lt_of_not_ge hθ0, lt_of_not_ge hc⟩
            linarith [Real.pi_pos]
          simp only [bump, bump_thCut_eq_zero_of_gt h', mul_zero]
    simp only [slice, JfamP, Pz_apply, hJ, hb, mul_zero, sub_zero]
  -- ### the modulation constant and its side condition
  have hne : muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ ≠ -1 :=
    muDyn_ne_neg_one hC hXn hML
  -- ### the integrability certificates of the five pieces
  obtain ⟨hintL, hintN0, hintN, hintNs, hintAK, hangL, hangN0, hangN, hangNs, hangAK⟩ :=
    Work.FTS.StrongEps.EpsZero.RhsDensIntegrable (α := α) (Ce := Ce) (Cs := Cs)
      (μ := muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
      (lam := lamDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
      hα hC hzero hEll hstar
  -- ### the `AK`-piece with the `μ̄`-constant
  have hdensK : ∀ s : ℝ,
      Work.Construction.L12dens
        (Work.FTS.StrongEps.EpsZero.PK
          (Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
            (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ))) α) s
        = -(Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
            (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ)))
          * Work.Construction.L12dens (Work.Construction.AK α) s := by
    intro s
    simp only [Work.Construction.L12dens, Work.FM.L12dens, Work.FTS.StrongEps.EpsZero.PK]
    rw [show (fun θ : ℝ => Work.Spaces.K θ * (-(Work.FTS.StrongEps.EpsZero.Pmubar α
            (slice (JfamP ρ ε g) τ)
            (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ)))
              * Work.Construction.AK α s θ) / s)
        = fun θ : ℝ => (-(Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
            (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ))))
            * (Work.Spaces.K θ * Work.Construction.AK α s θ / s) from by
      funext θ; ring]
    exact MeasureTheory.integral_const_mul _ _
  have hintK : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PK
        (Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
          (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ))) α)) (Set.Ioi 0) := by
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ =>
        -(Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
          (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ)))
          * Work.Construction.L12dens (Work.Construction.AK α) s) (Set.Ioi 0) :=
      MeasureTheory.Integrable.const_mul hintAK _
    exact h1.congr_fun (fun s _ => (hdensK s).symm) measurableSet_Ioi
  have hangK : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PK
        (Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
          (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ))) α z θ
        / z) Work.Spaces.Iθ := by
    intro z hz
    have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        -(Work.FTS.StrongEps.EpsZero.Pmubar α (slice (JfamP ρ ε g) τ)
          (Work.FTS.StrongEps.EpsZero.PPsi E Φs (slice (JfamP ρ ε g) τ)))
          * (Work.Spaces.K θ * Work.Construction.AK α z θ / z)) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.const_mul (hangAK z hz) _
    exact h1.congr_fun (fun θ _ => by
      simp only [Work.FTS.StrongEps.EpsZero.PK]; ring) measurableSet_Icc
  -- ### the three obligations
  have hhadd : Work.Construction.L12 (dynLin α (JfamP ρ ε g) τ
        + dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ) 0
      = Work.Construction.L12 (dynLin α (JfamP ρ ε g) τ) 0
        - Work.Construction.mubar
            (Work.Construction.N0 α (Construction.Ftau α (JfamP ρ ε g) τ)
              (slice (JfamP ρ ε g) τ))
            (Work.Construction.N α (Construction.Ftau α (JfamP ρ ε g) τ)
              (slice (PsiCan Φs E (JfamP ρ ε g)) τ))
          * Work.Construction.L12 (Work.Construction.AK α) 0
        + Work.Construction.L12
            (Work.Construction.N0 α (Construction.Ftau α (JfamP ρ ε g) τ)
              (slice (JfamP ρ ε g) τ)) 0
        + Work.Construction.L12
            (Work.Construction.N α (Construction.Ftau α (JfamP ρ ε g) τ)
              (slice (PsiCan Φs E (JfamP ρ ε g)) τ)) 0
        + Work.Construction.L12 (Work.Construction.Nstar
            (muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
            (Work.Construction.lamfun
              (muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ))
            (slice (JfamP ρ ε g) τ)) 0 := by
    exact Work.FTS.StrongEps.EpsZero.Hadd (α := α) (Ce := Ce) (Cs := Cs)
      (μ := muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
      (lam := lamDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
      hα hC hzero hEll hstar hintL hintN0 hintN hintNs hintK
      hangL hangN0 hangN hangNs hangK
  have hhlin : Work.Construction.L12 (dynLin α (JfamP ρ ε g) τ) 0
      = Work.Construction.L12 (slice (JfamP ρ ε g) τ) 0 := by
    show Work.Construction.L12 (fun z θ => -(Work.Coercivity.LGammaT α
      (slice (JfamP ρ ε g) τ) z θ)) 0 = Work.Construction.L12 (slice (JfamP ρ ε g) τ) 0
    rw [Work.Construction.L12_neg,
      Work.FTS.StrongEps.EpsZero.LGammaT_zero_classC (α := α) hα hC hzero]
    ring
  have hhstar : Work.Construction.L12 (Work.Construction.Nstar
        (muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
        (Work.Construction.lamfun
          (muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ))
        (slice (JfamP ρ ε g) τ)) 0
      = - muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ
          * Work.Construction.L12 (slice (JfamP ρ ε g) τ) 0 :=
    Work.FTS.StrongEps.EpsZero.Nstar_zero_classC (α := α)
      (μ := muDyn α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ)
      hα hC hzero hne
  -- ### conclude
  have hmain := L12_zero_rhs_of (α := α) hα.1 hα.2 (JfamP ρ ε g)
    (PsiCan Φs E (JfamP ρ ε g)) τ hhadd hhlin hhstar
  show Work.Construction.L12 (dynLin α (JfamP ρ ε g) τ
    + dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ) 0 = 0
  rw [hmain, hC.l12, mul_zero]

end Work.FTS.StrongEps
