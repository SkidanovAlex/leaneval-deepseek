/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.StrongEps.EpsGdotThirdH` — `gdot` is `ℋ³`-honest at the `ε`-level

This is the sibling of `EpsGdotThird` (`Submission/Work/FTS/StrongEps/EpsGdotThird.lean`): the
`ℋ³`-membership and the uniform `ℋ³`-bound of the fake-time derivative `gdot g τ` of an
`ε`-solution `g` of the log-coordinate scheme, uniformly for `τ ∈ (0,T)`.

The difference to `EpsGdotThird` is the form in which the *regularity* of the scheme's
right-hand side is supplied.  There, the caller had to provide the single clause

  `hsmW : ∀ τ, ∀ n, ContDiffOn ℝ n (uncurry (epsWU α ρ ε Φs E g τ)) Quad`,

i.e. smoothness of the *sum* `epsW = 𝓛(J_ε g) + 𝓡 = linPart α (J_ε g_τ) + dynRHS ⋯`; here the
caller provides the corresponding clauses for the two *summands* separately (`hlinc`, `hrhsc`,
the shape in which the equation's regularity data is available at the `ε`-level, cf.
`EpsLimDbd_aux` and `StrongPersist/Dbd.lean`), and the sum is assembled inside.

## The route

At an interior fake time `IsEpsSol.gdot_eq` identifies, on the open quadrant,

  `gdot g τ = epsRHS α ρ ε Φs E g τ = J_ε (epsWU α ρ ε Φs E g τ)`   (`epsRHS_eq_Jeps_epsW`),

and `HkMem_congr_Q0` / `HkSq_congr_open` show that both conjuncts of the conclusion are
statements about the open quadrant alone.  For the remaining ingredient — the `ℋ³`-boundedness of
the *mollifier* on `epsW` — the `E1` chapter supplies `HkMem_Jeps` (membership) and
`HkSq_Jeps_le` (the `e^{Cε}`-bound), and both need

* `α ∈ Set.Ioc 0 1` (the range of the weight comparisons `Wt_shift_le`/`wdiv_shift_le`) — the
  hypothesis `hα1 : α ≤ 1` (in the intended instantiation the scheme runs at `pExp α = 3α ≤ 1`);
* `C^∞` of `epsW` on the open quadrant — assembled here from `hlinc`/`hrhsc`;
* `HkMem α 3 (epsW)` — from `L3Data.lin`/`L3Data.rhs` and `HkAddFin`.

The level-three data of the two summands is `L3Data` at the *mollified* slice
`f = slice (Jfam ρ ε g) τ`, whose class `H6Adm` and elliptic context `Ell6Ctx` come from
`EpsReg` through the bridges `H6Adm_Jfam` / `Ell6Ctx_of_classC` (both in `EpsGdotThird.lean`),
and the modulation bounds at that slice come from `MuLamOK` evaluated at the constant family
attached to `f` (`muDyn` sees a family only through its `τ`-slice).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Gdot
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.EpsGdotThird
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## Helper lemmas: the quadrant, and the modulation at the mollified slice -/

/-- The open quadrant of the `ε`-scheme and the one of the elliptic estimates are the same set. -/
theorem quad_eq_Q0 : (Quad : Set (ℝ × ℝ)) = Work.FTS.EllipticEst.Q0 := rfl

/-- **The modulation constant at the mollified slice.**  `muDyn` sees a family only through its
`τ`-slice, so at `J_ε g` it is `Construction.mufunS` evaluated at the profile. -/
theorem muDyn_Jfam_eq (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) :
    Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ
      = Work.Construction.mufunS α
          (Work.Construction.N0 α
            (Work.Construction.Ftot α (slice (Jfam ρ ε g) τ)) (slice (Jfam ρ ε g) τ))
          (Work.Construction.N α
            (Work.Construction.Ftot α (slice (Jfam ρ ε g) τ))
            (fun z θ => Φs z θ + E (slice (Jfam ρ ε g) τ) z θ))
          (slice (Jfam ρ ε g) τ) := rfl

/-- The same identification for the family which is constant in `τ` (the family at which the
`τ = 0` clause of `MuLamOK` is evaluated). -/
theorem muDyn_constFam_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (h : Fn) :
    Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => h z θ))
        (fun z θ _ => h z θ) 0
      = Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α h) h)
          (Work.Construction.N α (Work.Construction.Ftot α h)
            (fun z θ => Φs z θ + E h z θ)) h := rfl

/-- **The bridge from `MuLamOK` to the mollified family**: the modulation of `J_ε g` at `τ` is the
one of the constant family attached to `slice (Jfam ρ ε g) τ`, evaluated at `τ = 0`. -/
theorem muDyn_Jfam_slice_eq (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) (f : Fn) (hf : f = slice (Jfam ρ ε g) τ) :
    Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ
      = Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
          (fun z θ _ => f z θ) 0 := by
  subst hf
  rw [muDyn_Jfam_eq, muDyn_constFam_eq]

/-- **The `μ`/`λ` bounds at the mollified slice**, from `MuLamOK` at the constant family attached
to the slice. -/
theorem muLamOK_Jfam {α C₀ : ℝ} {Φs : Fn} {E : Fn → Fn} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {g : Fam}
    (hml : MuLamOK α C₀ Φs E) {τ : ℝ}
    (hC : Work.FTS.ClassC.ClassC α (slice (Jfam ρ ε g) τ))
    (hXn : Work.FTS.Nonlin.Xn α (slice (Jfam ρ ε g) τ) ≤ C₀ * α ^ 2) :
    |Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ| ≤ 1 / 2 ∧
      |Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ| ≤ 1 := by
  obtain ⟨h1, h2⟩ := hml (slice (Jfam ρ ε g) τ) hC hXn
  have hEq : Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g)) (Jfam ρ ε g) τ
      = Galerkin.muDyn α
          (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => slice (Jfam ρ ε g) τ z θ))
          (fun z θ _ => slice (Jfam ρ ε g) τ z θ) 0 :=
    muDyn_Jfam_slice_eq α ρ ε Φs E g τ (slice (Jfam ρ ε g) τ) rfl
  exact ⟨by rw [hEq]; exact h1, by simp only [Galerkin.lamDyn, hEq]; exact h2⟩

/-! ## The target -/

theorem EpsGdotThirdH {α α₂ Ce C3 Cpow C₀ Cs T ε B : ℝ} {ρ : ℝ × ℝ → ℝ}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {Φs g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) (hα : α ∈ Set.Ioc 0 α₂)
    (hα1 : α ≤ 1)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hsol : Work.FTS.StrongEps.IsEpsSol α ρ ε T Φs E g₀ g)
    (hreg : Work.FTS.StrongEps.EpsReg α ρ ε T g)
    (hlinc : ∀ τ ∈ Set.Ioo (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.StrongPersist.linPart α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.Jfam ρ ε g) τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Ioo (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.Jfam ρ ε g))
        (Work.FTS.StrongEps.Jfam ρ ε g) τ))
      Work.FTS.EllipticEst.Q0)
    (hb4 : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.Jfam ρ ε g) τ)
        ≤ C₀ * α ^ 2)
    (hb6 : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.Jfam ρ ε g) τ) ≤ B) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd := by
  classical
  -- `E1`: the two bounds for the mollifier
  obtain ⟨Cm, hCmpos, hJle⟩ := HkSq_Jeps_le ρ hρ.moll
  have hαI1 : α ∈ Set.Ioc 0 1 := ⟨hα.1, hα1⟩
  have hC3 : 0 < C3 := hL3.pos.1
  refine ⟨|Real.sqrt (Real.exp (Cm * ε)) * Real.sqrt 2 *
      (C3 * (1 + C₀ * α ^ 2) ^ 4
        + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
          * (1 + B) ^ 2)| + 1, by positivity, ?_⟩
  intro τ hτ
  have hτI : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  -- the mollified slice and its stream function
  set f : Fn := slice (Jfam ρ ε g) τ with hf
  set Φ : Fam := Work.FTS.Nonlin.PsiCan Φs E (Jfam ρ ε g) with hΦ
  -- the class data of the cross-section
  have hC : Work.FTS.ClassC.ClassC α f := by
    rw [hf]; exact (hreg.2 τ hτI).2.2
  have hadm : Work.FTS.StrongPersist.H6Adm α f := by
    rw [hf]; exact H6Adm_Jfam hreg hτI
  have hXn : Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 := by
    rw [hf]; exact hb4 τ hτI
  have hXn6 : Work.FTS.StrongGlobal.Xn6 α f ≤ B := by
    rw [hf]; exact hb6 τ hτI
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (slice Φ τ) :=
    Ell6Ctx_of_classC hEll hstar hC
  -- the modulation bounds
  have hMuLam := muLamOK_Jfam hml hC hXn
  have hmu : |Galerkin.muDyn α Φ (Jfam ρ ε g) τ| ≤ 1 / 2 := hMuLam.1
  have hlam : |Galerkin.lamDyn α Φ (Jfam ρ ε g) τ| ≤ 1 := hMuLam.2
  -- `S6` (the level-three package) at the two summands
  obtain ⟨hmem1raw, hbnd1raw⟩ := hL3.lin α hα f hadm
  obtain ⟨hmem2raw, hbnd2raw⟩ := hL3.rhs α hα E Φs (slice Φ τ) f Cs
    (Galerkin.muDyn α Φ (Jfam ρ ε g) τ) (Galerkin.lamDyn α Φ (Jfam ρ ε g) τ) (C₀ * α ^ 2)
    hell hadm hXn hmu hlam
  set u : Fn := Work.FTS.StrongPersist.linPart α f with hu
  set v : Fn := Work.FTS.StrongPersist.rhsOf α (Galerkin.muDyn α Φ (Jfam ρ ε g) τ)
    (Galerkin.lamDyn α Φ (Jfam ρ ε g) τ) (Work.Construction.Ftau α (Jfam ρ ε g) τ)
    (slice Φ τ) f with hv
  have hmem1 : Work.Spaces.HkMem α 3 u := hmem1raw
  have hmem2 : Work.Spaces.HkMem α 3 v := hmem2raw
  have hbnd1 : Work.Spaces.HkNorm α 3 u
      ≤ C3 * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 := hbnd1raw
  have hbnd2 : Work.Spaces.HkNorm α 3 v
      ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
        * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := hbnd2raw
  -- the two sides of the equation are exactly `u + v`
  have hsum : Galerkin.dynLin α (Jfam ρ ε g) τ + Galerkin.dynRHS α Φ (Jfam ρ ε g) τ
      = fun z θ => u z θ + v z θ := by
    funext z θ
    simp only [Pi.add_apply, hu, hv, hf,
      Work.FTS.StrongPersist.dynLin_eq_linPart, Work.FTS.StrongPersist.dynRHS_eq_rhsOf]
  have hW : epsWU α ρ ε Φs E g τ = fun z θ => u z θ + v z θ := by
    funext z θ
    have h := congrFun (congrFun hsum z) θ
    simpa only [epsWU, Pi.add_apply] using h
  -- regularity of the sum, and of the two summands at order three
  have hlreg : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
    rw [hu, hf]; exact hlinc τ hτ 3
  have hregr : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0 := by
    rw [hv, hf, ← Work.FTS.StrongPersist.dynRHS_eq_rhsOf α Φ (Jfam ρ ε g) τ]
    exact hrhsc τ hτ 3
  have hsmSum : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (fun z θ => u z θ + v z θ)) Quad := by
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
      rw [hu, hf]; exact hlinc τ hτ n
    have h2 : ContDiffOn ℝ n (Function.uncurry v) Work.FTS.EllipticEst.Q0 := by
      rw [hv, hf, ← Work.FTS.StrongPersist.dynRHS_eq_rhsOf α Φ (Jfam ρ ε g) τ]
      exact hrhsc τ hτ n
    rw [quad_eq_Q0]
    exact h1.add h2
  -- `ℋ³`-closure of the sum
  have hadd := Work.FTS.StrongPersist.HkAddFin (α := α) (k := 3) hlreg hregr hmem1 hmem2
  -- the `E1` chapter at `epsW`
  have hsmW : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (epsWU α ρ ε Φs E g τ)) Quad := by
    intro n; rw [hW]; exact hsmSum n
  have hmemW : Work.Spaces.HkMem α 3 (epsWU α ρ ε Φs E g τ) := by
    rw [hW]; exact hadd.1
  have hmemJ : Work.Spaces.HkMem α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ)) :=
    HkMem_Jeps hρ.moll hαI1 hε hsmW hmemW
  have hSqJ : Work.Spaces.HkSq α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ))
      ≤ Real.exp (Cm * ε) * Work.Spaces.HkSq α 3 (epsWU α ρ ε Φs E g τ) :=
    hJle α hαI1 3 ε hε hε1 (epsWU α ρ ε Φs E g τ) hsmW hmemW hmemJ
  -- back to `gdot`
  have hgd : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Jeps ρ ε (epsWU α ρ ε Φs E g τ) z θ = Galerkin.gdot g τ z θ := by
    intro z θ hz hθ
    rw [← epsRHS_eq_Jeps_epsWU α ρ ε Φs E g τ]
    exact (IsEpsSol.gdot_eq hsol hz hθ hτ).symm
  refine ⟨Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hmemJ
    (fun z hz θ hθ => hgd z θ hz hθ), ?_⟩
  have hsq : Work.Spaces.HkSq α 3 (Galerkin.gdot g τ)
      = Work.Spaces.HkSq α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 3
      (fun z θ hz hθ hlt => (hgd z θ hz ⟨hθ, hlt⟩).symm)
  have hnorm : Work.Spaces.HkNorm α 3 (Galerkin.gdot g τ)
      = Work.Spaces.HkNorm α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ)) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
  rw [hnorm]
  -- the two summand bounds at the pinned level
  have hbnd1' : Work.Spaces.HkNorm α 3 u ≤ C3 * (1 + C₀ * α ^ 2) ^ 4 := by
    rw [hu]
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have h1 : 1 + Work.FTS.Nonlin.Xn α f ≤ 1 + C₀ * α ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Work.FTS.Nonlin.Xn α f := by linarith
    exact le_trans hbnd1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 4) hC3.le)
  have hbnd2' : Work.Spaces.HkNorm α 3 v
      ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
        * (1 + B) ^ 2 := by
    have hXn60 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have h1 : 1 + Work.FTS.StrongGlobal.Xn6 α f ≤ 1 + B := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Work.FTS.StrongGlobal.Xn6 α f := by linarith
    have hnn : (0 : ℝ) ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow)
        * (1 + C₀ * α ^ 2) ^ 4 := by
      have ha : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have hb : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hα.1.le _
      have hc : (0 : ℝ) ≤ (1 + C₀ * α ^ 2) ^ 4 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hC3.le ha) hb) hc
    exact le_trans hbnd2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hnn)
  calc Work.Spaces.HkNorm α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ))
      = Real.sqrt (Work.Spaces.HkSq α 3 (Jeps ρ ε (epsWU α ρ ε Φs E g τ))) := rfl
    _ ≤ Real.sqrt (Real.exp (Cm * ε) * Work.Spaces.HkSq α 3 (epsWU α ρ ε Φs E g τ)) :=
        Real.sqrt_le_sqrt hSqJ
    _ = Real.sqrt (Real.exp (Cm * ε))
          * Real.sqrt (Work.Spaces.HkSq α 3 (epsWU α ρ ε Φs E g τ)) := by
        rw [Real.sqrt_mul (Real.exp_pos _).le]
    _ = Real.sqrt (Real.exp (Cm * ε)) * Work.Spaces.HkNorm α 3 (epsWU α ρ ε Φs E g τ) := rfl
    _ ≤ Real.sqrt (Real.exp (Cm * ε)) * (Real.sqrt 2 *
          (Work.Spaces.HkNorm α 3 u + Work.Spaces.HkNorm α 3 v)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [hW]
        exact hadd.2
    _ = Real.sqrt (Real.exp (Cm * ε)) * Real.sqrt 2 *
          (Work.Spaces.HkNorm α 3 u + Work.Spaces.HkNorm α 3 v) := by ring
    _ ≤ Real.sqrt (Real.exp (Cm * ε)) * Real.sqrt 2 *
          (C3 * (1 + C₀ * α ^ 2) ^ 4
            + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
              * (1 + B) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hbnd1' hbnd2') ?_
        exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ |Real.sqrt (Real.exp (Cm * ε)) * Real.sqrt 2 *
          (C3 * (1 + C₀ * α ^ 2) ^ 4
            + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
              * (1 + B) ^ 2)| + 1 :=
        le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one)

end Work.FTS.StrongEps
