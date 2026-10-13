import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.NRow5
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

open scoped Real
open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The pointwise tools

The `μ`-block of the dynamic right-hand side is `-μ̄·AK α + N_* μ (lamfun μ) g`, and the estimate
below is the pointwise telescoping of that block along the difference `d = g - g'`, using

* the paper's collapse `N_* μ (lamfun μ) g = μ·(D_z g - g)` (valid for `μ ≠ -1`; the two
  hypotheses `|μ| ≤ 1/2` of the statement are what produce `μ ≠ -1`);
* the additivity of `D_z` on the open quadrant for a pointwise decomposition `g = d + g'`.

On the `HkNorm`-side everything is then the subadditivity of `HkNorm` on the open-quadrant class
(`RHS.HkNorm_add_le_open`) together with the two `ℋ⁵`-comparisons `Xn_Dz_le_Xn5` and
`HkNorm_mono_of_mem`. -/

/-- **`D_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k`.** -/
private lemma Dz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : SmoothOpen f') (hk : SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ + Work.Spaces.Dz k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := f)
    (G := fun z θ => f' z θ + k z θ) (fun z θ _ _ _ => h z θ) 1 z θ hz hθ0 hθ1
  have h2 := Work.FTS.EllipticEst.SmoothOpen.DzIter_add hf' hk 1 z θ hz hθ0 hθ1
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h1.trans h2

/-- `Xn` only sees the values on the open quadrant. -/
private lemma Xn_congr_open (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.Nonlin.Xn α f = Work.FTS.Nonlin.Xn α g := by
  rw [show Work.FTS.Nonlin.Xn α f = Work.Spaces.HkNorm α 4 f from rfl,
    show Work.FTS.Nonlin.Xn α g = Work.Spaces.HkNorm α 4 g from rfl,
    Work.Spaces.HkNorm, Work.Spaces.HkNorm,
    Work.FTS.EllipticEst.HkSq_congr_open α 4 h]

/-- `Xn` is homogeneous for the multiplication by a scalar. -/
private lemma Xn_const_mul (α : ℝ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => c * f z θ) = |c| * Work.FTS.Nonlin.Xn α f := by
  have h1 : (fun z θ : ℝ => c * f z θ) = c • f := by
    funext z θ; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Work.FTS.EllipticEst.HkNorm_smul c α 4 f

/-- **Subadditivity of `Xn` on the open-quadrant class**, in the difference form. -/
private lemma Xn_sub_le (α : ℝ) (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ - g z θ)
      ≤ 2 * (Work.FTS.Nonlin.Xn α f + Work.FTS.Nonlin.Xn α g) := by
  have hgs : SmoothOpen (fun z θ => -g z θ) := hg.neg
  have hgm : Work.Spaces.HkMem α 4 (fun z θ => -g z θ) := Work.FTS.NonlinRows.HkMem_neg' α 4 hmg
  have h1 := HkNorm_add_le_open α 4 hα hf hgs hmf hgm
  have hneg : Work.Spaces.HkNorm α 4 (fun z θ : ℝ => - g z θ) = Work.Spaces.HkNorm α 4 g := by
    have h2 : (fun z θ : ℝ => - g z θ) = (-1 : ℝ) • g := by
      funext z θ; simp [Pi.smul_apply]
    rw [h2, Work.FTS.EllipticEst.HkNorm_smul]
    norm_num
  rw [hneg] at h1
  rw [Xn_congr_open α (f := fun z θ => f z θ - g z θ) (g := fun z θ => f z θ + - g z θ)
    (fun z θ _ _ _ => by ring)]
  simpa only [Work.FTS.Nonlin.Xn] using h1

theorem sharp_muBlock_summand {α α₂ Ci Ct Ce Cs Kd : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hEllSub : ∀ g g' : Work.FTS.Galerkin.Fn,
      EllSol (fun z θ => g z θ - g' z θ) = fun z θ => EllSol g z θ - EllSol g' z θ)
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ g g' h : Work.FTS.Galerkin.Fn,
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h →
      (∀ z θ, h z θ = g z θ - g' z θ) → α ≤ 1 →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) g| ≤ 1 / 2 →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) g'| ≤ 1 / 2 →
      |Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ))
        - Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ))|
        ≤ Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h →
      |Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
          (Work.Construction.N α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + EllSol g z θ)) g
        - Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
          (Work.Construction.N α (Work.Construction.Ftot α g')
            (fun z θ => Φs z θ + EllSol g' z θ)) g'|
        ≤ Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α h →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
            (Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)) g z θ)
        - (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
            (Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')) g' z θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
            (Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)) g z θ)
        - (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
            (Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')) g' z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
            (Work.Construction.N α (Work.Construction.Ftot α g)
              (fun z θ => Φs z θ + EllSol g z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
                (Work.Construction.N α (Work.Construction.Ftot α g)
                  (fun z θ => Φs z θ + EllSol g z θ)) g)) g z θ)
        - (-(Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
            (Work.Construction.N α (Work.Construction.Ftot α g')
              (fun z θ => Φs z θ + EllSol g' z θ))) * Work.Construction.AK α z θ
          + Work.Construction.Nstar
              (Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')
              (Work.Construction.lamfun (Work.Construction.mufunS α
                (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
                (Work.Construction.N α (Work.Construction.Ftot α g')
                  (fun z θ => Φs z θ + EllSol g' z θ)) g')) g' z θ))
        ≤ C * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') ^ 2
            * Work.FTS.GalFields.Xn5 α h := by
  -- the uniform norm bound of `AK α` (row `rak` of the row bundle)
  obtain ⟨Kak, hKakpos, hKak⟩ := (Work.FTS.NonlinRows.NAux3 (IP := IP) hN hE).1
  have hCpos : 0 < 2 * |Kd| * (Kak + 8) + 20 := by
    have h1 : 0 ≤ 2 * |Kd| * (Kak + 8) :=
      mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg Kd)) (by linarith)
    linarith
  refine ⟨2 * |Kd| * (Kak + 8) + 20, hCpos, ?_⟩
  intro g g' d hg hg' hd hdiff hα1 hmu1 hmu2 hKdbar hKdmu
  -- ## the two modulation constants
  set mu : ℝ := Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) g with hmu_def
  set mu' : ℝ :=
    Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
      (Work.Construction.N α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) g' with hmu'_def
  set mb : ℝ := Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) with hmb_def
  set mb' : ℝ :=
    Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g') g')
      (Work.Construction.N α (Work.Construction.Ftot α g')
        (fun z θ => Φs z θ + EllSol g' z θ)) with hmb'_def
  set C : ℝ := 2 * |Kd| * (Kak + 8) + 20 with hC_def
  have hmu_ne : mu ≠ -1 := by
    intro hcon; rw [hcon] at hmu1; norm_num at hmu1
  have hmu'_ne : mu' ≠ -1 := by
    intro hcon; rw [hcon] at hmu2; norm_num at hmu2
  -- ## the collapse `N_* μ (lamfun μ) g = μ·(D_z g - g)` (pointwise, for `μ ≠ -1`)
  have hcol : ∀ (μ : ℝ), μ ≠ -1 → ∀ g₀ : ℝ → ℝ → ℝ, ∀ z θ,
      Work.Construction.Nstar μ (Work.Construction.lamfun μ) g₀ z θ
        = μ * (Work.Spaces.Dz g₀ z θ - g₀ z θ) := by
    intro μ hμ g₀ z θ
    have h1 : (1 : ℝ) + μ ≠ 0 := by intro hh; exact hμ (by linarith)
    have hcoef : μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
      rw [Work.Construction.lamfun]; field_simp; ring
    simp only [Work.Construction.Nstar, Work.Spaces.Dz]
    rw [hcoef]; ring
  -- ## the class data
  have hgS : SmoothOpen g := Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1
  have hgS' : SmoothOpen g' := Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg'.reg.1
  have hdS : SmoothOpen d := Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hd.reg.1
  have hgM5 : Work.Spaces.HkMem α 5 g := Work.FTS.OpenPkg.galClass_HkMem5 hg
  have hgM5' : Work.Spaces.HkMem α 5 g' := Work.FTS.OpenPkg.galClass_HkMem5 hg'
  have hdM5 : Work.Spaces.HkMem α 5 d := Work.FTS.OpenPkg.galClass_HkMem5 hd
  have hgM4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hgS hgM5
  have hgM4' : Work.Spaces.HkMem α 4 g' :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hgS' hgM5'
  have hdM4 : Work.Spaces.HkMem α 4 d :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hdS hdM5
  have hpg : Work.FTS.OpenPkg.PiecesHk α g Φs (EllSol g) :=
    Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hg hstar (hell g hg)
  have hpg' : Work.FTS.OpenPkg.PiecesHk α g' Φs (EllSol g') :=
    Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hg' hstar (hell g' hg')
  have hpd : Work.FTS.OpenPkg.PiecesHk α d Φs (EllSol d) :=
    Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hd hstar (hell d hd)
  have hAKsm : SmoothOpen (Work.Construction.AK α) := Work.FTS.StrongPersist.AK_smoothO α
  have hAKmem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα hα1
  have hAKb : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ Kak :=
    (hKak (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hstar.toStarPkgo (hell g hg))).2
  have hDzdm : Work.Spaces.HkMem α 4 (Work.Spaces.Dz d) := hpd.pDz
  have hDzg'm : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g') := hpg'.pDz
  -- ## the pointwise decomposition of `D_z g`
  have hgdec : ∀ z θ, g z θ = d z θ + g' z θ := fun z θ => by linarith [hdiff z θ]
  have hDz_add : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.Dz g z θ = Work.Spaces.Dz d z θ + Work.Spaces.Dz g' z θ :=
    Dz_add_of_smoothOpen (f := g) (f' := d) (k := g') hdS hgS' hgdec
  -- ## the two sizes `S` and `T`
  have hY5 : 0 ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have hY5' : 0 ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  have hZ5 : 0 ≤ Work.FTS.GalFields.Xn5 α d := Work.Spaces.HkNorm_nonneg α 5 d
  set S : ℝ := (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
      * Work.FTS.GalFields.Xn5 α d with hS_def
  set T : ℝ := (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') ^ 2
      * Work.FTS.GalFields.Xn5 α d with hT_def
  have hS0 : 0 ≤ S := by rw [hS_def]; exact mul_nonneg (by linarith) hZ5
  have hT0 : 0 ≤ T := by rw [hT_def]; exact mul_nonneg (sq_nonneg _) hZ5
  have hP1 : 1 ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by linarith
  have hY'P : Work.FTS.GalFields.Xn5 α g'
      ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by linarith
  have hST : S ≤ T := by
    rw [hS_def, hT_def]; exact mul_le_mul_of_nonneg_right (by nlinarith [hP1]) hZ5
  have hZT : Work.FTS.GalFields.Xn5 α d ≤ T := by rw [hT_def]; nlinarith [hP1, hZ5]
  have hSP : S * Work.FTS.GalFields.Xn5 α g' ≤ T := by
    rw [hS_def, hT_def]; nlinarith [hP1, hZ5, hY'P]
  have hgoal : C * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') ^ 2
      * Work.FTS.GalFields.Xn5 α d = C * T := by rw [hT_def]; ring
  -- ## the two telescoped Lipschitz bounds (the statement's hypotheses, in `|Kd|·S`-form)
  have hbd : |mb - mb'| ≤ |Kd| * S := by
    have he : Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
        * Work.FTS.GalFields.Xn5 α d = Kd * S := by rw [hS_def]; ring
    calc |mb - mb'|
        ≤ Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α d := hKdbar
      _ = Kd * S := he
      _ ≤ |Kd| * S := mul_le_mul_of_nonneg_right (le_abs_self Kd) hS0
  have hbdmu : |mu - mu'| ≤ |Kd| * S := by
    have he : Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
        * Work.FTS.GalFields.Xn5 α d = Kd * S := by rw [hS_def]; ring
    calc |mu - mu'|
        ≤ Kd * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
            * Work.FTS.GalFields.Xn5 α d := hKdmu
      _ = Kd * S := he
      _ ≤ |Kd| * S := mul_le_mul_of_nonneg_right (le_abs_self Kd) hS0
  -- ## the three summands of the telescoped block
  have hsm1 : SmoothOpen (fun z θ => -(mb - mb') * Work.Construction.AK α z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _ hAKsm
  have hsm2 : SmoothOpen (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _ (Work.FTS.NonlinRows.smoothOpen_sub hdS.Dz hdS)
  have hsm3 : SmoothOpen (fun z θ => (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _
      (Work.FTS.NonlinRows.smoothOpen_sub hgS'.Dz hgS')
  have hsm23 : SmoothOpen (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)
      + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_add hsm2 hsm3
  have hsmNice : SmoothOpen (fun z θ => -(mb - mb') * Work.Construction.AK α z θ
      + (mu * (Work.Spaces.Dz d z θ - d z θ)
          + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_add hsm1 hsm23
  have hnegsD : SmoothOpen (fun z θ => - d z θ) := hdS.neg
  have hnegsDm : Work.Spaces.HkMem α 4 (fun z θ => - d z θ) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hdM4
  have hnegsG' : SmoothOpen (fun z θ => - g' z θ) := hgS'.neg
  have hnegsG'm : Work.Spaces.HkMem α 4 (fun z θ => - g' z θ) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hgM4'
  have hsubDm : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hdS.Dz hnegsD hDzdm hnegsDm)
      (fun z hz θ hθ => by ring)
  have hsubG'm : Work.Spaces.HkMem α 4 (fun z θ => Work.Spaces.Dz g' z θ - g' z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hgS'.Dz hnegsG' hDzg'm hnegsG'm)
      (fun z hz θ hθ => by ring)
  have hm1 : Work.Spaces.HkMem α 4 (fun z θ => -(mb - mb') * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-(mb - mb')) hAKmem
  have hm2 : Work.Spaces.HkMem α 4 (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 mu hsubDm
  have hm3 : Work.Spaces.HkMem α 4 (fun z θ => (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (mu - mu') hsubG'm
  have hm23 : Work.Spaces.HkMem α 4 (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)
      + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)) :=
    Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm2 hsm3 hm2 hm3
  have hmNice : Work.Spaces.HkMem α 4 (fun z θ => -(mb - mb') * Work.Construction.AK α z θ
      + (mu * (Work.Spaces.Dz d z θ - d z θ)
          + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ))) :=
    Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hsm1 hsm23 hm1 hm23
  -- ## the three `Xn`-bounds
  have hX1 : Work.FTS.Nonlin.Xn α (fun z θ => -(mb - mb') * Work.Construction.AK α z θ)
      ≤ |Kd| * S * Kak := by
    rw [Xn_const_mul]
    have h1 : |-(mb - mb')| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α)
        = |mb - mb'| * Work.FTS.Nonlin.Xn α (Work.Construction.AK α) := by rw [abs_neg]
    rw [h1]
    exact mul_le_mul hbd hAKb (Work.Spaces.HkNorm_nonneg α 4 (Work.Construction.AK α))
      (mul_nonneg (abs_nonneg Kd) hS0)
  have hX2 : Work.FTS.Nonlin.Xn α (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ))
      ≤ 2 * Work.FTS.GalFields.Xn5 α d := by
    rw [Xn_const_mul]
    have hsub : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ)
        ≤ 2 * (Work.FTS.GalFields.Xn5 α d + Work.FTS.GalFields.Xn5 α d) := by
      refine le_trans (Xn_sub_le α hα hdS.Dz hdS hDzdm hdM4) ?_
      have h1 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz d) ≤ Work.FTS.GalFields.Xn5 α d :=
        Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hdS hdM5
      have h2 : Work.FTS.Nonlin.Xn α d ≤ Work.FTS.GalFields.Xn5 α d :=
        Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hdM5
      linarith
    have hmul : |mu| * Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz d z θ - d z θ)
        ≤ (1 / 2) * (2 * (Work.FTS.GalFields.Xn5 α d + Work.FTS.GalFields.Xn5 α d)) :=
      mul_le_mul hmu1 hsub
        (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz d z θ - d z θ))
        (by norm_num)
    linarith [hmul]
  have hX3 : Work.FTS.Nonlin.Xn α (fun z θ => (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ))
      ≤ |Kd| * S * (4 * Work.FTS.GalFields.Xn5 α g') := by
    rw [Xn_const_mul]
    have hsub : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz g' z θ - g' z θ)
        ≤ 4 * Work.FTS.GalFields.Xn5 α g' := by
      have h1 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Spaces.Dz g' z θ - g' z θ)
          ≤ 2 * (Work.FTS.GalFields.Xn5 α g' + Work.FTS.GalFields.Xn5 α g') := by
        refine le_trans (Xn_sub_le α hα hgS'.Dz hgS' hDzg'm hgM4') ?_
        have h2 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz g') ≤ Work.FTS.GalFields.Xn5 α g' :=
          Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hgS' hgM5'
        have h3 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g' :=
          Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) hgM5'
        linarith
      linarith
    exact mul_le_mul hbdmu hsub
      (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Spaces.Dz g' z θ - g' z θ))
      (mul_nonneg (abs_nonneg Kd) hS0)
  have hX23 := HkNorm_add_le_open α 4 hα hsm2 hsm3 hm2 hm3
  have hX23b : Work.FTS.Nonlin.Xn α (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)
        + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ))
      ≤ 2 * (2 * Work.FTS.GalFields.Xn5 α d
          + |Kd| * S * (4 * Work.FTS.GalFields.Xn5 α g')) := by
    refine le_trans hX23 ?_
    linarith [hX2, hX3]
  have hXnNice : Work.FTS.Nonlin.Xn α (fun z θ => -(mb - mb') * Work.Construction.AK α z θ
        + (mu * (Work.Spaces.Dz d z θ - d z θ)
            + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)))
      ≤ 2 * (Work.FTS.Nonlin.Xn α (fun z θ => -(mb - mb') * Work.Construction.AK α z θ)
          + Work.FTS.Nonlin.Xn α (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)
              + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ))) :=
    HkNorm_add_le_open α 4 hα hsm1 hsm23 hm1 hm23
  have hstep1 : 2 * (Work.FTS.Nonlin.Xn α (fun z θ => -(mb - mb') * Work.Construction.AK α z θ)
        + Work.FTS.Nonlin.Xn α (fun z θ => mu * (Work.Spaces.Dz d z θ - d z θ)
            + (mu - mu') * (Work.Spaces.Dz g' z θ - g' z θ)))
      ≤ 2 * (|Kd| * S * Kak
          + 2 * (2 * Work.FTS.GalFields.Xn5 α d
            + |Kd| * S * (4 * Work.FTS.GalFields.Xn5 α g'))) :=
    mul_le_mul_of_nonneg_left (by linarith [hX1, hX23b]) (by norm_num)
  have hstep2 : 2 * (|Kd| * S * Kak
          + 2 * (2 * Work.FTS.GalFields.Xn5 α d
            + |Kd| * S * (4 * Work.FTS.GalFields.Xn5 α g')))
      ≤ C * T := by
    have e0 : 2 * (|Kd| * S * Kak
          + 2 * (2 * Work.FTS.GalFields.Xn5 α d
            + |Kd| * S * (4 * Work.FTS.GalFields.Xn5 α g')))
        = 2 * (|Kd| * (S * Kak)) + 8 * Work.FTS.GalFields.Xn5 α d
          + 16 * (|Kd| * (S * Work.FTS.GalFields.Xn5 α g')) := by ring
    have e1 : 2 * (|Kd| * (S * Kak)) ≤ 2 * (|Kd| * (T * Kak)) := by
      have h := mul_le_mul_of_nonneg_right hST (le_of_lt hKakpos)
      have h2 := mul_le_mul_of_nonneg_left h (abs_nonneg Kd)
      linarith
    have e2 : 8 * Work.FTS.GalFields.Xn5 α d ≤ 8 * T := by linarith [hZT]
    have e3 : 16 * (|Kd| * (S * Work.FTS.GalFields.Xn5 α g'))
        ≤ 16 * (|Kd| * T) := by
      have h := mul_le_mul_of_nonneg_left hSP (abs_nonneg Kd)
      linarith
    have e4 : C * T = 2 * (|Kd| * (T * Kak)) + 8 * T + 16 * (|Kd| * T) + 12 * T := by
      rw [hC_def]; ring
    rw [e0, e4]
    linarith [e1, e2, e3, hT0]
  refine ⟨?_, ?_, ?_⟩
  · -- the `SmoothOpen` conjunct
    refine Work.FTS.PhiStar.CoreAux.SmoothOpen.congr hsmNice ?_
    intro z θ hz hθ0 hθ1
    rw [hcol mu hmu_ne g z θ, hcol mu' hmu'_ne g' z θ, hDz_add z θ hz hθ0 hθ1, hgdec z θ]
    ring
  · -- ## the `HkMem` conjunct
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hmNice ?_
    intro z hz θ hθ
    rw [hcol mu hmu_ne g z θ, hcol mu' hmu'_ne g' z θ, hDz_add z θ hz hθ.1 hθ.2, hgdec z θ]
    ring
  · -- ## the `Xn` conjunct
    rw [hgoal]
    refine le_trans ?_ (le_trans hXnNice (le_trans hstep1 hstep2))
    exact le_of_eq (Xn_congr_open α (fun z θ hz hθ0 hθ1 => by
      rw [hcol mu hmu_ne g z θ, hcol mu' hmu'_ne g' z θ, hDz_add z θ hz hθ0 hθ1, hgdec z θ]
      ring))

end Work.FTS.GalFields.RHS
