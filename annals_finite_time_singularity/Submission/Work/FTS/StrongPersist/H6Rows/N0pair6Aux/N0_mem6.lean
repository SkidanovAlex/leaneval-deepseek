import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMaj6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
import Submission.Work.FTS.StrongPersist.angmul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.Nonlinear.Open.Row23
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkMem_X_close6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N0_mem6` — the `ℋ⁶`-membership of the `N₀`-row of the level-six modulation table

`N₀ α (F_* + f) f` is the quadratic term of the modulation equation (Elgindi, tex (N0)); the
lemma proved here is that it is honest in `ℋ⁶` for every datum `f` of the coercivity class
`H6Adm α f` with order-seven honesty `HkMem α 7 f`, uniformly for `0 < α ≤ 1`.

## Route

`N0_eq_sum` splits `N₀ = N01 + ⋯ + N06`; the two pieces `N01, N02` collapse
(`N0_first_two_eq'`) to `close6 α = Kfac α · rhoR · psiA α`, and on the open quadrant the
remaining pieces combine into the three *lanes*

* `sep6 α = Kfac α · rhoR · psiA α` (the collapsed pair; `FstarI12H6`);
* `L₁₂(f)·(Aexp α + PsiF α f)`, where `Aexp α = (1+z)/(2α)·close6 α` is the explicit form of
  the `F_*`-derivative combination `(3/(2α))D_θF_* - c2m·D_zF_*` and
  `PsiF = (1/α)f + (3/(2α))D_θf - c2m·D_zf`; this lane is a *radial multiplier*
  (`L₁₂(f)` is radial, `C⁶` on `(0,∞)` with `D_z`-jets bounded by `C₆·|f|_{ℋ⁶}`, `L12Sup6`)
  applied to a smooth `ℋ⁶` field;
* `L₁₂(F_*)·(-(c2m)·D_zf)`, which is the `𝒲^{6,∞}`-product lane of `N0coefA6_WlInf6`.

The three lanes are added with the finite-order additivity `hkMem_add_of_contDiffOn`, and the
identification with `N₀` is the pointwise identity on the open quadrant.
-/

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Smoothness helpers -/

/-- A radial factor which is `C⁶` on `(0,∞)` times a function which is `C⁶` on the open
quadrant is `C⁶` on the open quadrant. -/
private lemma contDiffOn_six_radial_mul {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hψ : ContDiffOn ℝ 6 (Function.uncurry ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => X z * ψ z θ)) Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => X z * ψ z θ)
      = (fun p : ℝ × ℝ => X p.1) * Function.uncurry ψ := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact (hX.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul hψ

/-! ## The radial multiplier at level six -/

/-- **The radial multiplier**: a radial factor `X` which is `C⁶` on `(0,∞)` with all its
`D_z`-jets up to order six bounded by `B`, times a datum `ψ` which is smooth on the open
quadrant and honest in `ℋ⁶`, is again in `ℋ⁶`. -/
private theorem HkMem_radial_mul6 {α B : ℝ} {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hb : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j X z| ≤ B)
    (hψsm : Work.FTS.EllipticEst.SmoothOpen ψ) (hψmem : Work.Spaces.HkMem α 6 ψ) :
    Work.Spaces.HkMem α 6 (fun z θ => X z * ψ z θ) := by
  obtain ⟨K, hKpos, hmaj⟩ := radialMaj6 α B X ψ hB hX hψsm hb
  refine Work.FTS.LocData.HkMem_of_majorant α 6
    (M := fun z θ => K * Work.Spaces.HkIntegrand α 6 ψ z θ)
    (radialMul6Cont α X ψ hX hψsm) ?_ ?_ ?_
  · intro z hz
    exact (hψmem.1 z hz).const_mul K
  · refine (hψmem.2.const_mul K).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg hKpos.le (Work.Spaces.HkIntegrand_nonneg α 6 ψ 0 θ)
    · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      · exact hmaj z hz θ hθi
      · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 6
          (fun z θ => X z * ψ z θ) z θ
          (Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi)]
        exact mul_nonneg hKpos.le (Work.Spaces.HkIntegrand_nonneg α 6 ψ z θ)

/-! ## The three lanes -/

/-- `(1+z)/(2α)`: the reciprocal of the zero mode `L₁₂(F_*)(z) = 2α/(1+z)` (up to the factor
`1+z`). -/
def Frac (α : ℝ) : ℝ → ℝ := fun z => (1 + z) / (2 * α)

/-- The explicit form `(1+z)/(2α)·close6 α = 4α c2m(θ)Γ(θ)z²/(c(1+z)³)` of the `F_*`-derivative
combination `(3/(2α))D_θF_* - c2m(θ)·D_zF_*` of the fourth and fifth rows of the table. -/
def Aexp (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Frac α z * Work.FTS.StrongPersist.H6Rows.close6 α z θ

/-- `(1/α)f + (3/(2α))D_θf - c2m(θ)·D_zf`: the `f`-dependent combination multiplying
`L₁₂(f)`. -/
def PsiF (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz f z θ

/-- `-(c2m(θ))·D_zf`: the field of the sixth row (`N06`), paired with `L₁₂(F_*)`. -/
def PsiB (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-(Work.Construction.c2m θ)) * Work.Spaces.Dz f z θ

private theorem PsiB_eq (f : ℝ → ℝ → ℝ) :
    PsiB f = fun z θ => -(Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
  funext z θ; simp only [PsiB]; ring

/-! ## The explicit form of the `I₄ᵃ + I₅ᵃ` combination on the open quadrant -/

private theorem Aexp_eq_combination {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = Aexp α z θ := by
  have hz0 : (0 : ℝ) < 1 + z := by linarith
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  have hkey := Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1
    (le_of_lt hz) ⟨hθ.1.le, hθ.2.le⟩
  rw [hL12F] at hkey
  rw [Aexp, Frac]
  have h2 : (2 * α / (1 + z))
        * ((3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      = 8 * α ^ 2 * Work.Construction.c2m θ * z ^ 2 * Work.Spaces.Gam α θ
        / (Work.Spaces.c α * (1 + z) ^ 4) := by
    rw [show (2 * α / (1 + z))
          * ((3 / (2 * α)) * Work.Construction.s2 θ
              * Work.Spaces.pth (Work.Construction.Fstar α) z θ
            - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
        = (3 / (2 * α)) * Work.Construction.s2 θ * (2 * α / (1 + z))
              * Work.Spaces.pth (Work.Construction.Fstar α) z θ
          - Work.Construction.c2m θ * (2 * α / (1 + z))
              * Work.Spaces.Dz (Work.Construction.Fstar α) z θ from by ring]
    exact hkey
  have h3 : (1 + z) / (2 * α)
        * ((2 * α / (1 + z))
          * ((3 / (2 * α)) * Work.Construction.s2 θ
              * Work.Spaces.pth (Work.Construction.Fstar α) z θ
            - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
      = (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
    field_simp
  rw [← h3, h2, Work.FTS.StrongPersist.H6Rows.close6]

/-! ## The two `f`-fields -/

private theorem smoothOpen_PsiB {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (PsiB f) := by
  rw [PsiB_eq]
  exact Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_neg'
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
      hf.Dz)

private theorem HkMem_PsiB {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm7 : Work.Spaces.HkMem α 7 f) : Work.Spaces.HkMem α 6 (PsiB f) := by
  obtain ⟨Cc2, hCc2pos, hc2sm, hc2b, hc2jet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨CA6, hCA6, hangfun⟩ := Work.FTS.StrongPersist.angmul6
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) hfsm hm7
  have hang : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ) :=
    (hangfun α hα hα1 (fun θ => Work.Construction.c2m θ) (Work.Spaces.Dz f) Cc2 hc2sm
      (fun θ hθ => hc2b θ hθ)
      (fun i hi hi6 θ hθ => hc2jet i hi (le_trans hi6 (by norm_num)) 0 θ hθ)
      hfsm.Dz hDzmem).1
  rw [PsiB_eq]
  have heq : (fun z θ => -(Work.Construction.c2m θ * Work.Spaces.Dz f z θ))
      = fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
    funext z θ; ring
  rw [heq]
  exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hang

private theorem smoothOpen_PsiF {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (PsiF α f) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (1 / α) * f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hfsm
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hfsm.Dth
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
      hfsm.Dz
  have h12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_add h1 h2
  have h123 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ)
        - Work.Construction.c2m θ * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_sub h12 h3
  have heq : (fun z θ => ((1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ)
      - Work.Construction.c2m θ * Work.Spaces.Dz f z θ) = PsiF α f := by
    funext z θ; simp only [PsiF]
  rw [← heq]
  exact h123

private theorem HkMem_PsiF {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (PsiF α f) := by
  have h1 : Work.Spaces.HkMem α 6 (fun z θ => (1 / α) * f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (1 / α) hm6
  have hDth : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 6) (f := f) (by linarith) hfsm hm7
  have h2 : Work.Spaces.HkMem α 6
      (fun z θ => (3 / (2 * α)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α)) hDth
  have h3 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
    obtain ⟨Cc2, hCc2pos, hc2sm, hc2b, hc2jet⟩ :=
      Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
    obtain ⟨CA6, hCA6, hangfun⟩ := Work.FTS.StrongPersist.angmul6
    have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
      Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) hfsm hm7
    exact (hangfun α hα hα1 (fun θ => Work.Construction.c2m θ) (Work.Spaces.Dz f) Cc2 hc2sm
      (fun θ hθ => hc2b θ hθ)
      (fun i hi hi6 θ hθ => hc2jet i hi (le_trans hi6 (by norm_num)) 0 θ hθ)
      hfsm.Dz hDzmem).1
  have h12 : Work.Spaces.HkMem α 6 (fun z θ =>
      (1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ) :=
    Work.FTS.EllipticEst.HkMem_add_smoothOpen α 6 hα
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hfsm)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hfsm.Dth) h1 h2
  have hsum : Work.Spaces.HkMem α 6 (fun z θ =>
      ((1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ)
        + ((-1 : ℝ) * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ))) :=
    Work.FTS.EllipticEst.HkMem_add_smoothOpen α 6 hα
      (Work.FTS.StrongPersist.H6Pair6Aux.so_add
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hfsm)
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hfsm.Dth))
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1)
        (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
          (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
            Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m) hfsm.Dz))
      h12
      (Work.FTS.LocData.HkMem_const_mul α 6 (-1) h3)
  have heq : (fun z θ => ((1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ)
      + ((-1 : ℝ) * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ))) = PsiF α f := by
    funext z θ; simp only [PsiF]; ring
  rw [← heq]
  exact hsum

/-! ## Smoothness of the `F_*`-coefficients -/

private theorem smoothOpen_frac' (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z) * (2 * α)⁻¹) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_add (Work.FTS.StrongPersist.H6Pair6Aux.so_const 1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => contDiffOn_id)))
    (Work.FTS.StrongPersist.H6Pair6Aux.so_const ((2 * α)⁻¹))

private theorem smoothOpen_psiA (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.psiA α θ) := by
  unfold Work.Construction.psiA
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
    (Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α)

private theorem smoothOpen_Kfac_rhoR (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.Kfac α * Work.Construction.rhoR z) := by
  refine Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => ?_)
  have h1 : ContDiffOn ℝ n (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have h2 : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 4
  have h3 : ContDiffOn ℝ n (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) (Set.Ioi 0) :=
    h1.div h2 (fun z hz => pow_ne_zero 4 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz])))
  have h4 : ContDiffOn ℝ n (fun z : ℝ => Work.Construction.rhoR z) (Set.Ioi 0) := by
    simpa only [Work.Construction.rhoR] using h3
  exact contDiffOn_const.mul h4

private theorem smoothOpen_sep6 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongPersist.H6Rows.sep6 α) := by
  unfold Work.FTS.StrongPersist.H6Rows.sep6 Work.Construction.sepF
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul (smoothOpen_Kfac_rhoR α) (smoothOpen_psiA α)

private theorem smoothOpen_Aexp (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (Aexp α) := by
  have heq : Aexp α = fun z θ => (1 + z) * (2 * α)⁻¹
      * ((Work.Construction.Kfac α * Work.Construction.rhoR z) * Work.Construction.psiA α θ) := by
    funext z θ
    simp only [Aexp, Frac]
    rw [show Work.FTS.StrongPersist.H6Rows.close6 α z θ
        = Work.FTS.StrongPersist.H6Rows.sep6 α z θ from
      (Work.FTS.StrongPersist.H6Rows.sep6_eq_close6 α z θ).symm]
    simp only [Work.FTS.StrongPersist.H6Rows.sep6, Work.Construction.sepF]
    ring
  rw [heq]
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul (smoothOpen_frac' α)
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul (smoothOpen_Kfac_rhoR α) (smoothOpen_psiA α))

/-! ## The `Aexp`-membership -/

/-- **`Aexp α = (1+z)/(2α)·close6 α` is honest in `ℋ⁶`.**  This is the explicit form of the
`F_*`-derivative combination `(3/(2α))D_θF_* - c2m·D_zF_*`; its radial profile is
`∝ z²/(1+z)³` (one power of `(1+z)` less than `rhoR`), whose weighted `D_z`-jets decay like
`1/(1+z)`. -/
theorem Aexp_mem6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 6 (Aexp α) := by
  show Work.Spaces.HkMem α 6 (fun z θ =>
    (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ)
  exact Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkMem_X_close6 hα hα1

/-! ## The assembly -/

theorem N0_mem6 : ∃ α₂ : ℝ, 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.HkMem α 6
        (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) := by
  refine ⟨1, by norm_num, le_refl 1, ?_⟩
  intro α hαIoc f hAdm hm7
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hfsm, hm6⟩ := hAdm.reg
  have h0 : Work.Construction.L12 f 0 = 0 := hAdm.l12
  -- ## the radial multiplier `L₁₂(f)`: `C⁶` on `(0,∞)` with bounded `D_z`-jets
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  have hL12cd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 6 f hα hα1 hfsm hm6 (by norm_num)
    refine h.congr (fun z _ => ?_)
    exact (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm
  have hL12b : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    fun j hj z hz => hC₆ α f hα hα1 hfsm hm6 hm7 h0 j hj z hz
  have hB0 : 0 ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hC₆pos.le (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ## lane 1: the collapsed pair `sep6 α`
  have hL1 : Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Rows.sep6 α) := by
    obtain ⟨K12, hK12, hFstar⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := Work.FTS.StrongPersist.H6Rows.N012 α)
      (fun z θ hzθ => (Work.FTS.StrongPersist.H6Rows.sep6_eq_N012 hα hα1
        (le_of_lt hzθ.1) ⟨hzθ.2.1.le, hzθ.2.2.le⟩).symm) ?_
    exact (hFstar α hα hα1).1
  have hL1sm : ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α))
      Work.Construction.Qd :=
    Work.FTS.StrongPersist.H6Rows.contDiffOn_uncurry_sep6 α
  -- ## lane 2: `L₁₂(f)·(Aexp α + PsiF α f)`
  have hAexp : Work.Spaces.HkMem α 6 (Aexp α) := Aexp_mem6 hα hα1
  have hAexpsm : Work.FTS.EllipticEst.SmoothOpen (Aexp α) := smoothOpen_Aexp α
  have hPsism : Work.FTS.EllipticEst.SmoothOpen (PsiF α f) := smoothOpen_PsiF hfsm
  have hPsimem : Work.Spaces.HkMem α 6 (PsiF α f) := HkMem_PsiF hα hα1 hfsm hm6 hm7
  have hfield : Work.Spaces.HkMem α 6 (fun z θ => Aexp α z θ + PsiF α f z θ) :=
    Work.FTS.EllipticEst.HkMem_add_smoothOpen α 6 hα hAexpsm hPsism hAexp hPsimem
  have hfieldsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Aexp α z θ + PsiF α f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_add hAexpsm hPsism
  have hL2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)) :=
    HkMem_radial_mul6 hB0 hL12cd hL12b hfieldsm hfield
  have hL2cd : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)))
      Work.Construction.Qd :=
    contDiffOn_six_radial_mul hL12cd (hfieldsm.forall 6)
  -- ## lane 3: `L₁₂(F_*)·PsiB f`, which is the `𝒲^{6,∞}`-product of the sixth row
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) hfsm hm7
  have hL3 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ) := by
    obtain ⟨CA, hCApos, hN0coef⟩ := N0coefA6_WlInf6
    obtain ⟨hN0coefsm, hN0coefw, -⟩ := hN0coef α hα hα1
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => Fn0 α z θ * Work.Spaces.Dz f z θ) (fun z θ hzθ => ?_)
      (Work.FTS.StrongPersist.H6Pair6Aux.HkMem_mul_of_WlInf6 hα hα1 hN0coefsm hN0coefw
        hfsm.Dz hDzmem)
    show Fn0 α z θ * Work.Spaces.Dz f z θ
      = Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hzθ.1)]
    simp only [Fn0, PsiB]
    ring
  have hL3sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α) (smoothOpen_PsiB hfsm)
  have hL3cd : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ =>
        Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ))
      Work.Construction.Qd :=
    hL3sm.forall 6
  -- ## adding the three lanes
  have hL12 : Work.Spaces.HkMem α 6
      (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hL1sm hL2cd hL1 hL2
  have hL12cd : ContDiffOn ℝ 6
      (Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)))
      Work.Construction.Qd := by
    have h : Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ))
        = Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α)
          + Function.uncurry (fun z θ =>
              Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)) := by
      funext p; obtain ⟨z, θ⟩ := p; rfl
    rw [h]
    exact hL1sm.add hL2cd
  have hL123 : Work.Spaces.HkMem α 6
      ((Work.FTS.StrongPersist.H6Rows.sep6 α
          + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ))
        + fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hL12cd hL3cd hL12 hL3
  -- ## the identification with `N₀` on the open quadrant
  refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (f := (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ))
      + fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ)
    (fun z θ hzθ => ?_) hL123
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hzθ.2
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  have hpth : Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α)
      hfsm hz hθ
  have hDz : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add
        (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hfsm hz hθ)
  have hA := Aexp_eq_combination (α := α) (z := z) (θ := θ) hα hα1 hz hθ
  have hsep12 : Work.FTS.StrongPersist.H6Rows.sep6 α z θ
      = Work.Construction.N01 α (Work.Construction.Ftot α f) f z θ
        + Work.Construction.N02 α (Work.Construction.Ftot α f) f z θ := by
    rw [show Work.FTS.StrongPersist.H6Rows.sep6 α z θ
        = Work.FTS.StrongPersist.H6Rows.close6 α z θ from
      Work.FTS.StrongPersist.H6Rows.sep6_eq_close6 α z θ]
    simp only [Work.FTS.StrongPersist.H6Rows.close6, Work.Construction.N01, Work.Construction.N02]
    rw [← Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1
      (le_of_lt hz) ⟨hθ.1.le, hθ.2.le⟩]
    ring
  show (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (Aexp α z θ + PsiF α f z θ)) z θ
      + (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * PsiB f z θ) z θ
    = Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
  simp only [Pi.add_apply]
  rw [hsep12, Work.Construction.N0_eq_sum]
  simp only [Pi.add_apply, Work.Construction.N01, Work.Construction.N02, Work.Construction.N03,
    Work.Construction.N04, Work.Construction.N05, Work.Construction.N06]
  rw [hpth, hDz]
  rw [← hA]
  simp only [Aexp, Frac, PsiF, PsiB, Work.Spaces.Dth, Work.Spaces.Dz, Work.Spaces.pth,
    Work.Spaces.pz, Work.Construction.Ftot, Work.Construction.c2m, Work.Construction.s2]
  rw [hL12F]
  ring

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
