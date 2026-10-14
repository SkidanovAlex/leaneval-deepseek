import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowMulCoef
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.sep_mem6_open
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowStarDthAux.ZeroSlice
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0mem6Own =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The lane machinery for the `N₀`-row

Land the three lanes of the sibling file `H6Rows/N0pair6Aux/N0_mem6.lean` in a form that needs
no `SmoothOpen (fun z _ => L₁₂ f z)` (that hypothesis is not available for the bare-`f`
statement): the collapsed pair `sep6 α`, the radial-multiplier lane
`L₁₂(f)·(Aexp α + PsiF α f)` (via `HkMem_radial_mul6`), and the `𝒲^{6,∞}`-priced lane
`L₁₂(F_*)·PsiB f`.  The only genuinely analytic input is the `ℋ⁶`-membership of the explicit
`close6`-row scaled by `(1+z)/(2α)` (`ScaleClose6.HkMem_X_close6`).

The names below carry the `n0own`-prefix so that they do not collide with the sibling's
(private) helpers. -/

/-- A radial factor which is `C⁶` on `(0,∞)` times a function which is `C⁶` on the open
quadrant is `C⁶` on the open quadrant. -/
private lemma n0own_contDiffOn_six_radial_mul {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hψ : ContDiffOn ℝ 6 (Function.uncurry ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => X z * ψ z θ)) Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => X z * ψ z θ)
      = (fun p : ℝ × ℝ => X p.1) * Function.uncurry ψ := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]
  exact (hX.comp contDiffOn_fst (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul hψ

/-- `(1+z)/(2α)`: the reciprocal of the zero mode `L₁₂(F_*)(z) = 2α/(1+z)` (up to the factor
`1+z`). -/
def n0ownFrac (α : ℝ) : ℝ → ℝ := fun z => (1 + z) / (2 * α)

/-- The explicit form `(1+z)/(2α)·close6 α = 4α c2m(θ)Γ(θ)z²/(c(1+z)³)` of the `F_*`-derivative
combination `(3/(2α))D_θF_* - c2m(θ)·D_zF_*` of the fourth and fifth rows of the table. -/
def n0ownAexp (α : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => n0ownFrac α z * Work.FTS.StrongPersist.H6Rows.close6 α z θ

/-- `(1/α)f + (3/(2α))D_θf - c2m(θ)·D_zf`: the `f`-dependent combination multiplying
`L₁₂(f)`. -/
def n0ownPsiF (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  (1 / α) * f z θ + (3 / (2 * α)) * Work.Spaces.Dth f z θ
    - Work.Construction.c2m θ * Work.Spaces.Dz f z θ

/-- `-(c2m(θ))·D_zf`: the field of the sixth row (`N06`), paired with `L₁₂(F_*)`. -/
def n0ownPsiB (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (-(Work.Construction.c2m θ)) * Work.Spaces.Dz f z θ

private theorem n0ownPsiB_eq (f : ℝ → ℝ → ℝ) :
    n0ownPsiB f = fun z θ => -(Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
  funext z θ; simp only [n0ownPsiB]; ring

/-! ## The explicit form of the `I₄ᵃ + I₅ᵃ` combination on the open quadrant -/

private theorem n0ownAexp_eq_combination {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (3 / (2 * α)) * Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = n0ownAexp α z θ := by
  have hz0 : (0 : ℝ) < 1 + z := by linarith
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  have hkey := Work.Construction.N0_first_two_eq' (α := α) (z := z) (θ := θ) hα hα1
    (le_of_lt hz) ⟨hθ.1.le, hθ.2.le⟩
  rw [hL12F] at hkey
  rw [n0ownAexp, n0ownFrac]
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

private theorem n0own_smoothOpen_PsiB {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (n0ownPsiB f) := by
  rw [n0ownPsiB_eq]
  exact Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_neg'
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
      hf.Dz)


private theorem n0own_smoothOpen_PsiF {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hfsm : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (n0ownPsiF α f) := by
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
      - Work.Construction.c2m θ * Work.Spaces.Dz f z θ) = n0ownPsiF α f := by
    funext z θ; simp only [n0ownPsiF]
  rw [← heq]
  exact h123

private theorem n0own_HkMem_PsiF {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f) (hm7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (n0ownPsiF α f) := by
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
      + ((-1 : ℝ) * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ))) = n0ownPsiF α f := by
    funext z θ; simp only [n0ownPsiF]; ring
  rw [← heq]
  exact hsum

/-! ## Smoothness of the `F_*`-coefficients -/

private theorem n0own_smoothOpen_frac' (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z) * (2 * α)⁻¹) :=
  Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_add (Work.FTS.StrongPersist.H6Pair6Aux.so_const 1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => contDiffOn_id)))
    (Work.FTS.StrongPersist.H6Pair6Aux.so_const ((2 * α)⁻¹))

private theorem n0own_smoothOpen_psiA (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.psiA α θ) := by
  unfold Work.Construction.psiA
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul
    (Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)
    (Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α)

private theorem n0own_smoothOpen_Kfac_rhoR (α : ℝ) :
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


private theorem n0own_smoothOpen_Aexp (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (n0ownAexp α) := by
  have heq : n0ownAexp α = fun z θ => (1 + z) * (2 * α)⁻¹
      * ((Work.Construction.Kfac α * Work.Construction.rhoR z)
        * Work.Construction.psiA α θ) := by
    funext z θ
    simp only [n0ownAexp, n0ownFrac]
    rw [show Work.FTS.StrongPersist.H6Rows.close6 α z θ
        = Work.FTS.StrongPersist.H6Rows.sep6 α z θ from
      (Work.FTS.StrongPersist.H6Rows.sep6_eq_close6 α z θ).symm]
    simp only [Work.FTS.StrongPersist.H6Rows.sep6, Work.Construction.sepF]
    ring
  rw [heq]
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul (n0own_smoothOpen_frac' α)
    (Work.FTS.StrongPersist.H6Pair6Aux.so_mul (n0own_smoothOpen_Kfac_rhoR α)
      (n0own_smoothOpen_psiA α))

/-! ## The `Aexp`-membership, from the explicit `close6` row -/

private theorem n0own_Aexp_mem6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.HkMem α 6 (n0ownAexp α) := by
  show Work.Spaces.HkMem α 6 (fun z θ =>
    (1 + z) / (2 * α) * Work.FTS.StrongPersist.H6Rows.close6 α z θ)
  exact Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkMem_X_close6 hα hα1

-- The first half of the `N₀`-row: `N₀ α (F_* + f) f` is in `ℋ⁶`.
--
-- ROUTE.  `H6Adm α f` gives `reg : HQo α 6 f = (SmoothOpen f ∧ HkMem α 6 f)`, `vanish`,
-- `axis` and `l12 : L₁₂ f 0 = 0`.  `N0 α F f` (with `F = F_* + f`) is the explicit combination
-- `(3/(2α)) s2·L₁₂(F_*)·pth F_* - c₂ₘ·L₁₂(F_*)·Dz F_* + (1/α)(L₁₂ f·f)
--  + (3/(2α)) s2·L₁₂ f·pth F - c₂ₘ·L₁₂ f·Dz F - c₂ₘ·L₁₂(F_*)·Dz f`.
-- There are two routes:
-- (a) the sibling's `H6Pair6Aux.H6N0Aux.N0row_hsummem` +
--     `H6Pair6Aux.H6N0Aux.hkmem_N0pieces_own` + `HkMem_congr_Q0` (what
--     `H6N0Aux/N0row_main.lean` does), which needs `SmoothOpen (fun z _ => L₁₂ f z)` — not
--     available here (a `ctx` hypothesis in the sibling);
-- (b) directly from majorants, which avoids `SmoothOpen (L₁₂ f)`.
-- The proof below is route (b) in its lane form: on the open quadrant `N₀` is the sum of the
-- collapsed pair `sep6 α = close6 α` (`FstarI12H6`), the radial-multiplier lane
-- `L₁₂(f)·(Aexp α + PsiF α f)` (from `L12Sup6` + `HkMem_radial_mul6` + the `ℋ⁶`-membership of
-- the explicit `close6`-row, `ScaleClose6.HkMem_X_close6`), and the `𝒲^{6,∞}`-priced lane
-- `L₁₂(F_*)·PsiB f` (`N0coefA6_WlInf6` + `HkMem_mul_of_WlInf6`); the three are summed with
-- `hkMem_add_of_contDiffOn` and transported to `N₀` by `HkMem_congr_Qd`.
theorem N0mem6Own : ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f → 0 < α → α ≤ 1 →
    Work.Spaces.HkMem α 6
      (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) := by
  intro α f hAdm hm7 hα hα1
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
  have hAexp : Work.Spaces.HkMem α 6 (n0ownAexp α) := n0own_Aexp_mem6 hα hα1
  have hAexpsm : Work.FTS.EllipticEst.SmoothOpen (n0ownAexp α) := n0own_smoothOpen_Aexp α
  have hPsism : Work.FTS.EllipticEst.SmoothOpen (n0ownPsiF α f) := n0own_smoothOpen_PsiF hfsm
  have hPsimem : Work.Spaces.HkMem α 6 (n0ownPsiF α f) :=
    n0own_HkMem_PsiF hα hα1 hfsm hm6 hm7
  have hfield : Work.Spaces.HkMem α 6 (fun z θ => n0ownAexp α z θ + n0ownPsiF α f z θ) :=
    Work.FTS.EllipticEst.HkMem_add_smoothOpen α 6 hα hAexpsm hPsism hAexp hPsimem
  have hfieldsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => n0ownAexp α z θ + n0ownPsiF α f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_add hAexpsm hPsism
  have hL2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C₆ * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z)
      (fun z θ => n0ownAexp α z θ + n0ownPsiF α f z θ) hα hB0 hL12cd hL12b hfieldsm hfield
  have hL2cd : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ =>
        Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)))
      Work.Construction.Qd :=
    n0own_contDiffOn_six_radial_mul hL12cd (hfieldsm.forall 6)
  -- ## lane 3: `L₁₂(F_*)·PsiB f`, which is the `𝒲^{6,∞}`-product of the sixth row
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) hfsm hm7
  have hL3 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ) := by
    obtain ⟨CA, hCApos, hN0coef⟩ := N0coefA6_WlInf6
    obtain ⟨hN0coefsm, hN0coefw, -⟩ := hN0coef α hα hα1
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => Fn0 α z θ * Work.Spaces.Dz f z θ) (fun z θ hzθ => ?_)
      (Work.FTS.StrongPersist.H6Pair6Aux.HkMem_mul_of_WlInf6 hα hα1 hN0coefsm hN0coefw
        hfsm.Dz hDzmem)
    show Fn0 α z θ * Work.Spaces.Dz f z θ
      = Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hzθ.1)]
    simp only [Fn0, n0ownPsiB]
    ring
  have hL3sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α) (n0own_smoothOpen_PsiB hfsm)
  have hL3cd : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ =>
        Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ))
      Work.Construction.Qd :=
    hL3sm.forall 6
  -- ## adding the three lanes
  have hL12 : Work.Spaces.HkMem α 6
      (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hL1sm hL2cd hL1 hL2
  have hL12cd : ContDiffOn ℝ 6
      (Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)))
      Work.Construction.Qd := by
    have h : Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ))
        = Function.uncurry (Work.FTS.StrongPersist.H6Rows.sep6 α)
          + Function.uncurry (fun z θ =>
              Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)) := by
      funext p; obtain ⟨z, θ⟩ := p; rfl
    rw [h]
    exact hL1sm.add hL2cd
  have hL123 : Work.Spaces.HkMem α 6
      ((Work.FTS.StrongPersist.H6Rows.sep6 α
          + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ))
        + fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ) :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.hkMem_add_of_contDiffOn α 6 hL12cd hL3cd hL12 hL3
  -- ## the identification with `N₀` on the open quadrant
  refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
    (f := (Work.FTS.StrongPersist.H6Rows.sep6 α
        + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ))
      + fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ)
    (fun z θ hzθ => ?_) hL123
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hzθ.2
  have hL12F : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)
  have hpth : Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.NonlinRows.Rl1.openSlice_pth_add
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hfsm hz hθ
  have hDz : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ :=
    Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
      (Work.FTS.NonlinRows.Rl1.openSlice_pz_add
        (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hfsm hz hθ)
  have hA := n0ownAexp_eq_combination (α := α) (z := z) (θ := θ) hα hα1 hz hθ
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
        + fun z θ => Work.Construction.L12 f z * (n0ownAexp α z θ + n0ownPsiF α f z θ)) z θ
      + (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * n0ownPsiB f z θ) z θ
    = Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ
  simp only [Pi.add_apply]
  rw [hsep12, Work.Construction.N0_eq_sum]
  simp only [Pi.add_apply, Work.Construction.N01, Work.Construction.N02, Work.Construction.N03,
    Work.Construction.N04, Work.Construction.N05, Work.Construction.N06]
  rw [hpth, hDz]
  rw [← hA]
  simp only [n0ownAexp, n0ownFrac, n0ownPsiF, n0ownPsiB, Work.Spaces.Dth, Work.Spaces.Dz,
    Work.Spaces.pth, Work.Spaces.pz, Work.Construction.Ftot, Work.Construction.c2m,
    Work.Construction.s2]
  rw [hL12F]
  ring

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0piecesMem6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas -/

/-- `z ↦ L₁₂(f)(z)` is `C⁶` on `(0,∞)` whenever `f` is smooth on the open quadrant and honest
at order seven.  This is the finite-order replacement of the `ctx`-hypothesis
`SmoothOpen (fun z _ => L₁₂ f z)` of the sibling. -/
private theorem contDiffOn_six_L12 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
  have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα hα1 hfsm hm7 (by norm_num)
  refine (h.of_le (by norm_num)).congr (fun z _ => ?_)
  exact (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm

/-- The joint `C⁶`-smoothness on the open quadrant of a separable product `a(θ)·ρ(z)`, from
`C⁶`-smoothness of the two one-variable factors. -/
private theorem contDiffOn_uncurry_sep {a : ℝ → ℝ} {ρ : ℝ → ℝ}
    (ha : ContDiffOn ℝ 6 a (Set.Ioo 0 (Real.pi / 2)))
    (hρ : ContDiffOn ℝ 6 ρ (Set.Ioi 0)) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a θ * ρ z)) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
    ha.comp contDiffOn_snd (fun p hp => hp.2)
  have h2 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => ρ p.1) Work.FTS.EllipticEst.Q0 :=
    hρ.comp contDiffOn_fst (fun p hp => hp.1)
  have hfun : Function.uncurry (fun z θ => a θ * ρ z)
      = (fun p : ℝ × ℝ => a p.2) * (fun p : ℝ × ℝ => ρ p.1) := rfl
  rw [hfun]
  exact h1.mul h2

/-- **Continuity of the `ℋ⁶`-integrand of a separable product**, from `C⁶`-smoothness of the
two factors: the continuity hypothesis of `sep_mem6_open`. -/
private theorem continuousOn_HkIntegrand_sep6_priv {α : ℝ} {a : ℝ → ℝ} {ρ : ℝ → ℝ}
    (ha : ContDiffOn ℝ 6 a (Set.Ioo 0 (Real.pi / 2)))
    (hρ : ContDiffOn ℝ 6 ρ (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 6 (fun z θ => a θ * ρ z) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hQd : Work.FTS.CoercivityFix.Transfer.E2pkg.Qd = Work.FTS.EllipticEst.Q0 := rfl
  have hun : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => a θ * ρ z))
      Work.FTS.CoercivityFix.Transfer.E2pkg.Qd := by
    rw [hQd]
    exact contDiffOn_uncurry_sep ha hρ
  have hbc := Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn
    (G := fun z θ => a θ * ρ z) hun
  have hcont := Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
    hbc α
  rw [hQd] at hcont
  exact hcont

-- The `ℋ⁶`-memberships of the six `f`-dependent pieces of the `N₀`-row, at the bare-`f`
-- interface (`H6Adm α f` + `HkMem α 7 f`), i.e. WITHOUT the hypothesis
-- `SmoothOpen (fun z _ => L₁₂ f z)` that the sibling `H6Pair6Aux.H6N0Aux.hkmem_N0pieces_own`
-- carries.  They are needed to split the slot pairing of `N₀` into its pieces.
--
-- ROUTE.  `H6Adm α f` gives `SmoothOpen f`, `HkMem α 6 f`, `L₁₂ f 0 = 0`.  The sibling
-- `H6Rows/N0pair6Aux/N0_mem6.lean` contains a full lane proof of the membership of the *sum*
-- of the pieces under exactly these hypotheses, and the same lanes give the pieces:
--   * `NP3 = (1/α)·(L₁₂ f · f)`, `NP4b = (3/(2α))·(L₁₂ f · D_θ f)`,
--     `NP5b = (-1)·(c₂ₘ · L₁₂ f · D_z f)`: the radial-multiplier route
--     `H6Rows.N0pair6Aux.HkMem_radial_mul6` with `X := L₁₂ f`, which needs only
--     `ContDiffOn ℝ 6 (L₁₂ f) (Ioi 0)` (`UopHk.contDiffOn_L12_k α 7 f` plus
--     `H2.constructionL12_eq_ellipticL12`) and the jet bound `|DzdIter j (L₁₂ f)| ≤ C₆·HkNorm α 6 f`,
--     `j ≤ 6` (`H6Pair6Aux.L12Sup6`); scalar factors via `LocData.HkMem_const_mul`, and for
--     `NP5b` group the θ-only factor `c₂ₘ` with the radial coefficient (see `N0coefA6_WlInf6`).
--   * `NP4a = (3/(2α))·(L₁₂ f · D_θ F_*)`, `NP5a = (-1)·(L₁₂ f · (c₂ₘ·D_z F_*))`: same route
--     with `ψ := D_θ F_*` resp. `ψ := c₂ₘ·D_z F_*`.  CAVEAT: `DthFstar_W6`/`c2mDzFstar_W6`
--     give only `WlInfMem α 6`, so get `HkMem α 6 ψ` from
--     `H6Pair6Aux.N0SlotSplitAux.HkMem_mul_of_WlInf6` using the `F_*`-factor as the `𝒲^{6,∞}`
--     factor and the other factor (`F_*` resp. `c₂ₘ·F_*`) as `HQo`, OR via a decay majorant.
--   * `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`: `HkMem_mul_of_WlInf6` with coefficient
--     `c₂ₘ·L₁₂(F_*)` (`c2m_L12Fstar_W6`: `WlInfMem α 6` and `WlInf α 6 ≤ Cα`) against
--     `D_z f` (`HkMem α 6 (D_z f)` from `HkMem α 7 f`, `IPGen.HkMem_Dz_le`).
--
-- IMPLEMENTATION NOTE (added by the prover).  `NP3`, `NP4b` and `NP5b` are the radial-multiplier
-- pieces (`HkMem_radial_mul6` with `X = L₁₂ f`, whose only smoothness input is
-- `ContDiffOn ℝ 6 (L₁₂ f) (Ioi 0)` from `UopHk.contDiffOn_L12_k`), `NP6` is the `𝒲^{6,∞}`-product
-- with `N0coefA6_WlInf6`.  `NP4a` and `NP5a` are *not* obtainable with the radial multiplier
-- alone (neither `D_θF_*` nor `c₂ₘ·D_zF_*` lies in `ℋ⁶`: both are `~ z` near `z = 0` while the
-- weight `w ~ z^{-2}`); they are handled by the *separated-product* route of
-- `N0SepParts.N04a_mem`/`N05a_mem`, with the two `SmoothOpen (L₁₂ f)`-inputs replaced by the
-- finite-order data: `∂_θF_* = α(Γ'/c)φ`, `D_zF_* = α(Γ/c)D_zφ` with `φ = FM.Fstar`, so
-- `(3/(2α))·L₁₂(f)·D_θF_*` and `-L₁₂(f)·(c₂ₘ·D_zF_*)` are the separable products `a(θ)·ρ(z)`
-- with `ρ = L₁₂(f)·φ` resp. `ρ = L₁₂(f)·D_zφ` and `a = (3α/(2c))·q·Γ` resp. `a = -(α/c)·c₂ₘ·Γ`;
-- the membership of a separable product with only `C⁶`-inputs is the engine `sep_mem6_open`
-- (with its continuity hypothesis supplied by `continuousOn_HkIntegrand_sep6_priv`).
theorem N0piecesMem6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.StrongPersist.H6Adm α f) (hm7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP3 α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4b α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α f) ∧
    Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α f) := by
  obtain ⟨hfsm, hm6⟩ := hf.reg
  have h0 : Work.Construction.L12 f 0 = 0 := hf.l12
  have hcg : 0 < Work.Spaces.c α := by linarith [(Work.Spaces.c_bounds α hα hα1).1]
  -- ## the radial factor `L₁₂ f`
  obtain ⟨C₆, hC₆pos, hC₆⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  have hΛcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
    contDiffOn_six_L12 hα hα1 hfsm hm7
  have hΛjet : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    fun j hj z hz => hC₆ α f hα hα1 hfsm hm6 hm7 h0 j hj z hz
  have hΛB : 0 ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hC₆pos.le (Work.Spaces.HkNorm_nonneg α 6 f)
  have hΛslot : ∀ b : ℕ, b ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z
        * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7
    intro b hb
    refine ((hC₁ α f hα hα1 hfsm hm6 hm7 h0 b (by omega)).1).congr
      (Eventually.of_forall fun z => ?_)
    ring
  -- the radial multiplier
  have hradial : ∀ (ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen ψ →
      Work.Spaces.HkMem α 6 ψ →
      Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z * ψ z θ) :=
    fun ψ hψsm hψmem =>
      HkMem_radial_mul6 α (C₆ * Work.Spaces.HkNorm α 6 f)
        (fun z => Work.Construction.L12 f z) ψ hα hΛB hΛcd hΛjet hψsm hψmem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ## `NP3 = (1/α)·(L₁₂ f·f)`
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (1 / α) (hradial f hfsm hm6)
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (1 / α) * (Work.Construction.L12 f z * f z θ)) (fun z θ _ => ?_) h1
    rfl
  · -- ## `NP4a = (3/(2α))·(L₁₂ f·D_θ F_*)`
    obtain ⟨M₂, hM₂pos, hM₂⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
    obtain ⟨hFj6, -⟩ := Work.FTS.StrongPersist.H6Pair6Aux.Fstar_jets_shift M₂ hM₂
    have hslot1 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter j
          (fun z => Work.Construction.L12 f z * Work.FM.Fstar z) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz :=
      Work.FTS.StrongPersist.H6Pair6Aux.slots_radial_mul
        (X := fun z => Work.Construction.L12 f z) (r := fun z => Work.FM.Fstar z) (M := M₂)
        hΛcd (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_contDiffOn 6) hΛslot
        (fun m hm z hz => hFj6 m (by omega) z (le_of_lt hz))
    have ha4cd : ContDiffOn ℝ 6
        (fun θ : ℝ => (3 * α / (2 * Work.Spaces.c α))
          * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.contDiffOn_gamQfun α
          (3 * α / (2 * Work.Spaces.c α))).of_le (by simp [Work.Stability.smoothOrder])).congr (fun θ _ => by ring)
    have hr4cd : ContDiffOn ℝ 6
        (fun z : ℝ => Work.Construction.L12 f z * Work.FM.Fstar z) (Set.Ioi 0) :=
      hΛcd.mul (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_contDiffOn 6)
    have ha40 : ∀ θ ∈ Work.Spaces.Iθ,
        |(3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ)|
          ≤ |3 * α / (2 * Work.Spaces.c α)| * (4 / 3) := by
      intro θ hθ
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hqG : |Work.Spaces.qfun θ * Work.Spaces.Gam α θ| ≤ 4 / 3 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ (4 / 3) * 1 :=
              mul_le_mul hq hG1 hG0 (by norm_num)
          _ = 4 / 3 := by ring
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hqG (abs_nonneg _)
    have ha41 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        ((Work.Spaces.dthU^[i]) (fun θ' => (3 * α / (2 * Work.Spaces.c α))
            * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ')) θ) ^ 2
          ≤ ((3 * α / (2 * Work.Spaces.c α)) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
            * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i]) (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((3 * α / (2 * Work.Spaces.c α)) ^ 2
                * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hjet : |(Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ|
            ≤ Work.FTS.StrongPersist.H6Pair6Aux.gamqK * (Real.sin (2 * θ)) ^ (α / 5) := by
          have h := Work.FTS.StrongPersist.H6Pair6Aux.GamQfun_dthU_Iθ α hα hα1 i hi6 θ hθI
          rw [show (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)
              = fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t from by
            funext t; ring] at h
          exact h.trans (mul_le_mul_of_nonneg_left hGle
            Work.FTS.StrongPersist.H6Pair6Aux.gamqK_nonneg)
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (Work.FTS.StrongPersist.H6Pair6Aux.gamqK
                * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hjet 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ'))
            = fun θ' => (3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ' :=
          Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_const_mul
            (3 * α / (2 * Work.Spaces.c α))
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            = (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * (Work.FTS.StrongPersist.H6Pair6Aux.gamqK
                  * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, Work.FTS.StrongPersist.H6Pair6Aux.sq_sin_rpow hsin]
              ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_sq_le_sin_aux (κ := α / 5)
        (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2
          * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2) (by positivity) hinterior
    have hmem := sep_mem6_open (α := α) (κ := α / 5)
      (B0 := |3 * α / (2 * Work.Spaces.c α)| * (4 / 3))
      (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2
        * Work.FTS.StrongPersist.H6Pair6Aux.gamqK ^ 2)
      (a := fun θ => (3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Work.Construction.L12 f z * Work.FM.Fstar z)
      (by positivity) (by positivity) (by simp only [Work.Spaces.gam]; linarith)
      ha40 ha41 (continuousOn_HkIntegrand_sep6_priv ha4cd hr4cd) hslot1
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => ((3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.FM.Fstar z)) (fun z θ hzθ => ?_) hmem
    have hz : 0 < z := hzθ.1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hzθ.2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    show ((3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.FM.Fstar z)
      = Work.FTS.StrongPersist.H6Pair6Aux.NP4a α f z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP4a, Work.FTS.StrongPersist.H6Pair6Aux.NA4,
      Work.Spaces.Dth]
    rw [Work.FTS.StrongPersist.H6Pair6Aux.pth_Fstar_eq α z θ hθ]
    have hα0 : α ≠ 0 := ne_of_gt hα
    have hc0 : Work.Spaces.c α ≠ 0 := ne_of_gt hcg
    have h2α : (2 : ℝ) * α ≠ 0 := by positivity
    have h2c : (2 : ℝ) * Work.Spaces.c α ≠ 0 := by positivity
    have hkey : Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
        = α * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
      rw [Work.FTS.StrongPersist.H6Pair6Aux.s2_deriv_Gam_Iθ α hα hθI]
      ring
    have hA : (3 / (2 * α)) * (Work.Construction.L12 f z
          * (Real.sin (2 * θ) * (α * (deriv (Work.Spaces.Gam α) θ / Work.Spaces.c α)
            * Work.FM.Fstar z)))
        = (3 / (2 * α)) * α * (Work.Spaces.c α)⁻¹
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
          * (Work.Construction.L12 f z * Work.FM.Fstar z) := by ring
    rw [hA, hkey]
    first
      | (field_simp; ring)
      | field_simp
  · -- ## `NP4b = (3/(2α))·(L₁₂ f·D_θ f)`
    have hψmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
      Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 6) (f := f) (by linarith) hfsm hm7
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α))
        (hradial (Work.Spaces.Dth f) hfsm.Dth hψmem)
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ))
      (fun z θ _ => ?_) h1
    rfl
  · -- ## `NP5a = (-1)·(L₁₂ f·(c₂ₘ·D_z F_*))`
    obtain ⟨M₂, hM₂pos, hM₂⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
    obtain ⟨-, hFj6'⟩ := Work.FTS.StrongPersist.H6Pair6Aux.Fstar_jets_shift M₂ hM₂
    obtain ⟨D, hDpos, hD⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
    have hslot2 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z =>
          Work.Construction.L12 f z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z) z
            * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      Work.FTS.StrongPersist.H6Pair6Aux.slots_radial_mul
        (X := fun z => Work.Construction.L12 f z)
        (r := fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (M := M₂)
        hΛcd (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_shift_contDiffOn 6) hΛslot
        (fun m hm z hz => hFj6' m (by omega) z hz)
    have ha5cd : ContDiffOn ℝ 6
        (fun θ : ℝ => -(α / Work.Spaces.c α)
          * (Work.Construction.c2m θ * Work.Spaces.Gam α θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 6 (fun θ : ℝ => Work.Construction.c2m θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m.contDiffOn).of_le (by simp [Work.Stability.smoothOrder])
      have h2 : ContDiffOn ℝ 6 (fun θ : ℝ => Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_Gam_Ioo α).of_le (by simp [Work.Stability.smoothOrder])
      have hc : ContDiffOn ℝ 6 (fun _ : ℝ => -(α / Work.Spaces.c α))
          (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const
      have h12 : ContDiffOn ℝ 6
          (fun θ : ℝ => Work.Construction.c2m θ * Work.Spaces.Gam α θ)
          (Set.Ioo 0 (Real.pi / 2)) := h1.mul h2
      exact hc.mul h12
    have hr5cd : ContDiffOn ℝ 6
        (fun z : ℝ => Work.Construction.L12 f z
          * Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (Set.Ioi 0) :=
      hΛcd.mul (Work.FTS.StrongPersist.H6Pair6Aux.Fstar_shift_contDiffOn 6)
    have ha50 : ∀ θ ∈ Work.Spaces.Iθ,
        |-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ)|
          ≤ |α / Work.Spaces.c α| * 2 := by
      intro θ hθ
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hc2G : |Work.Construction.c2m θ * Work.Spaces.Gam α θ| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Construction.c2m θ| * Work.Spaces.Gam α θ ≤ 2 * 1 :=
              mul_le_mul (Work.FTS.StrongPersist.H6Pair6Aux.abs_c2m_le_two θ) hG1 hG0
                (by norm_num)
          _ = 2 := by ring
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left hc2G (abs_nonneg _)
    have ha51 : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        ((Work.Spaces.dthU^[i]) (fun θ' => -(α / Work.Spaces.c α)
            * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ')) θ) ^ 2
          ≤ ((α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
            * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
      have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i]) (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hbd : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) :=
          hD α hα hα1 i hi1 hi6 θ hθo
        have hsin2 : Real.sin (2 * θ) ^ 2 + α ≤ 2 := by
          have h1 := Real.sin_sq_le_one (2 * θ)
          linarith
        have h3 : 0 ≤ Real.sin (2 * θ) ^ 2 + α := by
          nlinarith [sq_nonneg (Real.sin (2 * θ)), hα.le]
        have h4 : 0 ≤ D * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_nonneg hDpos.le (Real.rpow_nonneg (le_of_lt hsin) _)
        have hstep : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by
          calc |(Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
              ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := hbd
            _ ≤ D * (Real.sin (2 * θ)) ^ (α / 5) * 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hGle hDpos.le) hsin2 h3 h4
            _ = 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by ring
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hstep 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ'))
            = fun θ' => -(α / Work.Spaces.c α) * (Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ' :=
          Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_const_mul (-(α / Work.Spaces.c α))
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((-(α / Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            = (α / Work.Spaces.c α) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (α / Work.Spaces.c α) ^ 2
              * (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, Work.FTS.StrongPersist.H6Pair6Aux.sq_sin_rpow hsin]
              ring
      exact Work.FTS.StrongPersist.H6Pair6Aux.dthU_iter_sq_le_sin_aux (κ := α / 5)
        (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2) (by positivity) hinterior
    have hmem := sep_mem6_open (α := α) (κ := α / 5)
      (B0 := |α / Work.Spaces.c α| * 2)
      (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
      (a := fun θ => -(α / Work.Spaces.c α)
        * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Work.Construction.L12 f z
        * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      (by positivity) (by positivity) (by simp only [Work.Spaces.gam]; linarith)
      ha50 ha51 (continuousOn_HkIntegrand_sep6_priv ha5cd hr5cd) hslot2
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (-(α / Work.Spaces.c α)
        * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z
          * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)) (fun z θ hzθ => ?_) hmem
    have hz : 0 < z := hzθ.1
    show (-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Work.Construction.L12 f z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      = Work.FTS.StrongPersist.H6Pair6Aux.NP5a α f z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5a, Work.FTS.StrongPersist.H6Pair6Aux.NA5]
    rw [Work.FTS.StrongPersist.H6Pair6Aux.Dz_Fstar_eq α z θ hz]
    ring
  · -- ## `NP5b = (-1)·(c₂ₘ·L₁₂ f·D_z f)`
    have hψsm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_neg
          (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
            Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m)) hfsm.Dz
    have hψmem : Work.Spaces.HkMem α 6
        (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.c2m_Dz_mem hα hα1 hfsm hm7
    have h1 : Work.Spaces.HkMem α 6
        (fun z θ => Work.Construction.L12 f z
          * (-(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ)) :=
      hradial (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) hψsm hψmem
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => Work.Construction.L12 f z
        * (-(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ)) (fun z θ _ => ?_) h1
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
    ring
  · -- ## `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`
    obtain ⟨CA, hCApos, hN0coef⟩ :=
      Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
    obtain ⟨hN0coefsm, hN0coefw, -⟩ := hN0coef α hα hα1
    have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
      Work.FTS.IPGen.HkMem_Dz_le hfsm hm7
    have hmul : Work.Spaces.HkMem α 6
        (fun z θ => (-(2 * α / (1 + z)) * Work.Construction.c2m θ)
          * Work.Spaces.Dz f z θ) :=
      Work.FTS.StrongPersist.H6Pair6Aux.HkMem_mul_of_WlInf6 hα hα1 hN0coefsm hN0coefw
        hfsm.Dz hDzmem
    refine Work.FTS.StrongPersist.H6Pair6Aux.HkMem_congr_Qd
      (f := fun z θ => (-(2 * α / (1 + z)) * Work.Construction.c2m θ)
        * Work.Spaces.Dz f z θ) (fun z θ hzθ => ?_) hmul
    have hz : 0 ≤ z := le_of_lt hzθ.1
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6, Work.FTS.StrongPersist.H6Pair6Aux.NA6]
    rw [Work.Construction.L12_Fstar_eq hα hα1 hz]
    ring

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

-- The `A · D_z f` slot row of the level-six `N₀`-pairing, with the SEPARABLE σ-decay
-- hypothesis on the coefficient.  For the intended `A = c₂ₘ(θ)·L₁₂(F_*)(z)` one has
-- `|D_θ^i c₂ₘ| ≤ 100000·sin(2θ)²` (`Work.FTS.StrongPersist.dthU_c2m_bound6`) and
-- `|D_z^j L₁₂(F_*)| ≤ Cα` (`Work.FTS.StrongPersist.c2mSix_bound_z` with `k = 0` together with
-- `FstarPkg.eqOn_L12_invH`), so the hypothesis holds with `K = Cα` and there is NO
-- `α`-threshold.  (This is strictly stronger than the `Abnd` hypothesis of
-- `H6Pair6Aux.T45AslotLe`, and unlike the σ-free hypothesis of `H6Pair6Aux.H6N0Aux.row_A_dz`
-- it makes every slot provable: the coefficient hypothesis is precisely the extra input that
-- was missing in `H6N0Aux/NOTES_commPiece_FALSE.md`.)
--
-- ROUTE.  `Submission/Work/FTS/StrongPersist/H6Pair6Aux/H6N0Aux/rowA_aux.lean` contains a
-- complete assembly of this row for the σ-free hypothesis.  NOTE: that module does NOT build
-- (it imports `H6N0Aux/commPiece.lean`, which fails to elaborate on a bare `π`, and whose
-- statement is FALSE).  Do NOT import it: COPY its contents into your own file
-- (`rowA_piece`, `rowA_mixed_succ_eq`, `rowA_piece_expansion`, and the Fubini + integrability
-- + binomial-summation assembly of `rowA_core`) and replace its two per-slot lemmas
-- (`rowA_lead_bound`, `rowA_piece_integrable`/`rowA_piece_bound`) by the case analysis below.
--
-- The Leibniz expansion is
--   `mixed b a (A · D_z f) = Σ_{i≤a} Σ_{j≤b} C(a,i)C(b,j)·(mixed j i A)·(mixed (b-j+1)(a-i) f)`
-- on the open quadrant (`TransportS.mixed_mul_Dz_open`), so each slot is `∫_z∫_θ ρ·X·G·H`
-- with `X := mixed j i A`, `G := mixed (b-j+1)(a-i) f`, `H := mixed b a f`.  Write
-- `σ := sin 2θ`, `w := Spaces.w`.  `IsLeafW α a ρ` gives `ρ ≤ w²σ^{-γ}` on the open quadrant
-- (with `η = 0.99 ≤ γ = 1+α/10`, and `leafGam` only when `a ≥ 1`).
--
-- * `(i,j) = (0,0)` (the only slot seeing the level-seven slot `mixed (b+1) a f`, order
--   `a+b+1 ≤ 7`): use `H6Pair6Aux.H6N0Aux.leadPiece` + `H6Pair6Aux.H6N0Aux.dzSelfA2d`
--   verbatim (they need only `|A| ≤ K`, which is `hAbd` at `i = 0` as the factor there is `1`);
--   gives `≤ 5K·HkSq α 6 f` and the integrability of the slot.
-- * `i = 0`, `j ≥ 1`: `X = DzIter j A` with `|X| ≤ K`; `G = mixed (b-j+1) a f` has the SAME
--   angular index `a` as the leaf weight `ρ` and order `a+(b-j+1) ≤ a+b ≤ 6`, and
--   `H = mixed b a f` has order `a+b ≤ 6`; both are dominated by `HkIntegrand α 6 f` with the
--   weight `ρ` via `H6Pair6Aux.T5bPrep.domLeaf_all`.  Then
--   `2|G||H| ≤ G²+H²` gives `|∫∫ρXGH| ≤ K·HkSq α 6 f`.
-- * `i ≥ 1`: `|X| ≤ Kσ`; since `ρ ≤ w²σ^{-γ}` and `σ^{1-γ} = σ^{-α/10} ≤ σ^{-η}` (because
--   `α/10 ≤ 0.1 < 0.99 = η`),
--       `ρ|X||G||H| ≤ K·w²σ^{-η}|G||H| ≤ K·(w²σ^{-η}G² + w²σ^{-γ}H²)`   pointwise
--   (`2ab ≤ a²+b²` with `σ^{-η}, σ^{-γ} ≥ 1`).  Both integrals are `≤ HkSq α 6 f` by
--   `H6Pair6Aux.intSlotLeHkSq α hm6`: `G` has order `(a-i)+(b-j+1) ≤ 6`, and `H` has `1 ≤ a`
--   with `a+b ≤ 6`; use the FIRST conjunct with `θw := σ^{-η}` in the case `a-i = 0` (then `G`
--   is a pure radial slot) and the SECOND conjunct with `θw := σ^{-η}` resp. `θw := σ^{-γ}`
--   when `a-i ≥ 1` resp. for `H`.  Hence `≤ 2K·HkSq α 6 f`; the same domination gives the
--   integrability of the slot (`HkIntegrand α 6 f` is integrable by `hm6`).
-- * Fubini and `Σ_{i≤a}Σ_{j≤b} C(a,i)C(b,j) = 2^a2^b ≤ 64` then give
--   `≤ (2·64+5)K·HkSq α 6 f ≤ 133·K·α^{-3}(1+Xn α f)^4(1+HkSq α 6 f)` (`α^{-3} ≥ 1`,
--   `(1+Xn)^4 ≥ 1`, `1+HkSq ≥ HkSq`), so any `C ≥ 133` works.
theorem RowAdz : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f →
      Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
        |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ))) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ C * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨400, by norm_num, ?_⟩
  intro α hα f A a b ρ K hso hm6 hm7 hAso hK hAbd hab hρ
  exact (rowA_core hα.1 hα.2 hK hso hAso hm6 hm7 hρ hAbd hab).trans
    (rowA_majorant hα.1 hα.2 hK)

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
