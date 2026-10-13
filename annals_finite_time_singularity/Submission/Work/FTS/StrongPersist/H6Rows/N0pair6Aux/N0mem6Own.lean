import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.hkmem_pieces_own
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0_mem6
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMaj6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkMem_X_close6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.angmul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.HkMem_add_smoothOpen
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.Nonlinear.Open.Row23

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

private theorem n0own_HkMem_PsiB {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f : ℝ → ℝ → ℝ} (hfsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hm7 : Work.Spaces.HkMem α 7 f) : Work.Spaces.HkMem α 6 (n0ownPsiB f) := by
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
  rw [n0ownPsiB_eq]
  have heq : (fun z θ => -(Work.Construction.c2m θ * Work.Spaces.Dz f z θ))
      = fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Spaces.Dz f z θ) := by
    funext z θ; ring
  rw [heq]
  exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hang

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

private theorem n0own_smoothOpen_sep6 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongPersist.H6Rows.sep6 α) := by
  unfold Work.FTS.StrongPersist.H6Rows.sep6 Work.Construction.sepF
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_mul (n0own_smoothOpen_Kfac_rhoR α)
    (n0own_smoothOpen_psiA α)

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
