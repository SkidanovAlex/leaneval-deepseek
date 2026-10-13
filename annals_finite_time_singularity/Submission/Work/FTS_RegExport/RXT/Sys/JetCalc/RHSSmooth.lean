import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.slice_space_lip
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.OpFacts
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.RHSSmooth` — smoothness of `F(σ)` and of `RHS σ`

`F_* = α(Γ/c)(2z/(1+z)²)` is `C^n` on the open quadrant for every `n`; the slice of the
sanitiser `GR α g` is `C^n` for `n ≤ 4` (`RegPkgMin.c4` + agreement with `g` on the quadrant);
hence `F(σ)` is `C^n` (`n ≤ 4`) and `RHS σ` is `C²` there.  Also the linearity of the mixed
operators on the three summands `Afun`, `Bfun`, `Cfun` of `RHS`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! ## §3 Smoothness of the profile and of the right-hand side on the open quadrant -/

/-- `F_* = α·(Γ/c)·(2z/(1+z)²)` is `C^n` on the open quadrant. -/
theorem contDiffOn_Fstar_Q0 (n : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ n (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Gam_Q0 α n
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun _ _ => hc)
  have h2 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS_RegExport.RXT.ftau_contDiffOn_FM_Fstar n).comp contDiffOn_fst
      (fun p hp => hp.1)
  exact (h2.mul h3).congr (fun _ _ => rfl)

/-- The sanitiser `GR α g` has the same `C^n` slices as `g` on the open quadrant. -/
theorem contDiffOn_slice_GR_Q0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {n : ℕ} (hn : n ≤ 4) (σ : ℝ) (hσ : 0 ≤ σ) :
    ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ)) Work.FTS.EllipticEst.Q0 := by
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g σ))
      Work.FTS.EllipticEst.Q0 := hOK.1.1.c4 σ hσ
  refine (h4.of_le (Nat.cast_le.mpr hn)).congr ?_
  intro p hp
  exact Work.FTS_RegExport.RXT.ftau_slice_GR_eq hσ hp.1 hp.2.1.le hp.2.2.le

/-- `F(σ) = F_* + gS α (tauExt g)(σ)` is `C^n` on the open quadrant for `n ≤ 4`. -/
theorem contDiffOn_FtauS_Q0 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {n : ℕ} (hn : n ≤ 4) (σ : ℝ) (hσ : 0 ≤ σ) :
    ContDiffOn ℝ n (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hF : ContDiffOn ℝ n
      (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_Fstar_Q0 n hβ hβ1
  have hG : ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.RegExportIface.RXT.GR α g) σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_slice_GR_Q0 hOK hn σ hσ
  refine (hF.add hG).congr (fun p _ => ?_)
  show Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2
      + Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.GR α g) σ p.1 p.2
    = FtauS α g σ p.1 p.2
  simp only [FtauS_apply, Work.FTS.Galerkin.slice]

/-- **`RHS` is `C²` on the open quadrant.**  It is a sum of products of the three coefficients
(`C²` by `hC2`) with `D_zF`, `D_θF`, `F` (`C²` because `F` is `C³`, `contDiffOn_FtauS_Q0`). -/
theorem contDiffOn_RHS {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) :
    ContDiffOn ℝ 2 (Function.uncurry (RHS α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨h1, h2, h3⟩ := hC2 σ hσ.1.le
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1.le
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    hQ3.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hA := h1.mul hDz
  have hB := h2.mul hDth
  have hC := h3.mul hQ2
  refine ((hA.add hB).add hC).neg.congr (fun p _ => ?_)
  show - (Work.FTS.RegExportIface.RXT.VR α Φs E g p.1 p.2 σ
        * Work.Spaces.Dz (FtauS α g σ) p.1 p.2
      + Work.FTS.RegExportIface.RXT.bR α Φs E g p.1 p.2 σ
        * Work.Spaces.Dth (FtauS α g σ) p.1 p.2
      + Work.FTS.RegExportIface.RXT.cR α Φs E g p.1 p.2 σ * FtauS α g σ p.1 p.2)
    = RHS α Φs E g σ p.1 p.2
  rw [RHS_apply]

/-! ## §4 The uniform local jet bounds for `RHS` -/

/-- The first summand of `RHS`: `Vz·D_zF`. -/
noncomputable def Afun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ
    * Work.Spaces.Dz (FtauS α g σ) z θ

/-- The second summand of `RHS`: `bR·D_θF`. -/
noncomputable def Bfun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
    * Work.Spaces.Dth (FtauS α g σ) z θ

/-- The third summand of `RHS`: `cs·F`. -/
noncomputable def Cfun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) (σ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * FtauS α g σ z θ

theorem RHS_eq_neg_sum (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam)
    (σ z θ : ℝ) :
    RHS α Φs E g σ z θ
      = - ((Afun α Φs E g σ z θ + Bfun α Φs E g σ z θ) + Cfun α Φs E g σ z θ) := by
  rw [RHS_apply]
  rfl

theorem RHS_eq_neg_sum_fun (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) (σ : ℝ) :
    RHS α Φs E g σ
      = fun z θ => - ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ) z θ := by
  funext z θ
  rw [RHS_eq_neg_sum]
  rfl

/-- **The summands of `RHS` are `C²` on the open quadrant** (needed for the linearity of the
mixed operators on the sum). -/
theorem contDiffOn_Afun {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) :
    ContDiffOn ℝ 2 (Function.uncurry (Afun α Φs E g σ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Bfun α Φs E g σ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 2 (Function.uncurry (Cfun α Φs E g σ)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨h1, h2, h3⟩ := hC2 σ hσ.1.le
  have hQ3 : ContDiffOn ℝ 3 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_FtauS_Q0 hα hα13 hOK (by norm_num) σ hσ.1.le
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry (FtauS α g σ)) Work.FTS.EllipticEst.Q0 :=
    hQ3.of_le (by norm_num)
  have hDz : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dz (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  have hDth : ContDiffOn ℝ 2
      (Function.uncurry (Work.Spaces.Dth (FtauS α g σ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_Dth_fin Work.FTS.EllipticEst.isOpen_Q0 hQ3
  refine ⟨?_, ?_, ?_⟩
  · exact (h1.mul hDz).congr (fun _ _ => rfl)
  · exact (h2.mul hDth).congr (fun _ _ => rfl)
  · exact (h3.mul hQ2).congr (fun _ _ => rfl)

/-- **Linearity of the mixed operators on `RHS σ`**: the jet of `RHS σ` is the sum of the jets of
its three summands, with a sign. -/
theorem mixed_RHS_eq {α C₀ S : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hC2 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ))
        Work.FTS.EllipticEst.Q0)
    {σ : ℝ} (hσ : σ ∈ Set.Ioc (0:ℝ) S) {j i : ℕ} (hji : j + i ≤ 2) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    Work.Spaces.mixed j i (RHS α Φs E g σ) z θ
      = - (Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ
          + Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ) := by
  obtain ⟨hA2, hB2, hC2'⟩ := contDiffOn_Afun hα hα13 hOK hC2 hσ
  have hAB : ContDiffOn ℝ 2 (Function.uncurry (Afun α Φs E g σ + Bfun α Φs E g σ))
      Work.FTS.EllipticEst.Q0 := hA2.add hB2
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθπ⟩
  have hsum : Work.Spaces.mixed j i ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ) z θ
      = Work.Spaces.mixed j i (Afun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Bfun α Φs E g σ) z θ
        + Work.Spaces.mixed j i (Cfun α Φs E g σ) z θ := by
    have hji' : i + j ≤ 2 := by rw [Nat.add_comm]; exact hji
    have h1 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hAB hC2' i j hji' (z, θ) hp
    have h2 := Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
        Work.FTS.EllipticEst.isOpen_Q0 hA2 hB2 i j hji' (z, θ) hp
    rw [h1, h2]
  have hneg := congrFun (congrFun (mixed_neg j i
    ((Afun α Φs E g σ + Bfun α Φs E g σ) + Cfun α Φs E g σ)) z) θ
  rw [RHS_eq_neg_sum_fun, hneg, hsum]

end Work.FTS_RegExport.RXT.Sys
