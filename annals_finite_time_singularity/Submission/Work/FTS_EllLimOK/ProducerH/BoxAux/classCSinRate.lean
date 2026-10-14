import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The full profile `F = F_* + w`. -/
abbrev Ft (α : ℝ) (w : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Construction.Ftot α w


/-- **`∂_θ(F_* + w) = ∂_θF_* + ∂_θw` on the open quadrant.** -/
theorem pth_Ftot (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Ft α w) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth w z θ := by
  intro z θ hQ
  have hz : 0 < z := hQ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hQ.2
  have h1 : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  have h2 : DifferentiableAt ℝ (fun θ' => w z θ') θ :=
    ((hw.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simp only [Ft, Work.Spaces.pth, Work.Construction.Ftot]
  rw [show (fun θ' => Work.Construction.Fstar α z θ' + w z θ')
      = (fun θ' => Work.Construction.Fstar α z θ') + (fun θ' => w z θ') from rfl]
  exact deriv_add h1 h2

/-- **`D_z(F_* + w) = D_zF_* + D_zw` on the open quadrant.** -/
theorem Dz_Ftot (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Ft α w) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz w z θ := by
  intro z θ hQ
  have hz : 0 < z := hQ.1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hQ.2
  have h1 : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
    ((hF.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (fun z' => w z' θ) z :=
    ((hw.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  simp only [Ft, Work.Spaces.Dz, Work.Spaces.pz, Work.Construction.Ftot]
  rw [show (fun z' => Work.Construction.Fstar α z' θ + w z' θ)
      = (fun z' => Work.Construction.Fstar α z' θ) + (fun z' => w z' θ) from rfl]
  rw [deriv_add h1 h2]
  ring

/-- **The split of `N₀` into its seven pieces, on the open quadrant.** -/
theorem N0_split_open (α : ℝ) {w : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α))
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Ft α w) w z θ
        = NA1 α z θ + (NP3 α w z θ + (NP4a α w z θ + (NP4b α w z θ
            + (NP5a α w z θ + (NP5b α w z θ + NP6 α w z θ))))) := by
  intro z θ hQ
  have hpth := pth_Ftot α hF hw z θ hQ
  have hDz := Dz_Ftot α hF hw z θ hQ
  simp only [Work.Construction.N0, Work.Construction.N01, Work.Construction.N02,
    Work.Construction.N03, Work.Construction.N04a, Work.Construction.N04b,
    Work.Construction.N05a, Work.Construction.N05b, Work.Construction.N06,
    Work.FTS.StrongPersist.H6Pair6Aux.NA1, Work.FTS.StrongPersist.H6Pair6Aux.NA4,
    Work.FTS.StrongPersist.H6Pair6Aux.NA5, Work.FTS.StrongPersist.H6Pair6Aux.NA6,
    Work.FTS.StrongPersist.H6Pair6Aux.NP3, Work.FTS.StrongPersist.H6Pair6Aux.NP4a,
    Work.FTS.StrongPersist.H6Pair6Aux.NP4b, Work.FTS.StrongPersist.H6Pair6Aux.NP5a,
    Work.FTS.StrongPersist.H6Pair6Aux.NP5b, Work.FTS.StrongPersist.H6Pair6Aux.NP6,
    Work.Spaces.Dth, Work.Construction.Ftot]
  rw [hpth, hDz]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Construction.s2]
  ring

/-! ## The `HkSq`-sub-additivity of the nested seven-fold sum -/

/-- **`HkSq` of the nested seven-fold sum**: six applications of `HkSq_add_le_open`, hence a
factor `2^6 = 64`. -/
theorem hkSq_sum7_le {α : ℝ} {k : ℕ} (hα : 0 < α)
    {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ → ℝ → ℝ}
    (hs₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (hs₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (hs₃ : Work.FTS.EllipticEst.SmoothOpen f₃) (hs₄ : Work.FTS.EllipticEst.SmoothOpen f₄)
    (hs₅ : Work.FTS.EllipticEst.SmoothOpen f₅) (hs₆ : Work.FTS.EllipticEst.SmoothOpen f₆)
    (hs₇ : Work.FTS.EllipticEst.SmoothOpen f₇)
    (hm₁ : Work.Spaces.HkMem α k f₁) (hm₂ : Work.Spaces.HkMem α k f₂)
    (hm₃ : Work.Spaces.HkMem α k f₃) (hm₄ : Work.Spaces.HkMem α k f₄)
    (hm₅ : Work.Spaces.HkMem α k f₅) (hm₆ : Work.Spaces.HkMem α k f₆)
    (hm₇ : Work.Spaces.HkMem α k f₇) :
    Work.Spaces.HkSq α k (fun z θ => f₁ z θ + (f₂ z θ + (f₃ z θ + (f₄ z θ
        + (f₅ z θ + (f₆ z θ + f₇ z θ))))))
      ≤ 64 * (Work.Spaces.HkSq α k f₁ + Work.Spaces.HkSq α k f₂ + Work.Spaces.HkSq α k f₃
          + Work.Spaces.HkSq α k f₄ + Work.Spaces.HkSq α k f₅ + Work.Spaces.HkSq α k f₆
          + Work.Spaces.HkSq α k f₇) := by
  have hs67 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f₆ z θ + f₇ z θ) := hs₆.add hs₇
  have hm67 : Work.Spaces.HkMem α k (fun z θ => f₆ z θ + f₇ z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₆ hs₇ hm₆ hm₇
  have hs567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₅ z θ + (f₆ z θ + f₇ z θ)) := hs₅.add hs67
  have hm567 : Work.Spaces.HkMem α k (fun z θ => f₅ z θ + (f₆ z θ + f₇ z θ)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₅ hs67 hm₅ hm67
  have hs4567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))) := hs₄.add hs567
  have hm4567 : Work.Spaces.HkMem α k (fun z θ => f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₄ hs567 hm₄ hm567
  have hs34567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))) := hs₃.add hs4567
  have hm34567 : Work.Spaces.HkMem α k
      (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₃ hs4567 hm₃ hm4567
  have hs234567 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))) := hs₂.add hs34567
  have hm234567 : Work.Spaces.HkMem α k
      (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))) :=
    Work.FTS.StrongPersist.H6Pair6Aux.HkMem_add_of_HkMem α k hs₂ hs34567 hm₂ hm34567
  have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₆ hs₇ hm₆ hm₇
  have h2 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₅ hs67 hm₅ hm67
  have h3 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₄ hs567 hm₄ hm567
  have h4 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₃ hs4567 hm₃ hm4567
  have h5 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₂ hs34567 hm₂ hm34567
  have h6 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hs₁ hs234567 hm₁ hm234567
  have nn : ∀ g : ℝ → ℝ → ℝ, 0 ≤ Work.Spaces.HkSq α k g := fun g =>
    Work.Spaces.HkSq_nonneg α k g
  have hchain : Work.Spaces.HkSq α k
      (fun z θ => f₁ z θ + (f₂ z θ + (f₃ z θ + (f₄ z θ
        + (f₅ z θ + (f₆ z θ + f₇ z θ))))))
      ≤ 2 * (Work.Spaces.HkSq α k f₁
          + 2 * (Work.Spaces.HkSq α k f₂
            + 2 * (Work.Spaces.HkSq α k f₃
              + 2 * (Work.Spaces.HkSq α k f₄
                + 2 * (Work.Spaces.HkSq α k f₅
                  + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇)))))) := by
    refine le_trans h6 ?_
    have a2 : Work.Spaces.HkSq α k
        (fun z θ => f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ))))
        ≤ 2 * (Work.Spaces.HkSq α k f₃
            + 2 * (Work.Spaces.HkSq α k f₄
              + 2 * (Work.Spaces.HkSq α k f₅
                + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇)))) := by
      refine le_trans h4 ?_
      linarith [h1, h2, h3, nn f₄, nn f₅, nn f₆, nn f₇]
    have a1 : Work.Spaces.HkSq α k
        (fun z θ => f₂ z θ + (f₃ z θ + (f₄ z θ + (f₅ z θ + (f₆ z θ + f₇ z θ)))))
        ≤ 2 * (Work.Spaces.HkSq α k f₂
            + 2 * (Work.Spaces.HkSq α k f₃
              + 2 * (Work.Spaces.HkSq α k f₄
                + 2 * (Work.Spaces.HkSq α k f₅
                  + 2 * (Work.Spaces.HkSq α k f₆ + Work.Spaces.HkSq α k f₇))))) := by
      refine le_trans h5 ?_
      linarith [a2, nn f₂, nn f₃]
    linarith [a1, nn f₁, nn f₂, nn f₃, nn f₄, nn f₅, nn f₆, nn f₇]
  refine le_trans hchain ?_
  linarith [nn f₁, nn f₂, nn f₃, nn f₄, nn f₅, nn f₆, nn f₇]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSAux.StreamDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The three stream functions, and their slices -/

/-- The stream function `Φ̃ = PhiTil α (F_* + W) (Φs + Φg)` of the full profile. -/
abbrev PsiTot (α : ℝ) (Φs W Φg : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α (Work.Construction.Ftot α W) (fun z θ => Φs z θ + Φg z θ)

/-- The star stream function `Φ̃_* = PhiTil α F_* Φs`. -/
abbrev PsiStar (α : ℝ) (Φs : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs

/-- The elliptic stream function `Φ̃_ell = PhiTil α W Φg`. -/
abbrev PsiEll (α : ℝ) (W Φg : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.PhiTil α W Φg

/-- `deriv` only depends on a neighbourhood: if `g =ᶠ[𝓝 z] g'` and `g'` is differentiable at `z`,
then the derivatives agree. -/
theorem deriv_eq_of_eventuallyEq {g g' : ℝ → ℝ} {z : ℝ} (h : g =ᶠ[𝓝 z] g')
    (hg' : DifferentiableAt ℝ g' z) : deriv g z = deriv g' z :=
  ((h.hasDerivAt_iff).mpr hg'.hasDerivAt).deriv

/-- `L₁₂(F_*)` is differentiable on `(0,∞)` (it is `2α/(1+z)` there). -/
theorem differentiableAt_L12_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z := by
  have hev : (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z')
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * α / (1 + z') := by
    filter_upwards [Ici_mem_nhds_of_pos hz] with z' hz'
    exact Work.Construction.L12_Fstar_eq hα hα1 hz'
  have hd : DifferentiableAt ℝ (fun z' : ℝ => 2 * α / (1 + z')) z := by
    have h1 : (1 : ℝ) + z ≠ 0 := by linarith
    fun_prop
  exact (hev.hasDerivAt_iff.mpr hd.hasDerivAt).differentiableAt

/-- `L₁₂(W)` is differentiable on `(0,∞)` for `W ∈ C^4(Q0) ∩ ℋ⁴`
(`Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4`). -/
theorem differentiableAt_L12_of_smoothOpen {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {W : ℝ → ℝ → ℝ} (hWs : Work.FTS.EllipticEst.SmoothOpen W)
    (hWm : Work.Spaces.HkMem α 4 W) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 W z') z :=
  (Work.FTS_RegExport.RXT.STC.hasDerivAt_L12_C4 hα hα1
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall W).mp hWs 4) hWm hz).differentiableAt

/-- `PhiTil α F Ψ` has differentiable slices as soon as `Ψ` does and `L₁₂(F)` is
differentiable in `z`. -/
theorem differentiableAt_PhiTil {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hΨz : DifferentiableAt ℝ (fun z' => Ψ z' θ) z)
    (hΨt : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ)
    (hF : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α F Ψ z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α F Ψ z θ') θ := by
  constructor
  · have h2 : DifferentiableAt ℝ (fun z' : ℝ =>
        ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F z') z :=
      hF.const_mul _
    have heq : (fun z' => Work.Construction.PhiTil α F Ψ z' θ)
        = fun z' : ℝ => Ψ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F z' := by
      funext z'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta] <;> ring
    rw [heq]
    exact hΨz.sub h2
  · have h2 : DifferentiableAt ℝ (fun θ' : ℝ =>
        ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ') θ :=
      (by have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
            simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
          simpa only [Work.Construction.s2] using h.differentiableAt :
        DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ).const_mul _
    have heq : (fun θ' => Work.Construction.PhiTil α F Ψ z θ')
        = fun θ' : ℝ => Ψ z θ'
          - ((1 / (4 * α)) * Work.Construction.L12 F z) * Work.Construction.s2 θ' := by
      funext θ'
      simp only [Work.Construction.PhiTil, Work.Construction.Theta] <;> ring
    rw [heq]
    exact hΨt.sub h2

/-- The `z`- and `θ`-slices of the star stream function are differentiable. -/
theorem PsiStar_diff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => PsiStar α Φs z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => PsiStar α Φs z θ') θ :=
  differentiableAt_PhiTil
    (Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦs hz hθ0 hθ1)
    (Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦs hz hθ0 hθ1)
    (differentiableAt_L12_Fstar hα hα1 hz)

/-- The `z`- and `θ`-slices of the elliptic stream function are differentiable. -/
theorem PsiEll_diff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W Φg : ℝ → ℝ → ℝ}
    (hWs : Work.FTS.EllipticEst.SmoothOpen W) (hWm : Work.Spaces.HkMem α 4 W)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z' => PsiEll α W Φg z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => PsiEll α W Φg z θ') θ :=
  differentiableAt_PhiTil
    (Work.FTS.StrongEps.EComparison.differentiableAt_zslice hΦg hz hθ0 hθ1)
    (Work.FTS.StrongEps.EComparison.differentiableAt_tslice hΦg hz hθ0 hθ1)
    (differentiableAt_L12_of_smoothOpen hα hα1 hWs hWm hz)

/-! ## The value and slice identities for the total stream function -/

/-- The value of the total stream function is the sum of the star and elliptic values. -/
theorem PsiTot_value_eq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z θ : ℝ} (hz : 0 ≤ z) :
    PsiTot α Φs W Φg z θ = PsiStar α Φs z θ + PsiEll α W Φg z θ := by
  simp only [PsiTot, PsiStar, PsiEll, Work.Construction.PhiTil, Work.Construction.Theta]
  rw [hadd z hz]
  ring

/-- The `θ`-slices of the total stream function are the sums of the `θ`-slices (as functions,
for fixed `z ≥ 0`). -/
theorem PsiTot_tslice_eq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z : ℝ} (hz : 0 ≤ z) :
    (fun θ => PsiTot α Φs W Φg z θ)
      = fun θ => PsiStar α Φs z θ + PsiEll α W Φg z θ := by
  funext θ
  exact PsiTot_value_eq hadd hz

/-- The `z`-slices of the total stream function agree, near `z`, with the sum of the star and
elliptic `z`-slices. -/
theorem PsiTot_zslice_eventuallyEq {α : ℝ} {Φs W Φg : ℝ → ℝ → ℝ}
    (hadd : ∀ z ∈ Set.Ici (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftot α W) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 W z)
    {z θ : ℝ} (hz : 0 < z) :
    (fun z' => PsiTot α Φs W Φg z' θ)
      =ᶠ[𝓝 z] fun z' => PsiStar α Φs z' θ + PsiEll α W Φg z' θ := by
  filter_upwards [Ici_mem_nhds_of_pos hz] with z' hz'
  exact PsiTot_value_eq hadd hz'

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCSinRate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `BoxAux.classCSinRate` — the angular vanishing rate of a class-`C` profile

For `0 < α ≤ 1` there is a constant `C = C(α) > 0` such that **every** class-`C` profile
`f` (`Work.FTS.ClassC.ClassC α f`) obeys, uniformly in `z > 0` and `θ ∈ (0,π/2)`,

  `|f z θ| ≤ C · Xn6 α f · (min θ (π/2 - θ)) ^ ((γ-1)/2)`,   `γ = gam α = 1 + α/10`,

i.e. `f` vanishes at both angular endpoints at least at the rate `sin(2θ)^((γ-1)/2)`.

**Route.**  A class-`C` profile has honest traces (`ClassC.tr`): `f z θ → 0` as `θ → 0⁺` and as
`θ → (π/2)⁻` for every `z > 0` (`Work.FTS.H2.HQ.BdryTraces.tendsto_theta_*`).  Hence `f z θ` is the
integral of its `θ`-derivative down to the endpoint, and the weighted Cauchy–Schwarz inequality

  `|f z θ - f z t| ≤ (∫_θ^t g'² sin^{2-γ})^{1/2} · (∫_θ^t sin^{γ-2})^{1/2}`

combined with `∫_θ^t sin(2σ)^{γ-2} ≤ 2(π/4)^{2-γ}/(γ-1)·(t-θ)^{γ-1}`
(`THL.integral_sin_two_rpow_le`) produces the exponent `(γ-1)/2` at *both* endpoints.

The remaining input is the `z`-uniform angular slice bound: for `1 ≤ a` and `a + b ≤ 5`,
`∫_θ (D_z^bD_θ^a f z θ)² sin(2θ)^{-γ} ≤ C · HkSq α 6 f` (`StrongPersist.N6.sliceAng_le6`), applied
at the slot `(b,a) = (0,1)` (`D_θ f = sin(2θ)·∂_θ f`).  The sub-interval form used here is
obtained from the full-`Iθ` form by monotonicity of the set integral, the integrability of the
integrand on `Iθ` being `StrongEps.integrableOn_mixed_sq_rpow6`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular facts -/

/-- `sin(2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s ^ a) ^ 2 = s ^ (2 * a)` for `s ≥ 0`. -/
private lemma rpow_sq {s a : ℝ} (hs : 0 ≤ s) : (s ^ a) ^ 2 = s ^ (2 * a) := by
  rw [← Real.rpow_two (s ^ a), ← Real.rpow_mul hs a 2,
    show a * 2 = 2 * a by ring]

/-- `s ^ 2 · s ^ (-γ) = s ^ (2 - γ)` for `s > 0`. -/
private lemma sq_mul_rpow_neg {s γ : ℝ} (hs : 0 < s) : s ^ 2 * s ^ (-γ) = s ^ (2 - γ) := by
  rw [← Real.rpow_two, ← Real.rpow_add hs,
    show (2 : ℝ) + -γ = 2 - γ by ring]

/-- `(s·a) ^ 2 · s ^ (-γ) = a ^ 2 · s ^ (2 - γ)` for `s > 0`. -/
private lemma mul_sq_mul_rpow_neg {s a γ : ℝ} (hs : 0 < s) :
    (s * a) ^ 2 * s ^ (-γ) = a ^ 2 * s ^ (2 - γ) := by
  rw [mul_pow, ← sq_mul_rpow_neg hs]
  ring

/-! ## The one-dimensional Cauchy–Schwarz rate lemma -/

/-- **The endpoint rate from the weighted angular `L²` bound.**  If `g` is differentiable on
`(0, π/2)` with derivative `g'`, continuous on `[a,b] ⊂ (0,π/2)`, and
`∫_a^b g'² sin(2·)^{2-γ} ≤ M` with `1 < γ ≤ 2`, then

  `|g b - g a| ≤ √M · √(2(π/4)^{2-γ}/(γ-1)) · (b-a)^{(γ-1)/2}`. -/
private theorem cs_rate {γ M a b : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) (hM : 0 ≤ M)
    {g g' : ℝ → ℝ}
    (hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' x) x)
    (hcont : ContinuousOn g' (Set.uIcc a b))
    (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2)
    (hint : ∫ x in a..b, (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) ≤ M) :
    |g b - g a| ≤ Real.sqrt M * Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
      * (b - a) ^ ((γ - 1) / 2) := by
  have hγm1 : 0 < γ - 1 := by linarith
  have hsin : ∀ x ∈ Set.uIcc a b, 0 < Real.sin (2 * x) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [Real.pi_pos, hx.2])
  -- the fundamental theorem of calculus on `[a,b]`
  have hder' : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact hder x ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hFTC : ∫ x in a..b, g' x = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder' hcont.intervalIntegrable
  -- the two Cauchy–Schwarz factors
  set A₁ : ℝ → ℝ := fun x => g' x * (Real.sin (2 * x)) ^ ((2 - γ) / 2) with hA₁
  set A₂ : ℝ → ℝ := fun x => (Real.sin (2 * x)) ^ ((γ - 2) / 2) with hA₂
  have hsincont : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcont₁ : ContinuousOn A₁ (Set.uIcc a b) :=
    hcont.mul (hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsin x hx))))
  have hcont₂ : ContinuousOn A₂ (Set.uIcc a b) :=
    hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsin x hx)))
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab.le hcont₁ hcont₂
  -- pointwise identities
  have hprod : ∀ x ∈ Set.uIcc a b, A₁ x * A₂ x = g' x := by
    intro x hx
    have hs := hsin x hx
    have h1 : (Real.sin (2 * x)) ^ ((2 - γ) / 2) * (Real.sin (2 * x)) ^ ((γ - 2) / 2) = 1 := by
      rw [← Real.rpow_add hs, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]
    simp only [hA₁, hA₂]
    rw [mul_assoc, h1, mul_one]
  have hsq₁ : ∀ x ∈ Set.uIcc a b, (A₁ x) ^ 2 = (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    have hs := hsin x hx
    simp only [hA₁]
    rw [mul_pow, rpow_sq hs.le, show 2 * ((2 - γ) / 2) = 2 - γ by ring]
  have hsq₂ : ∀ x ∈ Set.uIcc a b, (A₂ x) ^ 2 = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    have hs := hsin x hx
    simp only [hA₂]
    rw [rpow_sq hs.le, show 2 * ((γ - 2) / 2) = γ - 2 by ring]
  have hprodI : ∫ x in a..b, A₁ x * A₂ x = ∫ x in a..b, g' x :=
    intervalIntegral.integral_congr hprod
  have hsq₁I : ∫ x in a..b, (A₁ x) ^ 2
      = ∫ x in a..b, (g' x) ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) :=
    intervalIntegral.integral_congr hsq₁
  have hsq₂I : ∫ x in a..b, (A₂ x) ^ 2 = ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2) :=
    intervalIntegral.integral_congr hsq₂
  -- the `sin^{γ-2}` integral
  have hKnn : 0 ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)) hγm1.le
  have hsinInt : ∫ x in a..b, (Real.sin (2 * x)) ^ (γ - 2)
      ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1) := by
    have h := Work.FTS_RegExport.THL.integral_sin_two_rpow_le (p := γ - 1)
      (by linarith) (by linarith) ha hab.le hb
    rwa [show γ - 1 - 1 = γ - 2 by ring, show 1 - (γ - 1) = 2 - γ by ring] at h
  have hsqrt₂ : Real.sqrt (∫ x in a..b, (A₂ x) ^ 2)
      ≤ Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1)) * (b - a) ^ ((γ - 1) / 2) := by
    have hA2le : ∫ x in a..b, (A₂ x) ^ 2
        ≤ 2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1) := by
      rw [hsq₂I]; exact hsinInt
    have h1 : Real.sqrt (∫ x in a..b, (A₂ x) ^ 2)
        ≤ Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1)) :=
      Real.sqrt_le_sqrt hA2le
    have h2 : Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1) * (b - a) ^ (γ - 1))
        = Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1)) * (b - a) ^ ((γ - 1) / 2) := by
      rw [Real.sqrt_mul hKnn]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ b - a),
        show (γ - 1) * (1 / 2) = (γ - 1) / 2 by ring]
    rw [h2] at h1; exact h1
  have hsqrt₁ : Real.sqrt (∫ x in a..b, (A₁ x) ^ 2) ≤ Real.sqrt M := by
    refine Real.sqrt_le_sqrt ?_
    rw [hsq₁I]; exact hint
  calc |g b - g a| = |∫ x in a..b, g' x| := by rw [hFTC]
    _ = |∫ x in a..b, A₁ x * A₂ x| := by rw [hprodI]
    _ ≤ Real.sqrt (∫ x in a..b, (A₁ x) ^ 2) * Real.sqrt (∫ x in a..b, (A₂ x) ^ 2) := hcs
    _ ≤ Real.sqrt M * (Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
          * (b - a) ^ ((γ - 1) / 2)) :=
        mul_le_mul hsqrt₁ hsqrt₂ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt M * Real.sqrt (2 * (Real.pi / 4) ^ (2 - γ) / (γ - 1))
          * (b - a) ^ ((γ - 1) / 2) := by ring

/-! ## The target -/

theorem classCSinRate {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |f z θ| ≤ C * Work.FTS.StrongGlobal.Xn6 α f
          * (min θ (Real.pi / 2 - θ)) ^ ((Work.Spaces.gam α - 1) / 2) := by
  obtain ⟨Csl, hCslpos, hsl⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
  have hγ1 : 1 < Work.Spaces.gam α := by
    have h := Work.Spaces.gam_sub_one α; linarith
  have hγ2 : Work.Spaces.gam α ≤ 2 := by
    have h := Work.Spaces.gam_sub_one α; linarith
  have hp : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one α]; linarith
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hKpos : 0 < 2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1) :=
    div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hpi4 _)) hp
  refine ⟨Real.sqrt Csl * Real.sqrt
      (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1)),
    mul_pos (Real.sqrt_pos.mpr hCslpos) (Real.sqrt_pos.mpr hKpos), ?_⟩
  intro f hf z hz θ hθ
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 6 (by norm_num) hf.mem
  -- ## the slice derivative and its continuity
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun y : ℝ => f z y) (Work.Spaces.pth f z x) x := by
    intro x hx
    have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => f z y)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hF.curry_θ hz
    have hc : ContDiffOn ℝ 1 (fun y : ℝ => f z y) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hc0.of_le (WithTop.coe_le_coe.mpr le_top)
    have hd1 : DifferentiableOn ℝ (fun y : ℝ => f z y) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hc.differentiableOn one_ne_zero
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => f z y) x :=
      hd1.differentiableAt (isOpen_Ioo.mem_nhds hx)
    simpa only [Work.Spaces.pth] using hdiff.hasDerivAt
  have hcont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 →
      ContinuousOn (fun x : ℝ => Work.Spaces.pth f z x) (Set.uIcc a b) := by
    intro a b ha hab hb
    have hc0 : ContDiffOn ℝ Work.Stability.smoothOrder (fun y : ℝ => Work.Spaces.pth f z y)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hF.pth.curry_θ hz
    refine hc0.continuousOn.mono ?_
    rw [Set.uIcc_of_le hab]
    exact fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  -- ## the `z`-uniform angular slice bound, on sub-intervals
  have hslice : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < Real.pi / 2 →
      ∫ x in a..b, (Work.Spaces.pth f z x) ^ 2 * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)
        ≤ Csl * Work.Spaces.HkSq α 6 f := by
    intro a b ha hab hb
    have hint : IntegrableOn (fun x : ℝ => (Work.Spaces.mixed 0 1 f z x) ^ 2
        * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      Work.FTS.StrongEps.integrableOn_mixed_sq_rpow6 hF h6 0 1 (by norm_num) (by norm_num) hz
    have hcongr : ∫ x in a..b, (Work.Spaces.pth f z x) ^ 2
          * (Real.sin (2 * x)) ^ (2 - Work.Spaces.gam α)
        = ∫ x in a..b, (Work.Spaces.mixed 0 1 f z x) ^ 2
          * (Real.sin (2 * x)) ^ (-(Work.Spaces.gam α)) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hab] at hx
      have hs : 0 < Real.sin (2 * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
          (by linarith [Real.pi_pos, hx.2])
      have hmix : Work.Spaces.mixed 0 1 f z x
          = Real.sin (2 * x) * Work.Spaces.pth f z x := rfl
      rw [hmix, Work.Spaces.pth]
      exact (mul_sq_mul_rpow_neg (a := deriv (fun y : ℝ => f z y) x)
        (γ := Work.Spaces.gam α) hs).symm
    rw [hcongr, intervalIntegral.integral_of_le hab]
    refine le_trans (setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
            (by linarith [Real.pi_pos, hx.2])) _))
      (Eventually.of_forall fun x hx =>
        ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩)) ?_
    exact hsl α f 0 1 hα hα1 hF h6 (by norm_num) (by norm_num) z hz
  -- ## the angular endpoint traces
  have htr0 : Tendsto (fun y : ℝ => f z y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero (α := α) hα (k := 6) hf.tr
      (a := 0) (b := 0) (by norm_num) (z := z) hz
    simpa using h
  have htrpi : Tendsto (fun y : ℝ => f z y) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_pi (α := α) hα (k := 6) hf.tr
      (a := 0) (b := 0) (by norm_num) (z := z) hz
    simpa using h
  -- ## the one-step estimate
  set B : ℝ := Real.sqrt (Csl * Work.Spaces.HkSq α 6 f)
    * Real.sqrt (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1))
    with hBdef
  have hBnn : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hstep : ∀ {a b : ℝ}, 0 < a → a < b → b < Real.pi / 2 →
      |f z b - f z a| ≤ B * (b - a) ^ ((Work.Spaces.gam α - 1) / 2) := by
    intro a b ha hab hb
    have hM : 0 ≤ Csl * Work.Spaces.HkSq α 6 f :=
      mul_nonneg hCslpos.le (Work.Spaces.HkSq_nonneg α 6 f)
    have h1 := cs_rate hγ1 hγ2 hM hder (hcont ha hab.le hb) ha hab hb (hslice ha hab.le hb)
    rw [hBdef]
    exact h1
  -- ## the two endpoint rates
  have hR : |f z θ| ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) := by
    have htend : Tendsto (fun t : ℝ => B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2)
        + |f z t|) (𝓝[<] (Real.pi / 2))
        (𝓝 (B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2))) := by
      have h := (tendsto_const_nhds (x := B * (Real.pi / 2 - θ)
        ^ ((Work.Spaces.gam α - 1) / 2))).add htrpi.abs
      simpa using h
    have hev : ∀ᶠ t in 𝓝[<] (Real.pi / 2),
        |f z θ| ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by
      filter_upwards [Ioo_mem_nhdsLT hθ.2] with t ht
      have h1 : |f z t - f z θ| ≤ B * (t - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        hstep hθ.1 ht.1 ht.2
      have h2 : (t - θ) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        Real.rpow_le_rpow (le_of_lt (sub_pos.mpr ht.1)) (sub_le_sub_right ht.2.le θ)
          (div_nonneg hp.le (by norm_num))
      have h3 : B * (t - θ) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) :=
        mul_le_mul_of_nonneg_left h2 hBnn
      calc |f z θ| = |f z θ - f z t + f z t| := by ring_nf
        _ ≤ |f z θ - f z t| + |f z t| := abs_add_le _ _
        _ = |f z t - f z θ| + |f z t| := by rw [abs_sub_comm]
        _ ≤ B * (Real.pi / 2 - θ) ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by linarith
    exact ge_of_tendsto htend hev
  have hL : |f z θ| ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) := by
    have htend : Tendsto (fun t : ℝ => B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t|)
        (𝓝[>] (0 : ℝ)) (𝓝 (B * θ ^ ((Work.Spaces.gam α - 1) / 2))) := by
      have h := (tendsto_const_nhds (x := B * θ ^ ((Work.Spaces.gam α - 1) / 2))).add htr0.abs
      simpa using h
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        |f z θ| ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by
      filter_upwards [Ioo_mem_nhdsGT hθ.1] with t ht
      have h1 : |f z θ - f z t| ≤ B * (θ - t) ^ ((Work.Spaces.gam α - 1) / 2) :=
        hstep ht.1 ht.2 hθ.2
      have h2 : (θ - t) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ θ ^ ((Work.Spaces.gam α - 1) / 2) :=
        Real.rpow_le_rpow (le_of_lt (sub_pos.mpr ht.2)) (sub_le_self θ ht.1.le)
          (div_nonneg hp.le (by norm_num))
      have h3 : B * (θ - t) ^ ((Work.Spaces.gam α - 1) / 2)
          ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) :=
        mul_le_mul_of_nonneg_left h2 hBnn
      calc |f z θ| = |f z θ - f z t + f z t| := by ring_nf
        _ ≤ |f z θ - f z t| + |f z t| := abs_add_le _ _
        _ ≤ B * θ ^ ((Work.Spaces.gam α - 1) / 2) + |f z t| := by linarith
    exact ge_of_tendsto htend hev
  -- ## assembly
  have hB : B = Real.sqrt Csl * Real.sqrt
      (2 * (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (Work.Spaces.gam α - 1))
      * Work.FTS.StrongGlobal.Xn6 α f := by
    rw [hBdef, Work.FTS.StrongGlobal.Xn6, Work.Spaces.HkNorm,
      Real.sqrt_mul hCslpos.le (Work.Spaces.HkSq α 6 f)]
    ring
  rw [hB] at hL hR
  rcases le_total θ (Real.pi / 2 - θ) with h | h
  · rw [min_eq_left h]; exact hL
  · rw [min_eq_right h]; exact hR

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
end
