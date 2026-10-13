import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS_RegExport.RXT.C2Assemble

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Psi` — the two open-quadrant inputs of `coeff_C2`

* `slice (psiR α Φs E (tauExt g)) τ` agrees on `Q0` with `PsiCan Φs E g · τ`, hence is `C³`
  there (`FTS_FinalLeaves.psiCan_C3_proved`).
* `F(τ) = F_* + gS α (tauExt g)(τ)` — the two summands are `C²` on `Q0`: `F_*` because `Γ` is
  smooth on the open interval and `F_{*,rad}(z) = 2z/(1+z)²`, the `g`-part because
  `gS α (tauExt g) = g(τ)` on the open quadrant and `RegPkgMin.c4` gives `C⁴`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (DynOK' LimApprox)
open Work.FTS.RegExportIface.RXT (GR ΦR)

set_option autoImplicit false

/-! ## `Γ` and `F_{*,rad}` are smooth on the open quadrant -/

theorem contDiffOn_Gam_Q0 (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Work.FTS.EllipticEst.Q0 := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hp.2.1, Real.pi_pos]) (by linarith [hp.2.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

theorem contDiffOn_FM_Fstar (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden (fun z hz => pow_ne_zero 2 (by
    have hz' : (0 : ℝ) < z := hz
    linarith))
  refine h.congr (fun z _ => ?_)
  simp only [Pi.div_apply, Work.FM.Fstar]

/-- A function of `z` alone is `C^n` on `Q0` when it is `C^n` on `(0,∞)`. -/
theorem contDiffOn_fst_of {n : ℕ} {a : ℝ → ℝ} (ha : ContDiffOn ℝ n a (Set.Ioi 0)) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 :=
  ha.comp contDiffOn_fst (fun p hp => hp.1)

theorem contDiffOn_Fstar_Q0 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 := by
  have hGam : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := contDiffOn_Gam_Q0 α 2
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      Work.FTS.EllipticEst.Q0 :=
    hGam.div contDiffOn_const (fun p hp => hc)
  have h2 : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => α * (Work.Spaces.Gam α p.2 / Work.Spaces.c α))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul h1
  have h3 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Work.FM.Fstar p.1)
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_fst_of (contDiffOn_FM_Fstar 2)
  exact (h2.mul h3).congr (fun p _ => rfl)

/-! ## The sanitised family `GR α g` agrees with `g` on the open quadrant -/

theorem GR_of_quad {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : GR α g z θ τ = g z θ τ := by
  have h : GR α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ := by
    simp only [GR, Work.FTS.FinalV2.gS, hz, h0, h1, and_self, ↓reduceIte]
  rw [h, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

theorem slice_GR_eq {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {z θ : ℝ}
    (hz : 0 < z) (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) :
    slice (GR α g) τ z θ = slice g τ z θ :=
  GR_of_quad hτ hz h0 h1

theorem contDiffOn_slice_GR_Q0 {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hOK : DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) (τ : ℝ) (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 2 (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := by
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  refine (h4.of_le (by norm_num)).congr ?_
  intro p hp
  exact slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le

/-- **`F(τ) = F_* + g(τ)` is `C²` on the open quadrant.** -/
theorem contDiffOn_Ftau_Q0 {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hOK : DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) (τ : ℝ) (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ))
      Work.FTS.EllipticEst.Q0 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  exact (contDiffOn_Fstar_Q0 hαG hαG1).add (contDiffOn_slice_GR_Q0 hOK τ hτ)

/-! ## The stream function `slice (psiR α Φs E (tauExt g)) τ` is `C³` -/

theorem slice_PhiR_eq {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ : ℝ}
    (hτ : 0 ≤ τ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    slice (ΦR α Φs E g) τ z θ = Work.FTS.Nonlin.PsiCan Φs E g z θ τ := by
  have h1 : slice (ΦR α Φs E g) τ z θ
      = Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g) z θ τ := by
    show Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z θ τ = _
    rw [Work.FTS.RegExportIface.psiR_of_mem hz hθ0 hθ1]
  rw [h1]
  simp only [Work.FTS.Nonlin.PsiCan, Work.FTS.FinalV2.slice_tauExt g hτ]

theorem contDiffOn_slice_PhiR_Q0 {α C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hOK : DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) (τ : ℝ) (hτ : 0 ≤ τ) :
    ContDiffOn ℝ 3 (Function.uncurry (slice (ΦR α Φs E g) τ)) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS_FinalLeaves.psiCan_C3_proved hEL3 hStar hOK τ hτ).congr
    (fun p hp => slice_PhiR_eq hτ hp.1 hp.2.1 hp.2.2)

end Work.FTS_RegExport.RXT
