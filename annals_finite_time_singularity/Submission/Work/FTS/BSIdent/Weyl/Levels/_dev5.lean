import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev5

open Filter Set MeasureTheory
open scoped Topology

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

noncomputable def GG (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ

theorem GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ

theorem GG_of_neg {w θ : ℝ} (hθ : θ < 0) : GG Φ τ w θ = -(Φ w (-θ) τ) :=
  Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ)

theorem contDiffAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : -1 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  hsm w θ hw (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])

theorem diffAt2_GG_of_ne {w θ : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw : -1 < w) (hθ : θ ≠ 0) (hθ' : |θ| < Real.pi / 2 + 1) :
    Work.Cyl.DiffAt2 (GG Φ τ) w θ := by
  have hθ'' : |(-θ)| < Real.pi / 2 + 1 := by rwa [abs_neg]
  rcases lt_or_gt_of_ne hθ with hlt | hgt
  · have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w, θ) :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hlt
    have hev : (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) =ᶠ[𝓝 (w, θ)]
        (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) := by
      filter_upwards [hnb] with p hp
      exact GG_of_neg (Φ := Φ) (τ := τ) hp
    have hσ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2)) (w, θ) :=
      contDiffAt_fst.prodMk contDiffAt_snd.neg
    have hΦc : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (w, -θ) :=
      contDiffAt_Phi (τ := τ) (Φ := Φ) hsm hw hθ''
    have hcomp : DifferentiableAt ℝ (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ) (w, θ) := by
      have hcc := ContDiffAt.comp (x := (w, θ)) (f := fun p : ℝ × ℝ => (p.1, -p.2))
        (g := fun q : ℝ × ℝ => Φ q.1 q.2 τ) hΦc hσ
      exact hcc.differentiableAt (by norm_num)
    exact (hcomp.neg).congr_of_eventuallyEq hev
  · have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w, θ) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hgt
    have hev : (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) =ᶠ[𝓝 (w, θ)]
        (fun p : ℝ × ℝ => Φ p.1 p.2 τ) := by
      filter_upwards [hnb] with p hp
      exact GG_of_nonneg (Φ := Φ) (τ := τ) hp.le
    have hΦc : DifferentiableAt ℝ (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (w, θ) :=
      (contDiffAt_Phi (τ := τ) (Φ := Φ) hsm hw hθ').differentiableAt (by norm_num)
    exact hΦc.congr_of_eventuallyEq hev

/-! ## The meridian stream function as `psiCore` -/

theorem merPsiT_eq_core (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) {τ : ℝ} (hτ : τ = Physical.clockInv C t) :
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t
      = Work.FTS.BSIdent.Cyl.psiCore (Work.FTS.Regularity.pExp α) (A τ)⁻¹ (B τ) (GG Φ τ) := by
  subst hτ
  rw [Work.FTS.BSIdent.Cyl.merPsiT_eq_psiCore]
  rfl

theorem merPsiT_apply_core (α : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.BSIdent.Fam)
    (C : Physical.PhysClock) (t : ℝ) {τ : ℝ} (hτ : τ = Physical.clockInv C t) (r z : ℝ) :
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z
      = Work.Cyl.rhoP r z ^ 2 * (A τ)⁻¹ * GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α
          / B τ) (Work.Cyl.thetaP r z) := by
  rw [merPsiT_eq_core α A B Φ C t hτ]
  rfl

/-- `ψ` vanishes on the plane `θ = 0`. -/
theorem merPsiT_zero_snd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {τ : ℝ} (hτ : τ = Physical.clockInv C t)
    (hB : 0 < B τ) (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {r : ℝ} (hr : 0 < r) :
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r 0 = 0 := by
  rw [merPsiT_apply_core α A B Φ C t hτ]
  have hθ : Work.Cyl.thetaP r 0 = 0 := by simp [Work.Cyl.thetaP]
  rw [hθ]
  have hw : 0 < Work.Cyl.rhoP r 0 ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr 0) _) hB
  rw [GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl, h0 _ hw, mul_zero]

/-- `∂_rψ` vanishes on the plane `θ = 0`. -/
theorem pdR_merPsiT_zero_snd {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {τ : ℝ} (hτ : τ = Physical.clockInv C t)
    (hB : 0 < B τ) (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) {r : ℝ} (hr : 0 < r) :
    Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0 = 0 := by
  have hev : (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' 0)
      =ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with r' hr'
    exact merPsiT_zero_snd hτ hB h0 hr'
  show deriv (fun r' : ℝ => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r' 0) r = 0
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- `ψ/r` is `ρ c (Φ̂/cos θ)`. -/
theorem merPsiT_div_fst {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ} {τ : ℝ} (hτ : τ = Physical.clockInv C t)
    {r z : ℝ} (hr : 0 < r) :
    Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z / r
      = Work.Cyl.rhoP r z * (A τ)⁻¹
        * (GG Φ τ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ)
            (Work.Cyl.thetaP r z) / Real.cos (Work.Cyl.thetaP r z)) := by
  rw [merPsiT_apply_core α A B Φ C t hτ]
  have hcos := Work.Cyl.cos_thetaP hr z
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  rw [hcos]
  field_simp

end Work.FTS.BSIdent.Weyl.Dev5
