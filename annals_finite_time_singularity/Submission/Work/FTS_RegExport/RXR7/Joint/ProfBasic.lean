import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.FTS_RegExport.RXT.jc3
import Submission.Work.FTS_RegExport.RXR7.Joint.CLM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

/-! ## §2  The slab identity `Prof α g = F_* + g` -/

/-- On the open quadrant and for `τ ≥ 0`, the full profile `Prof α g = profFull α (extG (GR α g))`
agrees with `F_* + g`: the sanitiser `gS` and the right-Taylor extension `tauExt` are inert there
and the `z ≤ 0` branch of `extG` is inactive. -/
theorem Prof_eq {α : ℝ} {g : Fam} {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ Real.pi / 2) (hτ : 0 ≤ τ) :
    Prof α g z θ τ = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ τ := by
  simp only [Prof, Work.FTS.Regularity.profFull_apply, GR,
    Work.FTS.FinalV2.extG_gS_of_mem α (Work.FTS.FinalV2.tauExt g) hθ0 hθ1,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ,
    Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- The slab form of the identity. -/
theorem Prof_eq_on_slab {α : ℝ} {g : Fam} {S : ℝ} :
    Set.EqOn (fun p : ℝ × ℝ × ℝ => Prof α g p.1 p.2.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) p.1 p.2.1 + g p.1 p.2.1 p.2.2)
      (R7Slab S) := fun p hp =>
  Prof_eq hp.1 hp.2.1.1.le hp.2.1.2.le hp.2.2.1

/-! ## §3  Joint continuity of the order-`≤ 3` jets (from `RXT.jc3`) -/

theorem mixedJets_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) {j i : ℕ}
    (hji : j + i ≤ 3) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (slice g p.2.2) p.1 p.2.1)
      (R7Slab S) :=
  Work.FTS_RegExport.RXT.jc3 hα hα13 hOK S hS j i hji

/-! ## §4  Smoothness of the explicit profile `F_*` -/

/-- `F_* = α (Γ/c) 2z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem Fstar_contDiffAt {α : ℝ} {n : WithTop ℕ∞} {q : ℝ × ℝ}
    (h1 : 0 < q.1) (h2 : 0 < q.2) (h3 : q.2 < Real.pi / 2) :
    ContDiffAt ℝ n (fun q' : ℝ × ℝ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2) q := by
  have hsin : 0 < Real.sin q.2 :=
    Real.sin_pos_of_pos_of_lt_pi h2 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos q.2 :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h3⟩
  have hbase : Real.sin q.2 * Real.cos q.2 ^ 2 ≠ 0 := by positivity
  have h1' : ContDiffAt ℝ n (fun q' : ℝ × ℝ => Real.sin q'.2 * Real.cos q'.2 ^ 2) q :=
    ((Real.contDiff_sin.contDiffAt).comp q contDiffAt_snd).mul
      (((Real.contDiff_cos.contDiffAt).comp q contDiffAt_snd).pow 2)
  have h2' : ContDiffAt ℝ n
      (fun q' : ℝ × ℝ => (Real.sin q'.2 * Real.cos q'.2 ^ 2) ^
        ((Work.FTS.Regularity.pExp α) / 3)) q :=
    h1'.rpow_const_of_ne hbase
  have h4 : ContDiffAt ℝ n (fun q' : ℝ × ℝ =>
      (Real.sin q'.2 * Real.cos q'.2 ^ 2) ^ ((Work.FTS.Regularity.pExp α) / 3)
        * (Work.Spaces.c (Work.FTS.Regularity.pExp α))⁻¹) q := h2'.mul contDiffAt_const
  have h5 : ContDiffAt ℝ n (fun q' : ℝ × ℝ => 2 * q'.1 / (1 + q'.1) ^ 2) q :=
    (((contDiffAt_const (x := q) (c := (2 : ℝ))).mul contDiffAt_fst).div
      (((contDiffAt_const (x := q) (c := (1 : ℝ))).add contDiffAt_fst).pow 2) (by positivity))
  have h6 := (contDiffAt_const (x := q) (c := Work.FTS.Regularity.pExp α)).mul (h4.mul h5)
  have hfun : (fun q' : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2)
      = fun q' : ℝ × ℝ => Work.FTS.Regularity.pExp α *
          (((Real.sin q'.2 * Real.cos q'.2 ^ 2) ^ ((Work.FTS.Regularity.pExp α) / 3)
            * (Work.Spaces.c (Work.FTS.Regularity.pExp α))⁻¹) * (2 * q'.1 / (1 + q'.1) ^ 2)) := by
    funext q'
    rw [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.Gam, div_eq_mul_inv]
    ring
  rw [hfun]
  exact h6

/-- `F_*` is differentiable on the open quadrant. -/
theorem Fstar_differentiableAt {α : ℝ} {q : ℝ × ℝ}
    (h1 : 0 < q.1) (h2 : 0 < q.2) (h3 : q.2 < Real.pi / 2) :
    DifferentiableAt ℝ (fun q' : ℝ × ℝ =>
      Work.Construction.Fstar (Work.FTS.Regularity.pExp α) q'.1 q'.2) q :=
  (Fstar_contDiffAt (n := 1) h1 h2 h3).differentiableAt one_ne_zero

/-! ## §5  The candidate derivative field of the profile -/

/-- The `z`-coordinate of the candidate derivative of `Prof` on the slab. -/
def FPz (α : ℝ) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) p.1 p.2.1
    + Work.Spaces.mixed 1 0 (slice g p.2.2) p.1 p.2.1 / p.1

/-- The `θ`-coordinate of the candidate derivative of `Prof` on the slab. -/
def FPt (α : ℝ) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) p.1 p.2.1
    + Work.Spaces.mixed 0 1 (slice g p.2.2) p.1 p.2.1 / Real.sin (2 * p.2.1)

/-- The `τ`-coordinate of the candidate derivative of `Prof` on the slab (from the transport
form of the profile equation). -/
def FR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (p : ℝ × ℝ × ℝ) : ℝ :=
  -K7 α Φs E g p.1 p.2.1 p.2.2

/-- The candidate derivative of the R7 profile at a point of the slab. -/
def ProfD (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (p : ℝ × ℝ × ℝ) :
    (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  tripleCLM (FPz α g p) (FPt α g p) (FR α Φs E g p)

theorem ProfD_apply (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (p v : ℝ × ℝ × ℝ) :
    ProfD α Φs E g p v = FPz α g p * v.1 + FPt α g p * v.2.1 + FR α Φs E g p * v.2.2 :=
  tripleCLM_apply _ _ _ _

/-- `mixed 1 0 f = z ∂_z f`. -/
theorem mixed_one_zero (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 f z θ = z * Work.Spaces.pz f z θ := rfl

/-- `mixed 0 1 f = sin(2θ) ∂_θ f`. -/
theorem mixed_zero_one (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl

theorem pz_eq_mixed_div (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz f z θ = Work.Spaces.mixed 1 0 f z θ / z := by
  rw [mixed_one_zero, mul_div_cancel_left₀ _ hz]

theorem pth_eq_mixed_div (f : ℝ → ℝ → ℝ) {z θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) :
    Work.Spaces.pth f z θ = Work.Spaces.mixed 0 1 f z θ / Real.sin (2 * θ) := by
  rw [mixed_zero_one, mul_div_cancel_left₀ _ h]

/-- The non-vanishing of `sin 2θ` on the slab. -/
theorem sin_two_ne_zero {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-! ## §6  Joint continuity of the candidate field on the slab -/

/-- The `z`-coordinate `FPz` is continuous on the slab. -/
theorem FPz_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hFz : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => FPz α g p) (R7Slab S) := by
  refine hFz.add ?_
  refine (mixedJets_contOn hS hα hα13 hOK (j := 1) (i := 0) (by norm_num)).div
    continuous_fst.continuousOn (fun p hp => ne_of_gt hp.1)

/-- The `θ`-coordinate `FPt` is continuous on the slab. -/
theorem FPt_contOn {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hFt : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => FPt α g p) (R7Slab S) := by
  refine hFt.add ?_
  refine (mixedJets_contOn hS hα hα13 hOK (j := 0) (i := 1) (by norm_num)).div
    ((Real.continuous_sin.comp (continuous_const.mul (continuous_fst.comp continuous_snd))).continuousOn)
    (fun p hp => sin_two_ne_zero hp.2.1.1 hp.2.1.2)

/-- The candidate field is continuous on the slab. -/
theorem ProfD_contOn {α : ℝ} {Φs' : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hPz : ContinuousOn (fun p : ℝ × ℝ × ℝ => FPz α g p) (R7Slab S))
    (hPt : ContinuousOn (fun p : ℝ × ℝ × ℝ => FPt α g p) (R7Slab S))
    (hK : ContinuousOn (fun p : ℝ × ℝ × ℝ => K7 α Φs' E g p.1 p.2.1 p.2.2) (R7Slab S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs' E g p) (R7Slab S) := by
  have hfun : (fun p : ℝ × ℝ × ℝ => ProfD α Φs' E g p)
      = fun p => FPz α g p • p1 + FPt α g p • p2 + (-K7 α Φs' E g p.1 p.2.1 p.2.2) • p3 := by
    funext p; rfl
  rw [hfun]
  exact ((hPz.smul continuousOn_const).add (hPt.smul continuousOn_const)).add
    (hK.neg.smul continuousOn_const)

end Work.FTS_RegExport.RXR7
