import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.VopGen.a11OfCore
import Submission.Work.FTS.ClassC.VopGen.truncFacts
import Submission.Work.FTS.ClassC.VopGen.truncHonest
import Submission.Work.FTS.ClassC.VopGen.truncSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.Core.truncSetup` — auxiliary facts for the truncation half

Shared infrastructure for `Work.FTS.ClassC.VopGen.Core.truncProof` (`VopGen.TruncStmt`):

* the a.e. description of the product domain `Iz ×ˢ Iθ` and the continuity of the angular
  weight on the open quadrant (in the exact syntactic shapes used later);
* the product rules for `χ²·X` and `χ²·X·σ`;
* the Clairaut transfer of the `(1,2)`-slot, the Agmon slice inequality in the `D_z∂_θ²` form,
  the joint integrability of the pairing `w²·(X·D_zY·σ)` and the two majorant facts.
-/

namespace Work.FTS.ClassC.VopGen.Core

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ)

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-- A.e. points of `Iz ×ˢ Iθ` lie in the open quadrant. -/
theorem ae_mem_Q0_prod : ∀ᵐ p ∂(volume.restrict (Iz ×ˢ Iθ)), p ∈ Work.FTS.EllipticEst.Q0 := by
  have h1 : ∀ᵐ p ∂(volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))),
      p ∈ Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioo)
      (fun p hp => hp)
  have hcomp : (volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) : Measure (ℝ × ℝ))
      = volume.restrict (Iz ×ˢ Iθ) :=
    Work.FTS.ClassC.aslotAux.BslOpPth.restrict_prod_eq_restrict_Q0.symm.trans
      Work.FTS.ClassC.aslotAux.BslOpPth.restrict_rect_eq.symm
  rwa [hcomp] at h1

/-- The angular weight `sgm α θ = sin(2θ)^{2-γ}` is continuous on the open quadrant (in the
exact syntactic shape used by the integrands below). -/
theorem continuousOn_sgm_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => sgm α p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  simpa only [sgm] using Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_sigma_Q0 α

/-- The product rule for `χ²·X` on a slice of the open quadrant. -/
theorem deriv_chi_sq_mul {χ : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hχd : Differentiable ℝ χ)
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    z * deriv (fun z' => (χ z') ^ 2 * X z' θ) z
      = (2 * (z * χ z * deriv χ z)) * X z θ + (χ z) ^ 2 * (z * Work.Spaces.pz X z θ) := by
  have h1 : HasDerivAt (fun z' => (χ z') ^ 2) (2 * (χ z) ^ (2 - 1) * deriv χ z) z :=
    (hχd.differentiableAt.hasDerivAt).pow 2
  have h2 : HasDerivAt (fun z' => X z' θ) (Work.Spaces.pz X z θ) z :=
    hX.hasDerivAt_slice hθ hz
  have h3 : deriv (fun z' => χ z' ^ 2 * X z' θ) z
      = 2 * χ z ^ (2 - 1) * deriv χ z * X z θ + χ z ^ 2 * Work.Spaces.pz X z θ := by
    rw [show (fun z' => χ z' ^ 2 * X z' θ) = (fun z' => χ z' ^ 2) * (fun z' => X z' θ) from rfl]
    exact (h1.mul h2).deriv
  rw [h3]
  norm_num
  ring

/-- The same product rule with the angular weight attached. -/
theorem deriv_chi_sq_mul_sgm {α : ℝ} {χ : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : Work.FTS.EllipticEst.SmoothOpen X) (hχd : Differentiable ℝ χ)
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    z * deriv (fun z' => (χ z') ^ 2 * X z' θ * sgm α θ) z
      = sgm α θ * ((2 * (z * χ z * deriv χ z)) * X z θ + (χ z) ^ 2
          * (z * Work.Spaces.pz X z θ)) := by
  have h1 : (fun z' => (χ z') ^ 2 * X z' θ * sgm α θ)
      = (fun z' => sgm α θ * ((χ z') ^ 2 * X z' θ)) := by
    funext y; ring
  rw [h1, deriv_const_mul_field]
  rw [show z * (sgm α θ * deriv (fun z' => χ z' ^ 2 * X z' θ) z)
      = sgm α θ * (z * deriv (fun z' => χ z' ^ 2 * X z' θ) z) from by ring,
    deriv_chi_sq_mul hX hχd hθ hz]

/-- **The `(1,2)`-slot of `A = z²∂_z²Ψ` in the `D_z(∂_θ²A)` form** (Clairaut). -/
theorem clairautSlot {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨_, _, prZ, _⟩ := slotFacts_ddz hα1 hα hα4 h
  have hAof : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  refine MeasureTheory.Integrable.congr prZ ?_
  filter_upwards [ae_mem_Q0_prod] with p hp
  rw [Work.FTS.EllipticEst.Prop.pthIter2_Dz_eq_of_smooth hAof (z := p.1) (θ := p.2) hp]
  rfl

/-- Slicewise honesty of the Clairaut slot. -/
theorem clairautSlice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(volume.restrict Iz),
      IntegrableOn (fun θ => (Work.Spaces.Dz (YY Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iθ := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨slZ, _, _, _⟩ := slotFacts_ddz hα1 hα hα4 h
  have hAof : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  filter_upwards [slZ, Work.FTS.EllipticEst.Prop.ae_restrict_Iz_pos] with z hz hzpos
  refine MeasureTheory.Integrable.congr hz ?_
  refine Work.FTS.EllipticEst.Prop.ae_restrict_Iθ (fun θ hθ => ?_)
  rw [Work.FTS.EllipticEst.Prop.pthIter2_Dz_eq_of_smooth hAof (z := z) (θ := θ)
    ⟨hzpos, hθ⟩]
  rfl

/-- Outer integrability of the Clairaut slot. -/
theorem clairautOuter {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (Work.Spaces.Dz (YY Ψ) z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
      (volume.restrict Iz) := by
  have h := (show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) from by
    rw [prod_restrict_eq_rect]; exact clairautSlot hα hα4 h)
  exact h.integral_prod_left

/-- **The Agmon slice inequality in the `D_z(∂_θ²A)` form** (`X = D_z(z²∂_z²Ψ)`,
`Y = ∂_θ²(z²∂_z²Ψ)`). -/
theorem agmonSlice (hSlice : SliceAgmonStmt) {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(volume.restrict Iz),
      (∫ θ in Iθ, (Work.Spaces.pth (XX Ψ) z θ) ^ 2 * sgm α θ)
        ≤ -(∫ θ in Iθ, XX Ψ z θ * Work.Spaces.Dz (YY Ψ) z θ * sgm α θ) := by
  have hAof : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)
  have hsl0 := hSlice α F Ψ hα hα4 h
  filter_upwards [hsl0, Work.FTS.EllipticEst.Prop.ae_restrict_Iz_pos] with z hz hzpos
  have hcong : (∫ θ in Iθ, Work.Spaces.Dz (Aof Ψ) z θ
        * (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Aof Ψ))) z θ
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Iθ, XX Ψ z θ * Work.Spaces.Dz (YY Ψ) z θ
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    refine Work.FTS.EllipticEst.Prop.setIntegral_Iθ_congr (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.Prop.pthIter2_Dz_eq_of_smooth hAof (z := z) (θ := θ)
      ⟨hzpos, hθ.1, hθ.2⟩]
    rfl
  rw [hcong] at hz
  exact hz

/-- **Joint integrability of the pairing** `w²·(X·D_zY·σ)`. -/
theorem pairIntegrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (w p.1) ^ 2 * (XX Ψ p.1 p.2 * Work.Spaces.Dz (YY Ψ) p.1 p.2
        * sgm α p.2)) (Iz ×ˢ Iθ) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨_, _, prX, _⟩ := slotFacts_pure hα1 hα hα4 h 1 (by norm_num)
  have hXX : Work.FTS.EllipticEst.SmoothOpen (XX Ψ) :=
    (Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).Dz
  have hYY : Work.FTS.EllipticEst.SmoothOpen (YY Ψ) :=
    (Work.FTS.EllipticEst.Prop.aofSmoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).pth.pth
  have hmaj : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) (Iz ×ˢ Iθ) :=
    prX.add (clairautSlot hα hα4 h)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · have hwc : ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_w_sq_Q0
    have hXc : ContinuousOn (fun p : ℝ × ℝ => XX Ψ p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      smoothOpen_continuousOn hXX
    have hDY : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (YY Ψ) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      smoothOpen_continuousOn hYY.Dz
    have h4 : ContinuousOn (fun p : ℝ × ℝ => sgm α p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_sgm_Q0 α
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2 * (XX Ψ p.1 p.2
        * Work.Spaces.Dz (YY Ψ) p.1 p.2 * sgm α p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h5 := (hwc.mul (hXc.mul hDY)).mul h4
      convert h5 using 1
      ext p
      simp only [Pi.mul_apply]
      ring
    have h6 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    rwa [prod_restrict_eq_rect] at h6
  · refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_)
    have hs : 0 ≤ sgm α p.2 := by rw [sgm]; exact sigma_nonneg hp.2
    have hw : 0 ≤ (w p.1) ^ 2 := sq_nonneg _
    have h2 : 2 * |XX Ψ p.1 p.2| * |Work.Spaces.Dz (YY Ψ) p.1 p.2|
        ≤ (XX Ψ p.1 p.2) ^ 2 + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 := by
      have h := sq_nonneg (|XX Ψ p.1 p.2| - |Work.Spaces.Dz (YY Ψ) p.1 p.2|)
      rw [sub_sq, sq_abs, sq_abs] at h
      nlinarith [h]
    have hmid : |XX Ψ p.1 p.2| * |Work.Spaces.Dz (YY Ψ) p.1 p.2|
        ≤ ((XX Ψ p.1 p.2) ^ 2 + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2) / 2 := by
      linarith [h2]
    have h5 : 0 ≤ (w p.1) ^ 2 * sgm α p.2 := mul_nonneg hw hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hs]
    calc (w p.1) ^ 2 * (|XX Ψ p.1 p.2| * |Work.Spaces.Dz (YY Ψ) p.1 p.2| * sgm α p.2)
        = (w p.1) ^ 2 * sgm α p.2
            * (|XX Ψ p.1 p.2| * |Work.Spaces.Dz (YY Ψ) p.1 p.2|) := by ring
      _ ≤ (w p.1) ^ 2 * sgm α p.2
            * (((XX Ψ p.1 p.2) ^ 2 + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hmid h5
      _ = ((XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
            + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) / 2 := by ring_nf
      _ ≤ (XX Ψ p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
            + (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2 := by
          have ha : 0 ≤ (XX Ψ p.1 p.2) ^ 2 * ((w p.1) ^ 2 * sgm α p.2) :=
            mul_nonneg (sq_nonneg _) h5
          have hb : 0 ≤ (Work.Spaces.Dz (YY Ψ) p.1 p.2) ^ 2 * ((w p.1) ^ 2 * sgm α p.2) :=
            mul_nonneg (sq_nonneg _) h5
          linarith

/-- Outer integrability of the pairing. -/
theorem pairOuterIntegrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (w z) ^ 2 * (XX Ψ z θ * Work.Spaces.Dz (YY Ψ) z θ * sgm α θ))
      (volume.restrict Iz) := by
  have h := (show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (w p.1) ^ 2 * (XX Ψ p.1 p.2 * Work.Spaces.Dz (YY Ψ) p.1 p.2
        * sgm α p.2)) ((volume.restrict Iz).prod (volume.restrict Iθ)) from by
    rw [prod_restrict_eq_rect]; exact pairIntegrable hα hα4 h)
  exact h.integral_prod_left


/-- Outer integrability of the majorant of the pairing. -/
theorem outerMajorant {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (w z) ^ 2 * ((XX Ψ z θ) ^ 2
        + (Work.Spaces.Dz (YY Ψ) z θ) ^ 2) * sgm α θ) (volume.restrict Iz) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨slX, outX, _, _⟩ := slotFacts_pure hα1 hα hα4 h 1 (by norm_num)
  have h1 : MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, XX Ψ z θ ^ 2 * (w z) ^ 2 * sgm α θ) (volume.restrict Iz) :=
    outX
  refine MeasureTheory.Integrable.congr (h1.add (clairautOuter hα hα4 h)) ?_
  filter_upwards [slX, clairautSlice hα hα4 h] with z hzX hzZ
  have hzX' : MeasureTheory.IntegrableOn
      (fun θ => XX Ψ z θ ^ 2 * (w z) ^ 2 * sgm α θ) Iθ := by
    simpa only [XX, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hzX
  simp only [Pi.add_apply]
  rw [← MeasureTheory.integral_add hzX' hzZ]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

end

end Work.FTS.ClassC.VopGen.Core
