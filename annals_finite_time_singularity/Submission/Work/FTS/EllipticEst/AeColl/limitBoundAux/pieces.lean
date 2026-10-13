import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.H2W.SlotA.cwPairBound
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.AngAWeak.AeEnergyMain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl.limitBoundAux.pieces` — shared ingredients for `AeColl.limitBound` (part 1)

The vocabulary is that of `AeColl/Defs` (`Pcut`, `Dcut`, `Trcut`, `Acut`, `Vfull`,
`Uz = z∂_zu`, `Vz = z∂_z∂_θu`, `Az = z²∂_z²u`, `wt = w²`, `sigθ = sin(2θ)^{-η}`).

This module (part 1) contains

* continuity of `Az u`, `Uz u`, `∂_θθu` on the open quadrant, from `AeData.smooth`;
* the bridge "diagonal `IPMem`s + continuity ⟹ mixed `IPMem`" for the open class;
* the honest pairings of the four slots, in particular the mixed ones
  `IPMem (Uz u) (∂_θθu)` and `IPMem (Az u) (∂_θθu)`;
* a Cauchy–Schwarz bound with a bounded radial coefficient.

Part 2 (`...limitBoundAux.pieces2`) contains the identifications of `Pcut u n`, `Vfull u`,
`Dcut u n`, `Trcut u n` with `z`-integrals of `z`-only slice functions, together with
integrability/monotonicity facts.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Continuity on the open quadrant -/

theorem w2_zero : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
  simp [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]

theorem sigθ_eq : sigθ = Work.FTS.EllipticEst.AngSecond.sig := rfl

theorem wt_eq : wt = Work.FTS.EllipticEst.AngSecond.w2 := rfl

theorem continuousOn_w2_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.w2 p.1)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))).pow 2

theorem continuousOn_sig_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin : ContinuousOn
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  simpa only [Work.FTS.EllipticEst.AngSecond.sig] using hsin

theorem continuousOn_wt : ContinuousOn wt (Set.Ioi 0) := by
  have hfun : wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; simp only [wt, Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem SmoothOpen_of_AeData {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) : Work.FTS.EllipticEst.SmoothOpen u :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)

theorem continuousOn_rad2 {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Az u)) Work.FTS.EllipticEst.Q0 :=
  (continuousOn_fst.pow 2).mul ((h.pzIter 2).continuousOn)

theorem continuousOn_grad {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Uz u)) Work.FTS.EllipticEst.Q0 :=
  continuousOn_fst.mul (h.pz).continuousOn

theorem continuousOn_ang2 {u : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (Function.uncurry (Work.Spaces.pthIter 2 u)) Work.FTS.EllipticEst.Q0 :=
  (h.pth.pth).continuousOn

/-! ## 2. The mixed `IPMem` from the diagonal ones, in the open class -/

/-- The mixed honesty `IPMem g h` follows from the two diagonal honesties once `g` and `h` are
continuous on the open quadrant. -/
theorem IPMem_of_diag_cont {g h : ℝ → ℝ → ℝ}
    (hgc : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hhc : ContinuousOn (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hgg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hhh : Work.FTS.EllipticEst.AngSecond.IPMem h h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h := by
  have hprod : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 * h p.1 p.2
      * Work.FTS.EllipticEst.AngSecond.w2 p.1 * Work.FTS.EllipticEst.AngSecond.sig p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((hgc.mul hhc).mul continuousOn_w2_Q0).mul continuousOn_sig_Q0
  refine Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm hgg hhh ?_ ?_
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hzero : (fun θ : ℝ => g 0 θ * h 0 θ * Work.FTS.EllipticEst.AngSecond.w2 0
          * Work.FTS.EllipticEst.AngSecond.sig θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [w2_zero]; ring
      rw [hzero]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hprod hzpos
  · exact Work.Spaces.aesm_of_continuousOn_Qd _ hprod

/-! ## 3. The honest pairings of the slots -/

theorem IPMem_grad_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Uz u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hU

theorem IPMem_ang2_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 h)

theorem IPMem_rad2_self {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Az u) :=
  Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 h)

theorem IPMem_grad_ang2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Work.Spaces.pthIter 2 u) :=
  IPMem_of_diag_cont (continuousOn_grad (SmoothOpen_of_AeData h))
    (continuousOn_ang2 (SmoothOpen_of_AeData h)) (IPMem_grad_self h hU) (IPMem_ang2_self h)

theorem IPMem_rad2_ang2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u) :=
  IPMem_of_diag_cont (continuousOn_rad2 (SmoothOpen_of_AeData h))
    (continuousOn_ang2 (SmoothOpen_of_AeData h)) (IPMem_rad2_self h) (IPMem_ang2_self h)

/-! ## 4. Cauchy–Schwarz with a bounded radial coefficient -/

/-- `IP (c·g) h` with a radial coefficient `|c| ≤ K`: dominated by `K·√(IP g g)·√(IP h h)`. -/
theorem IP_coef_le {c : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ z ∈ Work.Spaces.Iz, |c z| ≤ K)
    (hcaesm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict Work.Spaces.Iz))
    {g h : ℝ → ℝ → ℝ} (hgg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hhh : Work.FTS.EllipticEst.AngSecond.IPMem h h)
    (hgh : Work.FTS.EllipticEst.AngSecond.IPMem g h) :
    |Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ) h|
      ≤ K * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP g g)
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP h h) := by
  have hcg_g : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => c z * g z θ) g :=
    Work.FTS.EllipticEst.H2W.SlotA.IPMem_const_mul_left c K hc hcaesm g g
      (Work.FTS.EllipticEst.H2W.SlotA.IPMem_symm hgg)
  have hcg_cg : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => c z * g z θ)
      (fun z θ => c z * g z θ) :=
    Work.FTS.EllipticEst.H2W.SlotA.IPMem_const_mul_left c K hc hcaesm g
      (fun z θ => c z * g z θ) (Work.FTS.EllipticEst.H2W.SlotA.IPMem_symm hcg_g)
  have hcg_h : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => c z * g z θ) h :=
    Work.FTS.EllipticEst.H2W.SlotA.IPMem_const_mul_left c K hc hcaesm g h hgh
  have hcs := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hcg_cg hhh hcg_h
  have hquad : Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ)
      (fun z θ => c z * g z θ) ≤ K ^ 2 * Work.FTS.EllipticEst.AngSecond.IP g g := by
    have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, (c z * g z θ) * (c z * g z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        ≤ K ^ 2 * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      intro z hz
      have hL : MeasureTheory.IntegrableOn (fun θ => (c z * g z θ) * (c z * g z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          Work.Spaces.Iθ := hcg_cg.1 z hz
      have hR : MeasureTheory.IntegrableOn (fun θ => K ^ 2 * (g z θ * g z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ))
          Work.Spaces.Iθ := (hgg.1 z hz).const_mul (K ^ 2)
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_ae hL hR
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall (fun θ hθ => ?_)))
      have h1 : (c z) ^ 2 ≤ K ^ 2 := by
        have h2 := hc z hz
        nlinarith [abs_nonneg (c z), sq_abs (c z)]
      have hw := Work.FTS.EllipticEst.AngSecond.w2_nonneg z
      have hs := Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
      have hnn : 0 ≤ g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hw) hs
      calc (c z * g z θ) * (c z * g z θ) * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ
          = (c z) ^ 2 * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
        _ ≤ K ^ 2 * (g z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) := mul_le_mul_of_nonneg_right h1 hnn
        _ = K ^ 2 * (g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
    have hout := MeasureTheory.integral_mono_ae hcg_cg.2 (hgg.2.const_mul (K ^ 2))
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Filter.Eventually.of_forall hinner))
    calc Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ)
          (fun z θ => c z * g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (c z * g z θ) * (c z * g z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, K ^ 2 * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := hout
      _ = K ^ 2 * Work.FTS.EllipticEst.AngSecond.IP g g := by
          rw [MeasureTheory.integral_const_mul]; rfl
  have hsqrt : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ)
        (fun z θ => c z * g z θ))
      ≤ K * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP g g) := by
    have h1 := Real.sqrt_le_sqrt hquad
    have h2 : Real.sqrt (K ^ 2 * Work.FTS.EllipticEst.AngSecond.IP g g)
        = K * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP g g) := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
    rwa [h2] at h1
  calc |Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ) h|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => c z * g z θ)
            (fun z θ => c z * g z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP h h) := hcs
    _ ≤ (K * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP g g))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP h h) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

end Work.FTS.EllipticEst.AeColl
