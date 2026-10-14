import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.ShiftedTwoL2Clean
import Submission.Work.FTS.EllipticEst.Cores.TopSlotsTwoClean
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

private abbrev Ab (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
private abbrev Bb (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- The weak class descends in the level. -/
theorem l2_weakPos_descend {α : ℝ} {k l : ℕ} (hkl : l ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : EllWeakPos α k F Ψ) : EllWeakPos α l F Ψ := by
  obtain ⟨hsF, hsΨ, hsA, hsB⟩ : Work.FTS.EllipticEst.SmoothOpen F
      ∧ Work.FTS.EllipticEst.SmoothOpen Ψ
      ∧ Work.FTS.EllipticEst.SmoothOpen (Ab Ψ) ∧ Work.FTS.EllipticEst.SmoothOpen (Bb Ψ) := by
    have hs := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  have hsZP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
    (hsΨ.pth.pth).Dz
  exact ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
    HkMem_descend_open (α := α) hkl ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hsF) h.memF,
    HkMem_descend_open (α := α) hkl ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsA) h.memA,
    HkMem_descend_open (α := α) hkl ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsB) h.memB,
    HkMem_descend_open (α := α) hkl ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsZP)
      h.memZPth2⟩

/-- The level-`0` integrand is the single `D_z⁰`-slot. -/
theorem l2_HkIntegrand_zero_apply (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- A single level-`0` radial slot is dominated by the level-`2` integrand. -/
theorem l2_HkSq_zero_DzIter_le {α : ℝ} {F : ℝ → ℝ → ℝ} {j : ℕ} (hj : j ≤ 2)
    (hmem : Work.Spaces.HkMem α 2 F) :
    Work.Spaces.HkSq α 0 (Work.Spaces.DzIter j F) ≤ Work.Spaces.HkSq α 2 F := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => by
      rw [l2_HkIntegrand_zero_apply]; positivity) hmem.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => by rw [l2_HkIntegrand_zero_apply]; positivity)
    (hmem.1 z hz) (Eventually.of_forall fun θ => ?_)
  rw [l2_HkIntegrand_zero_apply]
  exact Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ j hj

/-- Arithmetic combining the two exact splittings with the lower-order and top-slot bounds. -/
theorem l2_split_arith {P B1 B2 A0 A1 A2 T1 Tz T2 : ℝ}
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (h : P ≤ B1 + 3 * B2 + T2) (h1 : B1 ≤ A0 + 2 * A1 + T1) (h2 : B2 ≤ A1 + 2 * A2 + Tz) :
    P ≤ 6 * (A0 + A1 + A2) + (T1 + 3 * Tz + T2) := by nlinarith [h, h1, h2, hA0, hA1]

/-- Arithmetic for the three level-`0` estimates. -/
theorem l2_low_arith {α4 A0 A1 A2 B0 B1 B2 H C0 C2 : ℝ}
    (h0 : α4 * A0 + B0 ≤ C0 * H) (h1 : α4 * A1 + B1 ≤ C0 * H) (h2 : α4 * A2 + B2 ≤ C2 * H) :
    α4 * (A0 + A1 + A2) + (B0 + B1 + B2) ≤ (2 * C0 + C2) * H := by
  nlinarith [h0, h1, h2]

/-- Arithmetic for the final combination. -/
theorem l2_combine_arith {α4 P Q SA SB TA TB C0 C2 C3 H : ℝ}
    (hsA : α4 * P ≤ α4 * (6 * SA) + α4 * TA) (hsB : Q ≤ 6 * SB + TB)
    (hlow : α4 * SA + SB ≤ (2 * C0 + C2) * H) (hT : α4 * TA + TB ≤ C3 * H) :
    α4 * P + Q ≤ (12 * C0 + 6 * C2 + C3) * H := by
  nlinarith [hsA, hsB, hlow, hT]

/-- `√x + √y ≤ √(2C)·√H` from `x + y ≤ C·H`. -/
theorem l2_sqrt_pair_le {x y H C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (h : x + y ≤ C * H) :
    Real.sqrt x + Real.sqrt y ≤ Real.sqrt (2 * C) * Real.sqrt H := by
  have h1 : Real.sqrt x + Real.sqrt y ≤ Real.sqrt (2 * (x + y)) := by
    have h2 : (Real.sqrt x + Real.sqrt y) ^ 2 ≤ 2 * (x + y) := by
      have hs : (Real.sqrt x - Real.sqrt y) ^ 2
          = x + y - 2 * Real.sqrt x * Real.sqrt y := by
        rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]; ring
      rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
      nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), hs]
    calc Real.sqrt x + Real.sqrt y = Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (2 * (x + y)) := Real.sqrt_le_sqrt h2
  have h3 : Real.sqrt (2 * (x + y)) ≤ Real.sqrt (2 * (C * H)) :=
    Real.sqrt_le_sqrt (by linarith)
  have h4 : Real.sqrt (2 * (C * H)) = Real.sqrt (2 * C) * Real.sqrt H := by
    rw [show 2 * (C * H) = (2 * C) * H from by ring, Real.sqrt_mul (by linarith)]
  linarith [h1, h3, h4.le, h4.ge]

/-- **The assembly**: the level-`2` estimate from the level-`0` estimate, the shifted level-`0`
estimate (`hP1`) and the level-`2` top angular slots (`hP23`). -/
theorem levelTwo_of_pieces
    (hP1 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Bb Ψ))
        ≤ C * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F))
    (hP23 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      EllWeakPos α 2 F Ψ →
      (α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Ab Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)))
        + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Bb Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Bb Ψ))
        ≤ C * Work.Spaces.HkSq α 2 F)
    (h0 : ∃ C : ℝ, 0 < C ∧ EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ EllEstUnif 2 C := by
  obtain ⟨C0, hC0pos, hC0⟩ := h0
  obtain ⟨C2, hC2pos, hC2⟩ := hP1
  obtain ⟨C3, hC3pos, hC3⟩ := hP23
  refine ⟨Real.sqrt (2 * (12 * C0 + 6 * C2 + C3)) + 1, ?_, ?_⟩
  · linarith [Real.sqrt_nonneg (2 * (12 * C0 + 6 * C2 + C3))]
  intro α F Ψ hα hα4 h
  -- ## the smoothness and class data
  have hslices := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hsΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hid := Work.FTS.EllipticEst.remov.Dz_slice_identities Ψ hsΨ
  have hcl0 : EllWeakPos α 0 F Ψ := l2_weakPos_descend (k := 2) (l := 0) (by norm_num) h
  have hcl1 : EllWeakPos α 1 (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    ShiftOfTwoLe (α := α) (k := 2) (le_refl 2) h
  have hcl2 : EllWeakPos α 0 (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    l2_weakPos_descend (k := 1) (l := 0) (by norm_num) hcl1
  -- ## the three level-`0` estimates
  have eA : α ^ 4 * Work.Spaces.HkSq α 0 (Ab Ψ) + Work.Spaces.HkSq α 0 (Bb Ψ)
      ≤ C0 * Work.Spaces.HkSq α 0 F := hC0 α F Ψ hα hα4 hcl0
  have eB : α ^ 4 * Work.Spaces.HkSq α 0 (Ab (Work.Spaces.DzIter 1 Ψ))
      + Work.Spaces.HkSq α 0 (Bb (Work.Spaces.DzIter 1 Ψ))
      ≤ C0 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) :=
    hC0 α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 hcl2
  have hAb : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Ab Ψ))
      = Work.Spaces.HkSq α 0 (Ab (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ hlt => hid.1 z θ hz hθ hlt)
  have hBb : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Bb Ψ))
      = Work.Spaces.HkSq α 0 (Bb (Work.Spaces.DzIter 1 Ψ)) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ hlt => hid.2 z θ hz hθ hlt)
  have eB' : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Ab Ψ))
      + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Bb Ψ))
      ≤ C0 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) := by
    rw [hAb, hBb]; exact eB
  have eC : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
      + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Bb Ψ))
      ≤ C2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) := hC2 α F Ψ hα hα4 h
  have eD := hC3 α F Ψ hα hα4 h
  -- ## slot comparisons and normalisation of the shifted operators
  have hF0 : Work.Spaces.HkSq α 0 F ≤ Work.Spaces.HkSq α 2 F :=
    l2_HkSq_zero_DzIter_le (α := α) (F := F) (j := 0) (by norm_num) h.memF
  have hF1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 F) ≤ Work.Spaces.HkSq α 2 F :=
    l2_HkSq_zero_DzIter_le (α := α) (F := F) (j := 1) (by norm_num) h.memF
  have hF2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 F) ≤ Work.Spaces.HkSq α 2 F :=
    l2_HkSq_zero_DzIter_le (α := α) (F := F) (j := 2) (le_refl 2) h.memF
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] at hAb hBb eB' eC eD hF0 hF1 hF2
  -- ## the HkMem and smoothness data for the splittings
  have hmemA1 : Work.Spaces.HkMem α 1 (Ab Ψ) :=
    HkMem_descend_open (α := α) (k := 1) (l := 2) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hslices.2.2.1) h.memA
  have hmemB1 : Work.Spaces.HkMem α 1 (Bb Ψ) :=
    HkMem_descend_open (α := α) (k := 1) (l := 2) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hslices.2.2.2) h.memB
  have hsmA : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Ab Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hslices.2.2.1
  have hsmB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bb Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hslices.2.2.2
  have hsmDzA : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz (Ab Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hslices.2.2.1.Dz)
  have hsmDzB : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz (Bb Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hslices.2.2.2.Dz)
  -- `HkMem` of the radially shifted fields: transport along the two slice identities
  -- `D_z(z²∂_z²Ψ) = z²∂_z²(D_zΨ)` and `D_z(∂_θ²Ψ) = ∂_θ²(D_zΨ)` from the `HkMem` fields of the
  -- *shifted* datum supplied by `hcl1`.
  have hmemDzA : Work.Spaces.HkMem α 1 (Work.Spaces.Dz (Ab Ψ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 1 hcl1.memA
      (fun z hz θ hθ => (hid.1 z θ hz hθ.1 hθ.2).symm)
  have hmemDzB : Work.Spaces.HkMem α 1 (Work.Spaces.Dz (Bb Ψ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 1 hcl1.memB
      (fun z hz θ hθ => (hid.2 z θ hz hθ.1 hθ.2).symm)
  -- ## the exact splittings, in normalised form
  have hA2 : Work.Spaces.HkSq α 2 (Ab Ψ) ≤ Work.Spaces.HkSq α 1 (Ab Ψ)
      + 3 * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Ab Ψ))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 2 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 2) (by norm_num) α (Ab Ψ) hsmA h.memA
    calc Work.Spaces.HkSq α 2 (Ab Ψ)
        ≤ Work.Spaces.HkSq α 1 (Ab Ψ)
            + (((2 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Ab Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 2 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 1 (Ab Ψ)
            + 3 * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Ab Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 2 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  have hA1 : Work.Spaces.HkSq α 1 (Ab Ψ) ≤ Work.Spaces.HkSq α 0 (Ab Ψ)
      + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 1) (by norm_num) α (Ab Ψ) hsmA hmemA1
    calc Work.Spaces.HkSq α 1 (Ab Ψ)
        ≤ Work.Spaces.HkSq α 0 (Ab Ψ)
            + (((1 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 0 (Ab Ψ)
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  have hAz : Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Ab Ψ))
      ≤ Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
      + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ)))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Ab Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 1) (by norm_num) α
      (Work.Spaces.DzIter 1 (Ab Ψ)) hsmDzA hmemDzA
    calc Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Ab Ψ))
        ≤ Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
            + (((1 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ)))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Ab Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ)))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Ab Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  have hB2 : Work.Spaces.HkSq α 2 (Bb Ψ) ≤ Work.Spaces.HkSq α 1 (Bb Ψ)
      + 3 * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Bb Ψ))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 2 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 2) (by norm_num) α (Bb Ψ) hsmB h.memB
    calc Work.Spaces.HkSq α 2 (Bb Ψ)
        ≤ Work.Spaces.HkSq α 1 (Bb Ψ)
            + (((2 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Bb Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 2 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 1 (Bb Ψ)
            + 3 * Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Bb Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 2 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  have hB1 : Work.Spaces.HkSq α 1 (Bb Ψ) ≤ Work.Spaces.HkSq α 0 (Bb Ψ)
      + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 1) (by norm_num) α (Bb Ψ) hsmB hmemB1
    calc Work.Spaces.HkSq α 1 (Bb Ψ)
        ≤ Work.Spaces.HkSq α 0 (Bb Ψ)
            + (((1 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 0 (Bb Ψ)
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  have hBz : Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Bb Ψ))
      ≤ Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
      + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Bb Ψ)))
      + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Bb Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    have h := Work.FTS.EllipticEst.remov.HkSq_step_le (k := 1) (by norm_num) α
      (Work.Spaces.DzIter 1 (Bb Ψ)) hsmDzB hmemDzB
    calc Work.Spaces.HkSq α 1 (Work.Spaces.Dz (Bb Ψ))
        ≤ Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
            + (((1 : ℕ) : ℝ) + 1) * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Bb Ψ)))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Bb Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := h
      _ = Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Bb Ψ)))
            + ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed 0 1 (Work.Spaces.Dz (Bb Ψ)) z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
  -- ## the lower-order sums
  have hlow : α ^ 4 * (Work.Spaces.HkSq α 0 (Ab Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ))))
      + (Work.Spaces.HkSq α 0 (Bb Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Bb Ψ))))
      ≤ (2 * C0 + C2) * Work.Spaces.HkSq α 2 F :=
    l2_low_arith
      (le_trans eA (mul_le_mul_of_nonneg_left hF0 (le_of_lt hC0pos)))
      (le_trans eB' (mul_le_mul_of_nonneg_left hF1 (le_of_lt hC0pos)))
      (le_trans eC (mul_le_mul_of_nonneg_left hF2 (le_of_lt hC2pos)))
  -- ## the two splittings, against the level-`2` norm
  have hsplitA : α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ)
      ≤ α ^ 4 * (6 * (Work.Spaces.HkSq α 0 (Ab Ψ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ)))))
        + α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.Dz (Ab Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)) := by
    have hX : Work.Spaces.HkSq α 2 (Ab Ψ)
        ≤ 6 * (Work.Spaces.HkSq α 0 (Ab Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
            + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ))))
          + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
            + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.Dz (Ab Ψ))
            + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)) :=
      l2_split_arith (Work.Spaces.HkSq_nonneg α 0 (Ab Ψ))
        (Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.Dz (Ab Ψ))) hA2 hA1 hAz
    have hα4nn : 0 ≤ α ^ 4 := by positivity
    calc α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ)
        ≤ α ^ 4 * (6 * (Work.Spaces.HkSq α 0 (Ab Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
              + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ))))
            + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
              + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.Dz (Ab Ψ))
              + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ))) :=
          mul_le_mul_of_nonneg_left hX hα4nn
      _ = α ^ 4 * (6 * (Work.Spaces.HkSq α 0 (Ab Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
              + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Ab Ψ)))))
            + α ^ 4 * (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab Ψ)
              + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.Dz (Ab Ψ))
              + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Ab Ψ)) := by ring
  have hsplitB : Work.Spaces.HkSq α 2 (Bb Ψ)
      ≤ 6 * (Work.Spaces.HkSq α 0 (Bb Ψ) + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Bb Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Work.Spaces.Dz (Bb Ψ))))
        + (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb Ψ)
          + 3 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.Dz (Bb Ψ))
          + Work.FTS.EllipticEst.remov.Step.Tk α 2 (Bb Ψ)) :=
    l2_split_arith (Work.Spaces.HkSq_nonneg α 0 (Bb Ψ))
      (Work.Spaces.HkSq_nonneg α 0 (Work.Spaces.Dz (Bb Ψ))) hB2 hB1 hBz
  -- ## the final combination
  have hmain : α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ) + Work.Spaces.HkSq α 2 (Bb Ψ)
      ≤ (12 * C0 + 6 * C2 + C3) * Work.Spaces.HkSq α 2 F :=
    l2_combine_arith hsplitA hsplitB hlow eD
  -- ## the square roots
  have hsqrt := l2_sqrt_pair_le
    (x := α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ)) (y := Work.Spaces.HkSq α 2 (Bb Ψ))
    (H := Work.Spaces.HkSq α 2 F) (C := 12 * C0 + 6 * C2 + C3)
    (mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 2 (Ab Ψ)))
    (Work.Spaces.HkSq_nonneg α 2 (Bb Ψ)) (Work.Spaces.HkSq_nonneg α 2 F)
    (by positivity : (0 : ℝ) ≤ 12 * C0 + 6 * C2 + C3) hmain
  have hα4sq : Real.sqrt (α ^ 4) = α ^ 2 := by
    rw [show α ^ 4 = (α ^ 2) ^ 2 from by ring, Real.sqrt_sq (by positivity)]
  have hfirst : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ))
      = α ^ 2 * Work.Spaces.HkNorm α 2 (Ab Ψ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), hα4sq, Work.Spaces.HkNorm]
  calc α ^ 2 * Work.Spaces.HkNorm α 2 (Ab Ψ) + Work.Spaces.HkNorm α 2 (Bb Ψ)
      = Real.sqrt (α ^ 4 * Work.Spaces.HkSq α 2 (Ab Ψ)) + Real.sqrt (Work.Spaces.HkSq α 2 (Bb Ψ)) := by
        rw [← hfirst, Work.Spaces.HkNorm]
    _ ≤ Real.sqrt (2 * (12 * C0 + 6 * C2 + C3)) * Real.sqrt (Work.Spaces.HkSq α 2 F) := hsqrt
    _ ≤ (Real.sqrt (2 * (12 * C0 + 6 * C2 + C3)) + 1) * Work.Spaces.HkNorm α 2 F := by
        rw [Work.Spaces.HkNorm]
        nlinarith [Real.sqrt_nonneg (2 * (12 * C0 + 6 * C2 + C3)),
          Real.sqrt_nonneg (Work.Spaces.HkSq α 2 F)]


end Work.FTS.EllipticEst.Cores
