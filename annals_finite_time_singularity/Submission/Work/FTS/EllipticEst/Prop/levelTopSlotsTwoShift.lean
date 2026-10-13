/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Prop.levelTopSlotsTwoShift`: Terms 3 and 4 of `Prop.levelTopSlotsTwo`

* **Term 3** (`aShiftSlotTop`): `α²√(Tk α 1 (z²∂_z²(D_zΨ))) ≤ C|F|_{ℋ²}` — the `A`-slot of the
  radially shifted datum.  The route is the mixed-derivative interpolation
  `Prop.mixedSlotInterpEta` applied to `G = z²∂_z²Ψ`, whose three right-hand slots are exactly the
  `ℋ⁰`-slots bounded by `TopSlotTwoFts.ShiftZeroSlots2`.
* **Term 4** (`bShiftSlotTop`): `√(Tk α 1 (∂_θ²(D_zΨ))) ≤ C|F|_{ℋ²}` — from `TT.slot11_le`,
  whose right-hand side is the three `j ≤ 2` pure slots of `∂_θ²Ψ`, the `ℋ²`-energy of the source
  and (Term 3) the `α⁴`-multiple of the `(1,1)`-slot of `z²∂_z²Ψ`.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta
import Submission.Work.FTS.EllipticEst.TT.slot11_le
import Submission.Work.FTS.EllipticEst.TopSlotTwoFts.ShiftZeroSlots2
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Clairaut identities -/

/-- `∂_θ` commutes with `D_z` on the open quadrant. -/
theorem pth_Dz_eqOn {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    AgreeOnQ (Work.Spaces.pth (Work.Spaces.Dz f)) (Work.Spaces.Dz (Work.Spaces.pth f)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((smoothOpen_iff_forall f).mp hf 2).contDiffAt (isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pth (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
    show deriv (fun θ' : ℝ => z * Work.Spaces.pz f z θ') θ
      = z * deriv (fun θ' : ℝ => Work.Spaces.pz f z θ') θ
    exact deriv_const_mul_field z
  have h2 : Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := rfl
  rw [h1, h2, ← Work.Spaces.pz_pth_comm hcd]

/-- `D_θ(D_z f) = D_z(D_θ f)` on the open quadrant. -/
theorem Dth_Dz_eqOn {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    AgreeOnQ (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dz (Work.Spaces.Dth f)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((smoothOpen_iff_forall f).mp hf 2).contDiffAt (isOpen_Q0.mem_nhds hmem)
  exact (Work.Spaces.Dz_Dth_comm hcd).symm

/-- The `(1,1)`-mixed slot of `f` is the `(0,1)`-slot of `D_z f` on the open quadrant. -/
theorem mixed01_Dz_eq_mixed11 {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) :
    AgreeOnQ (Work.Spaces.mixed 0 1 (Work.Spaces.DzIter 1 f))
      (Work.Spaces.mixed 1 1 f) := by
  intro z θ hz hθ hlt
  exact Dth_Dz_eqOn hf z θ hz hθ hlt

/-- The `(0,1)`-slot of `∂_θ²(D_zΨ)` is the `(1,1)`-slot of `∂_θ²Ψ`. -/
theorem mixed01_Bb_Dz_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) :
    AgreeOnQ (Work.Spaces.mixed 0 1 (Bb (Work.Spaces.DzIter 1 Ψ)))
      (Work.Spaces.mixed 1 1 (Bb Ψ)) := by
  intro z θ hz hθ hlt
  have hpt : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hB : SmoothOpen (Bb Ψ) := smoothOpen_pthIter_aux hΨ 2
  -- `Bb (D_zΨ) = D_z(BbΨ)` on the open quadrant
  have hcA : AgreeOnQ (Bb (Work.Spaces.DzIter 1 Ψ))
      (Work.Spaces.DzIter 1 (Bb Ψ)) := by
    intro z' θ' hz' hθ' hlt'
    simpa only [Function.uncurry] using
      (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 1
        (show (z', θ') ∈ Q0 from ⟨hz', hθ', hlt'⟩))
  have h1 : Work.Spaces.Dth (Bb (Work.Spaces.DzIter 1 Ψ)) z θ
      = Work.Spaces.Dth (Work.Spaces.DzIter 1 (Bb Ψ)) z θ :=
    hcA.Dth z θ hz hθ hlt
  have h2 : Work.Spaces.Dth (Work.Spaces.DzIter 1 (Bb Ψ)) z θ
      = Work.Spaces.Dz (Work.Spaces.Dth (Bb Ψ)) z θ :=
    Dth_Dz_eqOn hB z θ hz hθ hlt
  exact h1.trans h2

/-- `z²∂_z²(D_z^jΨ) = D_z^j(z²∂_z²Ψ)` on the open quadrant. -/
theorem Ab_DzIter_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) (j : ℕ) :
    AgreeOnQ (Ab (Work.Spaces.DzIter j Ψ)) (Work.Spaces.DzIter j (Ab Ψ)) := by
  intro z θ hz hθ hlt
  simpa only [Function.uncurry, Work.Spaces.mixed_zero_right] using
    (Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hΨ j 0
      (show (z, θ) ∈ Q0 from ⟨hz, hθ, hlt⟩))

/-- `z²∂_z²(D_zΨ) = D_z(z²∂_z²Ψ)` on the open quadrant. -/
theorem Ab_Dz_eqOn {Ψ : ℝ → ℝ → ℝ} (hΨ : SmoothOpen Ψ) :
    AgreeOnQ (Ab (Work.Spaces.DzIter 1 Ψ)) (Work.Spaces.DzIter 1 (Ab Ψ)) :=
  Ab_DzIter_eqOn hΨ 1

/-! ## Term 3 -/

/-- **The `A`-slot of the shifted datum.** -/
theorem aShiftSlotTop (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ))
        ≤ C * Work.Spaces.HkNorm α 2 F := by
  obtain ⟨CZ, hCZpos, hZA⟩ := HkSq_zero_Ab_DzIter_le h0
  obtain ⟨CZb, hCZbpos, hZB⟩ := HkSq_zero_DzIter_Bb_le h0
  obtain ⟨CI, hCIpos, hI⟩ := mixedSlotInterpEta
  refine ⟨Real.sqrt (CI * (2 * CZ + 4 * CZb) + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α F Ψ hα hα4 h
  have hgam : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hA : SmoothOpen (Ab Ψ) := smoothOpen_zsq_mul (hΨ.pzIter 2)
  have hα1 : α ≤ 1 := by linarith
  have hNF : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  -- the memberships needed by the interpolation
  have hmem2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Ab Ψ)) :=
    HkMem_zero_of_pointwise (c := 1) zero_le_one (hA.DzIter 2) h.memA
      (fun z θ hz hθ hlt => by
        rw [HkIntegrand_zero_apply]
        simpa only [one_mul] using
          Work.Spaces.sq_le_HkIntegrand_z α 2 (Ab Ψ) z θ 2 (by norm_num))
  have hmem1 : Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Ab Ψ)) :=
    HkMem_zero_of_pointwise (c := 1) zero_le_one (hA.Dz) h.memA
      (fun z θ hz hθ hlt => by
        rw [HkIntegrand_zero_apply]
        simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, one_mul] using
          Work.Spaces.sq_le_HkIntegrand_z α 2 (Ab Ψ) z θ 1 (by norm_num))
  have hmemX : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Ab Ψ)) :=
    HkMem_zero_pthIter2_Ab h
  -- the interpolation bound
  have hI' := hI α (Ab Ψ) hα hα4 hA (Ab_zero_left h.zero) (Ab_zero_right h.pi_half)
    hmem2 hmemX hmem1
  -- the left-hand side is the interpolated integral
  have hEq1 : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ))
      = Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Ab Ψ)) :=
    Tk_congr_open 1 (fun z θ hz hθ hlt => Ab_Dz_eqOn hΨ z θ hz hθ hlt)
  have hEq2 : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Work.Spaces.DzIter 1 (Ab Ψ))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Ab Ψ)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    rw [Tk_one_eq_int hgam]
    refine integral_prod_congr_open (fun z θ hz hθ hlt => ?_)
    rw [show Work.Spaces.pth (Work.Spaces.DzIter 1 (Ab Ψ)) z θ
        = Work.Spaces.Dz (Work.Spaces.pth (Ab Ψ)) z θ from
      pth_Dz_eqOn (smoothOpen_zsq_mul (hΨ.pzIter 2)) z θ hz hθ hlt]
  -- bounds on the three slots
  have hb1 : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
      ≤ CZ * Work.Spaces.HkSq α 2 F := by
    have hcong : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
        = Work.Spaces.HkSq α 0 (Ab (Work.Spaces.DzIter 2 Ψ)) :=
      (Work.FTS.EllipticEst.HkSq_congr_open α 0
        (fun z θ hz hθ hlt => (Ab_DzIter_eqOn hΨ 2 z θ hz hθ hlt).symm))
    rw [hcong]
    exact hZA α F Ψ hα hα4 h 2 (by norm_num)
  have hb2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
      ≤ 4 * (CZb * Work.Spaces.HkSq α 2 F) := by
    have h1 := HkSq_zero_pthIter2_Ab_le h
    have h2 := hZB α F Ψ hα hα4 h 2 (by norm_num)
    have h3 := hZB α F Ψ hα hα4 h 1 (by norm_num)
    linarith [h1, h2, h3]
  have hb3 : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
      ≤ CZ * Work.Spaces.HkSq α 2 F := by
    have hcong : Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ))
        = Work.Spaces.HkSq α 0 (Ab (Work.Spaces.DzIter 1 Ψ)) :=
      (Work.FTS.EllipticEst.HkSq_congr_open α 0
        (fun z θ hz hθ hlt => (Ab_Dz_eqOn hΨ z θ hz hθ hlt).symm))
    rw [hcong]
    exact hZA α F Ψ hα hα4 h 1 (by norm_num)
  -- the `α⁴`-weighted bound
  have hα41 : α ^ 4 ≤ 1 := pow_le_one₀ hα.le hα1
  have hmain : α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Ab (Work.Spaces.DzIter 1 Ψ))
      ≤ CI * ((2 * CZ + 4 * CZb) * Work.Spaces.HkSq α 2 F) := by
    have hsum : α ^ 4 * (Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ)))
        ≤ (2 * CZ + 4 * CZb) * Work.Spaces.HkSq α 2 F := by
      have hnn2 : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ)) :=
        Work.Spaces.HkSq_nonneg α 0 _
      have h4 : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
          ≤ 4 * (CZb * Work.Spaces.HkSq α 2 F) :=
        le_trans (mul_le_of_le_one_left hnn2 hα41) hb2
      have h4' : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
          ≤ 4 * CZb * Work.Spaces.HkSq α 2 F := by
        refine le_trans h4 (le_of_eq ?_)
        ring
      have e : α ^ 4 * (Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
            + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ)))
          = α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
            + α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ))
            + α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ)) := by ring
      rw [e]
      nlinarith [hb1, hb3, h4', hNF, hCZpos.le, hCZbpos.le]
    calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ))
        = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (Ab Ψ)) := by rw [hEq1]
      _ = α ^ 4 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth (Ab Ψ)) z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by rw [hEq2]
      _ ≤ α ^ 4 * (CI * ((Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
              + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ)))
            + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ)))) :=
          mul_le_mul_of_nonneg_left hI' (by positivity)
      _ = CI * (α ^ 4 * ((Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Ab Ψ))
              + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Ab Ψ)))
            + Work.Spaces.HkSq α 0 (Work.Spaces.Dz (Ab Ψ)))) := by ring
      _ ≤ CI * ((2 * CZ + 4 * CZb) * Work.Spaces.HkSq α 2 F) :=
          mul_le_mul_of_nonneg_left hsum hCIpos.le
  -- square roots
  have hs : Real.sqrt (α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Ab (Work.Spaces.DzIter 1 Ψ)))
      = α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Ab (Work.Spaces.DzIter 1 Ψ))) := by
    rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [← hs]
  calc Real.sqrt (α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Ab (Work.Spaces.DzIter 1 Ψ)))
      ≤ Real.sqrt ((CI * (2 * CZ + 4 * CZb) + 1) * Work.Spaces.HkSq α 2 F) := by
        refine Real.sqrt_le_sqrt ?_
        calc α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
              (Ab (Work.Spaces.DzIter 1 Ψ))
            ≤ CI * ((2 * CZ + 4 * CZb) * Work.Spaces.HkSq α 2 F) := hmain
          _ ≤ (CI * (2 * CZ + 4 * CZb) + 1) * Work.Spaces.HkSq α 2 F := by
              have := mul_nonneg hCIpos.le hNF
              nlinarith [this, hNF]
    _ = Real.sqrt (CI * (2 * CZ + 4 * CZb) + 1) * Work.Spaces.HkNorm α 2 F := by
        rw [Work.Spaces.HkNorm, Real.sqrt_mul (by positivity)]

/-! ## Term 4 -/

/-- **The `B`-slot of the shifted datum.** -/
theorem bShiftSlotTop (h0 : ∃ C₀ : ℝ, 0 < C₀ ∧ Work.FTS.EllipticEst.TT.EllWeak0 C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb (Work.Spaces.DzIter 1 Ψ)))
        ≤ C * Work.Spaces.HkNorm α 2 F := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.TT.slot11_le
  obtain ⟨CZb, hCZbpos, hZB⟩ := HkSq_zero_DzIter_Bb_le h0
  obtain ⟨C3, hC3pos, hC3⟩ := aShiftSlotTop h0
  refine ⟨Real.sqrt (K * (3 * CZb + 1 + C3 ^ 2)) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  have hB : SmoothOpen (Bb Ψ) := smoothOpen_pthIter_aux hΨ 2
  have hNF : (0 : ℝ) ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  -- the left-hand side is the `(1,1)`-slot of `∂_θ²Ψ`
  have hLHS : Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb (Work.Spaces.DzIter 1 Ψ))
      = Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) := by
    rw [show Work.FTS.EllipticEst.remov.Step.Tk α 1 (Bb (Work.Spaces.DzIter 1 Ψ))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
            (Bb (Work.Spaces.DzIter 1 Ψ)) z θ * Work.Spaces.Wt α z θ) from rfl]
    refine L2Sq_congr_open (fun z θ hz hθ hlt => ?_)
    rw [mixed01_Bb_Dz_eqOn hΨ z θ hz hθ hlt]
  -- the `α⁴`-term is Term 3
  have hswap : AgreeOnQ (Work.Spaces.mixed 0 1 (Ab (Work.Spaces.DzIter 1 Ψ)))
      (Work.Spaces.mixed 0 1 (Work.Spaces.DzIter 1 (Ab Ψ))) :=
    (Ab_Dz_eqOn hΨ).Dth
  have hmm := mixed01_Dz_eq_mixed11 (smoothOpen_zsq_mul (hΨ.pzIter 2))
  have hT3slot : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ)
      = Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ)) := by
    rw [show Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
            (Ab (Work.Spaces.DzIter 1 Ψ)) z θ * Work.Spaces.Wt α z θ) from rfl]
    refine (L2Sq_congr_open (fun z θ hz hθ hlt => ?_)).symm
    rw [hswap z θ hz hθ hlt, hmm z θ hz hθ hlt]
  -- the three pure slots
  have hsum : (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
      ≤ 3 * (CZb * Work.Spaces.HkSq α 2 F) := by
    have h1 : ∀ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ CZb * Work.Spaces.HkSq α 2 F := by
      intro j hj
      have hj2 : j ≤ 2 := by
        have := Finset.mem_range.mp hj; omega
      have hb := hZB α F Ψ hα hα4 h j hj2
      rw [HkSq_zero_Bb_DzIter_eq hΨ j] at hb
      rw [HkSq_zero_eq_L2Sq_zu α (Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ))] at hb
      exact hb
    calc (∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
            Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
        ≤ ∑ j ∈ Finset.range 3, (CZb * Work.Spaces.HkSq α 2 F) := Finset.sum_le_sum h1
      _ = 3 * (CZb * Work.Spaces.HkSq α 2 F) := by
          rw [Finset.sum_const, Finset.card_range]; norm_num
  -- the `α⁴`-term
  have hT3b : α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ C3 ^ 2 * Work.Spaces.HkSq α 2 F := by
    rw [hT3slot]
    have h3 := hC3 α F Ψ hα hα4 h
    have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Tk α 1 (Ab (Work.Spaces.DzIter 1 Ψ)) :=
      Work.FTS.EllipticEst.remov.Step.Tk_nonneg α 1 _
    have hsq : (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Ab (Work.Spaces.DzIter 1 Ψ)))) ^ 2
        = α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Ab (Work.Spaces.DzIter 1 Ψ)) := by
      rw [mul_pow, Real.sq_sqrt hnn]
      ring
    rw [← hsq]
    calc (α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Ab (Work.Spaces.DzIter 1 Ψ)))) ^ 2
        ≤ (C3 * Work.Spaces.HkNorm α 2 F) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
      _ = C3 ^ 2 * Work.Spaces.HkSq α 2 F := by
          rw [mul_pow, Work.Spaces.HkNorm, Real.sq_sqrt hNF]
  -- the slot-11 bound
  have hb := hK α F Ψ hα hα4 h
  rw [hLHS]
  have hstep : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ K * ((3 * (CZb * Work.Spaces.HkSq α 2 F)) + Work.Spaces.HkSq α 2 F
          + C3 ^ 2 * Work.Spaces.HkSq α 2 F) := by
    calc Work.Spaces.L2Sq (fun z θ =>
          Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ)
        ≤ K * ((∑ j ∈ Finset.range 3, Work.Spaces.L2Sq (fun z θ =>
              Work.Spaces.pthIter 2 (Work.Spaces.DzIter j Ψ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
            + Work.Spaces.HkSq α 2 F
            + α ^ 4 * Work.Spaces.L2Sq (fun z θ =>
                Work.Spaces.mixed 1 1 (Ab Ψ) z θ * Work.Spaces.Wt α z θ)) := hb
      _ ≤ K * ((3 * (CZb * Work.Spaces.HkSq α 2 F)) + Work.Spaces.HkSq α 2 F
            + C3 ^ 2 * Work.Spaces.HkSq α 2 F) := by
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          linarith [hsum, hT3b]
  have hfin : Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ)
      ≤ K * (3 * CZb + 1 + C3 ^ 2) * Work.Spaces.HkSq α 2 F := by
    refine le_trans hstep ?_
    rw [show K * ((3 * (CZb * Work.Spaces.HkSq α 2 F)) + Work.Spaces.HkSq α 2 F
          + C3 ^ 2 * Work.Spaces.HkSq α 2 F)
        = K * (3 * CZb + 1 + C3 ^ 2) * Work.Spaces.HkSq α 2 F from by ring]
  have hnn : (0 : ℝ) ≤ Work.Spaces.L2Sq (fun z θ =>
      Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ) :=
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  calc Real.sqrt (Work.Spaces.L2Sq (fun z θ =>
        Work.Spaces.mixed 1 1 (Bb Ψ) z θ * Work.Spaces.Wt α z θ))
      ≤ Real.sqrt (K * (3 * CZb + 1 + C3 ^ 2) * Work.Spaces.HkSq α 2 F) :=
        Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (K * (3 * CZb + 1 + C3 ^ 2)) * Work.Spaces.HkNorm α 2 F := by
        rw [Work.Spaces.HkNorm, Real.sqrt_mul (by positivity)]
    _ ≤ (Real.sqrt (K * (3 * CZb + 1 + C3 ^ 2)) + 1) * Work.Spaces.HkNorm α 2 F := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (K * (3 * CZb + 1 + C3 ^ 2)) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 2 F := Work.Spaces.HkNorm_nonneg α 2 F
        nlinarith [mul_nonneg h1 h2, h2]

end Work.FTS.EllipticEst.Prop
