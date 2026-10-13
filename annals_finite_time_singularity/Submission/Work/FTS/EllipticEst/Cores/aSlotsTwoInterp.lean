/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/aSlotsTwoInterp` — the shifted `A`-slot from the light-weight interpolation

The target `T2 = α⁴ · Tk α 1 (D_z A)` (`A = z²∂_z²Ψ`) is, on the open quadrant, the `(1,1)`-slot
`α⁴ L2Sq (mixed 1 1 A · Wt α)` of the datum `A` (commutation of `D_θ` and `D_z` on the open
quadrant), and this is *exactly* the left-hand side of Elgindi's light-weight interpolation
`TT.interpGamma` at `G = A` (`TT.L2Sq_slot11_eq`), with the angular weight `σ_a = sin(2θ)^{2-γ}`
carried by the `(1,1)`-slot of `A` in the class `EllWeakPos α 2`.

The three `ℋ⁰`-slots on the right-hand side of `interpGamma` at `G = A` are

* `α⁴ HkSq α 0 (DzIter 2 A)` — `= α⁴ HkSq α 0 (rad2 (DzIter 2 Ψ))`, the `j = 2` first slot of
  `Cores.shiftZeroSlots_clean`;
* `HkSq α 0 (pthIter 2 A)` — `≤ 2 HkSq α 0 (pthIter 2 (DzIter 2 Ψ)) + 2 HkSq α 0 (pthIter 2
  (DzIter 1 Ψ))`, the `j = 2, 1` second slots of `Cores.shiftZeroSlots_clean`;
* `α² HkSq α 0 (DzIter 1 A)` — `= α² HkSq α 0 (rad2 (DzIter 1 Ψ))`, the `j = 1` first slot.

All three are *proved* (axiom-clean, `h0`-conditional) in `Cores/aSlotsTwoDefs.lean`; the
hypotheses of the interpolation at `G = A` are one-liners from `H2W.AeDataAofAux` together with
the proved `TT.gammaHonesty`.  Hence the whole target reduces to the single analytic input
`TT.interpGamma` — equivalently to its core `TT.interpGamma_core` (delegated as
`interpGammaCoreFts`), through `interpGammaStmt_of_core`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cores.aSlotsTwoDefs
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.interpGamma
import Submission.Work.FTS.EllipticEst.TT.gammaHonesty
import Submission.Work.FTS.EllipticEst.TT.aShiftSlotAux
import Submission.Work.FTS.EllipticEst.H2W.AeDataAof
import Submission.Work.FTS.EllipticEst.H2W.HkMem_zero_slices
import Submission.Work.FTS.EllipticEst.H2W.ESV.easySlotsAe
import Submission.Work.FTS.EllipticEst.RPFresh.excess_finite
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof

/-! ## Congruence of `L2Sq` on the open quadrant -/

/-- **The weighted `L2Sq` of two functions agreeing on the open quadrant.**  The weight `Wt α`
vanishes on the degenerate set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` (Lean's `rpow` gives
`0^x = 0` for `x ≠ 0`), so the integrands agree *pointwise* on `Iz × Iθ`. -/
theorem l2sq_congr_q {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.Wt α z θ)
      = Work.Spaces.L2Sq (fun z θ => g z θ * Work.Spaces.Wt α z θ) := by
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hexp : -(Work.Spaces.gam α / 2) ≠ 0 := by linarith
  rw [Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hz0
  · subst hz0; simp [Work.Spaces.Wt, Work.Spaces.w]
  rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
  · subst hθ0
    have hzero : Work.Spaces.Wt α z 0 = 0 := by
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
      simp [Real.zero_rpow hexp]
    rw [hzero]; ring
  rcases eq_or_lt_of_le hθ.2 with hθ2 | hθ2
  · subst hθ2
    have hzero : Work.Spaces.Wt α z (Real.pi / 2) = 0 := by
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp [Real.zero_rpow hexp]
    rw [hzero]; ring
  · rw [h z θ hz0 hθ0 hθ2]

/-! ## The two statement-level `Prop`s of the interpolation -/

/-- **The analytic core of the light-weight interpolation** (the input `hcore` of
`TT.interpGamma_of_core`, and verbatim the statement of `TT.interpGamma_core`). -/
def InterpGammaCore : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      Work.FTS.EllipticEst.TT.Xint α G
        ≤ C * (Real.sqrt (Work.FTS.EllipticEst.TT.DDint α G
              * Work.FTS.EllipticEst.TT.TTint α G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))

/-- **The light-weight interpolation** (the conclusion of `TT.interpGamma`), in the shape in
which this file consumes it. -/
def InterpGammaStmt : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 G) →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 G) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz →
      α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ
            * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
        ≤ C * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 G)
            + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 G)
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 G))

/-- **The interpolation from its core**: `TT.interpGamma_of_core` with the slot comparison
`TT.interpGamma_slots`. -/
theorem interpGammaStmt_of_core (hcore : InterpGammaCore) : InterpGammaStmt :=
  Work.FTS.EllipticEst.TT.interpGamma_of_core hcore
    Work.FTS.EllipticEst.TT.interpGamma_slots

/-! ## The hypotheses of the interpolation at `G = A` -/

/-- **The hypotheses of `interpGamma` at `G = A = z²∂_z²Ψ`**, from the certificates of the weak
class (`H2W.AeDataAofAux`) and the proved `TT.gammaHonesty`. -/
theorem aHypotheses {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) ∧
      (∀ z : ℝ, Aof Ψ z 0 = 0) ∧
      (∀ z : ℝ, Aof Ψ z (Real.pi / 2) = 0) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Aof Ψ)) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 (Aof Ψ)) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Aof Ψ)) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz := by
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAofSm : Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨsm.pzIter 2)
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α (Aof Ψ)
      (Work.FTS.EllipticEst.H2W.Gof F) :=
    Work.FTS.EllipticEst.H2W.AeDataAof α F Ψ hα hα4 h
  exact ⟨hAofSm, fun z => hAe.dirZero z, fun z => hAe.dirPi z,
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2
      (Aof Ψ) ((hAofSm.DzIter 2).continuousOn) h.memA le_rfl,
    Work.FTS.EllipticEst.H2W.AeDataAofAux.HkMem_zero_pthIter2_zsq_pzIter2 hΨsm h.memB,
    Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1
      (Aof Ψ) ((hAofSm.DzIter 1).continuousOn) h.memA (by norm_num),
    Work.FTS.EllipticEst.TT.gammaHonesty hα hα4 h⟩

/-! ## The reduction -/

/-- **The shifted `A`-slot from the light-weight interpolation**: given `interpGamma` and the
level-`0` estimate `h0`, the target `T2 = α⁴ Tk α 1 (D_z A)` is `≤ C |F|²_{ℋ²}`. -/
theorem aSlotsTwoT2x_of_interpGamma
    (hI : InterpGammaStmt)
    (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨CI, hCIpos, hIb⟩ := hI
  obtain ⟨C₂, hC₂pos, hC₂b⟩ := shiftZeroSlots_clean 2 2 le_rfl
  obtain ⟨C₁, hC₁pos, hC₁b⟩ := shiftZeroSlots_clean 2 1 (by norm_num)
  set M : ℝ := max (max C₂ (2 * C₂ + 2 * C₁)) C₁ with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (le_trans (le_of_lt hC₂pos) (le_max_left _ _)) (le_max_left _ _)
  refine ⟨CI * (3 * M) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨hAso, hdir0, hdirpi, hM2, hMB, hM1, hgam⟩ := aHypotheses hα hα4 h
  have hFnn : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  -- ### the two `D_z`-slots (the `j = 2, 1` first slots of the shifted level-`0` estimate)
  have ez2 := hC₂b α F Ψ hα hα4 h h0
  have ez1 := hC₁b α F Ψ hα hα4 h h0
  have eD2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
      = Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter 2 Ψ) z θ) := by
    have h1 : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.DzIter 1 (Aof Ψ))
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
      Work.FTS.EllipticEst.Cores.Dz_zsq_pzIter_two_agree hΨso
    have h2 : Work.FTS.EllipticEst.AgreeOnQ
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter 1 Ψ) z θ))
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.Cores.Dz_zsq_pzIter_two_agree (hΨso.DzIter 1)
    exact Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 => by
      show Work.Spaces.DzIter 2 (Aof Ψ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
      exact (h1.Dz z θ hz hθ0 hθ1).trans (h2 z θ hz hθ0 hθ1))
  have eD1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))
      = Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter 1 Ψ) z θ) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
      Work.FTS.EllipticEst.Cores.Dz_zsq_pzIter_two_agree hΨso z θ hz hθ0 hθ1)
  have b2 : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
      ≤ M * Work.Spaces.HkSq α 2 F := by
    have hleft : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
        = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.Spaces.DzIter 2 Ψ) z θ) := by rw [eD2]
    have hstep : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter 2 Ψ) z θ) ≤ C₂ * Work.Spaces.HkSq α 2 F := by
      linarith [ez2, Work.Spaces.HkSq_nonneg α 0
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))]
    have hC₂M : C₂ ≤ M := by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact le_trans (le_of_eq hleft) (le_trans hstep
      (mul_le_mul_of_nonneg_right hC₂M hFnn))
  have b1 : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))
      ≤ M * Work.Spaces.HkSq α 2 F := by
    have hleft : α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))
        = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.Spaces.DzIter 1 Ψ) z θ) := by rw [eD1]
    have hstep : α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.DzIter 1 Ψ) z θ) ≤ C₁ * Work.Spaces.HkSq α 2 F := by
      linarith [ez1, Work.Spaces.HkSq_nonneg α 0
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))]
    have hC₁M : C₁ ≤ M := by rw [hMdef]; exact le_max_right _ _
    exact le_trans (le_of_eq hleft) (le_trans hstep
      (mul_le_mul_of_nonneg_right hC₁M hFnn))
  -- ### the angular slot `∂_θ²A`
  have hEZ2 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
      ≤ C₂ * Work.Spaces.HkSq α 2 F := by
    have hstep : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 => by
        have hc := Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 2 hΨso
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
        simpa only [Function.uncurry_apply_pair] using hc.symm)
    have hn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.Spaces.DzIter 2 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
    rw [hstep]
    linarith [ez2, hn]
  have hEZ1 : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
      ≤ C₁ * Work.Spaces.HkSq α 2 F := by
    have hstep : Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 => by
        have hc := Work.FTS.EllipticEst.H2W.pthIter_two_DzIter_comm Ψ 1 hΨso
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
        simpa only [Function.uncurry_apply_pair] using hc.symm)
    have hn : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.Spaces.DzIter 1 Ψ) z θ) :=
      mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
    rw [hstep]
    linarith [ez1, hn]
  have bB : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
      ≤ M * Work.Spaces.HkSq α 2 F := by
    have hidentA : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
        = Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
            (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 =>
        Work.FTS.EllipticEst.H2W.AeDataAofAux.pthIter_two_zsq_pzIter2_eq hΨso hz
          ⟨hθ0, hθ1⟩)
    have hidentB : Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
          (Work.Spaces.pthIter 2 Ψ) z θ)
        = Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 0 (fun z θ hz hθ0 hθ1 => by
        have h2 := Work.FTS.EllipticEst.zsq_pzIter2_eq (Work.Spaces.pthIter 2 Ψ)
          ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).hasDerivAt_slice
            ⟨hθ0, hθ1⟩ hz).differentiableAt
          ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).hasDerivAt_slice_pzIter 1
            ⟨hθ0, hθ1⟩ hz).differentiableAt
        show z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
          = (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)
              - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
        simpa using h2)
    have hsub := Work.FTS.EllipticEst.H2W.HkSq_zero_sub_le α
      (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
      (Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 2
        (Work.Spaces.pthIter 2 Ψ)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 2).continuousOn
        h.memB le_rfl)
      (Work.FTS.EllipticEst.H2W.AeDataAofAux.excess_zsummand_mem α 2 1
        (Work.Spaces.pthIter 2 Ψ)
        ((Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨso 2).DzIter 1).continuousOn
        h.memB (by norm_num))
    have hsum : 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
        + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ))
        ≤ (2 * C₂ + 2 * C₁) * Work.Spaces.HkSq α 2 F := by
      have h1 := mul_le_mul_of_nonneg_left hEZ2 (by norm_num : (0:ℝ) ≤ 2)
      have h2 := mul_le_mul_of_nonneg_left hEZ1 (by norm_num : (0:ℝ) ≤ 2)
      linarith
    have hMM : 2 * C₂ + 2 * C₁ ≤ M := by
      rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    calc Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)
            - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) := hidentA.trans hidentB
      _ ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ))
            + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) := hsub
      _ ≤ (2 * C₂ + 2 * C₁) * Work.Spaces.HkSq α 2 F := hsum
      _ ≤ M * Work.Spaces.HkSq α 2 F := mul_le_mul_of_nonneg_right hMM hFnn
  -- ### the interpolation at `G = A`
  have hIapp := hIb α (Aof Ψ) hα hα4 hAso hdir0 hdirpi hM2 hMB hM1 hgam
  have hα2le : α ^ 2 ≤ 1 := by nlinarith [hα, hα4]
  have hcomb : α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
        + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
      ≤ (3 * M) * Work.Spaces.HkSq α 2 F := by
    have h1 : α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ)))
        ≤ M * Work.Spaces.HkSq α 2 F := by
      calc α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ)))
          ≤ 1 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))) :=
            mul_le_mul_of_nonneg_right hα2le
              (mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _))
        _ = α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ)) := one_mul _
        _ ≤ M * Work.Spaces.HkSq α 2 F := b2
    have h2 : α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
        ≤ M * Work.Spaces.HkSq α 2 F :=
      calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
          ≤ 1 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ)) :=
            mul_le_mul_of_nonneg_right hα2le (Work.Spaces.HkSq_nonneg α 0 _)
        _ = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ)) := one_mul _
        _ ≤ M * Work.Spaces.HkSq α 2 F := bB
    have h3 : α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
        ≤ M * Work.Spaces.HkSq α 2 F := by
      have he : α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
          = α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)) := by ring
      rw [he]; exact b1
    calc α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
        = α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ)))
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
          + α ^ 2 * (α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ))) := by ring
      _ ≤ M * Work.Spaces.HkSq α 2 F + M * Work.Spaces.HkSq α 2 F
          + M * Work.Spaces.HkSq α 2 F := add_le_add (add_le_add h1 h2) h3
      _ = (3 * M) * Work.Spaces.HkSq α 2 F := by ring
  have hfinal : α ^ 4 * Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth (Aof Ψ))
        z θ * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z)
      ≤ CI * (3 * M) * Work.Spaces.HkSq α 2 F := by
    refine hIapp.trans ?_
    calc CI * α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))
        = CI * (α ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 2 (Aof Ψ))
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aof Ψ))
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.DzIter 1 (Aof Ψ)))) := by ring
      _ ≤ CI * ((3 * M) * Work.Spaces.HkSq α 2 F) :=
          mul_le_mul_of_nonneg_left hcomb (le_of_lt hCIpos)
      _ = CI * (3 * M) * Work.Spaces.HkSq α 2 F := by ring
  -- ### back to the `Tk`-form of the target
  have hTk : Work.FTS.EllipticEst.remov.Step.Tk α 1
        (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      = Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dz (Work.Spaces.pth (Aof Ψ)) z θ
          * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) / 2) * Work.Spaces.w z) := by
    rw [show Work.FTS.EllipticEst.remov.Step.Tk α 1
          (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1 (Aof Ψ) z θ
            * Work.Spaces.Wt α z θ) from ?_]
    · exact Work.FTS.EllipticEst.TT.L2Sq_slot11_eq α (Aof Ψ) hα hα4
    · rw [show Work.FTS.EllipticEst.remov.Step.Tk α 1
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
          = Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1 (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
                * Work.Spaces.Wt α z θ) from rfl]
      refine l2sq_congr_q (α := α) hα (fun z θ hz hθ hlt => ?_)
      have hp : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
      have hq := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
        Work.FTS.EllipticEst.isOpen_Q0
        (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall (Aof Ψ)).mp hAso n) 1 1 hp
      simpa only [Function.uncurry_apply_pair, Work.Spaces.mixed_zero_left,
        Work.FTS.EllipticEst.H2W.Aof] using hq
  rw [hTk]
  nlinarith [hfinal, hFnn]

end

end Work.FTS.EllipticEst.Cores
