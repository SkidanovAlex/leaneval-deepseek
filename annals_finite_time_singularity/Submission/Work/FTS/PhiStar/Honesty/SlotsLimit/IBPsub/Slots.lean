/-
# `FTS/PhiStar/Honesty/SlotsLimit/IBPsub.Slots`

The transposes of the three slot operators

* `slot1 f = z² ∂_z² f` — two plain `z`-integrations by parts (the factor `z²` is simply
  multiplied onto the test function),
* `slot2 f = ∂_θ² f` — two plain `θ`-integrations by parts,
* `slot3 f = D_z ∂_θ² f` — the `D_z`-transpose followed by two plain `θ`-integrations by parts,

together with the closure of `TestQ0` under the three slot transposes.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Iterate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Closure of `SmoothOpen` and `TestQ0` for the slot operators -/

/-- Multiplication by a power of `z` preserves smoothness on the open quadrant. -/
theorem smoothOpen_zpow_mul (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ k * f z θ) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ k) Q0 :=
    (contDiff_fst.pow k).contDiffOn
  exact h.mul hf

/-- The slot operators preserve smoothness on the open quadrant. -/
theorem smoothOpen_slot {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (slot r f) := by
  rcases r with _ | _ | r
  · show Work.FTS.EllipticEst.SmoothOpen (slot1 f)
    exact smoothOpen_zpow_mul 2 (Work.FTS.EllipticEst.SmoothOpen.pzIter hf 2)
  · show Work.FTS.EllipticEst.SmoothOpen (slot2 f)
    exact smoothOpen_pthIter hf 2
  · show Work.FTS.EllipticEst.SmoothOpen (slot3 f)
    exact Work.FTS.EllipticEst.SmoothOpen.Dz (smoothOpen_pthIter hf 2)

/-- The transpose of the first slot preserves the class of test functions. -/
theorem testQ0_slot1Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot1Star ψ) :=
  testQ0_pzIterStar (testQ0_zpow_mul 2 h) 2

/-- The transpose of the second slot preserves the class of test functions. -/
theorem testQ0_slot2Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot2Star ψ) :=
  testQ0_pthIterStar h 2

/-- The transpose of the third slot preserves the class of test functions. -/
theorem testQ0_slot3Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot3Star ψ) :=
  testQ0_pthIterStar (testQ0_DzStar h) 2

/-! ## The transposes of the three slots -/

/-- **The transpose of `slot1 f = z² ∂_z² f`.** -/
theorem integral_slot1_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pzIterStar 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
  have hz2 : TestQ0 (fun z θ => z ^ 2 * ψ z θ) := testQ0_zpow_mul 2 hψ
  have hstep : ∫ p : ℝ × ℝ,
        Work.Spaces.pzIter 2 f p.1 p.2 * (p.1 ^ 2 * ψ p.1 p.2)
      = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 :=
    integral_pzIter_mul_eq 2 hf hz2
  calc ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pzIter 2 f p.1 p.2 * (p.1 ^ 2 * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [slot1]; ring
    _ = ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
        rw [hstep]
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
    _ = ∫ p : ℝ × ℝ,
          f p.1 p.2 * pzIterStar 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pzIterStar]

/-- **The transpose of `slot2 f = ∂_θ² f`.** -/
theorem integral_slot2_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 ψ p.1 p.2 := by
  have hstep := integral_pthIter_mul_eq 2 hf hψ
  calc ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * ψ p.1 p.2 := rfl
    _ = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pthIter 2 ψ p.1 p.2 := hstep
    _ = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 ψ p.1 p.2 := by
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pthIterStar]

/-- **The transpose of `slot3 f = D_z ∂_θ² f`.** -/
theorem integral_slot3_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 (DzStar ψ) p.1 p.2 := by
  have h1 : ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * DzStar ψ p.1 p.2 :=
    integral_Dz_mul_eq (g := Work.Spaces.pthIter 2 f) (ψ := ψ)
      (smoothOpen_pthIter hf 2) hψ
  have h2 := integral_pthIter_mul_eq 2 (g := f) (ψ := DzStar ψ) hf (testQ0_DzStar hψ)
  calc ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * DzStar ψ p.1 p.2 := h1
    _ = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pthIter 2 (DzStar ψ) p.1 p.2 := h2
    _ = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 (DzStar ψ) p.1 p.2 := by
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pthIterStar]

/-! ## The sub-slot transposition on `ℝ²` -/

/-- The transposition of the `(j,i)`-sub-slot of the `r`-th slot, as an identity of integrals
over `ℝ²` (which is where the integration by parts lives). -/
theorem integral_mixed_subSlot (r j i : ℕ) {f φ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hφ : TestQ0 φ) :
    ∫ p : ℝ × ℝ, Work.Spaces.mixed j i (slot r f) p.1 p.2 * φ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * subSlotStar r j i φ p.1 p.2 := by
  rw [integral_mixed_mul_eq j i (hg := smoothOpen_slot hf r) (hψ := hφ)]
  rcases r with _ | _ | r
  · show ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot1Star (mixedStar j i φ) p.1 p.2
    exact integral_slot1_mul_eq hf (testQ0_mixedStar hφ j i)
  · show ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot2Star (mixedStar j i φ) p.1 p.2
    exact integral_slot2_mul_eq hf (testQ0_mixedStar hφ j i)
  · show ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot3Star (mixedStar j i φ) p.1 p.2
    exact integral_slot3_mul_eq hf (testQ0_mixedStar hφ j i)

end Work.FTS.PhiStar.Honesty.SlotsLimit
