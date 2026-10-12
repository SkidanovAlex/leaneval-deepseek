import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Bridge
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The mean-free projection `boxQ` at the box `A = acube a` with `volA = a³`
coincides with the corpus projection `aQ a`. -/
lemma boxQ_acube_eq_aQ {a : ℝ} {N : ℕ} (i : Fin N) (Φ : X N → ℝ) :
    boxQ (a ^ 3) (acube a) i Φ = aQ a i Φ := by
  unfold boxQ boxP aQ aP
  rfl

/-- The windowed-exponential amplitude `tBamp` built from the box window
`chiScale a` agrees with the corpus slot amplitude `rawSlotAmp a`: the
integrand vanishes off `acube a` (`chiScale_mem_acube`). -/
lemma tBamp_chiScale_eq_rawSlotAmp {a : ℝ} (ha : 0 < a) {N : ℕ} (p : ℝ³)
    (Φ : X N → ℝ) (i : Fin N) (x : X N) :
    tBamp (chiScale a) p Φ i x = rawSlotAmp a p Φ i x := by
  unfold tBamp rawSlotAmp
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube a)
    (f := fun z : ℝ³ => (chiScale a z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Φ (Function.update x i z) : ℂ))
    (fun z hz => by
      have h0 : chiScale a z = 0 := by
        by_contra h
        exact hz (chiScale_mem_acube ha h)
      simp [h0])]

theorem tBdiagForm_chiScale_eq_T0Form {a : ℝ} {n : ℕ} (ha : 0 < a) (F : ℝ → ℝ) (Ψ : Submission.BoseGases.X (n + 1) → ℝ) : Work.SmallBoxTBWord.tBdiagForm a (Submission.BoseGases.acube a) (a ^ 3) (Submission.BoseGases.chiScale a) F Ψ = Submission.BoseGases.T0Form a F Ψ := by
  unfold tBdiagForm T0Form
  simp only [boxQ_acube_eq_aQ, tBamp_chiScale_eq_rawSlotAmp ha]

end Work.SmallBoxTBWord
