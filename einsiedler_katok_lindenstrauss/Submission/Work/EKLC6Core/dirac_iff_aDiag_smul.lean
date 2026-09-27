import Mathlib
import Submission.Work.EKLC6Core.Covariant

namespace Work.EKLC6Core

open MeasureTheory
open Work.EKLContract

theorem dirac_iff_aDiag_smul {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (t : Fin 3 → ℝ)
    {x : Work.EKLContract.X3}
    (hx : x ∈ X' ∩ X'')
    (hx' : Work.EKLContract.aDiag t • x ∈ X' ∩ X'') :
    (ν x = MeasureTheory.Measure.dirac 1) ↔
      (ν (Work.EKLContract.aDiag t • x) = MeasureTheory.Measure.dirac 1) := by
  -- Along one step of the diagonal flow, `A`-covariance writes `ν z` as a scalar multiple of
  -- the image of `ν y` under conjugation, `z = aDiag s • y`.  The normalisation
  -- `ν z (Box1 U) = 1` pins that scalar to `1` as soon as `ν y = dirac 1`, because
  -- conjugation fixes `1` and `1 ∈ Box1 U`.
  have key : ∀ (y z : X3) (s : Fin 3 → ℝ), y ∈ X' ∩ X'' → z ∈ X' ∩ X'' →
      aDiag s • y = z → ν y = Measure.dirac 1 → ν z = Measure.dirac 1 := by
    intro y z s hy hz hyz hdy
    obtain ⟨c, -, -, hceq⟩ := hcov s y hy.2 (by rw [hyz]; exact hz.2)
    have h1 : ν z = c • Measure.dirac (1 : SL3) := by
      rw [← hyz, hceq, hdy, Measure.map_dirac]
      congr 1
      simp
    have hnorm : ν z (Box1 U) = 1 := hL.normalised z hz.1
    have hd : (Measure.dirac (1 : SL3)) (Box1 U) = 1 := by
      rw [Measure.dirac_apply]
      simp [Box1]
    rw [h1, Measure.smul_apply, hd, smul_eq_mul, mul_one] at hnorm
    rw [h1, hnorm, one_smul]
  constructor
  · intro h
    exact key x (aDiag t • x) t hx hx' rfl h
  · intro h
    exact key (aDiag t • x) x (-t) hx' hx (aDiag_neg_smul t x) h

end Work.EKLC6Core
