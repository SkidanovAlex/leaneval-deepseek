import Mathlib
import Submission.Work.FIArea7.SumChiDefs
import Submission.Work.FIArea7.UniCharTerm6

namespace Work.FIArea7

/-- **`uniSChar` is the Fourier transform of the class function `uniClassFn`.** -/
theorem uniSChar_eq_sum_uniClassFn (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q]
    (ε : GaussianInt → ℤ) (v : GaussianInt → ℂ) (k : ℤ)
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ) :
    Work.FIArea7.uniSChar Pa Q ε v k χ
      = ∑ a : Work.FIArea7.GaussUnit Q,
          Work.FIArea7.uniClassFn Pa Q (Work.FIArea7.uniCoeff ε v k) a * χ (Additive.ofMul a) := by
  classical
  -- `uniSChar` is the `z`-sum over the box of `unitCoeff Q c z · χ(unitClassD Q z)`; the
  -- coefficient `unitCoeff Q c z = star (c z) · [z unit mod Q]` vanishes off the units, so
  -- restricting the box sum to the units turns it into `Σ_z star (c z) · χ(unitClassD Q z)`.
  have hA : Work.FIArea7.uniSChar Pa Q ε v k χ
      = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q),
            star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)) := by
    rw [Work.FIArea7.uniSChar]
    have hpt : ∀ z, Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε v k) z * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z))
        = if Nat.Coprime (Work.FIPlan.gnorm z) Q then star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)) else 0 := by
      intro z
      rw [Work.FIArea7.unitCoeff, Work.FIArea7.unitInd]
      by_cases h : Nat.Coprime (Work.FIPlan.gnorm z) Q <;> simp [h]
    calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε v k) z * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z))
        = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (if Nat.Coprime (Work.FIPlan.gnorm z) Q then star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)) else 0) :=
          Finset.sum_congr rfl (fun z _ => hpt z)
      _ = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q), star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)) := by
          rw [Finset.sum_filter]
  -- On the other side, `uniClassFn` groups the unit-box points `z` by their class
  -- `unitClassD Q z`; summing the class function against `χ` recombines the fibres.
  have hB : (∑ a : Work.FIArea7.GaussUnit Q,
          Work.FIArea7.uniClassFn Pa Q (Work.FIArea7.uniCoeff ε v k) a * χ (Additive.ofMul a))
      = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q),
            star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)) := by
    simp only [Work.FIArea7.uniClassFn, Work.FIArea7.uniUnitBox]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_mul _ _ _)]
    have h2 : (∑ a : Work.FIArea7.GaussUnit Q,
          ∑ z ∈ ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q)).filter (fun z => Work.FIArea7.unitClassD Q z = a),
            star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul a))
        = (∑ a : Work.FIArea7.GaussUnit Q,
          ∑ z ∈ ((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q)).filter (fun z => Work.FIArea7.unitClassD Q z = a),
            star (Work.FIArea7.uniCoeff ε v k z) * χ (Additive.ofMul (Work.FIArea7.unitClassD Q z))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro z hz
      rw [show a = Work.FIArea7.unitClassD Q z from (Finset.mem_filter.mp hz).2.symm]
    rw [h2]
    exact Finset.sum_fiberwise _ _ _
  rw [hA, hB]

end Work.FIArea7
