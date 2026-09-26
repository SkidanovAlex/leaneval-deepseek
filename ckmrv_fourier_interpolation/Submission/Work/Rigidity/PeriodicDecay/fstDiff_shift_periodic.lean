import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff

namespace Work.Rigidity.PeriodicDecay

/-- The function `z ↦ fstDiff f (z + I)` on `ℂ` is periodic of period `1` whenever `f` is
annihilated by `(T − I)²`.  Indeed, for `z` with `-1 < z.im` both points `z + I` and
`z + 1 + I` are in the upper half plane and differ by the translation `1`, under which
`fstDiff f` is invariant by `Work.Rigidity.fstDiff_vadd_one_iff`; for `z.im ≤ -1` the
section `UpperHalfPlane.ofComplex` is constant (it only depends on the imaginary part
being nonpositive), so both sides are literally the same. -/
theorem fstDiff_shift_periodic {f : UpperHalfPlane → ℂ} (hT : Work.Rigidity.AnnT2 f) :
    Function.Periodic
      (fun z : ℂ => Work.Rigidity.fstDiff f (UpperHalfPlane.ofComplex (z + Complex.I))) 1 := by
  intro z
  show Work.Rigidity.fstDiff f (UpperHalfPlane.ofComplex ((z + 1) + Complex.I)) =
      Work.Rigidity.fstDiff f (UpperHalfPlane.ofComplex (z + Complex.I))
  have hper : ∀ τ : UpperHalfPlane,
      Work.Rigidity.fstDiff f ((1 : ℝ) +ᵥ τ) = Work.Rigidity.fstDiff f τ :=
    (Work.Rigidity.fstDiff_vadd_one_iff f).mp hT
  have him : ((z + 1) + Complex.I).im = (z + Complex.I).im := by
    simp only [Complex.add_im, Complex.one_im, Complex.I_im]
    ring
  by_cases hw : 0 < (z + Complex.I).im
  · -- the interesting case: `z + I` and `z + 1 + I` both lie in `ℍ`, and `fstDiff f` is
    -- invariant under translation by `1`
    have hw' : 0 < ((z + 1) + Complex.I).im := him ▸ hw
    have hstep : ((1 : ℝ) +ᵥ (⟨z + Complex.I, hw⟩ : UpperHalfPlane))
        = UpperHalfPlane.ofComplex ((z + 1) + Complex.I) := by
      ext
      rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      push_cast
      ring
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw, ← hstep]
    exact hper _
  · -- `ofComplex` is constant on the set of points with nonpositive imaginary part
    have hwle : (z + Complex.I).im ≤ 0 := le_of_not_gt hw
    have hw'le : ((z + 1) + Complex.I).im ≤ 0 := by rw [him]; exact hwle
    exact congrArg (Work.Rigidity.fstDiff f)
      (UpperHalfPlane.ofComplex_apply_eq_of_im_nonpos hw'le hwle)

end Work.Rigidity.PeriodicDecay
