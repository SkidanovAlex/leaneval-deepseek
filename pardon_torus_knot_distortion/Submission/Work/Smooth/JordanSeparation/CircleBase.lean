import Submission.Work.Smooth.JordanSeparation.Transfer

/-!
# The base case of the exhaustion: a round circle bounds a disc

`discExtension_circleCurve`: the round circle `θ ↦ c + r·e^{iθ}` bounds an injectively
parametrised disc, namely the radial map `w ↦ c + r·w`.  This is the starting point of every
"sweep"/"exhaustion" route to the Jordan–Schoenflies theorem: the collar transfer
(`CollarTransfer.lean`) moves a filling from a curve to curves parallel to it, and an exhaustion
starts from a small round circle inside the domain.

The round circle is a genuine curve of the required kind: `circleCurve c r` is a `C¹` (`C^∞`)
`2π`-periodic plane curve, and it is `IsSimple` for `r ≠ 0`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section


/-- The **round circle** of centre `c` and radius `r`, as a plane curve. -/
def circleCurve (c : ℂ) (r : ℝ) : PlaneCurve where
  γ := fun θ => c + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  cont := continuous_const.add (continuous_const.mul
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
  periodic := fun θ => by
    have h1 : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
    show c + (r : ℂ) * Complex.exp ((((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I)
      = c + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
    rw [h1, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

@[simp] theorem circleCurve_apply (c : ℂ) (r θ : ℝ) :
    circleCurve c r θ = c + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := rfl

/-- **The round circle bounds an injectively parametrised disc** — the base case of every
exhaustion argument: the radial map `w ↦ c + r·w`. -/
theorem discExtension_circleCurve (c : ℂ) {r : ℝ} (hr : 0 < r) :
    DiscExtension (circleCurve c r) := by
  refine ⟨⟨fun w : Disc => c + (r : ℂ) * (w : ℂ), ?_⟩, ?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul continuous_subtype_val)
  · intro w w' h
    refine Subtype.ext (mul_left_cancel₀ ?_ (add_left_cancel h))
    exact_mod_cast (ne_of_gt hr)
  · intro θ
    show c + (r : ℂ) * ((circlePoint θ : Disc) : ℂ) = circleCurve c r θ
    rw [circlePoint_coe]
    rfl

end

end Work.Smooth.JordanSeparation
