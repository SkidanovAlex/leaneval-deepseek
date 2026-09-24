import ChallengeDeps
import Submission.PerronOn
import Submission.SuperharmonicX

/-!
# The dual (balayage) Perron theorem

`Submission.IsPerronOn.upperEnvelope_harmonic` produces a harmonic function as the **upper**
envelope of a family of *subharmonic* functions closed under harmonic replacement.  The dual
statement produces a harmonic function as the **lower** envelope of a family of *superharmonic*
functions.  The dual is what one needs for the balayage (sweeping) construction of the Green
function: the Green function is the infimum of the superharmonic functions with non-negative
values and a logarithmic pole.

The passage to the dual is purely formal: the pointwise infimum of `F` is the negative of the
pointwise supremum of `-F`, while the *superharmonic* family conditions for `F` are exactly the
*subharmonic* Perron conditions for `-F` (using the negation bridges of
`Submission/SuperharmonicX.lean` and the fact that the pointwise minimum of two superharmonic
functions is superharmonic).  Hence the dual theorem follows from the existing Perron theorem,
and we *define* the dual family predicate by transport:

`IsPerronOnInf F W U := IsPerronOn ((fun f => -f) '' F) (fun x => -W x) U`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The **lower envelope** of a family of real-valued functions: the pointwise infimum. -/
def lowerEnvelope (F : Set (X → ℝ)) : X → ℝ := fun x => sInf (F.image (fun f => f x))

/-- The lower envelope of `F` is the negative of the upper envelope of `-F`. -/
theorem lowerEnvelope_eq_neg_upperEnvelope (F : Set (X → ℝ)) (x : X) :
    lowerEnvelope F x = -upperEnvelope ((fun f : X → ℝ => -f) '' F) x := by
  have himg : ((fun f : X → ℝ => -f) '' F).image (fun g => g x)
      = -((fun f : X → ℝ => f x) '' F) := by
    ext y
    simp
    constructor
    · rintro ⟨f, hf, h⟩
      exact ⟨f, hf, by linarith⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨f, hf, by linarith⟩
  rw [lowerEnvelope, upperEnvelope, himg]
  have h := Real.sInf_neg (-((fun f : X → ℝ => f x) '' F))
  rw [show -(-((fun f : X → ℝ => f x) '' F)) = ((fun f : X → ℝ => f x) '' F) from by
        ext z; simp [Set.mem_neg]] at h
  exact h

/-- **Dual (balayage) Perron family.**  The negation of a Perron family of subharmonic functions:
a family of superharmonic functions, bounded below on `U`, closed under pointwise minima and
closed under harmonic replacement in small chart discs. -/
def IsPerronOnInf (F : Set (X → ℝ)) (W : X → ℝ) (U : Set X) : Prop :=
  IsPerronOn ((fun f : X → ℝ => -f) '' F) (fun x => -W x) U

theorem IsPerronOnInf.nonempty {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (h : IsPerronOnInf F W U) : F.Nonempty := by
  obtain ⟨g, ⟨f, hf, -⟩⟩ := h.1
  exact ⟨f, hf⟩

/-- **The dual Perron theorem**: the lower envelope of a balayage family is harmonic. -/
theorem IsPerronOnInf.lowerEnvelope_harmonic {F : Set (X → ℝ)} {W : X → ℝ} {U : Set X}
    (hU : IsOpen U) (h : IsPerronOnInf F W U) : HarmonicOnX (lowerEnvelope F) U := by
  have hharm := h.upperEnvelope_harmonic hU
  have hfun : lowerEnvelope F = fun x => -upperEnvelope ((fun f : X → ℝ => -f) '' F) x := by
    funext x
    exact lowerEnvelope_eq_neg_upperEnvelope F x
  rw [hfun]
  exact hharm.neg

end Submission
