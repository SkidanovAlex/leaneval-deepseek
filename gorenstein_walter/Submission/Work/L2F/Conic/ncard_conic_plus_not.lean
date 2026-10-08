import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.Param
import Submission.Work.L2F.Conic.conicParam_mem
import Submission.Work.L2F.Conic.conicSlope_conicParam
import Submission.Work.L2F.Conic.conicParam_conicSlope

namespace Work.L2F.Conic

/-- If `-1` is not a square in a finite field of odd characteristic, the conic `a² + b² = 1` has
`q + 1` points.  Proof: `(a,b) ↦ a/(1 - b)` is a bijection from the conic minus `(0,1)` onto
`{t : F // t² + 1 ≠ 0}` (inverse `t ↦ (2t/(t²+1), (t²-1)/(t²+1))`).  Since `t² + 1 = 0` has no
solution, the conic has `1 + q` points. -/
theorem ncard_conic_plus_not (F : Type*) [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (h : ∀ i : F, i * i ≠ -1) :
    {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard = Nat.card F + 1 := by
  -- `conicSlope` and `conicParam` are mutually inverse, so they exhibit a bijection between the
  -- conic and `F ⊔ {∞} = Option F`; hence the conic has `Nat.card (Option F) = q + 1` points.
  have key := Set.ncard_congr (s := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1})
    (t := (Set.univ : Set (Option F))) (f := fun p _ => conicSlope F p)
    (fun _ _ => Set.mem_univ _)
    (fun a b ha hb hab => by
      have h' := congrArg (conicParam F) hab
      rw [conicParam_conicSlope F h2 ha, conicParam_conicSlope F h2 hb] at h'
      exact h')
    (fun m _ => ⟨conicParam F m, conicParam_mem F h m, conicSlope_conicParam F h2 h m⟩)
  simpa using key

end Work.L2F.Conic
