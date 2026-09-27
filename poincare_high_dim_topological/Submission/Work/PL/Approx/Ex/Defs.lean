import Submission.Work.PL.Approx.SdSubdiv

/-!
# A counterexample showing that `RestrictsTo` is not automatic

`RestrictsTo` (`Submission/Work/PL/Approx/Defs.lean`) is the compatibility hypothesis of the
frozen variant `pl_approx_frozen`.  It is *not* satisfied by every subcomplex: take the complex
`K` on the two points `0` and `one₁` of `E 1` with faces `{0}`, `{one₁}`, `{0, one₁}` and the
subcomplex `L` with faces `{0}`, `{one₁}`.  For the (unsubdivided) face `s = {0, one₁}` every
vertex lies in `L.space`, so `PL.simp (frozenPart L s)` is the whole segment while
`PL.simp s ∩ L.space = {0, one₁}`.

This file provides the point `one₁`; the counterexample itself is `Ex/not_restrictsTo`.
-/

namespace Work.PL.Approx.Ex

noncomputable section

/-- The point `1` of `E 1`. -/
def one₁ : PL.E 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

/-- The two-point vertex set `{0, one₁}` of `E 1`. -/
def twoVerts : Finset (PL.E 1) := {0, one₁}

@[simp] lemma zero_mem_twoVerts : (0 : PL.E 1) ∈ twoVerts := by simp [twoVerts]

@[simp] lemma one₁_mem_twoVerts : one₁ ∈ twoVerts := by simp [twoVerts]

lemma one₁_ne_zero : one₁ ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : PL.E 1 => ((WithLp.equiv 2 (Fin 1 → ℝ)) x) 0) h
  simp [one₁, WithLp.equiv] at h1

end

end Work.PL.Approx.Ex
