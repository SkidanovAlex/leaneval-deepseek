import Mathlib

/-!
# Filling finitely many points by punctured limits

If `f : ℂ → ℂ` is holomorphic off a finite set `P`, the natural "filled" function agrees with
`f` off `P` and at `p ∈ P` carries the value `limUnder (𝓝[≠] p) f`, the punctured limit of `f`
at `p`.  When `f` is moreover locally bounded at each point of `P`, the removable singularity
theorem shows that this filled function is entire; that is the content of
`Submission.Work.EQ.polynomial_of_analyticOn_compl_finset`.
-/

namespace Work.EQ

open Filter _root_.Topology

/-- Replace the value of `f` at every point of the finite set `P` by the punctured limit
`limUnder (𝓝[≠] z) f` (an arbitrary value when that limit does not exist). -/
noncomputable def fill (f : ℂ → ℂ) (P : Finset ℂ) : ℂ → ℂ :=
  fun z => if z ∈ P then limUnder (𝓝[≠] z) f else f z

@[simp] lemma fill_of_notMem {f : ℂ → ℂ} {P : Finset ℂ} {z : ℂ} (hz : z ∉ P) :
    fill f P z = f z := by
  simp [fill, hz]

lemma fill_of_mem {f : ℂ → ℂ} {P : Finset ℂ} {z : ℂ} (hz : z ∈ P) :
    fill f P z = limUnder (𝓝[≠] z) f := by
  simp [fill, hz]

end Work.EQ
