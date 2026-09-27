import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Interp

/-- Two affine maps `A B : ℝᴺ → ℝⁿ` that agree on the vertices of a finite vertex set `s` agree
on the whole simplex `PL.simp s` spanned by `s`.  Indeed `{x | A x = B x}` is convex (it is the
preimage of `{0}` under the affine map `A - B`), so it contains the convex hull of `s`. -/
lemma eqOn_simp_of_eqOn {N n : ℕ} (s : Finset (PL.E N)) (A B : PL.E N →ᵃ[ℝ] PL.E n)
    (h : ∀ v ∈ s, A v = B v) : ∀ x ∈ PL.simp s, A x = B x := by
  have hsub : (s : Set (PL.E N)) ⊆ {x | A x = B x} := by
    intro v hv
    exact h v (by simpa using hv)
  have hconv : Convex ℝ {x | A x = B x} := by
    have heq : {x | A x = B x} = (A - B) ⁻¹' ({0} : Set (PL.E n)) := by
      ext x; simp [sub_eq_zero]
    rw [heq]
    exact Convex.affine_preimage (A - B) (convex_singleton 0)
  intro x hx
  exact convexHull_min hsub hconv hx

end Work.PL.Approx.Interp
