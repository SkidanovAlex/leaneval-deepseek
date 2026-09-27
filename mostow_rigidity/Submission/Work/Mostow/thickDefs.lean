import Mathlib
import Submission.Mostow.SubHypDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

/-!
# Vocabulary for the maximal-injectivity-radius chapter (`thickMax`)

`thick Γ u` is the injectivity radius of the discrete group `Γ` at the point `u` of the chart
`E n = ℍⁿ`: the infimum of the displacement `hdist u (γ • u)` over the nontrivial `γ ∈ Γ`.

Also recorded here: the `θ`/Klein form of the hyperboloid lift, `hlift u = tpart u • θ (klein u)`,
which is the bridge between the hyperboloid model and the affine chart.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The injectivity radius (thickness) of `Γ` at `u`: the infimum of the displacements
`hdist u ((γ : PO n 1) • u)` over the nontrivial elements `γ` of `Γ`. -/
def thick (Γ : Subgroup (PO n 1)) (u : E n) : ℝ :=
  ⨅ γ : {γ : Γ // γ ≠ 1}, hdist u ((γ : PO n 1) • u)

/-- The hyperboloid lift is the `tpart`-multiple of the `θ`-vector of the Klein coordinate. -/
lemma hlift_smul_theta (u : E n) : hlift u = tpart u • theta ((tpart u)⁻¹ • u) := by
  funext j
  rcases j with i | k
  · rw [hlift_inl, Pi.smul_apply, theta_inl, PiLp.smul_apply,
      smul_inv_smul₀ (Hyper.tpart_ne_zero u)]
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [hlift_inr, Pi.smul_apply, theta_inr, smul_eq_mul, mul_one]

end

end Work.Mostow
