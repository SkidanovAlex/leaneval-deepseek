import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.det_gam_gen

namespace Work.HP.Lat

/-- The determinant of `Λ_v ∩ Λ_w = latOrth v ⊓ latOrth w` is the covolume of `ℤv ⊕ ℤw` divided
by the gcd of the `2 × 2` minors (the paper's "Lemma determinant global", `k = 2`).

Suggested route: let `P̄ = span_ℝ(v,w) ∩ ℤ^ι` be the saturation of `ℤv + ℤw`, so that
`latOrth v ⊓ latOrth w = orthLat P̄` (the `orthLat` of `Work.HP.Vero`).  Ingredients: (i) for saturated
`L ⊆ ℤ^ι`, `detL (orthLat L) = detL L` — choose a `ℤ`-basis `b₁,…,b_R` of `L`, extend it to a
`ℤ`-basis of `ℤ^ι` with matrix `B`, set `M = BᵀB`; then `orthLat L` has a basis whose Gram matrix is
the trailing `(N-R) × (N-R)` block of `M⁻¹`, whose determinant is `det(M_first)/det M` by a
Schur-complement computation; (ii) `detL P̄ = wedgeNorm v w / |gcdMinors2 v w|` since
`[P̄ : ℤv ⊕ ℤw] = gcdMinors2 v w` (Smith normal form: the gcd of the `2×2` minors is the product
of the invariant factors) and `detL (ℤv ⊕ ℤw) = wedgeNorm v w`. -/
theorem detL_inf_latOrth {ι : Type*} [Fintype ι] (v w : ι → ℤ)
    (hvw : LinearIndependent ℤ ![v, w]) :
    detL (latOrth v ⊓ latOrth w) = wedgeNorm v w / |(gcdMinors2 v w : ℝ)| := by
  classical
  rw [(Work.HP.det_gam_gen v w hvw).1,
    abs_of_nonneg (by exact_mod_cast Work.HP.DGG.gcdMinors2_nonneg v w)]

end Work.HP.Lat
