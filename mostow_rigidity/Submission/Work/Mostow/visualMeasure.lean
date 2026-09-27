import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.visualAux

/-! Guidance from the project lead (the requester):

# Area T3 — visualMeasure : VisualProp n   (lead's design)

visual n u = sigma n with density P(u,ξ) = exp(−(n−1)·busemann ξ u) = (tpart u − ⟪u,ξ⟫)^{−(n−1)}
(the Poisson kernel). sigma n = normalised `toSphere` of Lebesgue, pushed to E n by Subtype.val.

## Clauses and routes
1. support/atoms/positivity (easy): sigma lives on Sph (image of Subtype.val); sigma has no atoms for n ≥ 2
   (`toSphere` = n·Leb(cone); the cone over a point is a segment, Lebesgue-null); an open U meeting Sph
   has a cone with nonempty interior, so positive mass; P > 0 and continuous, bounded on Sph for fixed u
   (tpart u − ‖u‖ ≤ tpart u − ⟪u,ξ⟫ ≤ tpart u + ‖u‖).
2. THE TRANSFORMATION LAW (the real work): for g ∈ PO,
     sigma.map (bd g) = (ξ ↦ P(g•0, ξ)) · sigma                                  (★)
   (★) is exactly the u = 0 case of the clause (visual 0 = sigma since busemann ξ 0 = 0). The general case is
   then FREE: write u = h•0 (transitivity via boosts); (★) for h gives visual u = sigma.map (bd h); then
   (visual u).map (bd g) = sigma.map (bd g ∘ bd h) = sigma.map (bd (g*h)) (composition law on Sph, sigma lives on
   Sph; use `Measure.map_map` + `Measure.map_congr` a.e.) = visual ((g*h)•0) = visual (g•u).
   Probability: visual u = sigma.map (bd h) has mass 1. In test-function form (★) says
   ∫ F(bd g ξ) dsigma(ξ) = ∫ F(η) P(g•0, η) dsigma(η): P(g•0, ·) is the Jacobian of the INVERSE map bd g⁻¹.
   Route for (★) — reduce to generators and do ONE Jacobian computation:
   - O(n) part: g = diag(Q,1): bd g ξ = Q ξ, sigma is invariant (`toSphere` of the O(n)-invariant Lebesgue
     measure; `LinearIsometryEquiv.measurePreserving`), P(0,·) = 1. ✓
   - Every g = B_v · diag(Q,1) (B_v the boost to v = g•0, see HandOff of hypIsometry: B_v = [[I+vvᵀ/(1+t), v],[vᵀ,t]]).
     So it suffices to prove (★) for boosts B_v.
   - For a boost: bd(B_v) ξ = ((ξ + (⟪v,ξ⟫/(1+t) + 1)v) ) / (⟪v,ξ⟫ + t). Extend it to the degree-1 homogeneous
     map G(x) = ‖x‖ · bd(B_v)(x/‖x‖) on E∖{0}. `toSphere` measures a set A ⊂ Sph by n·Leb(cone A) with
     cone A = {r ξ : 0 < r ≤ 1, ξ ∈ A}, and G(cone A) = cone(bd A). By change of variables
     (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, G injective, C¹ off 0), Leb(cone(bd A)) =
     ∫_{cone A} |det DG|, and |det DG(rξ)| = J(ξ) (degree-0 homogeneous): DG(ξ)ξ = G(ξ) is the unit normal at
     G(ξ), DG(ξ) maps T_ξSph to T_{G ξ}Sph, so det DG(ξ) = sphere-Jacobian. Polar integration of a degree-0
     function over the cone gives (1/n)∫_A J dσ̃. Compute det DG(ξ) directly (a rank-one perturbation of a
     scalar matrix: `Matrix.det_one_add_col_mul_row`). Expected: the sphere Jacobian of bd(B_v) at ξ is
     (t + ⟪v,ξ⟫)^{−(n−1)}, i.e. P(−v, ξ); combined with bd(B_v)⁻¹ = bd(B_{−v}) this is (★). Verify the sign on
     paper with n = 2 (a circle map) before writing Lean.
3. atoms of the image and positivity are preserved automatically.

## Not needed
No spherical coordinates, no Möbius-group theory, no Poisson integral formula / harmonic functions.
Delegate: (1) as small lemmas; the boost Jacobian computation; the cone/polar transfer lemma for toSphere;
the reduction to generators.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem visualMeasure (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    VisualProp n :=
  Work.Mostow.visualProp_of_transLaw n hn hA (fun g => Work.Mostow.sigma_map_bd n hn hA g)

end Work.Mostow
