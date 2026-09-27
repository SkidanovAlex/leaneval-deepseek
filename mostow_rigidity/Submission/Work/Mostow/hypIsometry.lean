import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.HypAux
import Submission.Work.Mostow.hdistBasic
import Submission.Work.Mostow.hdistContinuous
import Submission.Work.Mostow.hdistIsCompact
import Submission.Work.Mostow.smulContDiff
import Submission.Work.Mostow.smulGH
import Submission.Work.Mostow.busemannCocycle

/-! Guidance from the project lead (the requester):

# Area T2 — hypIsometry : HypIsometryProp n   (lead's design)

Assume POActionProp (action laws, `(A : PO) • u = actO A u`, faithfulness). Work on the hyperboloid:
x = hlift u, ⟨x,y⟩ = Σ xᵢyᵢ − x₀y₀. Key identity: tpart u * tpart v − ⟪u,v⟫ = −⟨hlift u, hlift v⟩ =: c(u,v).

## The explicit boost (build first; used everywhere)
For v ∈ E n with t = tpart v, the matrix B_v (block form on spatial ⊕ time):
  B_v = [[ I + vvᵀ/(1+t),  v ], [ vᵀ, t ]].
Check B_vᵀ J B_v = J (uses ‖v‖² = t² − 1); B_v · e₀ = hlift v; B_v₀₀ = t > 0; B_v⁻¹ = B_{−v}.
So `(B_v : PO) • 0 = v`: PO acts transitively. Orthogonal Q ∈ O(n) gives block diag(Q,1) ∈ O(n,1), acting by u ↦ Q u.

## Clauses
1. c(u,v) ≥ 1, with equality iff u = v: (1+a²)(1+b²) − (1+ab)² = (a−b)² with a=‖u‖, b=‖v‖, plus ⟪u,v⟫ ≤ ab;
   equality forces a = b and ⟪u,v⟫ = ab ⇒ u = v. Hence hdist = arcosh c ≥ 0, = 0 iff u = v; symmetric.
2. invariance: ⟨Mx,My⟩ = ⟨x,y⟩ and the sheet lemma (hlift (g•u) = ± M hlift u with the same sign for u and v)
   ⇒ c(g•u, g•v) = c(u,v).
3. triangle: by invariance move the middle point to 0 (boost by B_{−v}): with a = hdist u 0, b = hdist 0 w,
   u = sinh a · p, w = sinh b · q (‖p‖=‖q‖=1; tpart = cosh), c(u,w) = cosh a cosh b − sinh a sinh b ⟪p,q⟫
   ≤ cosh(a+b). arcosh monotone. Record the EQUALITY case (⟪p,q⟫ = −1: 0 lies on the geodesic) — the
   localIsom area needs it.
4. continuity of hdist: `Real.continuous_arcosh`-type facts / continuity on [1,∞). Compact balls:
   c(u,v) ≥ tpart v (tpart u − ‖u‖) and tpart u − ‖u‖ = 1/(tpart u + ‖u‖) > 0 ⇒ bounded; closed ⇒ compact.
5. isometries are in PO: F distance-preserving. Let g₁ = B_{F 0}, F₁ = g₁⁻¹ • F(·): F₁ 0 = 0.
   cosh hdist(0,u) = tpart u ⇒ ‖F₁ u‖ = ‖u‖; then c(F₁u,F₁v) = c(u,v) ⇒ ⟪F₁u,F₁v⟫ = ⟪u,v⟫.
   Inner-product preserving with F₁0 = 0 ⇒ linear isometry (expand ‖F₁(a u + b v) − a F₁u − b F₁v‖² = 0) ⇒
   F₁ = Q ∈ O(n) ⇒ F = (g₁ · diag(Q,1)) • ·.
6. smoothness: actO A u is linear in (u, tpart u); tpart is smooth (1+‖u‖² > 0; `contDiff_norm_sq`, sqrt away
   from 0). ContDiff ℝ 1 suffices.
7. metric: d(hlift)_u v = (v, ⟪u,v⟫/tpart u), and ⟨d hlift v, d hlift v⟩ = gH u v. Differentiating
   hlift ∘ (g•) = ±M ∘ hlift and using (a) gives gH preservation.
8. hjac (g•·) u = 1: gH u is the quadratic form of G_u = I − uuᵀ/(1+‖u‖²), det G_u = 1/(1+‖u‖²) = tpart u⁻²
   (`Matrix.det_one_add_col_mul_row` / matrix determinant lemma). Preservation: Dᵀ G_{gu} D = G_u ⇒
   det(D)² = tpart(g•u)² / tpart(u)² ⇒ |det D| · tpart u / tpart (g•u) = 1.
9. MeasurePreserving (volH): g• is a C¹ bijection (inverse g⁻¹•) with hjac = 1; change of variables
   `lintegral_image_eq_lintegral_abs_det_fderiv_mul` with the density tpart⁻¹ gives volH (g • s) = volH s.
10. Busemann cocycle: with θ_ξ = (ξ,1), M θ_ξ = w₀ · θ_{bd g ξ}, and busemann ξ u = log(−⟨hlift u, θ_ξ⟩).
   So busemann (bd g ξ) (g•u) = busemann ξ u + log(tsign/w₀) — constant in u; evaluate at u = 0 (busemann ξ 0 = 0).

## Going wide
Delegate in parallel: boost lemma, c ≥ 1 + equality, invariance, triangle (+equality case), compact balls,
isometry ⇒ PO, smoothness+gH, det/hjac, measure preservation, cocycle.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Hyper

/-- `HypIsometryProp n` holds for *every* `n`: none of its clauses needs a lower bound on the
dimension.  (The stated `hypIsometry` below has the hypothesis `3 ≤ n` only because its contract
carries it; the lead's `hypIsometry_ge2` is the same proof.) -/
theorem hypIsometryAll (n : ℕ) (hA : POActionProp n) : HypIsometryProp n :=
  ⟨(hdistBasic n).1, (hdistBasic n).2.1, (hdistBasic n).2.2, hdistTriangle' hA,
    hdistContinuous n, fun u r => hdistIsCompact n u r, hdist_smul' hA, isomEqSmul' hA,
    smulContDiff n hA, smulGH n hA, hjac_smul' hA, measurePreserving_smul' hA,
    busemannCocycle n hA⟩

theorem hypIsometry (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) : HypIsometryProp n :=
  hypIsometryAll n hA

end Work.Mostow
