import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.SigmaMoments
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.BusemannDeriv
import Submission.Work.Mostow.BusemannBound
import Submission.Work.Mostow.HProps
import Submission.Work.Mostow.CauchySchwarz
import Submission.Work.Mostow.PhiBary
import Submission.Work.Mostow.NatMapFDeriv
import Submission.Work.Mostow.NatMapConj
import Submission.Work.Mostow.LinAlgTriangular
import Submission.Work.Mostow.LinAlgIsom
import Submission.Work.Mostow.Comp0
import Submission.Work.Mostow.PhiDerivY
import Submission.Work.Mostow.GvC1
import Submission.Work.Mostow.GvZero
import Submission.Work.Mostow.LinAlgMatrixIneq
import Submission.Work.Mostow.IsInvertible_of_pd
import Submission.Work.Mostow.HEigen
import Submission.Work.Mostow.PfunFacts
import Submission.Work.Mostow.N2Eigen
import Submission.Work.Mostow.JacLinAlg

/-! Guidance from the project lead (the requester):

# Area N2 — natMapJac : NatMapJacProp n   (the BCG inequality; lead's design — CRUX A)

F = natMap φ, φ a homeomorphism of Sph. Claims: F is C¹, hjac F ≤ 1, and hjac F u = 1 ⇒ dF_u is gH-isometric.
Reference: Besson–Courtois–Gallot, GAFA 5 (1995) §5 and ETDS 16 (1996); here everything is explicit.

## 1. Reduce every pointwise claim to u = 0, F(u) = 0
For u and y = F u pick g, h ∈ PO with g•0 = u, h•0 = y (boosts). Put φ' := bd h⁻¹ ∘ φ ∘ bd g (again a homeomorphism
of Sph). By VisualProp + BaryProp (as in natMapEquiv — reuse its helper): natMap φ' = h⁻¹ • natMap φ (g • ·), so
natMap φ'(0) = 0. hjac and gH-isometry of differentials are invariant under composing with isometries on both sides
(HypIsometryProp: hjac (g•·) = 1, gH preserved, chain rule; hjac(F∘G)(u) = hjac F (G u) · hjac G u).
At 0: tpart 0 = 1, gH 0 = Euclidean, so hjac F 0 = |det DF(0)| and "isometric" = orthogonal.

## 2. Differentiability (implicit function theorem)
Set, for x, y ∈ E n,  G(x,y) := ∫_Sph ∇_y busemann(φθ, y) · P(x,θ) dsigma(θ)   ∈ E n (Euclidean gradient),
P(x,θ) = exp(−(n−1) busemann θ x). Facts:
- busemann(ξ,·) is smooth, with derivatives of every order bounded uniformly for ξ ∈ Sph and y in compacts
  (closed formulas: B = log(tpart y − ⟪y,ξ⟫), argument ≥ tpart y − ‖y‖ > 0). Same for P in x.
  ⇒ G is C¹ jointly (`hasFDerivAt_integral_of_dominated_of_fderiv_le`, compactness of Sph gives the domination).
- y ↦ baryFun(ν_x)(y) (ν_x = (visual x).map φ) has gradient G(x,·)/(normalisation-free) — so F(x) is the unique zero
  of G(x,·) (strict convexity: BaryProp minimiser + critical point ⇔ minimiser for convex functions).
- ∂_y G(x,y) is positive definite (Hessian of a strictly convex function; at (0,0) it is I − H, see §3).
- IFT (`HasStrictFDerivAt.implicitFunction` / `ImplicitFunctionData`) ⇒ near x₀ the zero set is a C¹ graph;
  uniqueness of the zero ⇒ it is F. So F is C¹ (ContDiff ℝ 1 via `contDiff_iff_contDiffAt`), and
  DF = −(∂_yG)⁻¹ ∂_xG.

## 3. The computation at x = 0, y = F(0) = 0 (all Euclidean)
- ∇_y busemann(ξ, y)|_{y=0} = −ξ;  Hess_y busemann(ξ,·)|_0 = I − ξξᵀ   (expand log(1 + ‖y‖²/2 − ⟪y,ξ⟫ + …)).
- ∂_x P(x,θ)|_{x=0} v = (n−1)⟪θ, v⟫.
- G(0,0) = −∫ φθ dsigma(θ) = 0 (this IS "F(0) = 0").
- ∂_yG(0,0) = ∫ (I − φθ φθᵀ) dsigma = I − H,  H := ∫ φθ φθᵀ dsigma(θ): symmetric, H ⪰ 0, tr H = 1, and H ≺ I
  (⟪Hw,w⟫ = 1 for a unit w would force φθ = ±w a.e., impossible for an injective φ and atomless sigma).
- ∂_xG(0,0) v = −(n−1) ∫ φθ ⟪θ,v⟫ dsigma(θ).
  ⇒ (I − H) DF(0) v = (n−1) ∫ φθ ⟪θ, v⟫ dsigma(θ).                                         (†)
- ∫ θθᵀ dsigma = I/n (sigma invariant under coordinate reflections and permutations — `toSphere` of Lebesgue
  which is invariant under linear isometries; trace = 1).

## 4. The inequality (pure linear algebra; delegate each item)
Let L := (I − H) DF(0), c := (n−1)/√n. From (†) and Cauchy–Schwarz in L²(sigma):
  ⟪L v, w⟫ ≤ (n−1) (∫⟪φθ,w⟫²)^{1/2} (∫⟪θ,v⟫²)^{1/2} = c · ⟪Hw,w⟫^{1/2} · ‖v‖.                    (‡)
(a) Triangular-basis lemma: for any linear L and symmetric H ⪰ 0 satisfying (‡) for all v, w:
    |det L| ≤ cⁿ · det(H)^{1/2}.  Proof: let w₁..wₙ be an orthonormal eigenbasis of H. If det L = 0 done. Else
    Gram–Schmidt the vectors L⁻¹w₁, …, L⁻¹wₙ into an orthonormal v₁..vₙ with span(v₁..vₖ) = span(L⁻¹w₁..L⁻¹wₖ);
    then L vₖ ∈ span(w₁..wₖ), the matrix (⟪L vᵢ, wⱼ⟫) is triangular, |det L| = ∏ |⟪L vₖ, wₖ⟫| ≤ ∏ c λₖ^{1/2}.
    (Sign: use (‡) with ±w.)
(b) Matrix lemma (n ≥ 3 is used HERE): for λ₁..λₙ ∈ [0,1) with Σ λᵢ = 1:
       ∏ λᵢ^{1/2} / ∏ (1 − λᵢ) ≤ (√n/(n−1))ⁿ, with equality iff all λᵢ = 1/n.
    Proof: maximise f(λ) = Σ (½ log λᵢ − log(1−λᵢ)) on the open simplex. CAREFUL at the boundary: f → −∞ when some
    λᵢ → 0 with no λⱼ → 1, but for n = 3 near a corner (1−ε, ε/2, ε/2) f → −log 2 ≈ −0.693, finite; the centre value
    is 3(½log(1/3) − log(2/3)) ≈ −0.432, so the corner is still lower (for n = 2 the lemma is FALSE: f is unbounded).
    Handle the boundary by an explicit bound near the faces, then compactness. At an interior maximum, Lagrange: ψ(λᵢ) := 1/(2λᵢ) + 1/(1−λᵢ) takes one value. ψ is strictly convex on
    (0,1), so the λᵢ take at most two values a < b, k of them equal a, n−k equal b. Show that for n ≥ 3 any such
    two-value critical point with a ≠ b is not a maximum (compare with the second-order condition / direct
    comparison against λ = 1/n; this is the BCG appendix computation — do it as an explicit one-variable inequality).
    If this Lagrange route is painful: alternative — prove the equivalent inequality
       Σ log(1−λᵢ) − ½ Σ log λᵢ ≥ n log((n−1)/n) + (n/2) log n
    by a tangent-line trick: find constants α, β with −log(1−λ) + ½ log λ ≤ α + β(λ − 1/n) + [something ≤ 0]
    valid on [0,1) for n ≥ 3 … (check numerically first; n = 3 is the tightest case). Keep the equality case.
(c) Combine: det(I − H) = ∏(1 − λᵢ), |det DF(0)| = |det L| / det(I−H) ≤ cⁿ ∏λᵢ^{1/2}/∏(1−λᵢ) ≤ 1.
(d) Equality: hjac = 1 forces equality in (b) ⇒ H = I/n. Then (‡) reads ⟪L v, w⟫ ≤ (n−1)/n ‖v‖‖w‖, i.e.
    ‖DF(0)‖_op ≤ 1 (L = ((n−1)/n)·DF(0)), together with |det DF(0)| = 1 ⇒ all singular values are 1 ⇒ DF(0) is
    orthogonal ⇒ gH 0 (DF v) = ‖v‖² = gH 0 v. (No Cauchy–Schwarz equality analysis needed.)

## Not needed
No Patterson–Sullivan theory, no entropy, no calibration/degree theory, no lattice hypothesis (this Prop holds for
EVERY boundary homeomorphism). No spectral theory beyond `Matrix.IsHermitian` eigenbases.
## Going wide
Parallel children: reduction-to-0 lemma; derivatives of busemann/P (closed forms + bounds); G is C¹; IFT wrapper;
formula (†); ∫θθᵀ = I/n; (a); (b) with equality; (d).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory


/-! ## Assembly of the proof of `NatMapJacProp`

The proof has two halves.

### A. The core case: `F(0) = 0`

Let `φ` be a bijection of `Sph n`, continuous there, with `natMap φ 0 = 0`.  Put `F = natMap φ`,
`H = Hlin n φ` (the second-moment operator `w ↦ ∫ ⟪φξ,w⟫ • φξ dσ`), and

`N = Nlin n φ = (n-1) • ∫ ⟪ξ,·⟫ • φξ dσ`.

1. `PhiBary` identifies `Phi n φ x ·` with `baryFun ((visual n x).map φ)`; `PhiDerivY` gives
   `∇_y Phi n φ x · = Gv n φ x ·`; `GvZero` then shows the *unique* zero of `Gv n φ x ·` is
   `natMap φ x` (using `BaryProp` for existence and strict geodesic convexity for uniqueness).
2. `GvC1` makes `(x,y) ↦ Gv n φ x y` a C¹ map with derivative `DGv`; `HProps` gives that
   `DGv 0 0 ∘L inr = 1 - H` is positive definite (`IsInvertible_of_pd`);
   `Comp0` evaluates `DGv 0 0` at `(0,0)`: `(v,0) ↦ -N v` and `(0,w) ↦ w - H w`.
3. `NatMapFDeriv` (implicit function theorem) then yields `ContDiffAt ℝ 1 F 0` and
   `fderiv ℝ F 0 = (1 - H).inverse ∘L N`, i.e. `(1 - H) ∘ DF(0) = N`.                       (†)
4. `CauchySchwarz` turns (†) into `⟪N v, w⟫ ≤ ((n-1)/√n) · √⟪H w,w⟫ · ‖v‖`; `LinAlgTriangular`
   gives `|det N| ≤ c^n √(det H)` with `c = (n-1)/√n`.
5. `HEigen` diagonalises `H`: eigenvalues `λᵢ ∈ [0,1)`, `Σλᵢ = 1`, `det H = ∏λᵢ`,
   `det (1 - H) = ∏(1-λᵢ)`.  Hence
   `hjac F 0 = |det N| / det (1-H) ≤ c^n ∏√λᵢ/∏(1-λᵢ) ≤ 1`
   by `LinAlgMatrixIneq`.
6. Equality: `hjac F 0 = 1` forces equality in `LinAlgMatrixIneq`, so `λᵢ = 1/n` and
   `H = (1/n)•1`, hence `1 - H = ((n-1)/n)•1`, `N = ((n-1)/n)•DF(0)`.  The Cauchy–Schwarz bound
   gives `‖N‖ ≤ (n-1)/n`, so `‖DF(0)‖ ≤ 1`; with `|det DF(0)| = 1` this makes `DF(0)` an
   isometry (`LinAlgIsom`), which is the claim (`gH 0 = ‖·‖²`).

### B. Reduction to the core case

For arbitrary `u`, let `y = natMap φ u`, pick boosts `g`, `h` with `g • 0 = u`, `h • 0 = y`
(`BoostTransitive`), and set `ψ = bd h⁻¹ ∘ φ ∘ bd g`.  `NatMapConj` gives
`natMap ψ v = h⁻¹ • natMap φ (g • v)`, so `natMap ψ 0 = 0` and the core case applies to `ψ`.
Composing with the isometries (`HypIsometryProp`: `hjac` of an isometry is `1`, the metric is
preserved, chain rule) transports `ContDiffAt`, the inequality `hjac ≤ 1` and the equality case
from `0` (for `ψ`) back to `u` (for `φ`). -/


/-! ## Helper lemmas for the assembly -/

/-- The chain rule for `hjac` (the hyperbolic Jacobian), for `C¹` maps. -/
lemma hjac_comp {n : ℕ} {F G : E n → E n} {u : E n}
    (hF : ContDiffAt ℝ 1 F (G u)) (hG : ContDiffAt ℝ 1 G u) :
    hjac (fun w => F (G w)) u = hjac F (G u) * hjac G u := by
  have h1 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have dF : HasFDerivAt F (fderiv ℝ F (G u)) (G u) := (hF.differentiableAt h1).hasFDerivAt
  have dG : HasFDerivAt G (fderiv ℝ G u) u := (hG.differentiableAt h1).hasFDerivAt
  have hd : fderiv ℝ (fun w => F (G w)) u = (fderiv ℝ F (G u)) ∘L (fderiv ℝ G u) := by
    rw [show (fun w => F (G w)) = F ∘ G from rfl]
    exact (dF.comp u dG).fderiv
  rw [hjac, hjac, hjac, hd]
  simp only [ContinuousLinearMap.det, Function.comp_apply]
  rw [show ((fderiv ℝ F (G u) ∘SL fderiv ℝ G u : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n)
        = (fderiv ℝ F (G u) : E n →ₗ[ℝ] E n) ∘ₗ (fderiv ℝ G u : E n →ₗ[ℝ] E n) from rfl]
  rw [LinearMap.det_comp, abs_mul]
  have ht : tpart (G u) ≠ 0 := ne_of_gt (tpart_pos _)
  field_simp

/-- `gH 0` is the Euclidean square norm. -/
lemma gH_zero {n : ℕ} (w : E n) : gH 0 w = ‖w‖ ^ 2 := by
  rw [gH, inner_zero_left, norm_zero]
  norm_num

/-- `Slin n φ` evaluated: `(Slin n φ) v = ∫ ξ, ⟪ξ,v⟫ • φ ξ ∂σ`. -/
theorem Slin_apply (n : ℕ) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (hprob : IsProbabilityMeasure (sigma n)) (hsupp : sigma n (Sph n)ᶜ = 0) :
    ∀ v : E n, Slin n φ v = ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n) := by
  haveI := hprob
  intro v
  have hmem : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
    rw [ae_iff]; simpa only [Set.compl_def] using hsupp
  have hunitφ : ∀ᵐ ξ ∂(sigma n), ‖φ ξ‖ = 1 :=
    (hmem.mono fun ξ h => hbij.1 h).mono fun ξ h => by
      rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at h
      exact h
  have hcontOn : ContinuousOn (fun ξ : E n => (innerSL ℝ ξ).smulRight (φ ξ)) (Sph n) := by
    have hφ' : Continuous fun x : (Sph n : Set (E n)) => φ x.1 :=
      (continuousOn_iff_continuous_domRestrict).mp hcont
    have hInner : Continuous fun x : (Sph n : Set (E n)) => innerSL ℝ x.1 :=
      (innerSL ℝ : E n →L[ℝ] (E n →L[ℝ] ℝ)).continuous.comp continuous_subtype_val
    have hsm : Continuous fun q : (E n →L[ℝ] ℝ) × E n => q.1.smulRight q.2 :=
      (ContinuousLinearMap.smulRightL ℝ (E n) (E n)).continuous₂
    rw [continuousOn_iff_continuous_domRestrict]
    exact hsm.comp (hInner.prodMk hφ')
  have hae : AEMeasurable (fun ξ : E n => (innerSL ℝ ξ).smulRight (φ ξ)) (sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n →L[ℝ] E n)
      Metric.isClosed_sphere.measurableSet hcontOn hsupp
  have hLint : Integrable (fun ξ : E n => (innerSL ℝ ξ).smulRight (φ ξ)) (sigma n) := by
    refine Integrable.of_bound hae.aestronglyMeasurable 1 ?_
    filter_upwards [hmem, hunitφ] with ξ hξ hφξ
    have hξ1 : ‖ξ‖ = 1 := by
      rw [Sph, Metric.mem_sphere, dist_eq_norm, sub_zero] at hξ; exact hξ
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, hξ1, one_mul, hφξ]
  have h1 : (∫ ξ, (innerSL ℝ ξ).smulRight (φ ξ) ∂(sigma n)) v
      = ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n) := by
    rw [ContinuousLinearMap.integral_apply hLint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply])
  simpa only [Slin] using h1


theorem natMapJac_core (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hV : VisualProp n) (hB : BaryProp n) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (h0 : natMap φ 0 = 0) :
    ContDiffAt ℝ 1 (natMap φ) 0 ∧ hjac (natMap φ) 0 ≤ 1 ∧
      (hjac (natMap φ) 0 = 1 → ∀ v, gH (natMap φ 0) (fderiv ℝ (natMap φ) 0 v) = gH 0 v) := by
  obtain ⟨hprob, hsupp, hatom, hmean, hsecond⟩ := SigmaMoments n (by omega)
  have hprob1 : (sigma n) Set.univ = 1 := by
    haveI : IsProbabilityMeasure (sigma n) := hprob
    exact measure_univ
  obtain ⟨hd1, hd2, hg0, hh0⟩ := BusemannDeriv n
  obtain ⟨hg, hh⟩ := BusemannBound n
  obtain ⟨hp1, hp0, hpfpos, hdp0, hp⟩ := PfunFacts n
  have hbary := PhiBary n hV φ hbij hcont
  have hder := PhiDerivY n φ hbij hcont hd1 hd2 hg hh
  have hzero := GvZero n hV hB φ hbij hcont hbary hder
  obtain ⟨hgvc1, hgvder⟩ := GvC1 n φ hbij hcont hd1 hd2 hp1 hg hh hp
  obtain ⟨hHsym, hHpsd, hHtr, hHstrict⟩ := HProps n (by omega) φ hbij hcont hprob1 hsupp hatom
  obtain ⟨hcomp01, hcomp02⟩ := Comp0 n φ hbij hcont hp0 hdp0 hg0 hh0 hprob1
  have hSlin := Slin_apply n φ hbij hcont hprob hsupp
  have hNlin : ∀ v : E n, Nlin n φ v = ((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n) := by
    intro v
    rw [show Nlin n φ v = ((n : ℝ) - 1) • (Slin n φ) v from by rw [Nlin]; simp]
    rw [hSlin v]
  have hAeq : (DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (E n) (E n)) = (1 - Hlin n φ) := by
    refine ContinuousLinearMap.ext fun w => ?_
    show (DGv n φ 0 0) (0, w) = (1 - Hlin n φ) w
    simpa using hcomp02 w
  have hBeq : (DGv n φ 0 0 ∘L ContinuousLinearMap.inl ℝ (E n) (E n)) = -Nlin n φ := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h2 : (-Nlin n φ) v = -((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n) := by
      have hh : (-Nlin n φ) v
          = -(((n : ℝ) - 1) • ∫ ξ, (inner ℝ ξ v) • φ ξ ∂(sigma n)) := by
        have hh := congrArg Neg.neg (hNlin v)
        simpa using hh
      rw [hh, ← neg_smul]
    show (DGv n φ 0 0) (v, 0) = (-Nlin n φ) v
    rw [h2]
    simpa using hcomp01 v
  have hinvH : (1 - Hlin n φ).IsInvertible := IsInvertible_of_pd n (Hlin n φ) hHstrict
  have hinv : (DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (E n) (E n)).IsInvertible := by
    rw [hAeq]; exact hinvH
  obtain ⟨hcd0, hder0⟩ := NatMapFDeriv n hV hB φ hbij hcont hzero hgvc1 hgvder hinv h0
  have hkey : (1 - Hlin n φ) ∘L fderiv ℝ (natMap φ) 0 = Nlin n φ := by
    rw [hder0.fderiv, hBeq, ← hAeq]
    rw [show -((DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (E n) (E n)).inverse ∘L (-(Nlin n φ)))
        = (DGv n φ 0 0 ∘L ContinuousLinearMap.inr ℝ (E n) (E n)).inverse ∘L Nlin n φ from by
      simp]
    rw [← ContinuousLinearMap.comp_assoc, hinv.self_comp_inverse, ContinuousLinearMap.id_comp]
  have htri : ∀ v w : E n, inner ℝ (Nlin n φ v) w ≤
      (((n : ℝ) - 1) / Real.sqrt n) * Real.sqrt (inner ℝ (Hlin n φ w) w) * ‖v‖ := by
    intro v w
    have h := CauchySchwarz n φ hbij hcont hprob1 hsupp hsecond v w
    rwa [← hNlin v] at h
  obtain ⟨hJacLe, hJacEq⟩ := JacLinAlg n hn (Hlin n φ) (Nlin n φ) (fderiv ℝ (natMap φ) 0)
    hkey htri hHsym hHpsd hHstrict hHtr
  have ht0 : tpart (0 : E n) = 1 := by rw [tpart, norm_zero]; norm_num
  have hJacob : hjac (natMap φ) 0 = |(fderiv ℝ (natMap φ) 0).det| := by
    rw [hjac, h0, ht0]; norm_num
  refine ⟨hcd0, ?_, ?_⟩
  · rw [hJacob]; exact hJacLe
  · intro h1 v
    have hdet1 : |(fderiv ℝ (natMap φ) 0).det| = 1 := by rw [← hJacob]; exact h1
    obtain ⟨hHsmul, hDFle⟩ := hJacEq hdet1
    have hisom := LinAlgIsom ((fderiv ℝ (natMap φ) 0).toLinearMap) hDFle (by simpa using hdet1)
    have hsq : ‖(fderiv ℝ (natMap φ) 0).toLinearMap v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hisom v v]
    have hnorm : ‖(fderiv ℝ (natMap φ) 0).toLinearMap v‖ = ‖v‖ := by
      have h := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h
    rw [h0, gH_zero, gH_zero]
    exact congrArg (fun t => t ^ 2) hnorm


/-- **Reduction.**  If the core case at `0` is known for every boundary bijection `ψ` with
`natMap ψ 0 = 0`, then the full statement follows by conjugating with boosts. -/
theorem natMapJac_reduce (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hV : VisualProp n) (hB : BaryProp n) (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (core : ∀ ψ : E n → E n, Set.BijOn ψ (Sph n) (Sph n) → ContinuousOn ψ (Sph n) →
      natMap ψ 0 = 0 →
      ContDiffAt ℝ 1 (natMap ψ) 0 ∧ hjac (natMap ψ) 0 ≤ 1 ∧
        (hjac (natMap ψ) 0 = 1 → ∀ v, gH (natMap ψ 0) (fderiv ℝ (natMap ψ) 0 v) = gH 0 v)) :
    ContDiff ℝ 1 (natMap φ) ∧ (∀ u, hjac (natMap φ) u ≤ 1) ∧
      ∀ u, hjac (natMap φ) u = 1 →
        ∀ v, gH (natMap φ u) (fderiv ℝ (natMap φ) u v) = gH u v := by
  have hAkeep := hA
  have hBT := BoostTransitive n hAkeep
  obtain ⟨-, -, -, hOneAct, hMulAct, -, -, -, -, -, -, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, hsmul_cd, hsmul_gH, hsmul_hjac, -, -⟩ := hI
  have key : ∀ u : E n, ContDiffAt ℝ 1 (natMap φ) u ∧ hjac (natMap φ) u ≤ 1 ∧
      (hjac (natMap φ) u = 1 → ∀ v, gH (natMap φ u) (fderiv ℝ (natMap φ) u v) = gH u v) := by
    intro u
    obtain ⟨g0, hg0⟩ := hBT.1 u
    obtain ⟨h0, hh0⟩ := hBT.1 (natMap φ u)
    let ψ : E n → E n := fun ξ => bd h0⁻¹ (φ (bd g0 ξ))
    obtain ⟨hbijψ, hcontψ, hconjψ⟩ := NatMapConj n hAkeep hV hB φ hbij hcont g0 h0
    have hg0inv : g0⁻¹ • u = 0 := by
      rw [← hg0, ← hMulAct g0⁻¹ g0 (0 : E n), inv_mul_cancel, hOneAct]
    have hψ0 : natMap ψ 0 = 0 := by
      rw [hconjψ 0, hg0, ← hh0, ← hMulAct h0⁻¹ h0 (0 : E n), inv_mul_cancel, hOneAct]
    have hcore := core ψ hbijψ hcontψ hψ0
    have hnatw : ∀ w : E n, natMap φ w = h0 • natMap ψ (g0⁻¹ • w) := by
      intro w
      have h2 : g0 • (g0⁻¹ • w) = w := by rw [← hMulAct g0 g0⁻¹ w, mul_inv_cancel, hOneAct]
      have h3 : natMap ψ (g0⁻¹ • w) = h0⁻¹ • natMap φ w := by
        rw [hconjψ (g0⁻¹ • w), h2]
      rw [h3, ← hMulAct h0 h0⁻¹ (natMap φ w), mul_inv_cancel, hOneAct]
    have hnat0 : natMap φ = fun w : E n => h0 • natMap ψ (g0⁻¹ • w) := funext hnatw
    have h1' : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
    have hcdA : ContDiffAt ℝ 1 (fun w : E n => h0 • w) (natMap ψ (g0⁻¹ • u)) :=
      (hsmul_cd h0).contDiffAt
    have hcdB : ContDiffAt ℝ 1 (fun w : E n => g0⁻¹ • w) u := (hsmul_cd g0⁻¹).contDiffAt
    have hcψ' : ContDiffAt ℝ 1 (natMap ψ) (g0⁻¹ • u) := by rw [hg0inv]; exact hcore.1
    have hcdψB : ContDiffAt ℝ 1 (fun w : E n => natMap ψ (g0⁻¹ • w)) u := hcψ'.comp u hcdB
    have hcdφ : ContDiffAt ℝ 1 (natMap φ) u := by
      rw [hnat0]
      exact hcdA.comp u hcdψB
    have hjj : hjac (natMap φ) u = hjac (natMap ψ) 0 := by
      rw [hnat0,
        hjac_comp (F := fun w : E n => h0 • w) (G := fun w : E n => natMap ψ (g0⁻¹ • w))
          hcdA hcdψB,
        hjac_comp (F := natMap ψ) (G := fun w : E n => g0⁻¹ • w) hcψ' hcdB,
        hsmul_hjac h0 (natMap ψ (g0⁻¹ • u)), hsmul_hjac g0⁻¹ u, hg0inv]
      ring
    have hB : HasFDerivAt (fun w : E n => g0⁻¹ • w)
        (fderiv ℝ (fun w : E n => g0⁻¹ • w) u) u := (hcdB.differentiableAt h1').hasFDerivAt
    have hψ : HasFDerivAt (natMap ψ) (fderiv ℝ (natMap ψ) (g0⁻¹ • u)) (g0⁻¹ • u) :=
      (hcψ'.differentiableAt h1').hasFDerivAt
    have hψB : HasFDerivAt (fun w => natMap ψ (g0⁻¹ • w))
        ((fderiv ℝ (natMap ψ) (g0⁻¹ • u)) ∘L
          (fderiv ℝ (fun w : E n => g0⁻¹ • w) u)) u := hψ.comp u hB
    have hA' : HasFDerivAt (fun w : E n => h0 • w)
        (fderiv ℝ (fun w : E n => h0 • w) (natMap ψ (g0⁻¹ • u))) (natMap ψ (g0⁻¹ • u)) :=
      (hcdA.differentiableAt h1').hasFDerivAt
    have hAb : HasFDerivAt (fun w => h0 • natMap ψ (g0⁻¹ • w))
        ((fderiv ℝ (fun w : E n => h0 • w) (natMap ψ (g0⁻¹ • u))) ∘L
          ((fderiv ℝ (natMap ψ) (g0⁻¹ • u)) ∘L
            (fderiv ℝ (fun w : E n => g0⁻¹ • w) u))) u := hA'.comp u hψB
    have hfder : ∀ v, fderiv ℝ (natMap φ) u v =
        fderiv ℝ (fun w : E n => h0 • w) (natMap ψ 0)
          (fderiv ℝ (natMap ψ) 0 (fderiv ℝ (fun w : E n => g0⁻¹ • w) u v)) := by
      intro v
      rw [hnat0, hAb.fderiv, hg0inv, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply]
    have hnatφu : natMap φ u = h0 • natMap ψ 0 := by rw [hnatw u, hg0inv]
    refine ⟨hcdφ, ?_, ?_⟩
    · rw [hjj]; exact hcore.2.1
    · intro h1 v
      have hψ1 : hjac (natMap ψ) 0 = 1 := by rw [← hjj]; exact h1
      have hder := hcore.2.2 hψ1
      calc gH (natMap φ u) (fderiv ℝ (natMap φ) u v)
          = gH (h0 • natMap ψ 0) (fderiv ℝ (fun w : E n => h0 • w) (natMap ψ 0)
              (fderiv ℝ (natMap ψ) 0 (fderiv ℝ (fun w : E n => g0⁻¹ • w) u v))) := by
            rw [hnatφu, hfder v]
        _ = gH (natMap ψ 0)
              (fderiv ℝ (natMap ψ) 0 (fderiv ℝ (fun w : E n => g0⁻¹ • w) u v)) :=
            hsmul_gH h0 (natMap ψ 0) _
        _ = gH 0 (fderiv ℝ (fun w : E n => g0⁻¹ • w) u v) := hder _
        _ = gH u v := by
            have hh := hsmul_gH g0⁻¹ u v
            rwa [hg0inv] at hh
  refine ⟨contDiff_iff_contDiffAt.mpr (fun u => (key u).1), fun u => (key u).2.1,
    fun u hu v => (key u).2.2 hu v⟩

theorem natMapJac (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hV : VisualProp n) (hB : BaryProp n) : NatMapJacProp n := by
  intro φ hbij hcont
  exact natMapJac_reduce n hn hA hI hV hB φ hbij hcont
    (fun ψ hb hc h0 => natMapJac_core n hn hA hV hB ψ hb hc h0)

end Work.Mostow
