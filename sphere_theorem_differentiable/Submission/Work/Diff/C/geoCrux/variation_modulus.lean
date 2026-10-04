import Mathlib
import Submission.Work.Diff.C.geoCrux.TwoCentre.Core
import Submission.Work.Diff.C.geoCrux.sharp.Defs
import Submission.Work.Diff.C.geoCrux.sharp.VarMod
import Submission.Work.Diff.C.geoCrux.sharp.anchor_of_twoCentre
import Submission.Work.Diff.C.geoCrux.sharp.anchor_arith
import Submission.Work.Diff.C.geoCrux.sharp.varfield_ne_zero
import Submission.Work.Diff.C.geoCrux.sharp.ray_package
import Submission.Work.Diff.C.geoCrux.sharp.Pieces
import Submission.Work.Diff.C.geoCrux.VariationCrux
import Submission.Work.Diff.C.geoCrux.sharp.modulus_anchored_pos
import Submission.Work.Diff.C.geoCrux.hmod.NBound

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric Filter
open Submission.GlobalExp Submission.Geodesic

namespace Work.Diff.C.geoCrux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## The radial variation field

`curveVelocity (fun r => GExp q (σ • (v + r • ξ))) 0` is the velocity at `0` of the curve
`r ↦ GExp q (σ • (v + r • ξ))`; it is the Jacobi field along the ray `t ↦ GExp q (t • v)` with
`J 0 = 0` and `∇J(0) = ξ` (a radial variation field of the family of rays out of `q`). -/


/-- **The anchor: the modulus bound for the radial variation field at every scale `σ ≤ π/3`.**

For a unit vector `v ∈ T_qM`, `0 < σ` with `2σ < ρ₀ = π - arccos (1-c)` and `cos σ ≥ 1/2`, and every
`ξ ⊥ v`,
`‖curveVelocity (fun r => GExp q (σ • (v + r • ξ))) 0‖ ≤ sin σ · (1 + 7 ε₁) · ‖ξ‖`.

This is the output of the two-centre argument (`Work.Diff.C.geoCrux.TwoCentreCoreProp` at the pair
`(σ, 2σ)`, where `κ = twoK σ (2σ)`, `λ = twoL σ (2σ)`, `δ = twoD ε₁ σ (2σ)`,
`η = twoE ε₁ σ (2σ)`, `κλ = 1/sin²σ`): with `N` the operator norm of `ξ ↦ Z_ξ(σ)` on `v^⊥` one has
`(κ-δ)(λ-η)N² ≤ 1`, and `Work.Diff.C.geoCrux.twoCentre_N_bound` gives `N ≤ sin σ(1+6ε₁)`. -/
abbrev AnchorProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (σ : ℝ) (hσ0 : 0 < σ) (h2σ : 2 * σ < Real.pi - Real.arccos (1 - c))
    (hcos : 1 / 2 ≤ Real.cos σ)
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0),
    ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        (σ • (v + r • ξ))) 0‖
      ≤ Real.sin σ * (1 + 7 * ε₁) * ‖ξ‖

/-- **Non-vanishing of the radial variation field** (non-conjugacy below `ρ₀`).

For a unit `v ∈ T_qM`, `ξ ⊥ v` with `ξ ≠ 0`, and `0 < t < ρ₀ = π - arccos (1-c)`:
`curveVelocity (fun r => GExp q (t • (v + r • ξ))) 0 ≠ 0`.

Proof: `curveVelocity_GExp_smul_variation` writes the field as
`(d (GExp q)_{t•v})(t • ξ)`; `d (GExp q)_{t•v}` is invertible because `t • v` lies in the segment
domain (`Submission.SegmentDomain.mem_segmentDomain_iff` with
`Submission.InjRadiusCut.injAtLeast_iff_forall_cutTime_le`), by
`Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain`. -/
abbrev VarFieldNeZeroProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0) (hξ0 : ξ ≠ 0)
    (t : ℝ) (ht0 : 0 < t) (htρ : t ≤ Real.pi - Real.arccos (1 - c)),
    Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
        (t • (v + r • ξ))) 0 ≠ 0

/-! ## Statements of the pieces requested from the fleet

The following `Prop`s are the (closed) statements of the three independent pieces of the proof of
`VariationModulusProp` that are delegated; they are collected here so that the delegated files can
import this module.

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-/

/-- **The backward Jacobi field from a second centre.**  For a unit vector `v ∈ T_qM`, a length
`s ∈ (0, ρ₀)` (`ρ₀ = π - arccos (1-c)`) and a direction `W ⊥ v`, there is a Jacobi field `J` along
the ray `γ t = GExp q (t • v)` with `J s = 0` and `J 0 = W`, and its initial covariant derivative
realises (minus) the Hessian of the distance from the second centre `γ s = GExp q (s • v)` at the
base point `q`:

`⟪∇J(0), W'⟫ = - rhess (rdist (γ s)) q W W'`  for all `W' ⊥ v`.

The field is the radial variation field of the family of rays **out of `γ s`**, reparametrised
backwards (`J t = Z_η(s-t)` with `Z_η` the variation field of `r ↦ GExp (γ s) (r • (-γ'(s) + r'•η))`);
the identity is `Work.Diff.C.dmRadialBridge` applied to that family (with `d := s`) together with the
reversed-geodesic identity `Submission.GExpTranslate.GExp_translate`.  The existence of the field (for
*arbitrary* `W ⊥ v`, not just those in the image of `η ↦ Z_η(s)`) uses the invertibility of
`d (GExp (γ s))` at `-s γ'(s)` — which follows from `hcut` through
`Submission.SegmentDomain.mem_segmentDomain_iff` +
`Submission.ConjEnergy.isInvertible_mfderiv_of_mem_segmentDomain` and
`Submission.InjRadiusCut.injAtLeast_iff_forall_cutTime_le` — by a dimension count (both the domain
`⟨γ'(s)⟩ᗮ` and the target `⟨v⟩ᗮ` have dimension `finrank ℝ E - 1`), the target being forced by the
Gauss pairing (`Work.OddBound.longHomotopy.gauss_pairing_fibre`). -/
abbrev BackwardShapeProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2)
    (hcut : ∀ q : M, Submission.InjRadius.InjAtLeast hmet q (Real.pi - Real.arccos (1 - c)))
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (s : ℝ) (hs0 : 0 < s) (hsρ : s < Real.pi - Real.arccos (1 - c))
    (W : TangentSpace I q) (hW : Inner.inner ℝ v W = 0),
    ∃ J : (t : ℝ) → TangentSpace I (Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)),
      (∀ t : ℝ, Submission.RauchGlobal.IsJacobiAt cov
        (fun t : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (t • v)) J t) ∧
      J s = 0 ∧ J 0 = W ∧
      ∀ W' : TangentSpace I q, Inner.inner ℝ v W' = 0 →
        Inner.inner ℝ (Submission.JacobiGlobal.covAlong cov J 0) W'
          = - Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M)
              (Submission.GlobalExp.GExp (cov := cov) hmet q (s • v)) z) q W W'

/-- **The extraction of the operator-norm bound from the two-centre inequality.**  Pure real
analysis.  This is `Work.Diff.C.geoCrux.twoCentre_N_bound` with the hypothesis
`(κ - δ)(λ - η)N² ≤ 1` weakened to the form in which the two-centre Wronskian argument delivers it,
`(κλ - κη - λδ - δη)N² ≤ 1`; the loss is `O(ε₁²)` in the relative error, which the numerical endgame
absorbs. -/
abbrev NBoundProp : Prop :=
  ∀ {σ κ lam η δ N ε₁ : ℝ}, 0 < Real.sin σ → 0 ≤ ε₁ → ε₁ ≤ 1 / 24 → 0 < κ → 0 < lam →
    0 ≤ η → 0 ≤ δ → 0 ≤ N → κ * lam = 1 / (Real.sin σ) ^ 2 →
    η ≤ 3 * ε₁ * lam → δ ≤ 3 * ε₁ * κ →
    (κ * lam - κ * η - lam * δ - δ * η) * N ^ 2 ≤ 1 →
    N ≤ Real.sin σ * (1 + 7 * ε₁)

/-- **The numerical endgame of the propagation.**  For `0 < c ≤ 1/4`, `0 ≤ ε₁`, `4 ε₁ π < c`,
`ρ₀ = π - arccos (1-c)` and `ρ₀/4 < ρ ≤ ρ₀`:
`(1 + 7ε₁) · (tan(ρ/2)/tan(ρ₀/8))^{ε₁} ≤ 1 + 25 ε₁ / sin ρ`.
This is the factor by which the anchored Sturm comparison
(`Work.Diff.C.geoCrux.modulus_anchored`) with the anchor at `δ = ρ₀/4` inflates the modulus; it is
absorbed by the additive `25 ε₁` of the target.  (Uses `tan(ρ/2) · sin ρ = 1 - cos ρ ≤ 2` and
`tan(ρ₀/8) ≥ 3/10`.) -/
abbrev PropArithProp : Prop :=
  ∀ {c ε₁ ρ : ℝ}, 0 < c → c ≤ 1 / 4 → 0 ≤ ε₁ → 4 * ε₁ * Real.pi < c →
    Real.pi - Real.arccos (1 - c) < 4 * ρ →
    ρ ≤ Real.pi - Real.arccos (1 - c) →
    (1 + 7 * ε₁) * (Real.tan (ρ / 2) / Real.tan ((Real.pi - Real.arccos (1 - c)) / 8)) ^ ε₁
      ≤ 1 + 25 * ε₁ / Real.sin ρ

/-- **The anchor, from the two-centre core.**  This is the local form of
`Work.Diff.C.geoCrux.sharp.anchor_of_twoCentre`, with the core's conclusion supplied as an explicit
hypothesis about the operator norm `N` of `ξ ↦ Z_ξ(σ)`: `‖Z_η(σ)‖ ≤ N‖η‖` for `η ⊥ v` together with
the *Wronskian* coefficient inequality
`(κλ - κη - λδ - δη)N² ≤ 1` (`κ = twoK σ (2σ)`, `λ = twoL σ (2σ)`, `δ = twoD ε₁ σ (2σ)`,
`η = twoE ε₁ σ (2σ)`).  That is exactly the hypothesis of `Work.Diff.C.geoCrux.hmod.NBound`, which
extracts `N ≤ sin σ (1 + 7ε₁)`. -/
theorem anchor_from_core (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) (hε₁ : 0 ≤ ε₁)
    (hnum2 : 4 * ε₁ * Real.pi < c)
    (q : M) (v : TangentSpace I q) (hv : Inner.inner ℝ v v = 1)
    (σ : ℝ) (hσ0 : 0 < σ) (h2σ : 2 * σ < Real.pi - Real.arccos (1 - c))
    (hcos : 1 / 2 ≤ Real.cos σ) (ξ : TangentSpace I q) (hξ : Inner.inner ℝ v ξ = 0)
    (hN : ∃ N : ℝ, 0 ≤ N ∧
      (∀ η : TangentSpace I q, Inner.inner ℝ v η = 0 →
        ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
          (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
            (σ • (v + r • η))) 0‖ ≤ N * ‖η‖) ∧
      0 < twoK σ (2 * σ) ∧ 0 < twoL σ (2 * σ) ∧
      (twoK σ (2 * σ) * twoL σ (2 * σ) - twoK σ (2 * σ) * twoE ε₁ σ (2 * σ)
        - twoL σ (2 * σ) * twoD ε₁ σ (2 * σ) - twoD ε₁ σ (2 * σ) * twoE ε₁ σ (2 * σ))
        * N ^ 2 ≤ 1) :
    ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖
      ≤ Real.sin σ * (1 + 7 * ε₁) * ‖ξ‖ := by
  obtain ⟨N, hN0, hNZ, hKpos, hLpos, hN2⟩ := hN
  have hε₁' : ε₁ ≤ 1 / 24 := by
    nlinarith [hnum2, hc1, hε₁, Real.pi_gt_three]
  have hρ0lt : Real.pi - Real.arccos (1 - c) < Real.pi := by
    have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
    linarith
  have h2σπ : 2 * σ < Real.pi := lt_trans h2σ hρ0lt
  have hspos : 0 < Real.sin σ := Real.sin_pos_of_pos_of_lt_pi hσ0 (by linarith)
  have hη : 0 ≤ twoE ε₁ σ (2 * σ) := by
    rw [twoE_two_mul]
    have h2 : 0 < Real.sin (2 * σ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2σπ
    positivity
  have hδ : 0 ≤ twoD ε₁ σ (2 * σ) := by
    rw [twoD_two_mul]
    positivity
  have hNbound : N ≤ Real.sin σ * (1 + 7 * ε₁) :=
    Work.Diff.C.geoCrux.hmod.NBound hspos hε₁ hε₁' hKpos hLpos hη hδ hN0 (twoK_mul_twoL hσ0 h2σπ)
      (twoE_le_twoL hε₁ hσ0 h2σπ hcos) (twoD_le_twoK hε₁ hσ0 h2σπ hcos) hN2
  have hZ : ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖
      ≤ N * ‖ξ‖ := hNZ ξ hξ
  calc ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
        (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (σ • (v + r • ξ))) 0‖
      ≤ N * ‖ξ‖ := hZ
    _ ≤ (Real.sin σ * (1 + 7 * ε₁)) * ‖ξ‖ :=
        mul_le_mul_of_nonneg_right hNbound (norm_nonneg ξ)

/-! ## The base-point surjectivity of the backward family

For a unit `v`, `0 < t < ρ₀` and `W ⊥ v`, there is a backward field out of `γ(t)` with value `W` at
`q`; this is the `u = t` case of `Work.Diff.C.geoCrux.tcPrayFld_surj` (invertibility of
`d (GExp (γ t))` at `-t γ'(t)`). -/
theorem bwd_surj_base (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {c : ℝ}
    (hcut : ∀ x : M, Submission.InjRadius.InjAtLeast hmet x (rho0 c))
    {q : M} {v : TangentSpace I q} (hvn : ‖v‖ = 1) (hv0 : v ≠ 0)
    {t : ℝ} (ht0 : 0 < t) (ht : t < rho0 c)
    {W : TangentSpace I q} (hW : tcIn (M := M) (I := I) q v W = 0) :
    ∃ η : TangentSpace I (tcGam (cov := cov) hmet q v t),
      tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t) η
          (-(tcVel (cov := cov) hmet q v t)) = 0 ∧
      tcPrayFld (cov := cov) hmet q v t η t = W := by
  have hwn : ‖-(tcVel (cov := cov) hmet q v t)‖ = 1 := by
    rw [norm_neg, tcVel_norm (cov := cov) hmet hv0 t, hvn]
  obtain ⟨e, he⟩ := Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt
    (I := I) (cov := cov) hmet htor (hcut (tcGam (cov := cov) hmet q v t))
    (w := t • (-(tcVel (cov := cov) hmet q v t)))
    (by rw [norm_smul, Real.norm_of_nonneg ht0.le, hwn, mul_one]; exact ht)
  have hval : tcPrayFld (cov := cov) hmet q v t ((1 / t) • (e.symm W)) t = W := by
    have h1 : tcPrayFld (cov := cov) hmet q v t ((1 / t) • (e.symm W)) t
        = (mfderiv 𝓘(ℝ, E) I (fun w : E => Submission.GlobalExp.GExp (cov := cov) hmet
            (tcGam (cov := cov) hmet q v t) w)
            (t • (-(tcVel (cov := cov) hmet q v t)))) (e.symm W) := by
      rw [tcPrayFld_eq_mfderiv]
      congr 1
      rw [smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [h1, ← he]
    exact ContinuousLinearEquiv.apply_symm_apply e W
  have hη : tcIn (M := M) (I := I) (tcGam (cov := cov) hmet q v t)
      ((1 / t) • (e.symm W)) (-(tcVel (cov := cov) hmet q v t)) = 0 := by
    have hG := tcPrayFld_gauss (cov := cov) hmet htor (q := q) (v := v) t
      ((1 / t) • (e.symm W)) t
    rw [hval] at hG
    have hpt : tcPray (cov := cov) hmet q v t t = q := by
      show Submission.GlobalExp.GExp (cov := cov) hmet (tcGam (cov := cov) hmet q v t)
        (t • (-(tcVel (cov := cov) hmet q v t))) = q
      have h := tc_rev_point (cov := cov) hmet hvn t 0
      rw [sub_zero] at h
      exact h.trans (by simp [tcGam])
    rw [hpt] at hG
    have hvel : Submission.Geodesic.curveVelocity (I := I)
        (tcPray (cov := cov) hmet q v t) t = -v := by
      have h := tc_rev_vel (cov := cov) hmet hvn hv0 t 0
      rw [sub_zero, tcVel_zero (cov := cov) hmet hv0] at h
      exact h
    rw [hvel] at hG
    have h1 : tcIn (M := M) (I := I) q W (-v) = 0 := by
      rw [show (-v : TangentSpace I q) = (-1 : ℝ) • v from (neg_one_smul ℝ v).symm,
        tcIn_smul_right, tcIn_symm, hW, mul_zero]
    rw [h1] at hG
    exact (mul_eq_zero.mp hG.symm).resolve_left (ne_of_gt ht0)
  exact ⟨_, hη, hval⟩

/-! ## The assembly

Everything is assembled from the proved pieces of `Work.Diff.C.geoCrux.sharp.*`: the modulus
assembly `varMod_core`, the non-vanishing `Zf_ne_zero`, the log-derivative bound `logderiv_le`, the
anchored Sturm comparison `modulus_anchored_pos` and the numerical endgame `anchor_arith`; the
anchor is supplied by `anchor_from_core` from the two-centre core `twoCentre_core`. -/

/-- **The radial modulus bound for the radial variation fields** (the target). -/
theorem variation_modulus : Work.Diff.C.geoCrux.VariationModulusProp := by
  intro E iE1 iE2 iE3 iE4 H iH I M iM1 iM2 iM3 iM4 iRB iCM iBd iNt iCS iPC cov iCov
    hmet htor c ε₁ hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv ρ hρ0 hρπ ξ hξ
  have hmain := Work.Diff.C.geoCrux.sharp.varMod_core (I := I) (M := M) (cov := cov)
    hmet htor hc hc1 hε₁ hnum2 hcut q v hv ρ hρ0 hρπ ξ hξ
    (fun σ hσ0 h2σ hcos η hη => by
      have h2σ' : 2 * σ < Real.pi - Real.arccos (1 - c) := by
        have hσπ : σ < Real.pi := by
          have h : 0 < Real.arccos (1 - c) := Real.arccos_pos.mpr (by linarith)
          linarith [h2σ]
        have hσle : σ ≤ Real.pi / 3 := by
          by_contra h
          push Not at h
          have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := σ)
            (by positivity) hσπ.le h
          rw [Real.cos_pi_div_three] at hlt
          linarith
        have harccos_lt : Real.arccos (1 - c) < Real.pi / 3 := by
          have h1 : Real.arccos (1 - c) < Real.arccos (1 / 2) :=
            Real.arccos_lt_arccos (by norm_num) (by linarith) (by linarith)
          have h2 : Real.arccos (1 / 2) = Real.pi / 3 := by
            rw [← Real.cos_pi_div_three]
            exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
          rwa [h2] at h1
        linarith [hσle, harccos_lt, h2σ]
      obtain ⟨N, h0, hZ, h1, h2, h3⟩ :=
        Work.Diff.C.geoCrux.variation.twoCentre_N_pair (I := I) (M := M) (cov := cov)
          hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcut q v hv σ hσ0 h2σ'
      have hZ' : ∀ η' : TangentSpace I q, Inner.inner ℝ v η' = 0 →
          ‖Submission.Geodesic.curveVelocity (I := I) (M := M)
            (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q
              (σ • (v + r • η'))) 0‖ ≤ N * ‖η'‖ := by
        intro η' hη'
        have h := hZ η' hη'
        have h2 : ‖Zf (cov := cov) hmet q v η' σ‖
            = ‖tcFwd (cov := cov) hmet q v η' σ‖ := rfl
        rw [← h2, Work.Diff.C.geoCrux.Zf_norm_eq (cov := cov) hmet q v η' σ] at h
        exact h
      have hraw := anchor_from_core (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁ hnum2 q v
        hv σ hσ0 h2σ' hcos η hη ⟨N, h0, hZ', h1, h2, h3⟩
      rwa [← Work.Diff.C.geoCrux.Zf_norm_eq (cov := cov) hmet q v η σ] at hraw)
    (fun η hη hη0 t ht0 htρ =>
      Work.Diff.C.geoCrux.sharp.Zf_ne_zero (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv η hη hη0 t ht0 htρ)
    (fun η hη hη0 t ht0 htρ =>
      Work.Diff.C.geoCrux.sharp.logderiv_le (I := I) (M := M) (cov := cov)
        hmet htor hc hc1 hε₁ hnum2 hsmC hHess hcont hgrad hcut q v hv η hη hη0 t ht0 htρ)
    (fun {v' w' ε δ d A} hδ hδd hε hdπ hδpos hdpos hder hwb hanchor =>
      Work.Diff.C.geoCrux.sharp.modulus_anchored_pos hδ hδd hε hdπ hδpos hdpos hder hwb hanchor)
    (fun {c' ε₁' ρ'} hc' hc1' hε₁' hnum2' hρ' hρπ' =>
      Work.Diff.C.geoCrux.sharp.anchor_arith hc' hc1' hε₁' hnum2' hρ' hρπ')
  rw [← Work.Diff.C.geoCrux.Zf_norm_eq (cov := cov) hmet q v ξ ρ]
  exact hmain

end Work.Diff.C.geoCrux

