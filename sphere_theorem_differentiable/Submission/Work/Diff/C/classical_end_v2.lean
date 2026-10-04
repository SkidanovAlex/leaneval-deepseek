import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.Scale
import Submission.Work.Diff.C.osc_lower
import Submission.Work.Diff.C.cap_avoid
import Submission.Work.Diff.C.cutoff_psi
import Submission.Work.Diff.C.dist_lt_pi
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.model_lower_off_bad
import Submission.Work.Diff.C.cend_constants
import Submission.Work.Diff.C.cend_constants_extra
import Submission.Work.Diff.C.fcos_inputs3
import Submission.Work.Diff.C.gram_pointwise2
import Submission.Work.Diff.C.local_diffeo_of_gram
import Submission.Work.Diff.C.hess_upper
import Submission.Work.Diff.C.hess_lower
import Submission.Work.Diff.C.inj_radius_v2
import Submission.Work.Diff.C.eikonal_of_inj_v2
import Submission.Work.Diff.C.dist_eikonal2
import Submission.Work.Diff.C.diffeo_of_local
import Submission.Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
import Submission.Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: the classical high-pinching differentiable sphere theorem (`classical_end_v2`)

This is the assembly of the classical endgame: a compact, simply connected manifold carrying a
smooth metric whose Levi-Civita connection is `(κ, (1+η)κ]`-pinched for a small `η = η(n)` is
diffeomorphic to the standard sphere.

## Structure of the proof

* **Normalisation** (`Work.Diff.C.pinchedFor_scale`): scale the metric by `κ`; the connection is
  unchanged and the pinching becomes `(1, 1+η]`.  This is the only place where the *given* metric
  enters: the diffeomorphism produced below is metric-independent.
* **The four analytic inputs**, proved in other areas and imported at the end (all live):
  `Work.Diff.C.dist_eikonal2` (`EikonalInput`), `Work.Diff.C.hess_upper` (`HessUpperInput`),
  `Work.Diff.C.hess_lower` (`HessLowerInput`), `Work.Diff.C.diffeo_of_local`
  (`DiffeoOfLocalInput`).
* **The middle construction** (the remaining work): with `f_i = cos ∘ d(q_i,·)`, where
  `q_0 = p`, `q_{i+1} = exp_p((π/2)·e_i)` for a `g`-orthonormal basis `e_1,…`, and `ψ` the cutoff of
  `Work.Diff.C.cutoff_psi`, the functions `F_i = ψ ∘ f_i` satisfy the hypotheses of
  `Work.Diff.C.local_diffeo_of_gram` (`Work.Diff.C.gram_pointwise`), so `G = F/|F|` is a local
  diffeomorphism onto `SphereD E`; `DiffeoOfLocalInput` then gives the diffeomorphism.

## Status (state of the area, for the next session)

PROVED, in `Submission/Work/Diff/C/`:

* `Scale.pinchedFor_scale` (`Diff/C/Scale`): scaling the metric by `κ` divides the pinching
  constants by `κ`.  Used in step 1 above, which is therefore *complete*.
* `osc_lower`, `cutoff_psi`, `cap_avoid`, `ray_cover`, `gram_along`, `numeric_constants`
  (`Diff/C/<name>`): the trigonometric corner bound, the cutoff function, the "the radial segment
  stays inside `{f > -1 + 2c}`" bootstrap, the radial representation of a point, the integrated
  Gram bound along a geodesic, and the numerical inequalities for the constants below.
* `classical_end_v2` is reduced here to `classical_end_assembly` plus the four analytic inputs.

IN FLIGHT (children of this session): `ray_cos_compare` (Lemma R, the ODE comparison along a
radial geodesic), `fcos_hess` (Hessian of `cos ∘ d`), `fcos_inputs` (the region hypotheses
`SmoothOnRegion`/`HessBoundRegion`/`Continuous`/`|∇| ≤ 1` for `fcos q`), `init_data`
(`f_0(p) = 1`, `∇f_0(p) = 0`, `f_i(p) = 0`, `∇f_i(p) = e_i`), `gram_pointwise` (the pointwise
Gram bounds for `F_i = ψ ∘ f_i`), `local_diffeo_of_gram` (`G = F/|F|` is a local diffeomorphism).

REMAINING (`classical_end_assembly`):

* pick `p : M` and a `g`-orthonormal basis `e` of `T_pM` (`OrthonormalBasis`),
* `Work.Diff.C.fcos_inputs` + `Work.Diff.C.init_data` give the hypotheses of
  `Work.Diff.C.gram_pointwise` (note `hdiam` from `Work.Diff.C.dist_lt_pi`),
* `Work.Diff.C.gram_pointwise` gives the hypotheses of `Work.Diff.C.local_diffeo_of_gram`
  (entrywise → form conversion: `|A_ij - δ_ij| ≤ ε₂` for all `i,j` gives the form bound with the
  factor `n + 1`, easy),
* `DiffeoOfLocalInput` (the live contract `Work.Diff.C.diffeo_of_local`) finishes.

⚠️ TWO CAVEATS discovered while writing this file (see also the caution in `Setup.lean`):

1. **The endpoint `rdist = 0`.**  The region `{fcos q > -1 + c}` contains the centre `q`, and the
   Hessian-comparison quantity `cos d - sin d·√(1+η)·cot(√(1+η)d)` equals `1` at `d = 0` in Lean
   (`Real.cot 0 = 0`).  Hypotheses of the form "`max(… at d) ≤ ε` for `d ∈ [0, arccos(-1+c)]`"
   therefore force `ε ≥ 1` and are useless.  `fcos_hess` and `fcos_inputs` as delegated contain
   this defect; they must be restated with the comparison hypothesis restricted to `0 < d` and the
   centre treated separately (at the centre `Hess (cos ∘ d)(q) = -g` holds exactly).
2. **`eta0` must be tiny.**  The constants satisfy the chain
   `√c ≳ η/ε₁` (from `hkey`), `3c ≤ 1 - cos α`, `4πε₁ < c`, and
   `100(n+2)(ε₁π + α + √c) < 1`; this is satisfiable only for very small `η`
   (e.g. `η = 1e-14`, `c ≈ 1e-14`, `ε₁ ≈ 1e-7`, `α ≈ 1e-4`), not for `1e-6`.
   `numeric_constants` currently only proves the *shape* of the inequalities for the constants
   `α = 1/(10^4 m)`, `c = 1/(10^10 m²)`, `ε₁ = 1/(10^12 m²)`; the final `eta0` and the relation
   `√c ≳ η/ε₁` still have to be fixed and proved.
-/


set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section BasisInsts

variable [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The standard orthonormal basis of `T_pM`, indexed by `Fin (finrank ℝ E)`. -/
noncomputable def onBasis (p : M) : Fin (Module.finrank ℝ E) → TangentSpace I p :=
  fun i => stdOrthonormalBasis ℝ (TangentSpace I p)
    (Fin.cast (show Module.finrank ℝ E = Module.finrank ℝ (TangentSpace I p) from rfl) i)

theorem onBasis_orthonormal (p : M) (i j : Fin (Module.finrank ℝ E)) :
    Inner.inner ℝ (onBasis (I := I) p i) (onBasis (I := I) p j) =
      if i = j then 1 else 0 := by
  simp only [onBasis, OrthonormalBasis.inner_eq_ite, Fin.cast_inj]

/-- Entrywise bounds on the Gram matrix give the quadratic-form bound used by
`Work.Diff.C.local_diffeo_of_gram`. -/
theorem gram_entrywise_to_form {n : ℕ} {F : Fin (n + 1) → M → ℝ} {X ε₂ : ℝ} (hX : 0 ≤ X)
    (hε₂ : ((n : ℝ) + 1) * X ≤ ε₂)
    (hentry : ∀ (x : M) (i j : Fin (n + 1)),
      |gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0)| ≤ X) :
    ∀ (x : M) (cc : Fin (n + 1) → ℝ),
      |(∑ i, ∑ j, cc i * cc j * gp (I := I) (M := M) (F i) (F j) x) - (∑ i, cc i ^ 2)|
        ≤ ε₂ * (∑ i, cc i ^ 2) := by
  intro x cc
  have hdiag : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        cc i * cc j * (if i = j then (1 : ℝ) else 0)) = ∑ i, cc i ^ 2 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun i _ => (pow_two (cc i)).symm
  have hdecomp : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        cc i * cc j * gp (I := I) (M := M) (F i) (F j) x) - (∑ i, cc i ^ 2)
      = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), cc i * cc j *
          (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0)) := by
    rw [← hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hdecomp]
  have hstats : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        |cc i * cc j * (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0))|)
      ≤ X * (∑ i : Fin (n + 1), |cc i|) ^ 2 := by
    have hstep : ∀ i j : Fin (n + 1),
        |cc i * cc j * (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0))|
          ≤ |cc i| * |cc j| * X := by
      intro i j
      rw [abs_mul, abs_mul]
      gcongr
      exact hentry x i j
    calc (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          |cc i * cc j * (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0))|)
        ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), |cc i| * |cc j| * X :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hstep i j
      _ = ((∑ i : Fin (n + 1), |cc i|) * (∑ j : Fin (n + 1), |cc j|)) * X := by
          rw [Finset.sum_mul_sum]
          simp only [Finset.sum_mul]
      _ = X * (∑ i : Fin (n + 1), |cc i|) ^ 2 := by ring
  have hcs : (∑ i : Fin (n + 1), |cc i|) ^ 2 ≤ ((n : ℝ) + 1) * ∑ i : Fin (n + 1), cc i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin (n + 1) => |cc i|)
    have hcard : ((Finset.univ : Finset (Fin (n + 1))).card : ℝ) = (n : ℝ) + 1 := by
      simp
    have hsq : ∑ i : Fin (n + 1), |cc i| ^ 2 = ∑ i : Fin (n + 1), cc i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sq_abs]
    rw [hcard, hsq] at h
    exact h
  have hnn : 0 ≤ ∑ i : Fin (n + 1), cc i ^ 2 :=
    Finset.sum_nonneg fun i _ => pow_two_nonneg (cc i)
  calc |∑ i : Fin (n + 1), ∑ j : Fin (n + 1), cc i * cc j *
        (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0))|
      ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          |cc i * cc j * (gp (I := I) (M := M) (F i) (F j) x - (if i = j then 1 else 0))| :=
        le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ X * (∑ i : Fin (n + 1), |cc i|) ^ 2 := hstats
    _ ≤ X * (((n : ℝ) + 1) * ∑ i : Fin (n + 1), cc i ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hX
    _ ≤ ε₂ * (∑ i : Fin (n + 1), cc i ^ 2) := by
        have : X * (((n : ℝ) + 1) * ∑ i, cc i ^ 2)
            = (((n : ℝ) + 1) * X) * ∑ i, cc i ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hε₂ hnn

end BasisInsts

section Assembly

variable [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- Assembly of the classical endgame: the `(n+1)`-point construction. -/
theorem classical_end_assembly
    (hdim : 2 ≤ Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η) (hη3 : η < 3)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hInj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) hmet
      (Real.pi / Real.sqrt (1 + η)))
    (hEik : EikonalInput (I := I) (M := M) cov η)
    (hUpper : HessUpperInput (I := I) (M := M) cov)
    (hLower : HessLowerInput (I := I) (M := M) cov η)
    (hDiffeo : DiffeoOfLocalInput (I := I) (M := M))
    (hpinch : Pinched cov 1 (1 + η))
    (hηsmall : η ≤ 1 / (10 ^ 18 * ((Module.finrank ℝ E : ℝ) + 2) ^ 6)) :
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E) := by
  -- the pinching `(1, 1+η]` with `η < 3` gives `(1,4]`
  have hpinch4 : Pinched cov 1 4 := by
    intro X Y hX hY x h1 h2 h3
    obtain ⟨hlt, hle⟩ := hpinch X Y hX hY x h1 h2 h3
    exact ⟨hlt, le_trans hle (by linarith)⟩
  -- nonemptiness of the manifold (simple connectivity)
  haveI hne : Nonempty M := (simply_connected_iff_unique_homotopic M).mp inferInstance |>.1
  obtain ⟨p⟩ := hne
  -- the orthonormal basis of `T_pM`
  have hON : ∀ i j : Fin (Module.finrank ℝ E),
      Inner.inner ℝ (onBasis (I := I) p i) (onBasis (I := I) p j) = if i = j then 1 else 0 :=
    fun i j => onBasis_orthonormal (I := I) p i j
  -- the diameter bound (Bonnet–Myers)
  have hdiam : ∀ x : M, rdist (I := I) (M := M) p x ≤ Real.pi :=
    fun x => (dist_lt_pi (I := I) (M := M) hdim cov hmet htor hpinch4 p x).le
  -- the initial data at `p`
  have hinit : InitData (I := I) (M := M) (cov := cov) hmet p (onBasis (I := I) p) :=
    init_data (I := I) (M := M) hmet htor hη hη3 hInj hEik hON
  -- the numerical constants
  set δ : ℝ := η ^ (1 / 3 : ℝ) with hδdef
  set c : ℝ := 100 * δ ^ 2 with hcdef
  set ε₁ : ℝ := δ ^ 2 with hε₁def
  set α : ℝ := 1000 * δ with hαdef
  have hηsmall' : η ≤ 1 / (10 ^ 18 * ((Module.finrank ℝ E : ℝ) + 2) ^ 3) := by
    refine le_trans hηsmall (one_div_le_one_div_of_le (by positivity) ?_)
    have h2 : (1 : ℝ) ≤ ((Module.finrank ℝ E : ℝ) + 2) ^ 3 := by
      have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ 2 := pow_two_nonneg _
      nlinarith [h0, h1]
    nlinarith [h2, pow_pos (by linarith : (0 : ℝ) < ((Module.finrank ℝ E : ℝ) + 2)) 3]
  have hconsts : 0 < c ∧ c ≤ 1 / 4 ∧ 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ ε₁ ∧
      3 * c ≤ 1 - Real.cos α ∧ 4 * ε₁ * Real.pi < c ∧
      Real.arccos (-1 + c) < Real.pi / Real.sqrt (1 + η) ∧
      (∀ d : ℝ, 0 < d → d ≤ Real.arccos (-1 + c) →
        max (Real.cos d - Real.sin d * Real.sqrt (1 + η)
          * Real.cot (Real.sqrt (1 + η) * d)) 0 ≤ ε₁) ∧
      100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) < 1 := by
    have h := cend_constants (n := Module.finrank ℝ E) hdim hη hηsmall'
    dsimp only at h
    simpa only [hδdef, hcdef, hε₁def, hαdef] using h
  obtain ⟨hcpos, hcle, hαpos, hαle, hεge, hnum1, hnum2, harc, hkey, hfinal⟩ := hconsts
  -- the cutoff
  obtain ⟨ψ, hψsm, hψmono, hψderiv, hψid, hψcap⟩ := cutoff_psi hcpos
  -- the region facts for `fᵢ = cos ∘ d(qᵢ,·)`
  obtain ⟨hsm, hsmC, hHess, hcont, hgrad⟩ :
      (∀ q : M, SmoothOnRegion (I := I) (M := M) c (fcos (I := I) (M := M) q)) ∧
      (∀ (q x : M), -1 + c ≤ fcos (I := I) (M := M) q x →
        CMDiffAt ∞ (fcos (I := I) (M := M) q) x) ∧
      (∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q)) ∧
      (∀ q : M, Continuous (fcos (I := I) (M := M) q)) ∧
      (∀ (q x : M), -1 + c < fcos (I := I) (M := M) q x →
        Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
          (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
          = 1 - (fcos (I := I) (M := M) q x) ^ 2) :=
    fcos_inputs3 (I := I) (M := M) hdim hmet htor hη hη3 hcpos hεge hInj hEik hUpper hLower
      hpinch hpinch4 harc hkey
  -- the pointwise Gram estimates (from `Work.Diff.C.gram_pointwise2`)
  haveI hpath : PathConnectedSpace M := inferInstance
  obtain ⟨hFsm, hunit, hentry⟩ :=
    gram_pointwise2 (I := I) (M := M) hmet htor hdim hαpos hαle hcpos hcle hεge hnum1 hnum2
      hON hdiam hsm hsmC hHess hcont hgrad hinit ⟨hψsm, hψmono, hψderiv, hψid, hψcap⟩
  -- the quadratic-form version of the entrywise bounds
  set X : ℝ := 100 * ((Module.finrank ℝ E : ℝ) + 2)
    * (ε₁ * Real.pi + α + Real.sqrt c) with hXdef
  set ε₂ : ℝ := ((Module.finrank ℝ E : ℝ) + 1) * X with hε₂def
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have h2p : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 2 := by positivity
    have hsq : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hcpos
    positivity
  have hε₂le : ((Module.finrank ℝ E : ℝ) + 1) * X ≤ ε₂ := le_of_eq hε₂def.symm
  have hε₂0 : 0 ≤ ε₂ := by
    rw [hε₂def]
    exact mul_nonneg (by positivity) hX0
  have hε₂1 : ε₂ < 1 := by
    rw [hε₂def, hXdef]
    have h := cend_constants_extra (n := Module.finrank ℝ E) hdim hη hηsmall
    dsimp only at h
    simpa only [hδdef, hcdef, hε₁def, hαdef] using h.2
  have hgram' : ∀ (x : M) (cc : Fin (Module.finrank ℝ E + 1) → ℝ),
      |(∑ i, ∑ j, cc i * cc j * gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p (onBasis (I := I) p) i y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p (onBasis (I := I) p) j y)) x)
        - (∑ i, cc i ^ 2)| ≤ ε₂ * (∑ i, cc i ^ 2) :=
    gram_entrywise_to_form (n := Module.finrank ℝ E)
      (F := fun i : Fin (Module.finrank ℝ E + 1) => fun y : M =>
        ψ (fFam (I := I) (M := M) (cov := cov) hmet p (onBasis (I := I) p) i y))
      hX0 hε₂le hentry
  -- the local diffeomorphism
  obtain ⟨G, hG, -⟩ :
      ∃ G : M → SphereD E, IsLocalDiffeomorph I (𝓡 (Module.finrank ℝ E)) ∞ G ∧
        ∀ x : M, ∃ b : ℝ, 0 < b ∧
          ((G x : SphereD E) : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
            = b • (fun i : Fin (Module.finrank ℝ E + 1) =>
                ψ (fFam (I := I) (M := M) (cov := cov) hmet p (onBasis (I := I) p) i x)) := by
    refine local_diffeo_of_gram (I := I) (M := M) hFsm hε₂0 hε₂1 ?_ hgram'
    intro x
    refine le_trans (hunit x) ?_
    rw [hε₂def]
    refine le_mul_of_one_le_left hX0 ?_
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    linarith
  exact hDiffeo hdim G hG

end Assembly

/-- The pinching constant of the classical endgame: `1 + eta0` is the pinching constant that the
middle construction can handle. -/
-- chosen `η = η(n)` tiny enough for the constants of `Work.Diff.C.cend_constants`
noncomputable def eta0 (n : ℕ) : ℝ := 1 / (10 ^ 18 * ((n : ℝ) + 2) ^ 6)

/-- **Differentiable sphere theorem (classical high-pinching endgame).** -/
theorem classical_end_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E) :
    ClassicalEnd I M := by
  refine ⟨eta0 (Module.finrank ℝ E), ?_, ?_⟩
  · unfold eta0; positivity
  · intro g cov hcovsm htor hmet κ hκ hpinch
    -- 1.  The transfers read in the instance of the challenge statement, spelled out explicitly.
    have hpinch' : PinchedFor (I := I) (M := M) g.toRiemannianMetric cov κ ((1 + eta0 (Module.finrank ℝ E)) * κ) :=
      (pinchedFor_iff (hamb := (⟨g.toRiemannianMetric⟩ :
          RiemannianBundle (fun x : M ↦ TangentSpace I x)))
        (I := I) (M := M) cov κ ((1 + eta0 (Module.finrank ℝ E)) * κ)).mp hpinch
    have hmetFor : IsMetricCompatibleFor (I := I) (M := M) g.toRiemannianMetric cov :=
      (isMetricCompatibleFor_iff (hamb := (⟨g.toRiemannianMetric⟩ :
          RiemannianBundle (fun x : M ↦ TangentSpace I x))) (I := I) (M := M) cov).mp hmet
    have hsm_old : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
        IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := by
      haveI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      exact inferInstance
    obtain ⟨g', hg'⟩ := Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
      (E := fun x : M ↦ TangentSpace I x) g.toRiemannianMetric hκ
    -- 2.  Install the normalised metric `g' = κ • g` as the ambient instance.
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
      Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric
        (IB := I) (n := ∞) (F := E) (E := fun x : M ↦ TangentSpace I x)
        g.toRiemannianMetric g' hκ hg' hsm_old
    haveI : ContMDiffCovariantDerivative cov ∞ := hcovsm.some
    have hmet' : IsMetricCompatible cov :=
      (isMetricCompatibleFor_iff (I := I) (M := M) cov).mpr
        (Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric
          (M := M) (g := g.toRiemannianMetric) (g' := g') (c := κ) (cov := cov) hκ hg' hmetFor)
    have hpinch'' : Pinched cov 1 (1 + eta0 (Module.finrank ℝ E)) := by
      rw [pinchedFor_iff (I := I) (M := M) cov 1 (1 + eta0 (Module.finrank ℝ E))]
      have h := pinchedFor_scale (I := I) (M := M) (cov := cov) (g := g.toRiemannianMetric)
        (g' := g') (c := κ) hκ hg' hpinch'
      rw [show (1 + eta0 (Module.finrank ℝ E)) * κ / κ = 1 + eta0 (Module.finrank ℝ E) from mul_div_cancel_right₀ _ hκ.ne',
        show κ / κ = 1 from div_self hκ.ne'] at h
      exact h
    haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by linarith)
    haveI : PathConnectedSpace M := inferInstance
    -- 3.  The analytic inputs of the classical endgame, discharged by the proved sub-lemmas.
    have hηpos : 0 < eta0 (Module.finrank ℝ E) := by
      unfold eta0
      exact one_div_pos.mpr (by positivity)
    have hηlt3 : eta0 (Module.finrank ℝ E) < 3 := by
      unfold eta0
      rw [div_lt_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ ((Module.finrank ℝ E : ℝ) + 2) ^ 6 := by
        have h0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
        have h2le : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 2 := by linarith
        have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2le 6
        norm_num at hpow
        linarith
      have h3 : (0 : ℝ) < 10 ^ 18 * ((Module.finrank ℝ E : ℝ) + 2) ^ 6 := by positivity
      nlinarith [h1, h3]
    have hpinch4 : Pinched cov 1 4 := by
      intro X Y hX hY x h1 h2 h3
      obtain ⟨hlt, hle⟩ := hpinch'' X Y hX hY x h1 h2 h3
      exact ⟨hlt, le_trans hle (by linarith)⟩
    have hInj : Submission.InjRadius.InjAllAtLeast (I := I) (cov := cov) (hmet := hmet')
        (Real.pi / Real.sqrt (1 + eta0 (Module.finrank ℝ E))) :=
      inj_radius_v2 (I := I) (M := M) hdim cov hmet' htor hηpos hηlt3 hpinch''
    have hEik : EikonalInput (I := I) (M := M) cov (eta0 (Module.finrank ℝ E)) :=
      fun p y hy0 hy =>
        dist_eikonal2 (I := I) (M := M) cov hmet' htor hηpos hηlt3 hpinch'' p hy0 hy
    have hUpper : HessUpperInput (I := I) (M := M) cov :=
      fun p x hsm hunit V =>
        hess_upper (I := I) (M := M) cov hmet' htor hpinch4 p hsm hunit
    have hLower : HessLowerInput (I := I) (M := M) cov (eta0 (Module.finrank ℝ E)) :=
      fun p x hsm hunit hlt V =>
        hess_lower (I := I) (M := M) cov hmet' htor hηpos hpinch'' p hsm hunit hlt
    have hDiffeo : DiffeoOfLocalInput (I := I) (M := M) :=
      fun hdim2 G hG => diffeo_of_local (I := I) (M := M) hdim2 hG
    have hηsmall'' :
        eta0 (Module.finrank ℝ E) ≤ 1 / (10 ^ 18 * ((Module.finrank ℝ E : ℝ) + 2) ^ 6) := by
      unfold eta0; exact le_rfl
    exact classical_end_assembly (I := I) (M := M) (η := eta0 (Module.finrank ℝ E)) hdim
      hηpos hηlt3 hmet' htor hInj hEik hUpper hLower hDiffeo hpinch'' hηsmall''
end Work.Diff.C
