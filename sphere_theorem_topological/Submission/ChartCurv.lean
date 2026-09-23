import Submission.Jacobi
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve

/-!
# The curvature tensor in a chart

This file computes the Riemann curvature tensor `curv` (see `ChallengeDeps.lean`) in the chart at a
point `x₀`, in terms of the chart Christoffel symbols and their first derivatives in the base point.
This is the missing bridge between the intrinsic connection `cov` (out of which `curv` is
*defined*) and the coordinate computations (`chartCovDeriv`, the geodesic spray
`chartGeodesicVectorField`) on which the whole local theory of `Submission/Geodesic.lean` is built.

Write `B(q;a,b) = christoffelEval cov x₀ q a (frameVector x₀ q b)` for the Christoffel symbol read
in the chart (as a bilinear form on the coordinate vectors `a`, `b`), and
`∂B(q;v)(a,b) = mvfderiv (fun r => B(r;a,b)) q (frameVector x₀ q v)` for its derivative in the base
point.  The main outputs are

* `hasDerivAt_chrB_curve` : the chain rule along a curve,
  `d/dt B(c(t);a(t),b(t)) = ∂B(c(t);c'(t))(a(t),b(t)) + B(c(t);a'(t),b(t)) + B(c(t);a(t),b'(t))`;
* `cov_eq_frameVector_chartCoord` : the chart formula for `∇_v W` of a *global* smooth section `W`
  whose coordinate function near the point is `c`;
* `curvVec_eq_chart` : **the curvature tensor in coordinates**,
  `R(σ_c, σ_b)σ_a = σ_{∂B(·;c)(a,b) - ∂B(·;b)(a,c) + B(B(a,b),c) - B(B(a,c),b)}`.

## GOTCHA (important)

`lake build` compiles this workspace with `autoImplicit false` (set in `lakefile.toml`), while
`lake env lean FILE` does *not*: a lemma whose statement mentions a variable that is not among its
arguments (for instance a chart centre `x₀` that only occurs inside `(chartAt H x₀).source`)
elaborates fine with `lake env lean` but FAILS under `lake build`.  Always test with
`lake build Submission`.

## Implementation notes

The chart Christoffel symbol is read through the geodesic spray: for fixed basis vectors `e_i`,
`e_j` the functions `q ↦ B(q;e_i,e_j)` are `C^∞` on the chart (this is
`contDiffOn_chartSpray`, one entry at a time).  Everything else is the bilinearity of `B` in its two
vector slots, so all derivative computations are reduced to the finitely many entries `B(·;e_i,e_j)`
and the ordinary chain rule along a curve (`mvfderiv_comp_curve`).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.CurvatureVec
open Submission.Curvature
open Bundle
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
open Commons.Geometry.Manifold.Tangent

namespace Submission.ChartCurv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-! ## The Christoffel symbol as a bilinear form on coordinate vectors -/

/-- The chart Christoffel symbol as a bilinear form on coordinate vectors:
`B q a b = Γ(q)(a)(σ_b)`, where `σ_b` is the frame vector with coordinates `b`. -/
noncomputable def chrB (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M)
    (a b : E) : E :=
  christoffelEval cov x₀ p a (frameVector (I := I) x₀ p b)

lemma chrB_apply (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M) (a b : E) :
    chrB cov x₀ p a b = christoffelEval cov x₀ p a (frameVector (I := I) x₀ p b) := rfl

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

lemma chrB_add_fst (x₀ p : M) (a₁ a₂ b : E) (hp : p ∈ (chartAt H x₀).source) :
    chrB cov x₀ p (a₁ + a₂) b = chrB cov x₀ p a₁ b + chrB cov x₀ p a₂ b := by
  rw [chrB_apply, chrB_apply, chrB_apply, christoffelEval_add_left _ _ _ _ _ _ hp]

lemma chrB_smul_fst (x₀ p : M) (c : ℝ) (a b : E) (hp : p ∈ (chartAt H x₀).source) :
    chrB cov x₀ p (c • a) b = c • chrB cov x₀ p a b := by
  rw [chrB_apply, chrB_apply, christoffelEval_smul_left _ _ _ _ _ _ hp]

lemma chrB_add_snd (x₀ p : M) (a b₁ b₂ : E) :
    chrB cov x₀ p a (b₁ + b₂) = chrB cov x₀ p a b₁ + chrB cov x₀ p a b₂ := by
  rw [chrB_apply, chrB_apply, chrB_apply, frameVector_add, christoffelEval_add_right]

lemma chrB_smul_snd (x₀ p : M) (c : ℝ) (a b : E) :
    chrB cov x₀ p a (c • b) = c • chrB cov x₀ p a b := by
  rw [chrB_apply, chrB_apply, frameVector_smul, christoffelEval_smul_right]

lemma chrB_zero_fst (x₀ p : M) (b : E) : chrB cov x₀ p 0 b = 0 := by
  rw [chrB_apply, christoffelEval_zero_left]

lemma chrB_zero_snd (x₀ p : M) (a : E) : chrB cov x₀ p a 0 = 0 := by
  rw [chrB_apply, show frameVector (I := I) x₀ p (0 : E) = 0 from map_zero _, 
    christoffelEval_zero_right]

lemma chrB_sum_fst {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (a : ι → E) (b : E)
    (hp : p ∈ (chartAt H x₀).source) :
    chrB cov x₀ p (∑ i ∈ s, c i • a i) b = ∑ i ∈ s, c i • chrB cov x₀ p (a i) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chrB_zero_fst]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, chrB_add_fst _ _ _ _ _ hp,
        chrB_smul_fst _ _ _ _ _ hp, ih]

lemma chrB_sum_snd {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (b : ι → E) (a : E) :
    chrB cov x₀ p a (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i • chrB cov x₀ p a (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chrB_zero_snd]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, chrB_add_snd, chrB_smul_snd, ih]

/-! ## Smoothness of the Christoffel entries -/

/-- The basis of `E` used for all coordinate expansions. -/
local notation "bb" => Module.finBasis ℝ E

/-- One entry of the chart Christoffel symbol: `q ↦ B(q;e_i,e_j)`. -/
noncomputable def gammaEntry (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) : M → E :=
  fun q => chrB cov x₀ q (bb i) (bb j)

lemma gammaEntry_apply (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) (q : M) :
    gammaEntry cov x₀ i j q = chrB cov x₀ q (bb i) (bb j) := rfl

lemma contMDiffOn_gammaEntry [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (gammaEntry cov x₀ i j) (chartAt H x₀).source := by
  have hσ : ∀ k : Fin (Module.finrank ℝ E),
      CMDiff[(chartAt H x₀).source] ∞
        (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (bb k))) :=
    fun k => contMDiffOn_trivializationAt_symmL_section (I := I) (M := M) x₀ (bb k)
  have hW : CMDiff[(chartAt H x₀).source] ∞
      (T% (fun q : M => cov (frameSection (I := I) x₀ (bb i)) q
        (frameVector (I := I) x₀ q (bb j)))) :=
    contMDiffOn_cov_apply cov (inferInstance) (chartAt H x₀).open_source (hσ i) (hσ j)
  have h := contMDiffOn_continuousLinearMapAt_section (I := I) (M := M) x₀ hW
  rw [Set.inter_self] at h
  refine h.congr (fun q _ => ?_)
  rw [gammaEntry_apply, chrB_apply, christoffelEval_def]

lemma mdifferentiableAt_gammaEntry [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    MDifferentiableAt I 𝓘(ℝ, E) (gammaEntry cov x₀ i j) p :=
  (((contMDiffOn_gammaEntry (cov := cov) x₀ i j) p hp).contMDiffAt
    ((chartAt H x₀).open_source.mem_nhds hp)).mdifferentiableAt (by simp)

/-- The chain rule along a curve for a function `M → E`. -/
lemma hasDerivAt_comp_curve {g : M → E} {γ : ℝ → M} {t : ℝ}
    (hg : MDifferentiableAt I 𝓘(ℝ, E) g (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    HasDerivAt (fun s => g (γ s)) (mvfderiv I g (γ t) (curveVelocity (I := I) γ t)) t := by
  have hcomp : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) (fun s => g (γ s)) t := hg.comp t hγ
  rw [mdifferentiableAt_iff_differentiableAt] at hcomp
  refine hcomp.hasDerivAt.congr_deriv ?_
  show deriv ((fun y : M => g y) ∘ γ) t = _
  rw [← mvfderiv_comp_curve (I := I) hg hγ]
  rfl

/-- The derivative of the Christoffel symbol in the *base point*, at `p` in the direction `v`,
evaluated on the coordinate vectors `a`, `b`. -/
noncomputable def dB (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x₀ p : M)
    (v a b : E) : E :=
  mvfderiv I (fun q : M => chrB cov x₀ q a b) p (frameVector (I := I) x₀ p v)



/-! ## Expansion in the basis, and the chain rule -/

/-- `mvfderiv` respects eventual equality. -/
lemma mvfderiv_congr_of_eventuallyEq {g₁ g₂ : M → E} {x : M} (h : g₁ =ᶠ[𝓝 x] g₂) :
    mvfderiv I g₁ x = mvfderiv I g₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  -- v4.34: the rewrite leaves a `tangentSpaceCast`, definitionally the identity.
  all_goals first | rfl | (ext v; rfl)

/-- The frame vector is linear in the coordinate vector (difference form). -/
lemma frameVector_sub (x₀ p : M) (v w : E) :
    frameVector (I := I) x₀ p (v - w)
      = frameVector (I := I) x₀ p v - frameVector (I := I) x₀ p w := map_sub _ v w

/-- The Christoffel symbol expanded in the basis, in the two vector slots. -/
lemma chrB_eq_sum_gammaEntry (x₀ p : M) (a b : E) (hp : p ∈ (chartAt H x₀).source) :
    chrB cov x₀ p a b
      = ∑ i, ∑ j, (((bb).coord i) a * ((bb).coord j) b) • gammaEntry cov x₀ i j p := by
  classical
  conv_lhs => rw [← (bb).sum_repr a]
  rw [chrB_sum_fst _ _ _ _ _ _ hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← (bb).sum_repr b]
  rw [chrB_sum_snd, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, Module.Basis.coord_apply, Module.Basis.coord_apply, gammaEntry_apply]

/-- Differentiability of a finite sum of functions, in pointwise form. -/
lemma mdifferentiableAt_sum_fun {ι : Type} (s : Finset ι) (G : ι → M → E) {x : M}
    (h : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, E) (G i) x) :
    MDifferentiableAt I 𝓘(ℝ, E) (fun y : M => ∑ i ∈ s, G i y) x := by
  rw [show (fun y : M => ∑ i ∈ s, G i y) = (∑ i ∈ s, G i) from by
    funext y; rw [Finset.sum_apply]]
  exact MDifferentiableAt.sum (t := s) (f := G) (z := x) h

/-- Applied form: `mvfderiv` of a finite sum of functions. -/
lemma mvfderiv_sum_apply {ι : Type} (s : Finset ι) (f : ι → M → E) {x : M}
    {v : TangentSpace I x} (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, E) (f i) x) :
    mvfderiv I (fun y : M => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = (0 : M → E) := by
        funext y
        simp only [Finset.sum_empty, Pi.zero_apply]
      rw [hz, Finset.sum_empty]
      show mvfderiv I (fun _ : M => (0 : E)) x v = 0
      rw [mvfderiv_const, ContinuousLinearMap.zero_apply]
  | insert i s hi ih =>
      have hi' : MDifferentiableAt I 𝓘(ℝ, E) (f i) x := hf i (Finset.mem_insert_self i s)
      have hs' : ∀ j ∈ s, MDifferentiableAt I 𝓘(ℝ, E) (f j) x :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hsum : MDifferentiableAt I 𝓘(ℝ, E) (fun y : M => ∑ j ∈ s, f j y) x :=
        mdifferentiableAt_sum_fun s f hs'
      have hfun : (fun y : M => ∑ j ∈ insert i s, f j y)
          = (f i + fun y : M => ∑ j ∈ s, f j y) := by
        funext y
        rw [Finset.sum_insert hi]
        rfl
      rw [Finset.sum_insert hi, hfun, mvfderiv_add hi' hsum, ContinuousLinearMap.add_apply,
        ih hs']

/-- Applied form: `mvfderiv` of a constant scalar multiple. -/
lemma mvfderiv_const_smul_apply {c : ℝ} {g : M → E} {x : M} {v : TangentSpace I x}
    (hg : MDifferentiableAt I 𝓘(ℝ, E) g x) :
    mvfderiv I (fun y : M => c • g y) x v = c • mvfderiv I g x v := by
  have hconst : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => c) x := mdifferentiableAt_const
  have hfun : (fun y : M => c • g y) = (fun _ : M => c) • g := rfl
  rw [hfun, mvfderiv_smul (I := I) (x := x) (a := fun _ : M => c) hconst hg]
  simp only [add_apply, smul_apply, mvfderiv_const, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smulRight_apply, zero_smul, add_zero]

/-- **The derivative of the Christoffel symbol in the base point, expanded in the basis.** -/
lemma mvfderiv_chrB_apply [ContMDiffCovariantDerivative cov ∞] (x₀ p : M) (a b v : E)
    (hp : p ∈ (chartAt H x₀).source) :
    mvfderiv I (fun q : M => chrB cov x₀ q a b) p (frameVector (I := I) x₀ p v)
      = ∑ i, ∑ j, (((bb).coord i) a * ((bb).coord j) b) •
          mvfderiv I (gammaEntry cov x₀ i j) p (frameVector (I := I) x₀ p v) := by
  classical
  have hsrcev : (fun q : M => chrB cov x₀ q a b) =ᶠ[𝓝 p]
      (fun q : M => ∑ i, ∑ j, (((bb).coord i) a * ((bb).coord j) b) •
        gammaEntry cov x₀ i j q) := by
    filter_upwards [((chartAt H x₀).open_source).mem_nhds hp] with q hq
    exact chrB_eq_sum_gammaEntry (cov := cov) x₀ q a b hq
  rw [mvfderiv_congr_of_eventuallyEq hsrcev]
  rw [mvfderiv_sum_apply (I := I) Finset.univ
    (f := fun i q => ∑ j, (((bb).coord i) a * ((bb).coord j) b) • gammaEntry cov x₀ i j q)
    (v := frameVector (I := I) x₀ p v)
    (hf := fun i _ => mdifferentiableAt_sum_fun Finset.univ
      (G := fun j q => (((bb).coord i) a * ((bb).coord j) b) • gammaEntry cov x₀ i j q)
      (fun j _ => (mdifferentiableAt_const (c := ((bb).coord i) a * ((bb).coord j) b)).smul
        (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hp)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mvfderiv_sum_apply (I := I) Finset.univ
    (f := fun j q => (((bb).coord i) a * ((bb).coord j) b) • gammaEntry cov x₀ i j q)
    (v := frameVector (I := I) x₀ p v)
    (hf := fun j _ => (mdifferentiableAt_const (c := ((bb).coord i) a * ((bb).coord j) b)).smul
      (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hp))]
  exact Finset.sum_congr rfl fun j _ =>
    mvfderiv_const_smul_apply (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hp)


/-! ## The chain rule for the Christoffel symbol -/

/-- **The chain rule for the chart Christoffel symbol along a chart curve.**  For a coordinate
curve `u` with velocity `v` at `t` and coordinate fields `a`, `b` with derivatives `a'`, `b'`,

`d/dt B(c(t);a(t),b(t)) = ∂B(c(t);v)(a(t),b(t)) + B(c(t);a'(t),b(t)) + B(c(t);a(t),b'(t))`,

where `c(t) = (extChartAt I x₀).symm (u t)` and `∂B` is the derivative of `B` in the base point
(`dB`). -/
theorem hasDerivAt_chrB_curve [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u a b : ℝ → E} {v a' b' : E} {t : ℝ}
    (hu : HasDerivAt u v t) (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => chrB cov x₀ ((extChartAt I x₀).symm (u s)) (a s) (b s))
      (dB cov x₀ ((extChartAt I x₀).symm (u t)) v (a t) (b t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) a' (b t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (a t) b') t := by
  classical
  set γ : ℝ → M := fun s => (extChartAt I x₀).symm (u s) with hγdef
  have hγd : MDifferentiableAt 𝓘(ℝ) I γ t :=
    mdifferentiableAt_chartCurve (I := I) hu htgt hstay
  have hsrc : γ t ∈ (chartAt H x₀).source := mem_source_chartCurve (I := I) (x₀ := x₀) htgt
  have hvel : curveVelocity (I := I) γ t = frameVector (I := I) x₀ (γ t) v :=
    curveVelocity_chartCurve (I := I) hu htgt hstay
  have hsrcev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H x₀).source :=
    hstay.mono (fun s hs => mem_source_chartCurve (I := I) hs)
  -- the termwise derivatives
  have hterm : ∀ i j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => (((bb).coord i) (a s) * ((bb).coord j) (b s)) •
          gammaEntry cov x₀ i j (γ s))
        ((((bb).coord i) (a t) * ((bb).coord j) (b t)) •
            mvfderiv I (gammaEntry cov x₀ i j) (γ t) (curveVelocity (I := I) γ t)
          + ((((bb).coord i) a' * ((bb).coord j) (b t) + ((bb).coord i) (a t) *
              ((bb).coord j) b')) • gammaEntry cov x₀ i j (γ t)) t := by
    intro i j
    have hci : HasDerivAt (fun s => (bb).coord i (a s)) ((bb).coord i a') t :=
      (((bb).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t ha
    have hcj : HasDerivAt (fun s => (bb).coord j (b s)) ((bb).coord j b') t :=
      (((bb).coord j : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t hb
    have hG : HasDerivAt (fun s => gammaEntry cov x₀ i j (γ s))
        (mvfderiv I (gammaEntry cov x₀ i j) (γ t) (curveVelocity (I := I) γ t)) t :=
      hasDerivAt_comp_curve (I := I)
        (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hsrc) hγd
    have hsm := (hci.mul hcj).smul hG
    have hfun : (((fun s => (bb).coord i (a s)) * fun s => (bb).coord j (b s)) •
        fun s => gammaEntry cov x₀ i j (γ s))
        = (fun s => ((bb).coord i (a s) * (bb).coord j (b s)) • gammaEntry cov x₀ i j (γ s)) :=
      rfl
    rw [hfun] at hsm
    exact hsm
  -- assemble the sum
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, (((bb).coord i) (a s) * ((bb).coord j) (b s)) •
      gammaEntry cov x₀ i j (γ s))
      (∑ i, ∑ j, ((((bb).coord i) (a t) * ((bb).coord j) (b t)) •
            mvfderiv I (gammaEntry cov x₀ i j) (γ t) (curveVelocity (I := I) γ t)
          + ((((bb).coord i) a' * ((bb).coord j) (b t) + ((bb).coord i) (a t) *
              ((bb).coord j) b')) • gammaEntry cov x₀ i j (γ t))) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
      HasDerivAt.sum (u := Finset.univ) fun j _ => hterm i j
    have hfun : (∑ i, ∑ j, (fun s => (((bb).coord i) (a s) * ((bb).coord j) (b s)) •
        gammaEntry cov x₀ i j (γ s)))
        = (fun s => ∑ i, ∑ j, (((bb).coord i) (a s) * ((bb).coord j) (b s)) •
            gammaEntry cov x₀ i j (γ s)) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hfun] at h
    exact h
  -- go back to `chrB`
  have heq : (fun s => chrB cov x₀ (γ s) (a s) (b s)) =ᶠ[𝓝 t]
      (fun s => ∑ i, ∑ j, (((bb).coord i) (a s) * ((bb).coord j) (b s)) •
        gammaEntry cov x₀ i j (γ s)) :=
    hsrcev.mono (fun s hs => chrB_eq_sum_gammaEntry (cov := cov) x₀ (γ s) (a s) (b s) hs)
  have hsum' := hsum.congr_of_eventuallyEq heq
  -- identify the derivative
  have hval : (∑ i, ∑ j, ((((bb).coord i) (a t) * ((bb).coord j) (b t)) •
            mvfderiv I (gammaEntry cov x₀ i j) (γ t) (curveVelocity (I := I) γ t)
          + ((((bb).coord i) a' * ((bb).coord j) (b t) + ((bb).coord i) (a t) *
              ((bb).coord j) b')) • gammaEntry cov x₀ i j (γ t)))
      = dB cov x₀ (γ t) v (a t) (b t)
        + chrB cov x₀ (γ t) a' (b t) + chrB cov x₀ (γ t) (a t) b' := by
    rw [hvel, dB, mvfderiv_chrB_apply (cov := cov) x₀ (γ t) (a t) (b t) v hsrc,
      chrB_eq_sum_gammaEntry (cov := cov) x₀ (γ t) a' (b t) hsrc,
      chrB_eq_sum_gammaEntry (cov := cov) x₀ (γ t) (a t) b' hsrc]
    simp only [Finset.sum_add_distrib, add_smul]
    abel
  rwa [hval] at hsum'


/-! ## The chart formula for `∇` of a global section -/

/-- Applied form: `mvfderiv` of `q ↦ (coord i)(c q) • w`. -/
lemma mvfderiv_coord_smul_apply {c : M → E} {x : M} {v : TangentSpace I x}
    (i : Fin (Module.finrank ℝ E)) (hc : MDifferentiableAt I 𝓘(ℝ, E) c x) (w : E) :
    mvfderiv I (fun y : M => (bb).coord i (c y) • w) x v
      = (mvfderiv I (fun y : M => (bb).coord i (c y)) x v) • w := by
  have hlin : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => (bb).coord i (c y)) x :=
    (((bb).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).mdifferentiableAt.comp x hc
  have hconst : MDifferentiableAt I 𝓘(ℝ, E) (fun _ : M => w) x := mdifferentiableAt_const
  have hfun : (fun y : M => (bb).coord i (c y) • w)
      = (fun y : M => (bb).coord i (c y)) • (fun _ : M => w) := rfl
  rw [hfun, mvfderiv_smul (I := I) (x := x) hlin hconst]
  simp only [add_apply, ContinuousLinearMap.smul_apply, mvfderiv_const,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.smulRight_apply, smul_zero, zero_add]

/-- `mvfderiv` of a function into `E`, expanded in the basis of `E`. -/
lemma mvfderiv_eq_sum_coord {c : M → E} {x : M} (hc : MDifferentiableAt I 𝓘(ℝ, E) c x)
    {v : TangentSpace I x} :
    mvfderiv I c x v = ∑ i, (mvfderiv I (fun y : M => (bb).coord i (c y)) x v) • bb i := by
  classical
  have heq : c =ᶠ[𝓝 x] (fun y : M => ∑ i, (bb).coord i (c y) • bb i) :=
    Filter.Eventually.of_forall fun y => by
      rw [← (bb).sum_repr (c y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.coord_apply]
  rw [mvfderiv_congr_of_eventuallyEq heq]
  rw [mvfderiv_sum_apply (I := I) Finset.univ
    (f := fun i y => (bb).coord i (c y) • bb i) (v := v)
    (hf := fun i _ => by
      have hlin : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => (bb).coord i (c y)) x :=
        (((bb).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).mdifferentiableAt.comp x hc
      exact hlin.smul (mdifferentiableAt_const (c := bb i)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact mvfderiv_coord_smul_apply (I := I) i hc (bb i)


/-- The sum of the coordinate functionals times the basis vectors is the identity. -/
lemma sum_coord_smul_eq (v : E) : (∑ i, (bb).coord i v • bb i) = v := by
  classical
  rw [show (∑ i, (bb).coord i v • bb i) = ∑ i, (bb).repr v i • bb i from
    Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])]
  exact (bb).sum_repr v

/-- **The chart formula for `∇` of a global smooth section.**  If a globally smooth section `W`
agrees near `p` with the frame field of the smooth coefficient function `c`, then
`∇_v W = σ_{∂c(v) + B(c,v)}` in coordinates. -/
theorem cov_eq_frameVector_chartCoord [ContMDiffCovariantDerivative cov ∞]
    {W : Π x : M, TangentSpace I x} {c : M → E} {x₀ p : M}
    (hp : p ∈ (chartAt H x₀).source) (hW : CMDiff ∞ (T% W))
    (hc : ContMDiffAt I 𝓘(ℝ, E) ∞ c p)
    (heq : W =ᶠ[𝓝 p] fun q => frameVector (I := I) x₀ q (c q)) (v : E) :
    cov W p (frameVector (I := I) x₀ p v)
      = frameVector (I := I) x₀ p (mvfderiv I c p (frameVector (I := I) x₀ p v)
          + chrB cov x₀ p (c p) v) := by
  classical
  -- the frame field of `c` as a sum over the basis
  have hfr : (fun q : M => frameVector (I := I) x₀ q (c q))
      = (fun q : M => ∑ i, (bb).coord i (c q) • frameSection (I := I) x₀ (bb i) q) := by
    funext q
    show frameVector (I := I) x₀ q (c q)
      = ∑ i, (bb).coord i (c q) • frameSection (I := I) x₀ (bb i) q
    conv_lhs => rw [← sum_coord_smul_eq (c q)]
    rw [frameVector_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (bb).coord i (c q) • frameVector (I := I) x₀ q (bb i)
      = (bb).coord i (c q) • frameSection (I := I) x₀ (bb i) q
    rw [show frameSection (I := I) x₀ (bb i) q = frameVector (I := I) x₀ q (bb i) from rfl]
  have hkey := cov_eq_sum_of_eventuallyEq_pointwise (cov := cov) Finset.univ
    (fun i (q : M) => (bb).coord i (c q))
    (fun i (q : M) => frameSection (I := I) x₀ (bb i) q)
    (Z := W) (x := p) (v := frameVector (I := I) x₀ p v) (hW p)
    (fun i => contMDiffAt_frameSection (I := I) x₀ (bb i) hp)
    (fun i => (((bb).coord i : E →ₗ[ℝ] ℝ).toContinuousLinearMap).contMDiffAt.comp p hc)
    (heq.trans (Filter.Eventually.of_forall (fun q => congrFun hfr q)))
  rw [hkey]
  -- identify the two sums
  have hsum1 : (∑ i, (bb).coord i (c p) • cov (frameSection (I := I) x₀ (bb i)) p
        (frameVector (I := I) x₀ p v))
      = frameVector (I := I) x₀ p (chrB cov x₀ p (c p) v) := by
    have h1 : ∀ i, cov (frameSection (I := I) x₀ (bb i)) p (frameVector (I := I) x₀ p v)
        = frameVector (I := I) x₀ p
            (christoffelEval cov x₀ p (bb i) (frameVector (I := I) x₀ p v)) :=
      fun i => cov_frameSection_eq cov x₀ p (bb i) (frameVector (I := I) x₀ p v) hp
    simp only [h1]
    rw [← frameVector_sum, ← christoffelEval_sum_left Finset.univ cov x₀ p
      (fun i => (bb).coord i (c p)) (fun i => bb i) (frameVector (I := I) x₀ p v) hp]
    congr 1
    rw [chrB_apply, sum_coord_smul_eq]
  have hsum2 : (∑ i, mvfderiv I (fun q : M => (bb).coord i (c q)) p
        (frameVector (I := I) x₀ p v) • frameSection (I := I) x₀ (bb i) p)
      = frameVector (I := I) x₀ p (mvfderiv I c p (frameVector (I := I) x₀ p v)) := by
    simp only [frameSection_eq_frameVector]
    rw [← frameVector_sum, mvfderiv_eq_sum_coord (I := I) (hc.mdifferentiableAt (by simp))]
  rw [hsum1, hsum2, ← frameVector_add, add_comm]

/-! ## The coordinate function of a section, and the curvature tensor in coordinates -/

/-- The coordinate function of a section in the chart at `x₀`. -/
noncomputable def coordFun (x₀ : M) (W : Π x : M, TangentSpace I x) : M → E :=
  fun q => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (W q)

lemma coordFun_apply (x₀ : M) (W : Π x : M, TangentSpace I x) (q : M) :
    coordFun x₀ W q
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (W q) := rfl

lemma contMDiffAt_coordFun (x₀ : M) {W : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) {p : M}
    (hp : p ∈ (chartAt H x₀).source) : ContMDiffAt I 𝓘(ℝ, E) ∞ (coordFun x₀ W) p :=
  ((contMDiffOn_continuousLinearMapAt_section (I := I) (M := M) x₀ hW.contMDiffOn) p
    ⟨Set.mem_univ p, hp⟩).contMDiffAt (by
      simpa using (chartAt H x₀).open_source.mem_nhds hp)

lemma frameVector_coordFun_eq (x₀ : M) {W : Π x : M, TangentSpace I x} {q : M}
    (hq : q ∈ (chartAt H x₀).source) : frameVector (I := I) x₀ q (coordFun x₀ W q) = W q := by
  rw [coordFun_apply]
  exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt (R := ℝ)
    (by simpa using hq) (W q)

lemma coordFun_frameVector (x₀ : M) {q : M} (hq : q ∈ (chartAt H x₀).source) (v : E) :
    coordFun x₀ (fun y : M => frameVector (I := I) x₀ y v) q = v := by
  rw [coordFun_apply]
  exact Trivialization.continuousLinearMapAt_symmL (trivializationAt E (TangentSpace I) x₀)
    (R := ℝ) (by simpa using hq) v

/-- **The chart formula for `∇` of a global smooth section**, in terms of its coordinate function. -/
theorem cov_eq_frameVector_coordFun [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    {W : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) {p : M}
    (hp : p ∈ (chartAt H x₀).source) {v : E} :
    cov W p (frameVector (I := I) x₀ p v)
      = frameVector (I := I) x₀ p (mvfderiv I (coordFun x₀ W) p (frameVector (I := I) x₀ p v)
          + chrB cov x₀ p (coordFun x₀ W p) v) := by
  refine cov_eq_frameVector_chartCoord (cov := cov) (x₀ := x₀) (c := coordFun x₀ W) hp hW
    (contMDiffAt_coordFun (x₀ := x₀) hW hp) ?_ v
  filter_upwards [((chartAt H x₀).open_source).mem_nhds hp] with q hq
  exact (frameVector_coordFun_eq (x₀ := x₀) hq).symm

/-- The coordinate function of `∇_T W` is `d(coordinate function of W in the direction of T)`
plus the Christoffel correction. -/
lemma coordFun_cov [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    {W T : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) (hT : CMDiff ∞ (T% T))
    {p : M} (hp : p ∈ (chartAt H x₀).source) :
    coordFun x₀ (fun y : M => cov W y (T y)) p
      = mvfderiv I (coordFun x₀ W) p (T p)
        + chrB cov x₀ p (coordFun x₀ W p) (coordFun x₀ T p) := by
  have h := cov_eq_frameVector_coordFun (cov := cov) (x₀ := x₀) hW hp
    (v := coordFun x₀ T p)
  rw [frameVector_coordFun_eq (x₀ := x₀) hp] at h
  conv_lhs => rw [coordFun_apply, h]
  exact coordFun_frameVector (x₀ := x₀) hp _

/-- **The curvature tensor in coordinates.**  For the frame fields `σ_a`, `σ_b`, `σ_c` of the chart
at `x₀`, the curvature is again a frame field, with the coordinate vector given by the classical
formula `R = ∂Γ - ∂Γ + ΓΓ - ΓΓ`. -/
theorem curvVec_eq_chart [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    (x₀ p : M) (a b c : E) (hp : p ∈ (chartAt H x₀).source) :
    curvVec cov p (frameVector (I := I) x₀ p c) (frameVector (I := I) x₀ p b)
        (frameVector (I := I) x₀ p a)
      = frameVector (I := I) x₀ p
          (dB cov x₀ p c a b - dB cov x₀ p b a c
            + chrB cov x₀ p (chrB cov x₀ p a b) c - chrB cov x₀ p (chrB cov x₀ p a c) b) := by
  classical
  obtain ⟨S, hSsm, hSeq⟩ := exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ c hp
  obtain ⟨T, hTsm, hTeq⟩ := exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ b hp
  obtain ⟨W, hWsm, hWeq⟩ := exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ a hp
  have hSp : S p = frameVector (I := I) x₀ p c := hSeq.eq_of_nhds
  have hTp : T p = frameVector (I := I) x₀ p b := hTeq.eq_of_nhds
  have hWp : W p = frameVector (I := I) x₀ p a := hWeq.eq_of_nhds
  -- an open neighbourhood of `p` on which the three sections are the coordinate frame fields
  obtain ⟨U, hUne, hU⟩ := Filter.eventually_iff_exists_mem.mp ((hWeq.and hTeq).and hSeq)
  set V : Set M := interior (U ∩ (chartAt H x₀).source) with hVdef
  have hVopen : IsOpen V := isOpen_interior
  have hpV : p ∈ V := mem_interior_iff_mem_nhds.mpr
    (Filter.inter_mem hUne ((chartAt H x₀).open_source.mem_nhds hp))
  have hVsub : V ⊆ U ∩ (chartAt H x₀).source := interior_subset
  have hsrcV : ∀ q ∈ V, q ∈ (chartAt H x₀).source := fun q hq => (hVsub hq).2
  have hWV : ∀ q ∈ V, W q = frameVector (I := I) x₀ q a :=
    fun q hq => (hU q (hVsub hq).1).1.1
  have hTV : ∀ q ∈ V, T q = frameVector (I := I) x₀ q b :=
    fun q hq => (hU q (hVsub hq).1).1.2
  have hSV : ∀ q ∈ V, S q = frameVector (I := I) x₀ q c :=
    fun q hq => (hU q (hVsub hq).1).2
  have hcoordW : ∀ q ∈ V, coordFun x₀ W q = a := fun q hq => by
    rw [coordFun_apply, hWV q hq]
    exact coordFun_frameVector (x₀ := x₀) (hsrcV q hq) a
  have hcoordT : ∀ q ∈ V, coordFun x₀ T q = b := fun q hq => by
    rw [coordFun_apply, hTV q hq]
    exact coordFun_frameVector (x₀ := x₀) (hsrcV q hq) b
  have hcoordS : ∀ q ∈ V, coordFun x₀ S q = c := fun q hq => by
    rw [coordFun_apply, hSV q hq]
    exact coordFun_frameVector (x₀ := x₀) (hsrcV q hq) c
  -- smoothness of the two covariant derivatives
  have hZsm : CMDiff ∞ (T% (fun y : M => cov W y (T y))) :=
    contMDiff_cov_apply cov (inferInstance) hWsm hTsm
  have hZ'sm : CMDiff ∞ (T% (fun y : M => cov W y (S y))) :=
    contMDiff_cov_apply cov (inferInstance) hWsm hSsm
  -- the coordinate functions of `∇_T W` and `∇_S W`
  have hmvW (q : M) (hq : q ∈ V) (v : TangentSpace I q) :
      mvfderiv I (coordFun x₀ W) q v = 0 := by
    have hconst : coordFun x₀ W =ᶠ[𝓝 q] (fun _ : M => a) :=
      Filter.eventually_of_mem (hVopen.mem_nhds hq) (fun r hr => hcoordW r hr)
    rw [mvfderiv_congr_of_eventuallyEq hconst, mvfderiv_const]
    simp
  have hCZev : coordFun x₀ (fun y : M => cov W y (T y))
      =ᶠ[𝓝 p] (fun q : M => chrB cov x₀ q a b) := by
    filter_upwards [hVopen.mem_nhds hpV] with q hq
    rw [coordFun_cov (cov := cov) x₀ hWsm hTsm (hsrcV q hq), hcoordW q hq, hcoordT q hq,
      hmvW q hq _, zero_add]
  have hCZ'ev : coordFun x₀ (fun y : M => cov W y (S y))
      =ᶠ[𝓝 p] (fun q : M => chrB cov x₀ q a c) := by
    filter_upwards [hVopen.mem_nhds hpV] with q hq
    rw [coordFun_cov (cov := cov) x₀ hWsm hSsm (hsrcV q hq), hcoordW q hq, hcoordS q hq,
      hmvW q hq, zero_add]
  -- the bracket vanishes
  have hbr : mlieBracket I S T p = 0 := by
    rw [hSeq.mlieBracket_vectorField_eq hTeq]
    exact Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
      (I := I) x₀ c b hp
  -- the value of `curv` on the extensions
  have hcurv := curvVec_eq cov (inferInstance) hSsm hTsm hWsm hSp hTp hWp
  rw [hcurv]
  simp only [curv]
  have h1 : cov (fun y : M => cov W y (T y)) p (S p)
      = frameVector (I := I) x₀ p (dB cov x₀ p c a b + chrB cov x₀ p (chrB cov x₀ p a b) c) := by
    have h := cov_eq_frameVector_coordFun (cov := cov) (x₀ := x₀) hZsm (hsrcV p hpV) (v := c)
    rw [← hSp] at h
    rw [h, hCZev.eq_of_nhds, dB]
    congr 1
    rw [mvfderiv_congr_of_eventuallyEq (I := I) hCZev, ← hSp]
  have h2 : cov (fun y : M => cov W y (S y)) p (T p)
      = frameVector (I := I) x₀ p (dB cov x₀ p b a c + chrB cov x₀ p (chrB cov x₀ p a c) b) := by
    have h := cov_eq_frameVector_coordFun (cov := cov) (x₀ := x₀) hZ'sm (hsrcV p hpV) (v := b)
    rw [← hTp] at h
    rw [h, hCZ'ev.eq_of_nhds, dB]
    congr 1
    rw [mvfderiv_congr_of_eventuallyEq (I := I) hCZ'ev, ← hTp]
  have h3 : cov W p (mlieBracket I S T p) = 0 := by rw [hbr, map_zero]
  rw [h1, h2, h3]
  simp only [sub_zero]
  simp only [frameVector_sub, frameVector_add]
  abel

end

end Submission.ChartCurv




