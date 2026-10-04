import Submission.BonnetMyers
import Submission.CurveCov

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second variation of the energy for a quadratic family

This file proves the **general chart second-variation formula** for the *quadratic* family

`Ψ(s,t) = (extChartAt I x₀).symm (u t + s • η t + (s²/2) • ζ t)`

whose `s = 0` curve is a chart geodesic:

`E''(0) = 2 (⟪A L, w L⟫ - ⟪A 0, w 0⟫) - 2 ∫₀^L indexIntegrand`

where `E(s) = ∫₀^L ⟪∂_tΨ(s,t), ∂_tΨ(s,t)⟫ dt`, `A = ζ + Γ(η,η)` is the coordinate expression of
the covariant acceleration `∇_s∂_sΨ|₀` and `indexIntegrand` is the index form of
`Submission/BonnetMyers.lean` (`⟪η, R(η,γ')γ'⟫ - ⟪∇_tη, ∇_tη⟫`).

The straight-line formula (`famEnergy_second_deriv_eq`) is the special case `ζ = 0`, where the
boundary term is `⟪Γ(η,η), w⟫`.  The quadratic case is what is needed in order to glue the formula
over a cover of a long geodesic by charts.

## Status: PROVED (all declarations sorry-free)

`fam2Energy_second_deriv` is the main theorem.  The supporting API is

* `fam2`, `fam2S`, `fam2T`, `fam2ST`, `fam2Curve`, `fam2Energy`: the family and its partials;
* `fam2DsT`, `fam2DtS`, `fam2DsTderiv`, `fam2DsDsT`: the covariant derivatives `D_sT`, `D_tS`,
  `∂_s(D_sT)` and `D_sD_sT` in coordinates;
* `fam2A`, `fam2Aderiv`, `fam2DtA`: the acceleration `A = ζ + Γ(η,η)` and its derivatives;
* `hasDerivAt_fam2_s`, `hasDerivAt_fam2S_s/_t`, `hasDerivAt_fam2T_s/_t`, `hasDerivAt_fam2ST_s`,
  `hasDerivAt_fam2DsT_s`, `hasDerivAt_fam2A`, `hasDerivAt_famG2_s`, `hasDerivAt_fam2DsT_pair`;
* the joint continuity package (`continuousOn_fam2_prod`, …, `continuousOn_fam2DsDsT_prod`,
  `continuousOn_fam2A_curve`, `continuousOn_fam2DtA_curve`);
* `fam2Energy_hasDerivAt` (`E'(s) = 2 ∫ ⟪D_sT, T⟫`), `fam2Energy_deriv_second` (the second
  derivative of that integral);
* `dB_comm_snd` (**NEW GAP FILLED**: the derivative of the Christoffel symbol in the base point is
  symmetric in its last two arguments — a consequence of torsion-freeness, proved from
  `chrB_comm` + `mvfderiv_congr_of_eventuallyEq`);
* `fam2DsT_eq_fam2DtS` (Clairaut), **`fam2_ricci`** (`D_sD_sT|₀ = D_tA + R(η,w)η` in coordinates),
  `integral_fam2DtA` (the FTC for `D_tA`, using `D_tw = 0`).

## Structure of the proof

With `S = ∂_sΨ = η + s ζ`, `T = ∂_tΨ = w + s e + (s²/2) ζ'` and the covariant derivatives
`D_s y = ∂_s y + Γ(y, S)`, `D_t y = ∂_t y + Γ(y, T)`:

1. the product rule in `s` (`hasDerivAt_chartGram_curve`) gives
   `E'(s) = 2 ∫ ⟪D_sT, T⟫ dt`, and Clairaut (`∂_sT = ∂_tS`) plus the symmetry of `Γ` give
   `D_sT = D_tS`;
2. differentiating once more in `s` gives
   `E''(0) = 2 ∫ (⟪D_sD_sT, T⟫ + ⟪D_sT, D_sT⟫)|₀ dt`, and the Ricci identity in coordinates
   (`fam2_ricci`) gives `D_sD_sT|₀ = D_tA + R(η,w)η`;
3. `∫ ⟪D_tA, w⟫ = [⟪A,w⟫]₀^L` by the fundamental theorem of calculus (`D_tw = 0` on the geodesic),
   and the symmetry of the curvature turns `⟪R(η,w)η, w⟫` into `-⟪η, R(η,w)w⟫`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartCurv
open Submission.SecondVariation
open Submission.ChartConnection
open Submission.CurvatureVec
open Submission.IndexForm
open Submission.IndexForm2
open Submission.BonnetMyers

namespace Submission.SecondVar2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## The quadratic family and its partial derivatives -/

/-- The quadratic family `u t + s • η t + (s²/2) • ζ t`. -/
def fam2 (u η ζ : ℝ → E) (s t : ℝ) : E := u t + s • η t + (s ^ 2 / 2) • ζ t

/-- The `s`-velocity of the quadratic family. -/
def fam2S (η ζ : ℝ → E) (s t : ℝ) : E := η t + s • ζ t

/-- The `t`-velocity of the quadratic family (with `e = η'`, `ζ' = (ζ)'`). -/
def fam2T (w e ζ' : ℝ → E) (s t : ℝ) : E := w t + s • e t + (s ^ 2 / 2) • ζ' t

/-- The mixed partial `∂_s∂_tΨ = ∂_t∂_sΨ` (with `e = η'`, `ζ' = ζ'`). -/
def fam2ST (e ζ' : ℝ → E) (s t : ℝ) : E := e t + s • ζ' t

/-- The chart curve of the quadratic family. -/
def fam2Curve (x₀ : M) (u η ζ : ℝ → E) (s t : ℝ) : M := (extChartAt I x₀).symm (fam2 u η ζ s t)

/-- The energy of the quadratic family. -/
def fam2Energy (x₀ : M) (u η ζ w e ζ' : ℝ → E) (L s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..L,
    chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2T w e ζ' s t) (fam2T w e ζ' s t)

/-- `∂_s (D_sT)` in coordinates. -/
def fam2DsTderiv (x₀ : M) (u η ζ w e ζ' : ℝ → E) (s t : ℝ) : E :=
  ζ' t
    + dB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2S η ζ s t)
        (fam2T w e ζ' s t) (fam2S η ζ s t)
    + chrB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2ST e ζ' s t) (fam2S η ζ s t)
    + chrB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2T w e ζ' s t) (ζ t)

/-- `D_s T = ∂_sT + Γ(T,S)` in coordinates. -/
def fam2DsT (x₀ : M) (u η ζ w e ζ' : ℝ → E) (s t : ℝ) : E :=
  fam2ST e ζ' s t
    + chrB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2T w e ζ' s t) (fam2S η ζ s t)

/-- `D_t S = ∂_tS + Γ(S,T)` in coordinates. -/
def fam2DtS (x₀ : M) (u η ζ w e ζ' : ℝ → E) (s t : ℝ) : E :=
  fam2ST e ζ' s t
    + chrB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t) (fam2S η ζ s t) (fam2T w e ζ' s t)

/-- `D_sD_sT` in coordinates. -/
def fam2DsDsT (x₀ : M) (u η ζ w e ζ' : ℝ → E) (s t : ℝ) : E :=
  fam2DsTderiv (cov := cov) x₀ u η ζ w e ζ' s t
    + chrB cov x₀ (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2S η ζ s t)

/-- The coordinate expression of the intrinsic acceleration `∇_s∂_sΨ|₀ = ζ + Γ(η,η)`. -/
def fam2A (x₀ : M) (u η ζ : ℝ → E) : ℝ → E := fun t =>
  ζ t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (η t)

/-- `∂_t A` in coordinates. -/
def fam2Aderiv (x₀ : M) (u η ζ w e ζ' : ℝ → E) : ℝ → E := fun t =>
  ζ' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) (η t)
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (e t) (η t)
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (e t)

/-- `D_t A = ∂_t A + Γ(A, w)` in coordinates (`A = ζ + Γ(η,η)`). -/
def fam2DtA (x₀ : M) (u η ζ w e ζ' : ℝ → E) : ℝ → E := fun t =>
  fam2Aderiv (cov := cov) x₀ u η ζ w e ζ' t
    + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (fam2A (cov := cov) x₀ u η ζ t) (w t)


/-! ## Pointwise derivatives of the family -/

lemma hasDerivAt_fam2_s (u η ζ : ℝ → E) (s t : ℝ) :
    HasDerivAt (fun σ : ℝ => fam2 u η ζ σ t) (fam2S η ζ s t) s := by
  have h1 : HasDerivAt (fun σ : ℝ => σ • η t) (η t) s := by
    simpa using (hasDerivAt_id s).smul_const (η t)
  have h2 : HasDerivAt (fun σ : ℝ => (σ ^ 2 / 2) • ζ t) (s • ζ t) s := by
    have h3 : HasDerivAt (fun σ : ℝ => σ ^ 2 / 2) s s := by
      have h := (hasDerivAt_pow 2 s).div_const 2
      have hv : ((2 : ℕ) : ℝ) * s ^ (2 - 1) / 2 = s := by
        rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one]; ring
      rwa [hv] at h
    exact h3.smul_const (ζ t)
  have h4 : HasDerivAt (fun σ : ℝ => u t + σ • η t + (σ ^ 2 / 2) • ζ t) (η t + s • ζ t) s := by
    have h' := ((hasDerivAt_const (x := s) (c := u t)).add h1).add h2
    have hfun : (((fun _ : ℝ => u t) + fun σ : ℝ => σ • η t)
        + fun σ : ℝ => (σ ^ 2 / 2) • ζ t)
        = fun σ : ℝ => u t + σ • η t + (σ ^ 2 / 2) • ζ t := by
      funext σ; rfl
    rw [hfun] at h'
    simpa only [zero_add] using h'
  simpa only [fam2, fam2S] using h4

lemma hasDerivAt_fam2S_s (η ζ : ℝ → E) (s t : ℝ) :
    HasDerivAt (fun σ : ℝ => fam2S η ζ σ t) (ζ t) s := by
  have h1 : HasDerivAt (fun σ : ℝ => σ • ζ t) (ζ t) s := by
    simpa using (hasDerivAt_id s).smul_const (ζ t)
  have h2 : HasDerivAt (fun σ : ℝ => η t + σ • ζ t) (ζ t) s := by
    have h' := (hasDerivAt_const (x := s) (c := η t)).add h1
    have hfun : ((fun _ : ℝ => η t) + fun σ : ℝ => σ • ζ t) = fun σ : ℝ => η t + σ • ζ t := by
      funext σ; rfl
    rw [hfun] at h'
    simpa using h'
  simpa only [fam2S] using h2

lemma hasDerivAt_fam2S_t {η ζ e ζ' : ℝ → E} {s t : ℝ}
    (hη : HasDerivAt η (e t) t) (hζ : HasDerivAt ζ (ζ' t) t) :
    HasDerivAt (fun τ : ℝ => fam2S η ζ s τ) (fam2ST e ζ' s t) t := by
  have h1 : HasDerivAt (fun τ : ℝ => s • ζ τ) (s • ζ' t) t := hζ.const_smul s
  have h2 : HasDerivAt (fun τ : ℝ => η τ + s • ζ τ) (e t + s • ζ' t) t := hη.add h1
  simpa only [fam2S, fam2ST] using h2

lemma hasDerivAt_fam2T_s (w e ζ' : ℝ → E) (s t : ℝ) :
    HasDerivAt (fun σ : ℝ => fam2T w e ζ' σ t) (fam2ST e ζ' s t) s := by
  have h1 : HasDerivAt (fun σ : ℝ => σ • e t) (e t) s := by
    simpa using (hasDerivAt_id s).smul_const (e t)
  have h2 : HasDerivAt (fun σ : ℝ => (σ ^ 2 / 2) • ζ' t) (s • ζ' t) s := by
    have h3 : HasDerivAt (fun σ : ℝ => σ ^ 2 / 2) s s := by
      have h := (hasDerivAt_pow 2 s).div_const 2
      have hv : ((2 : ℕ) : ℝ) * s ^ (2 - 1) / 2 = s := by
        rw [show (2 - 1 : ℕ) = 1 by norm_num, pow_one]; ring
      rwa [hv] at h
    exact h3.smul_const (ζ' t)
  have h4 : HasDerivAt (fun σ : ℝ => w t + σ • e t + (σ ^ 2 / 2) • ζ' t)
      (e t + s • ζ' t) s := by
    have h' := ((hasDerivAt_const (x := s) (c := w t)).add h1).add h2
    have hfun : (((fun _ : ℝ => w t) + fun σ : ℝ => σ • e t)
        + fun σ : ℝ => (σ ^ 2 / 2) • ζ' t)
        = fun σ : ℝ => w t + σ • e t + (σ ^ 2 / 2) • ζ' t := by
      funext σ; rfl
    rw [hfun] at h'
    simpa using h'
  simpa only [fam2T, fam2ST] using h4

lemma hasDerivAt_fam2T_t {w e ζ' w' e' ζ'' : ℝ → E} {s t : ℝ}
    (hw : HasDerivAt w (w' t) t) (he : HasDerivAt e (e' t) t)
    (hζ' : HasDerivAt ζ' (ζ'' t) t) :
    HasDerivAt (fun τ : ℝ => fam2T w e ζ' s τ) (w' t + s • e' t + (s ^ 2 / 2) • ζ'' t) t := by
  have h1 : HasDerivAt (fun τ : ℝ => s • e τ) (s • e' t) t := he.const_smul s
  have h2 : HasDerivAt (fun τ : ℝ => (s ^ 2 / 2) • ζ' τ) ((s ^ 2 / 2) • ζ'' t) t :=
    hζ'.const_smul (s ^ 2 / 2)
  have h' := ((hw.add h1).add h2)
  have hfun : ((w + fun τ : ℝ => s • e τ) + fun τ : ℝ => (s ^ 2 / 2) • ζ' τ)
      = fun τ : ℝ => w τ + s • e τ + (s ^ 2 / 2) • ζ' τ := by
    funext τ; rfl
  rw [hfun] at h'
  exact h'

lemma hasDerivAt_fam2ST_s (e ζ' : ℝ → E) (s t : ℝ) :
    HasDerivAt (fun σ : ℝ => fam2ST e ζ' σ t) (ζ' t) s := by
  have h1 : HasDerivAt (fun σ : ℝ => σ • ζ' t) (ζ' t) s := by
    simpa using (hasDerivAt_id s).smul_const (ζ' t)
  have h2 : HasDerivAt (fun σ : ℝ => e t + σ • ζ' t) (ζ' t) s := by
    have h' := (hasDerivAt_const (x := s) (c := e t)).add h1
    have hfun : ((fun _ : ℝ => e t) + fun σ : ℝ => σ • ζ' t) = fun σ : ℝ => e t + σ • ζ' t := by
      funext σ; rfl
    rw [hfun] at h'
    simpa using h'
  simpa only [fam2ST] using h2

/-- **The `s`-derivative of `D_sT`** (the chain rule for the Christoffel symbol). -/
lemma hasDerivAt_fam2DsT_s [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η ζ w e ζ' : ℝ → E} {s t : ℝ}
    (htgt : fam2 u η ζ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, fam2 u η ζ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ : ℝ => fam2DsT (cov := cov) x₀ u η ζ w e ζ' σ t)
      (fam2DsTderiv (cov := cov) x₀ u η ζ w e ζ' s t) s := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀)
    (u := fun σ : ℝ => fam2 u η ζ σ t) (a := fun σ : ℝ => fam2T w e ζ' σ t)
    (b := fun σ : ℝ => fam2S η ζ σ t) (v := fam2S η ζ s t)
    (a' := fam2ST e ζ' s t) (b' := ζ t)
    (hasDerivAt_fam2_s u η ζ s t) (hasDerivAt_fam2T_s w e ζ' s t)
    (hasDerivAt_fam2S_s η ζ s t) htgt hstay
  have h' := (hasDerivAt_fam2ST_s e ζ' s t).add h
  have hfun : ((fun σ : ℝ => fam2ST e ζ' σ t)
      + fun σ : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (fam2 u η ζ σ t)) (fam2T w e ζ' σ t)
          (fam2S η ζ σ t))
      = fun σ : ℝ => fam2DsT (cov := cov) x₀ u η ζ w e ζ' σ t := by
    funext σ; rfl
  refine (h'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv ?_
  simp only [fam2DsTderiv, Pi.add_apply]
  abel


/-! ## Joint continuity of the family -/

lemma continuousOn_fam2_prod {u η ζ : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B) :
    ContinuousOn (fun q : ℝ × ℝ => fam2 u η ζ q.1 q.2) (A ×ˢ B) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => u q.2) (A ×ˢ B) :=
    hu.comp' continuousOn_snd (fun q hq => hq.2)
  have h2 : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => ζ q.2) (A ×ˢ B) :=
    hζ.comp' continuousOn_snd (fun q hq => hq.2)
  have h4 : ContinuousOn (fun q : ℝ × ℝ => q.1 • η q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h2
  have h5 : ContinuousOn (fun q : ℝ × ℝ => (q.1 ^ 2 / 2) • ζ q.2) (A ×ˢ B) :=
    (((continuousOn_fst.pow 2).div_const 2)).smul h3
  refine ((h1.add h4).add h5).congr (fun q hq => ?_)
  simp only [fam2, Pi.add_apply]

lemma continuousOn_fam2S_prod {η ζ : ℝ → E} {A B : Set ℝ}
    (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B) :
    ContinuousOn (fun q : ℝ × ℝ => fam2S η ζ q.1 q.2) (A ×ˢ B) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ => η q.2) (A ×ˢ B) :=
    hη.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => ζ q.2) (A ×ˢ B) :=
    hζ.comp' continuousOn_snd (fun q hq => hq.2)
  have h4 : ContinuousOn (fun q : ℝ × ℝ => q.1 • ζ q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h3
  refine (h2.add h4).congr (fun q hq => ?_)
  simp only [fam2S, Pi.add_apply, Pi.smul_apply]

lemma continuousOn_fam2T_prod {w e ζ' : ℝ → E} {A B : Set ℝ}
    (hw : ContinuousOn w B) (he : ContinuousOn e B) (hζ' : ContinuousOn ζ' B) :
    ContinuousOn (fun q : ℝ × ℝ => fam2T w e ζ' q.1 q.2) (A ×ˢ B) := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => w q.2) (A ×ˢ B) :=
    hw.comp' continuousOn_snd (fun q hq => hq.2)
  have h2 : ContinuousOn (fun q : ℝ × ℝ => e q.2) (A ×ˢ B) :=
    he.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => ζ' q.2) (A ×ˢ B) :=
    hζ'.comp' continuousOn_snd (fun q hq => hq.2)
  have h4 : ContinuousOn (fun q : ℝ × ℝ => q.1 • e q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h2
  have h5 : ContinuousOn (fun q : ℝ × ℝ => (q.1 ^ 2 / 2) • ζ' q.2) (A ×ˢ B) :=
    (((continuousOn_fst.pow 2).div_const 2)).smul h3
  refine ((h1.add h4).add h5).congr (fun q hq => ?_)
  simp only [fam2T, Pi.add_apply]

lemma continuousOn_fam2ST_prod {e ζ' : ℝ → E} {A B : Set ℝ}
    (he : ContinuousOn e B) (hζ' : ContinuousOn ζ' B) :
    ContinuousOn (fun q : ℝ × ℝ => fam2ST e ζ' q.1 q.2) (A ×ˢ B) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ => e q.2) (A ×ˢ B) :=
    he.comp' continuousOn_snd (fun q hq => hq.2)
  have h3 : ContinuousOn (fun q : ℝ × ℝ => ζ' q.2) (A ×ˢ B) :=
    hζ'.comp' continuousOn_snd (fun q hq => hq.2)
  have h4 : ContinuousOn (fun q : ℝ × ℝ => q.1 • ζ' q.2) (A ×ˢ B) :=
    continuousOn_fst.smul h3
  refine (h2.add h4).congr (fun q hq => ?_)
  simp only [fam2ST, Pi.add_apply]

lemma continuousOn_fam2Curve_prod {x₀ : M} {u η ζ : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B)
    (hmem : ∀ q ∈ A ×ˢ B, fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun q : ℝ × ℝ => fam2Curve (I := I) x₀ u η ζ q.1 q.2) (A ×ˢ B) :=
  (contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).continuousOn.comp'
    (continuousOn_fam2_prod hu hη hζ) hmem

lemma continuousOn_fam2DsT_prod [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u η ζ w e ζ' : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B)
    (hw : ContinuousOn w B) (he : ContinuousOn e B) (hζ' : ContinuousOn ζ' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B, fam2Curve (I := I) x₀ u η ζ q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => fam2DsT (cov := cov) x₀ u η ζ w e ζ' q.1 q.2) (A ×ˢ B) := by
  have hc := continuousOn_fam2Curve_prod (x₀ := x₀) hu hη hζ hmem
  have hS := continuousOn_fam2S_prod (A := A) (B := B) hη hζ
  have hT := continuousOn_fam2T_prod (A := A) (B := B) hw he hζ'
  have hST := continuousOn_fam2ST_prod (A := A) (B := B) he hζ'
  refine ((hST.add (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hT hS hmsrc))).congr
    (fun q hq => ?_)
  simp only [fam2DsT, Pi.add_apply]

lemma continuousOn_fam2DsTderiv_prod [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u η ζ w e ζ' : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B)
    (hw : ContinuousOn w B) (he : ContinuousOn e B) (hζ' : ContinuousOn ζ' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B, fam2Curve (I := I) x₀ u η ζ q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => fam2DsTderiv (cov := cov) x₀ u η ζ w e ζ' q.1 q.2)
      (A ×ˢ B) := by
  have hc := continuousOn_fam2Curve_prod (x₀ := x₀) hu hη hζ hmem
  have hS := continuousOn_fam2S_prod (A := A) (B := B) hη hζ
  have hT := continuousOn_fam2T_prod (A := A) (B := B) hw he hζ'
  have hST := continuousOn_fam2ST_prod (A := A) (B := B) he hζ'
  have hζc : ContinuousOn (fun q : ℝ × ℝ => ζ q.2) (A ×ˢ B) :=
    hζ.comp' continuousOn_snd (fun q hq => hq.2)
  have hζ'c : ContinuousOn (fun q : ℝ × ℝ => ζ' q.2) (A ×ˢ B) :=
    hζ'.comp' continuousOn_snd (fun q hq => hq.2)
  refine ((hζ'c.add ((continuousOn_dB_comp (cov := cov) (x₀ := x₀) hc hS hT hS hmsrc).add
    ((continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hST hS hmsrc).add
      (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hT hζc hmsrc))))).congr
    (fun q hq => ?_)
  simp only [fam2DsTderiv, Pi.add_apply]
  abel



/-! ## Pointwise derivatives of the energy integrand -/

/-- The `s`-derivative of the integrand `⟪T, T⟫` of the energy is `2 ⟪D_sT, T⟫`. -/
lemma hasDerivAt_famG2_s (hmet : IsMetricCompatible cov) (x₀ : M) {u η ζ w e ζ' : ℝ → E}
    {s t : ℝ}
    (htgt : fam2 u η ζ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, fam2 u η ζ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ : ℝ => chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ σ t)
        (fam2T w e ζ' σ t) (fam2T w e ζ' σ t))
      (2 * chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)) s := by
  have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
    (u := fun σ : ℝ => fam2 u η ζ σ t) (v := fam2S η ζ s t) (t := s)
    (hasDerivAt_fam2_s u η ζ s t) htgt hstay
    (h₁ := fun σ : ℝ => fam2T w e ζ' σ t) (h₂ := fun σ : ℝ => fam2T w e ζ' σ t)
    (h₁' := fam2ST e ζ' s t) (h₂' := fam2ST e ζ' s t)
    (hasDerivAt_fam2T_s w e ζ' s t) (hasDerivAt_fam2T_s w e ζ' s t)
  refine h.congr_deriv ?_
  simp only [fam2Curve]
  have hD : fam2ST e ζ' s t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t)) (fam2T w e ζ' s t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t)) (fam2S η ζ s t))
      = fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t := by
    simp only [fam2DsT, fam2Curve, chrB_apply]
  rw [hD, chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t))
      (fam2T w e ζ' s t) (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t), two_mul]

/-- The `s`-derivative of `⟪D_sT, T⟫`. -/
lemma hasDerivAt_fam2DsT_pair [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    (x₀ : M) {u η ζ w e ζ' : ℝ → E} {s t : ℝ}
    (htgt : fam2 u η ζ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, fam2 u η ζ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ : ℝ => chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ σ t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' σ t) (fam2T w e ζ' σ t))
      (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
          (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)
        + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)) s := by
  have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
    (u := fun σ : ℝ => fam2 u η ζ σ t) (v := fam2S η ζ s t) (t := s)
    (hasDerivAt_fam2_s u η ζ s t) htgt hstay
    (h₁ := fun σ : ℝ => fam2DsT (cov := cov) x₀ u η ζ w e ζ' σ t)
    (h₂ := fun σ : ℝ => fam2T w e ζ' σ t)
    (h₁' := fam2DsTderiv (cov := cov) x₀ u η ζ w e ζ' s t) (h₂' := fam2ST e ζ' s t)
    (hasDerivAt_fam2DsT_s (cov := cov) htgt hstay) (hasDerivAt_fam2T_s w e ζ' s t)
  refine h.congr_deriv ?_
  simp only [fam2Curve]
  have hD1 : fam2DsTderiv (cov := cov) x₀ u η ζ w e ζ' s t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t))
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t)) (fam2S η ζ s t))
      = fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s t := by
    simp only [fam2DsDsT, fam2DsT, fam2DsTderiv, fam2Curve, chrB_apply]
  have hD2 : fam2ST e ζ' s t
      + christoffelEval cov x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t)) (fam2T w e ζ' s t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (fam2 u η ζ s t)) (fam2S η ζ s t))
      = fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t := by
    simp only [fam2DsT, fam2Curve, chrB_apply]
  rw [hD1, hD2]

lemma continuousOn_fam2DsDsT_prod [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u η ζ w e ζ' : ℝ → E} {A B : Set ℝ}
    (hu : ContinuousOn u B) (hη : ContinuousOn η B) (hζ : ContinuousOn ζ B)
    (hw : ContinuousOn w B) (he : ContinuousOn e B) (hζ' : ContinuousOn ζ' B)
    (hmem : ∀ q ∈ A ×ˢ B, fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target)
    (hmsrc : ∀ q ∈ A ×ˢ B, fam2Curve (I := I) x₀ u η ζ q.1 q.2 ∈ (chartAt H x₀).source) :
    ContinuousOn (fun q : ℝ × ℝ => fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' q.1 q.2)
      (A ×ˢ B) := by
  have hc := continuousOn_fam2Curve_prod (x₀ := x₀) hu hη hζ hmem
  have hS := continuousOn_fam2S_prod (A := A) (B := B) hη hζ
  have hD := continuousOn_fam2DsT_prod (cov := cov) (x₀ := x₀) hu hη hζ hw he hζ' hmem hmsrc
  have hD' := continuousOn_fam2DsTderiv_prod (cov := cov) (x₀ := x₀) hu hη hζ hw he hζ' hmem hmsrc
  refine (hD'.add (continuousOn_chrB_comp (cov := cov) (x₀ := x₀) hc hD hS hmsrc)).congr
    (fun q hq => ?_)
  simp only [fam2DsDsT, Pi.add_apply]

/-! ## Differentiation of the energy -/

/-- **The first derivative of the energy** of the quadratic family, at an interior parameter. -/
theorem fam2Energy_hasDerivAt [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {u η ζ w e ζ' w' : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    {a₁ a₂ δ₁ δ₂ s₀ : ℝ} (ha₁ : a₁ < δ₁) (ha₂ : δ₂ < a₂) (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (hζ : ∀ t ∈ Icc 0 L, HasDerivAt ζ (ζ' t) t)
    (heC : ContinuousOn e (Icc 0 L)) (hζ'C : ContinuousOn ζ' (Icc 0 L))
    {A₀ B₀ : ℝ} (hA₀ : A₀ ≤ 0) (hB₀ : L ≤ B₀)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀, fam2 u η ζ s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => fam2Energy (I := I) x₀ u η ζ w e ζ' L s)
      (2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t) (fam2T w e ζ' s₀ t)) s₀ := by
  have huC : ContinuousOn u (Icc (0:ℝ) L) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc (0:ℝ) L) := HasDerivAt.continuousOn hw
  have hηC : ContinuousOn η (Icc (0:ℝ) L) := HasDerivAt.continuousOn hη
  have hζC : ContinuousOn ζ (Icc (0:ℝ) L) := HasDerivAt.continuousOn hζ
  have hsub : Icc (0:ℝ) L ⊆ Icc A₀ B₀ := Icc_subset_Icc hA₀ hB₀
  have hsub2 : Icc δ₁ δ₂ ⊆ Icc a₁ a₂ := Icc_subset_Icc ha₁.le ha₂.le
  have hmemR : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L,
      fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target :=
    fun q hq => hstay q.1 (hsub2 hq.1) q.2 (hsub hq.2)
  have hsrcR : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L,
      fam2Curve (I := I) x₀ u η ζ q.1 q.2 ∈ (chartAt H x₀).source :=
    fun q hq => mem_source_chartCurve (I := I) (hmemR q hq)
  -- joint continuity of the integrand and of its derivative
  have hF : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ p.1 p.2) (fam2T w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2))
      (Icc δ₁ δ₂ ×ˢ uIcc (0:ℝ) L) := by
    rw [uIcc_of_le hL]
    exact continuousOn_chartGram_comp (x₀ := x₀)
      (continuousOn_fam2Curve_prod (x₀ := x₀) huC hηC hζC hmemR)
      (continuousOn_fam2T_prod (A := Icc δ₁ δ₂) (B := Icc (0:ℝ) L) hwC heC hζ'C)
      (continuousOn_fam2T_prod (A := Icc δ₁ δ₂) (B := Icc (0:ℝ) L) hwC heC hζ'C) hsrcR
  have hF' : ContinuousOn (fun p : ℝ × ℝ => 2 * chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2))
      (Icc δ₁ δ₂ ×ˢ uIcc (0:ℝ) L) := by
    rw [uIcc_of_le hL]
    exact continuousOn_const.mul (continuousOn_chartGram_comp (x₀ := x₀)
      (continuousOn_fam2Curve_prod (x₀ := x₀) huC hηC hζC hmemR)
      (continuousOn_fam2DsT_prod (cov := cov) (x₀ := x₀) huC hηC hζC hwC heC hζ'C hmemR hsrcR)
      (continuousOn_fam2T_prod (A := Icc δ₁ δ₂) (B := Icc (0:ℝ) L) hwC heC hζ'C) hsrcR)
  -- the pointwise derivative
  have hd : ∀ s ∈ Icc δ₁ δ₂, ∀ t ∈ uIcc (0:ℝ) L,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ r t)
        (fam2T w e ζ' r t) (fam2T w e ζ' r t))
        (2 * chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)) s := by
    intro s hs t ht
    rw [uIcc_of_le hL] at ht
    have hs' : a₁ < s := lt_of_lt_of_le ha₁ hs.1
    have hs'' : s < a₂ := lt_of_le_of_lt hs.2 ha₂
    refine hasDerivAt_famG2_s (cov := cov) hmet x₀ (hmemR ⟨s, t⟩ ⟨hs, ht⟩) ?_
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hs', hs''⟩)
      (fun r hr => hstay r ⟨le_of_lt hr.1, le_of_lt hr.2⟩ t (hsub ht))
  have hmain := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc
    (F := fun s t => chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2T w e ζ' s t) (fam2T w e ζ' s t))
    (F' := fun s t => 2 * chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t))
    (a := 0) (b := L) h₁ h₂ hF hF' hd
  rw [intervalIntegral.integral_const_mul] at hmain
  simpa only [fam2Energy] using hmain

/-- **The second derivative of the energy** of the quadratic family, at an interior parameter. -/
theorem fam2Energy_deriv_second [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {u η ζ w e ζ' w' : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    {a₁ a₂ δ₁ δ₂ s₀ : ℝ} (ha₁ : a₁ < δ₁) (ha₂ : δ₂ < a₂) (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (hζ : ∀ t ∈ Icc 0 L, HasDerivAt ζ (ζ' t) t)
    (heC : ContinuousOn e (Icc 0 L)) (hζ'C : ContinuousOn ζ' (Icc 0 L))
    {A₀ B₀ : ℝ} (hA₀ : A₀ ≤ 0) (hB₀ : L ≤ B₀)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀, fam2 u η ζ s t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => 2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t))
      (2 * ∫ t in (0:ℝ)..L, (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
          (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s₀ t) (fam2T w e ζ' s₀ t)
        + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t))) s₀ := by
  have huC : ContinuousOn u (Icc (0:ℝ) L) := HasDerivAt.continuousOn hu
  have hwC : ContinuousOn w (Icc (0:ℝ) L) := HasDerivAt.continuousOn hw
  have hηC : ContinuousOn η (Icc (0:ℝ) L) := HasDerivAt.continuousOn hη
  have hζC : ContinuousOn ζ (Icc (0:ℝ) L) := HasDerivAt.continuousOn hζ
  have hsub : Icc (0:ℝ) L ⊆ Icc A₀ B₀ := Icc_subset_Icc hA₀ hB₀
  have hsub2 : Icc δ₁ δ₂ ⊆ Icc a₁ a₂ := Icc_subset_Icc ha₁.le ha₂.le
  have hmemR : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L,
      fam2 u η ζ q.1 q.2 ∈ (extChartAt I x₀).target :=
    fun q hq => hstay q.1 (hsub2 hq.1) q.2 (hsub hq.2)
  have hsrcR : ∀ q ∈ Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L,
      fam2Curve (I := I) x₀ u η ζ q.1 q.2 ∈ (chartAt H x₀).source :=
    fun q hq => mem_source_chartCurve (I := I) (hmemR q hq)
  -- joint continuity of the integrand and of its derivative
  have hF0 : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2))
      (Icc δ₁ δ₂ ×ˢ uIcc (0:ℝ) L) := by
    rw [uIcc_of_le hL]
    exact continuousOn_chartGram_comp (x₀ := x₀)
      (continuousOn_fam2Curve_prod (x₀ := x₀) huC hηC hζC hmemR)
      (continuousOn_fam2DsT_prod (cov := cov) (x₀ := x₀) huC hηC hζC hwC heC hζ'C hmemR hsrcR)
      (continuousOn_fam2T_prod (A := Icc δ₁ δ₂) (B := Icc (0:ℝ) L) hwC heC hζ'C) hsrcR
  have hF : ContinuousOn (fun p : ℝ × ℝ => 2 * chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2))
      (Icc δ₁ δ₂ ×ˢ uIcc (0:ℝ) L) := continuousOn_const.mul hF0
  have hF' : ContinuousOn (fun p : ℝ × ℝ => 2 * (chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
      (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2)
      + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2)))
      (Icc δ₁ δ₂ ×ˢ uIcc (0:ℝ) L) := by
    rw [uIcc_of_le hL]
    have h1 : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
        (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2) (fam2T w e ζ' p.1 p.2))
        (Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L) :=
      continuousOn_chartGram_comp (x₀ := x₀)
        (continuousOn_fam2Curve_prod (x₀ := x₀) huC hηC hζC hmemR)
        (continuousOn_fam2DsDsT_prod (cov := cov) (x₀ := x₀) huC hηC hζC hwC heC hζ'C hmemR hsrcR)
        (continuousOn_fam2T_prod (A := Icc δ₁ δ₂) (B := Icc (0:ℝ) L) hwC heC hζ'C) hsrcR
    have h2 : ContinuousOn (fun p : ℝ × ℝ => chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ p.1 p.2)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' p.1 p.2))
        (Icc δ₁ δ₂ ×ˢ Icc (0:ℝ) L) :=
      continuousOn_chartGram_comp (x₀ := x₀)
        (continuousOn_fam2Curve_prod (x₀ := x₀) huC hηC hζC hmemR)
        (continuousOn_fam2DsT_prod (cov := cov) (x₀ := x₀) huC hηC hζC hwC heC hζ'C hmemR hsrcR)
        (continuousOn_fam2DsT_prod (cov := cov) (x₀ := x₀) huC hηC hζC hwC heC hζ'C hmemR hsrcR)
        hsrcR
    exact continuousOn_const.mul (h1.add h2)
  -- the pointwise derivative
  have hd : ∀ s ∈ Icc δ₁ δ₂, ∀ t ∈ uIcc (0:ℝ) L,
      HasDerivAt (fun r : ℝ => 2 * chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ r t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' r t) (fam2T w e ζ' r t))
        (2 * (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
            (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)
          + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
            (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)
            (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t))) s := by
    intro s hs t ht
    rw [uIcc_of_le hL] at ht
    have hs' : a₁ < s := lt_of_lt_of_le ha₁ hs.1
    have hs'' : s < a₂ := lt_of_le_of_lt hs.2 ha₂
    have hpair := hasDerivAt_fam2DsT_pair (cov := cov) hmet x₀
      (u := u) (η := η) (ζ := ζ) (w := w) (e := e) (ζ' := ζ')
      (hmemR ⟨s, t⟩ ⟨hs, ht⟩) ?_
    · exact hpair.const_mul 2
    · exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hs', hs''⟩)
        (fun r hr => hstay r ⟨le_of_lt hr.1, le_of_lt hr.2⟩ t (hsub ht))
  have hmain := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_uIcc
    (F := fun s t => 2 * chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t))
    (F' := fun s t => 2 * (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)
      + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t)))
    (a := 0) (b := L) h₁ h₂ hF hF' hd
  have hfun : (fun s : ℝ => 2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀
      (fam2Curve (I := I) x₀ u η ζ s t)
      (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t))
      = (fun s : ℝ => ∫ t in (0:ℝ)..L, 2 * chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)) := by
    funext s
    rw [intervalIntegral.integral_const_mul]
  have hval : (2 : ℝ) * ∫ t in (0:ℝ)..L, (chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ s₀ t)
        (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s₀ t) (fam2T w e ζ' s₀ t)
      + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t))
      = ∫ t in (0:ℝ)..L, 2 * (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
          (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' s₀ t) (fam2T w e ζ' s₀ t)
        + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s₀ t)
            (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t)
            (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s₀ t)) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hfun, hval]
  exact hmain

/-! ## The auxiliary identities -/

/-- The `t`-derivative of `A = ζ + Γ(η,η)`. -/
lemma hasDerivAt_fam2A [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u η ζ w e ζ' : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hη : HasDerivAt η (e t) t) (hζ : HasDerivAt ζ (ζ' t) t)
    (htgt : u t ∈ (extChartAt I x₀).target) (hstay : ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target) :
    HasDerivAt (fam2A (cov := cov) x₀ u η ζ) (fam2Aderiv (cov := cov) x₀ u η ζ w e ζ' t) t := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := u) (a := η) (b := η)
    (v := w t) (a' := e t) (b' := e t) hu hη hη htgt hstay
  have h' := hζ.add h
  have hfun : ((ζ + fun r : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u r)) (η r) (η r)))
      = fam2A (cov := cov) x₀ u η ζ := by
    funext r; rfl
  rw [hfun] at h'
  refine h'.congr_deriv ?_
  simp only [fam2Aderiv]
  abel


/-- **The derivative of the Christoffel symbol in the base point is symmetric in its last two
arguments** (because the Christoffel symbol itself is, by torsion-freeness). -/
lemma dB_comm_snd [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (v a b : E) :
    dB cov x₀ p v a b = dB cov x₀ p v b a := by
  have h : (fun q : M => chrB cov x₀ q a b) =ᶠ[𝓝 p] (fun q : M => chrB cov x₀ q b a) := by
    filter_upwards [((chartAt H x₀).open_source).mem_nhds hp] with q hq
    exact chrB_comm (cov := cov) htor hq a b
  show mvfderiv I (fun q : M => chrB cov x₀ q a b) p (frameVector (I := I) x₀ p v)
    = mvfderiv I (fun q : M => chrB cov x₀ q b a) p (frameVector (I := I) x₀ p v)
  rw [mvfderiv_congr_of_eventuallyEq (I := I) h]

/-- **Clairaut's identity for the quadratic family**: `D_sT = D_tS` (the symmetry of the
Christoffel symbol and `∂_sT = ∂_tS`). -/
lemma fam2DsT_eq_fam2DtS (htor : cov.torsion = 0) {x₀ : M} {u η ζ w e ζ' : ℝ → E} {s t : ℝ}
    (hsrc : (extChartAt I x₀).symm (fam2 u η ζ s t) ∈ (chartAt H x₀).source) :
    fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t
      = fam2DtS (cov := cov) x₀ u η ζ w e ζ' s t := by
  simp only [fam2DsT, fam2DtS, fam2Curve]
  rw [chrB_comm (cov := cov) htor hsrc (fam2T w e ζ' s t) (fam2S η ζ s t)]

/-- **The Ricci identity for the quadratic family**, in coordinates:
`D_sD_sT|_{s=0} = D_tA + R(η,w)η`. -/
lemma fam2_ricci [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u η ζ w e ζ' : ℝ → E} {t : ℝ}
    (hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source) :
    fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t
      = fam2DtA (cov := cov) x₀ u η ζ w e ζ' t
        + (dB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (η t) (w t)
            - dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) (η t)
            + chrB cov x₀ ((extChartAt I x₀).symm (u t))
                (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (w t)) (η t)
            - chrB cov x₀ ((extChartAt I x₀).symm (u t))
                (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (η t)) (w t)) := by
  simp only [fam2DsDsT, fam2DsTderiv, fam2DsT, fam2DtA, fam2Aderiv, fam2A, fam2S, fam2T, fam2ST,
    fam2Curve, fam2, pow_two, zero_mul, zero_smul, add_zero, zero_add, mul_zero, zero_div]
  rw [chrB_add_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (e t)
        (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t)) (η t) hsrc,
    chrB_add_fst (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (ζ t)
        (chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (η t)) (w t) hsrc]
  rw [chrB_comm (cov := cov) htor hsrc (w t) (η t)]
  rw [chrB_comm (cov := cov) htor hsrc (w t) (ζ t)]
  rw [chrB_comm (cov := cov) htor hsrc (η t) (e t)]
  rw [dB_comm_snd (cov := cov) htor hsrc (η t) (η t) (w t)]
  abel



lemma continuousOn_fam2A_curve [ContMDiffCovariantDerivative cov ∞] {x₀ : M} {u η ζ : ℝ → E} {L : ℝ}
    (hu : ContinuousOn u (Icc (0:ℝ) L)) (hη : ContinuousOn η (Icc (0:ℝ) L))
    (hζ : ContinuousOn ζ (Icc (0:ℝ) L))
    (hmem : ∀ t ∈ Icc (0:ℝ) L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => fam2A (cov := cov) x₀ u η ζ t) (Icc (0:ℝ) L) := by
  have hγ := continuousOn_chartCurve hu hmem
  have hsrc := fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  refine ContinuousOn.congr ((hζ.add (continuousOn_chrB_curve (cov := cov) hγ hη hη hsrc)) :
    ContinuousOn (fun t : ℝ => ζ t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (η t))
      (Icc (0:ℝ) L)) (fun t ht => ?_)
  simp only [fam2A, Pi.add_apply]

lemma continuousOn_fam2DtA_curve [ContMDiffCovariantDerivative cov ∞] {x₀ : M}
    {u η ζ w e ζ' : ℝ → E} {L : ℝ}
    (hu : ContinuousOn u (Icc (0:ℝ) L)) (hη : ContinuousOn η (Icc (0:ℝ) L))
    (hζ : ContinuousOn ζ (Icc (0:ℝ) L)) (hw : ContinuousOn w (Icc (0:ℝ) L))
    (he : ContinuousOn e (Icc (0:ℝ) L)) (hζ' : ContinuousOn ζ' (Icc (0:ℝ) L))
    (hmem : ∀ t ∈ Icc (0:ℝ) L, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (Icc (0:ℝ) L) := by
  have hγ := continuousOn_chartCurve hu hmem
  have hsrc := fun t ht => mem_source_chartCurve (I := I) (hmem t ht)
  have hA := continuousOn_fam2A_curve (cov := cov) hu hη hζ hmem
  have h1 : ContinuousOn (fun t : ℝ =>
      ζ' t + dB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (e t) (η t)
        + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (η t) (e t)) (Icc (0:ℝ) L) := by
    refine ContinuousOn.congr ((hζ'.add ((continuousOn_dB_curve (cov := cov) hγ hw hη hη hsrc).add
        (continuousOn_chrB_curve (cov := cov) hγ he hη hsrc))).add
        (continuousOn_chrB_curve (cov := cov) hγ hη he hsrc)) (fun t ht => ?_)
    simp only [Pi.add_apply, add_assoc]
  have h2 : ContinuousOn (fun t : ℝ => fam2Aderiv (cov := cov) x₀ u η ζ w e ζ' t) (Icc (0:ℝ) L) := by
    refine ContinuousOn.congr h1 (fun t ht => ?_)
    simp only [fam2Aderiv, Pi.add_apply]
  refine ContinuousOn.congr (h2.add (continuousOn_chrB_curve (cov := cov) hγ hA hw hsrc)) (fun t ht => ?_)
  simp only [fam2DtA, Pi.add_apply]

/-- **The fundamental theorem of calculus for `D_tA`.**  Since the velocity is parallel, the
integral of `⟪D_tA, w⟫` is the boundary term `⟪A, w⟫`. -/
lemma integral_fam2DtA [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    {x₀ : M} {u η ζ w e ζ' w' : ℝ → E} {L : ℝ} (hL : 0 ≤ L)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (hζ : ∀ t ∈ Icc 0 L, HasDerivAt ζ (ζ' t) t)
    (heC : ContinuousOn e (Icc 0 L)) (hζ'C : ContinuousOn ζ' (Icc 0 L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    (hstay_u : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    ∫ t in (0:ℝ)..L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u L)) (fam2A (cov := cov) x₀ u η ζ L) (w L)
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (fam2A (cov := cov) x₀ u η ζ 0) (w 0) := by
  have hsrc : ∀ t ∈ Icc (0:ℝ) L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hstay_u t ht)
  have hstayn : ∀ t ∈ Icc (0:ℝ) L, ∀ᶠ r in 𝓝 t, u r ∈ (extChartAt I x₀).target := by
    intro t ht
    exact (hu t ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (hstay_u t ht))
  have hderiv : ∀ t ∈ uIcc (0:ℝ) L,
      HasDerivAt (fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
          (fam2A (cov := cov) x₀ u η ζ s) (w s))
        (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t)) t := by
    intro t ht
    rw [uIcc_of_le hL] at ht
    have hA := hasDerivAt_fam2A (cov := cov) (hu t ht) (hη t ht) (hζ t ht) (hstay_u t ht)
      (hstayn t ht)
    have h := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀ (hu t ht) (hstay_u t ht)
      (hstayn t ht) hA.differentiableAt.hasDerivAt (hw t ht).differentiableAt.hasDerivAt
    refine h.congr_deriv ?_
    rw [chartCovDeriv_apply (I := I) (hstay_u t ht), chartCovDeriv_apply (I := I) (hstay_u t ht),
      hA.deriv, (hw t ht).deriv]
    have h2 : w' t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) = 0 := by
      have hh := hgeo t ht
      rwa [chrB_apply (cov := cov) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)] at hh
    rw [h2, Submission.Gauss.chartGram_zero_snd, add_zero]
    simp only [fam2DtA, chrB_apply]
  have hint : IntervalIntegrable (fun t : ℝ => chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t)) volume 0 L :=
    (continuousOn_chartGram_curve (I := I)
      (continuousOn_chartCurve (HasDerivAt.continuousOn hu) hstay_u)
      (continuousOn_fam2DtA_curve (cov := cov) (HasDerivAt.continuousOn hu)
        (HasDerivAt.continuousOn hη) (HasDerivAt.continuousOn hζ) (HasDerivAt.continuousOn hw)
        heC hζ'C hstay_u)
      (HasDerivAt.continuousOn hw) hsrc).intervalIntegrable_of_Icc hL
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-! ## The second-variation formula -/

/-- **The second derivative of the energy of a quadratic family is the index form.** -/
theorem fam2Energy_second_deriv [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {u η ζ w e ζ' w' : ℝ → E} {L : ℝ} (hL : 0 < L)
    {a₁ a₂ : ℝ} (ha₁ : a₁ < 0) (ha₂ : 0 < a₂)
    (hu : ∀ t ∈ Icc 0 L, HasDerivAt u (w t) t) (hw : ∀ t ∈ Icc 0 L, HasDerivAt w (w' t) t)
    (hη : ∀ t ∈ Icc 0 L, HasDerivAt η (e t) t) (hζ : ∀ t ∈ Icc 0 L, HasDerivAt ζ (ζ' t) t)
    (heC : ContinuousOn e (Icc 0 L)) (hζ'C : ContinuousOn ζ' (Icc 0 L))
    (hgeo : ∀ t ∈ Icc 0 L, w' t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 0)
    {A₀ B₀ : ℝ} (hA₀ : A₀ ≤ 0) (hB₀ : L ≤ B₀)
    (hstay : ∀ s ∈ Icc a₁ a₂, ∀ t ∈ Icc A₀ B₀, fam2 u η ζ s t ∈ (extChartAt I x₀).target)
    (hstay_u : ∀ t ∈ Icc 0 L, u t ∈ (extChartAt I x₀).target) :
    HasDerivAt (deriv (fun s => fam2Energy (I := I) x₀ u η ζ w e ζ' L s))
      (2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u L)) (fam2A (cov := cov) x₀ u η ζ L) (w L)
          - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (fam2A (cov := cov) x₀ u η ζ 0) (w 0))
        - 2 * ∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t) 0 := by
  -- Step 1: the energy is differentiable near `0` with derivative `2 ∫ ⟪D_sT, T⟫`
  have hE1 : ∀ s ∈ Ioo a₁ a₂, HasDerivAt (fun s => fam2Energy (I := I) x₀ u η ζ w e ζ' L s)
      (2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)) s := by
    intro s hs
    have hs1 : a₁ < (a₁ + s) / 2 := by linarith [hs.1]
    have hs2 : (s + a₂) / 2 < a₂ := by linarith [hs.2]
    have hs3 : (a₁ + s) / 2 < s := by linarith [hs.1]
    have hs4 : s < (s + a₂) / 2 := by linarith [hs.2]
    exact fam2Energy_hasDerivAt (cov := cov) hmet x₀ hL.le (δ₁ := (a₁ + s) / 2)
      (δ₂ := (s + a₂) / 2) (s₀ := s) hs1 hs2 hs3 hs4 hu hw hη hζ heC hζ'C hA₀ hB₀ hstay
  have hev : deriv (fun s => fam2Energy (I := I) x₀ u η ζ w e ζ' L s)
      =ᶠ[𝓝 (0:ℝ)] (fun s => 2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t)) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ha₁ ha₂)
      (fun s hs => (hE1 s hs).deriv)
  -- Step 2: differentiate the integral a second time
  have hE2 : HasDerivAt (fun s => 2 * ∫ t in (0:ℝ)..L, chartGram (I := I) x₀
        (fam2Curve (I := I) x₀ u η ζ s t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' s t) (fam2T w e ζ' s t))
      (2 * ∫ t in (0:ℝ)..L, (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
          (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2T w e ζ' 0 t)
        + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t))) 0 := by
    exact fam2Energy_deriv_second (cov := cov) hmet x₀ hL.le (a₁ := a₁) (a₂ := a₂)
      (δ₁ := a₁ / 2) (δ₂ := a₂ / 2) (s₀ := 0) (by linarith) (by linarith)
      (by linarith) (by linarith) hu hw hη hζ heC hζ'C hA₀ hB₀ hstay
  have hcomb : HasDerivAt (deriv (fun s => fam2Energy (I := I) x₀ u η ζ w e ζ' L s))
      (2 * ∫ t in (0:ℝ)..L, (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
          (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2T w e ζ' 0 t)
        + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t)
          (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t))) 0 :=
    hev.hasDerivAt_iff.mpr hE2
  -- Step 3: identify the integrand
  have hbase : ∀ t : ℝ, fam2Curve (I := I) x₀ u η ζ 0 t = (extChartAt I x₀).symm (u t) := by
    intro t
    simp only [fam2Curve, fam2, pow_two, zero_mul, zero_div, zero_smul, add_zero]
  have hT0 : ∀ t : ℝ, fam2T w e ζ' 0 t = w t := by
    intro t
    simp only [fam2T, pow_two, zero_mul, zero_div, zero_smul, add_zero]
  have hDsT0 : ∀ t : ℝ, fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t = DtQ cov x₀ u η w e t := by
    intro t
    simp only [fam2DsT, fam2ST, fam2T, fam2S, DtQ, covDsP, famP, fam2Curve, fam2, fam,
      pow_two, zero_mul, zero_div, zero_smul, add_zero]
  have hpt : ∀ t ∈ Icc (0:ℝ) L, chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2T w e ζ' 0 t)
      + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t)
        + (Gt cov x₀ u η w e t - Rt cov x₀ u η w t) := by
    intro t ht
    have hsrc := mem_source_chartCurve (I := I) (hstay_u t ht)
    have h2nd : chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t)
        = Gt cov x₀ u η w e t := by
      rw [hbase t, hDsT0 t]
      rfl
    have h1st : chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2T w e ζ' 0 t)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t) - Rt cov x₀ u η w t := by
      rw [hbase t, hT0 t, chartGram_apply, chartGram_apply,
        fam2_ricci (cov := cov) htor (u := u) (η := η) (ζ := ζ) (w := w) (e := e) (ζ' := ζ') hsrc,
        frameVector_add,
        ← curvVec_eq_chart (cov := cov) htor (x₀ := x₀) (p := (extChartAt I x₀).symm (u t))
          (η t) (w t) (η t) hsrc,
        inner_add_left]
      congr 1
      rw [inner_curvVec_skew (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› hmet
        ((extChartAt I x₀).symm (u t)) (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (η t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))]
      rfl
    rw [h1st, h2nd]
    ring
  -- integrability of the pieces
  have hγ : ContinuousOn (fun t : ℝ => (extChartAt I x₀).symm (u t)) (Icc (0:ℝ) L) :=
    continuousOn_chartCurve (HasDerivAt.continuousOn hu) hstay_u
  have hsrcC : ∀ t ∈ Icc (0:ℝ) L, (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    fun t ht => mem_source_chartCurve (I := I) (hstay_u t ht)
  have hCint : IntervalIntegrable (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
      (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t)) volume 0 L :=
    (continuousOn_chartGram_curve (I := I) hγ
      (continuousOn_fam2DtA_curve (cov := cov) (HasDerivAt.continuousOn hu)
        (HasDerivAt.continuousOn hη) (HasDerivAt.continuousOn hζ) (HasDerivAt.continuousOn hw)
        heC hζ'C hstay_u)
      (HasDerivAt.continuousOn hw) hsrcC).intervalIntegrable_of_Icc hL.le
  have hDtQC : ContinuousOn (fun t : ℝ => DtQ cov x₀ u η w e t) (Icc (0:ℝ) L) := by
    have h1 : ContinuousOn (fun t : ℝ => e t + chrB cov x₀ ((extChartAt I x₀).symm (u t)) (w t) (η t))
        (Icc (0:ℝ) L) :=
      heC.add (continuousOn_chrB_curve (cov := cov) hγ (HasDerivAt.continuousOn hw)
        (HasDerivAt.continuousOn hη) hsrcC)
    refine ContinuousOn.congr h1 (fun t ht => ?_)
    simp only [DtQ, covDsP, famP, fam, zero_smul, add_zero]
  have hGtint : IntervalIntegrable (fun t : ℝ => Gt cov x₀ u η w e t) volume 0 L := by
    refine ((continuousOn_chartGram_curve (I := I) hγ hDtQC hDtQC hsrcC).intervalIntegrable_of_Icc hL.le)
  have hRtint : IntervalIntegrable (fun t : ℝ => Rt cov x₀ u η w t) volume 0 L :=
    ((continuousOn_Rt (cov := cov) (x₀ := x₀) htor (HasDerivAt.continuousOn hu)
      (HasDerivAt.continuousOn hη) (HasDerivAt.continuousOn hw) hstay_u).intervalIntegrable_of_Icc hL.le)
  have hDint : IntervalIntegrable (fun t : ℝ => Gt cov x₀ u η w e t - Rt cov x₀ u η w t)
      volume 0 L := hGtint.sub hRtint
  -- the integral identity
  have hIntEq : (∫ t in (0:ℝ)..L, (chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsDsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2T w e ζ' 0 t)
      + chartGram (I := I) x₀ (fam2Curve (I := I) x₀ u η ζ 0 t)
        (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t) (fam2DsT (cov := cov) x₀ u η ζ w e ζ' 0 t)))
      = (∫ t in (0:ℝ)..L, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (fam2DtA (cov := cov) x₀ u η ζ w e ζ' t) (w t))
        + ∫ t in (0:ℝ)..L, (Gt cov x₀ u η w e t - Rt cov x₀ u η w t) := by
    rw [← intervalIntegral.integral_add hCint hDint]
    exact intervalIntegral.integral_congr (fun t ht => by
      rw [uIcc_of_le hL.le] at ht
      exact hpt t ht)
  have hIntD : (∫ t in (0:ℝ)..L, (Gt cov x₀ u η w e t - Rt cov x₀ u η w t))
      = -∫ t in (0:ℝ)..L, indexIntegrand cov x₀ u η w e t := by
    rw [intervalIntegral.integral_sub hGtint hRtint]
    rw [show indexIntegrand cov x₀ u η w e
        = fun t : ℝ => Rt cov x₀ u η w t - Gt cov x₀ u η w e t from rfl,
      intervalIntegral.integral_sub hRtint hGtint]
    ring
  have hFTC := integral_fam2DtA (cov := cov) hmet hL.le hu hw hη hζ heC hζ'C hgeo hstay_u
  rw [hIntEq, hIntD, hFTC] at hcomb
  convert hcomb using 1
  ring

end
end Submission.SecondVar2