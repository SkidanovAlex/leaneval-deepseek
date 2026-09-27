import Mathlib
import Submission.Work.ManifoldParity.graph_tangent_field

/-!
# A nowhere-vanishing smooth field tangent to a locally-graph compact set

`Work.Drive.TParity.graph_tangent_field`: a compact `K ⊆ ℝⁿ` which is locally the graph of a smooth
`η` over a coordinate axis (`(η t) i = 0`, `y ∈ K ↔ y = (y i) • eᵢ + η (y i)`) admits a smooth
compactly supported `V` with `V x ≠ 0` and `V x` parallel to `eᵢ + η'(x i)(1)` for every local graph
representation at `x`.

The geometric content of the last condition is that `V x` is a non-zero element of the tangent line
`T_x K`, where `T_x K` is the line spanned by `eᵢ + η'(x i)(1)` for *any* local graph representation
at `x`; that the line does not depend on the representation is `tanVec_proportional` below.

This file contains the local (graph) part of the argument; the global existence of the field is
obtained from the companion development `Work.ManifoldParity.graph_tangent_field`
(in `Submission/Work/ManifoldParity/`), which proves the same statement from the
classification of compact `1`-manifolds: `K` is a finite union of circles, carries a
*continuous* nowhere-zero chartwise tangent field (`exists_continuous_tangent_field`), and that
field is smoothed and glued with cut-offs (`graph_tangent_field_of_continuous`).  The target
`Work.Drive.TParity.graph_tangent_field` below is that theorem, restated here.

The same result is also reached, inside this directory, by the four companion lemmas requested
alongside this file:

* `Work.Drive.TParity.exists_finite_parametrization` — `K` is the disjoint union of the images of
  finitely many smooth periodic regular curves `γ k : ℝ → ℝⁿ`;
* `Work.Drive.TParity.exists_chart_pieces` — a finite cover of `K` by graph patches with connected
  traces, each contained in the range of one of the curves;
* `Work.Drive.TParity.sign_deriv_dot_tanVec_const` — the orientation of a chart field relative to a
  parametrisation is constant on a connected chart trace;
* `Work.Drive.TParity.exists_partition_of_unity_subordinate`,
  `Work.Drive.TParity.exists_cutoff_eq_one_on` — the gluing and truncation tools.

Gluing the chart fields `tanVec (i j) (η j)` with the signs of the third item and the partition of
unity of the fourth gives a smooth compactly supported field which is a positive multiple of the
parametrisation derivative on `K`, hence non-zero and tangent; the tangency at an *arbitrary* chart
then follows from `tanVec_proportional` below.
-/

namespace Work.Drive.TParity

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-- The smoothness index `C^∞` (a bare `⊤` means *analytic*). -/
abbrev sm : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {n : ℕ}

/-- The graph curve of a local graph representation: `t ↦ t • eᵢ + η t`. -/
def gcurve (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  t • EuclideanSpace.single i (1 : ℝ) + η t

theorem gcurve_def (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    gcurve i η t = t • EuclideanSpace.single i (1 : ℝ) + η t := rfl

theorem gcurve_fun (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) :
    gcurve i η = fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ) + η t := rfl

/-- The `i`-th coordinate of a graph point is the parameter. -/
theorem gcurve_apply_i {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ∀ t, η t i = 0)
    (t : ℝ) : gcurve i η t i = t := by
  simp [gcurve_def, hη]

theorem contDiff_gcurve {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ContDiff ℝ sm η) :
    ContDiff ℝ sm (gcurve i η) := by
  rw [gcurve_fun]
  exact ((ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff).add hη

theorem continuous_gcurve {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : Continuous η) :
    Continuous (gcurve i η) := by
  rw [gcurve_fun]
  exact (continuous_id.smul continuous_const).add hη

/-- The derivative of the graph curve. -/
theorem hasDerivAt_gcurve {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ContDiff ℝ sm η)
    (t : ℝ) : HasDerivAt (gcurve i η) (EuclideanSpace.single i (1 : ℝ) + deriv η t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) t := by
    simpa using (hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))
  have h2 : HasDerivAt η (deriv η t) t :=
    ((hη.differentiable (by simp)).differentiableAt).hasDerivAt
  rw [gcurve_fun]
  exact h1.add h2

/-- The graph curve is injective. -/
theorem gcurve_injective {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ∀ t, η t i = 0) :
    Function.Injective (gcurve i η) := by
  intro s t hst
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hst
  rwa [gcurve_apply_i hη, gcurve_apply_i hη] at h

/-- The `i`-th coordinate of `fderiv ℝ η (x i) (1 : ℝ)` vanishes when `η` takes its values in the
coordinate hyperplane `{v | v i = 0}`. -/
theorem fderiv_coord_eq_zero {η : ℝ → EuclideanSpace ℝ (Fin n)} {i : Fin n}
    (hη : ContDiff ℝ sm η) (hη0 : ∀ t, η t i = 0) (x : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ η (x i) (1 : ℝ)) i = 0 := by
  have h0 : deriv (fun t : ℝ => η t i) (x i) = 0 := by
    rw [show (fun t : ℝ => η t i) = (fun _ => 0) from funext hη0]; simp
  have hd : HasFDerivAt (fun t : ℝ => η t i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ η (x i))) (x i) := by
    have hh := (EuclideanSpace.proj i).hasFDerivAt.comp (x i)
      (((hη.differentiable (by simp)).differentiableAt).hasFDerivAt)
    simpa [Function.comp_def] using hh
  rw [hd.hasDerivAt.deriv] at h0
  simpa using h0

/-- The tangent vector of a local graph representation of `K` at the point `x`:
`eᵢ + η'(x i)(1)`. -/
def tanVec (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i (1 : ℝ) + fderiv ℝ η (x i) (1 : ℝ)

theorem tanVec_eq (i : Fin n) (η : ℝ → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    tanVec i η x = EuclideanSpace.single i (1 : ℝ) + fderiv ℝ η (x i) (1 : ℝ) := rfl

/-- The tangent vector of a graph representation is non-zero: its `i`-th coordinate is `1`. -/
theorem tanVec_ne_zero {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ContDiff ℝ sm η)
    (hη0 : ∀ t, η t i = 0) (x : EuclideanSpace ℝ (Fin n)) : tanVec i η x ≠ 0 := by
  intro h
  have hcoord0 := fderiv_coord_eq_zero hη hη0 x
  have h1 : (tanVec i η x) i = 1 := by
    rw [tanVec_eq, PiLp.add_apply, PiLp.single_apply, if_pos rfl, hcoord0, add_zero]
  rw [h, PiLp.zero_apply] at h1
  exact one_ne_zero h1.symm

/-- The tangent vector is the derivative of the graph curve at the parameter of `x`. -/
theorem tanVec_eq_deriv {i : Fin n} {η : ℝ → EuclideanSpace ℝ (Fin n)} (hη : ContDiff ℝ sm η)
    (x : EuclideanSpace ℝ (Fin n)) :
    tanVec i η x = deriv (gcurve i η) (x i) := by
  rw [tanVec_eq, (hasDerivAt_gcurve hη (x i)).deriv, fderiv_eq_smul_deriv, one_smul]

/-- **The tangent line is well defined.**  If `(i, U, η)` and `(i', U', η')` are two local graph
representations of `K` at the same point `x ∈ K`, then the corresponding tangent vectors are
proportional with a non-zero factor. -/
theorem tanVec_proportional {K : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hxK : x ∈ K)
    {i i' : Fin n} {U U' : Set (EuclideanSpace ℝ (Fin n))} {η η' : ℝ → EuclideanSpace ℝ (Fin n)}
    (hU : IsOpen U) (hxU : x ∈ U) (hη : ContDiff ℝ sm η) (hηi : ∀ t, η t i = 0)
    (hKU : ∀ y ∈ U, (y ∈ K ↔ y = gcurve i η (y i)))
    (hU' : IsOpen U') (hxU' : x ∈ U') (hη' : ContDiff ℝ sm η')
    (_hηi' : ∀ t, η' t i' = 0)
    (hKU' : ∀ y ∈ U', (y ∈ K ↔ y = gcurve i' η' (y i'))) :
    ∃ c : ℝ, c ≠ 0 ∧ tanVec i η x = c • tanVec i' η' x := by
  set γ : ℝ → EuclideanSpace ℝ (Fin n) := gcurve i η with hγ
  have hγ_smooth : ContDiff ℝ sm γ := contDiff_gcurve hη
  have hxγ : γ (x i) = x := ((hKU x hxU).mp hxK).symm
  -- the reparametrisation `σ`
  set σ : ℝ → ℝ := fun t => (γ t) i' with hσ
  have hσ_smooth : ContDiff ℝ sm σ := by
    have h1 : (fun t : ℝ => (γ t) i')
        = (EuclideanSpace.proj i' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∘ γ := by
      funext t; rfl
    rw [hσ, h1]
    exact (EuclideanSpace.proj i').contDiff.comp hγ_smooth
  -- the graph curve of the first chart is the graph curve of the second, reparametrised
  have hev : γ =ᶠ[𝓝 (x i)] fun t => gcurve i' η' (σ t) := by
    have h1 : ∀ᶠ t in 𝓝 (x i), γ t ∈ U :=
      hγ_smooth.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds (by rw [hxγ]; exact hxU))
    have h2 : ∀ᶠ t in 𝓝 (x i), γ t ∈ U' :=
      hγ_smooth.continuous.continuousAt.preimage_mem_nhds
        (hU'.mem_nhds (by rw [hxγ]; exact hxU'))
    filter_upwards [h1, h2] with t htU htU'
    have htK : γ t ∈ K := by
      rw [hKU (γ t) htU]
      rw [show (γ t) i = t from gcurve_apply_i hηi t]
    rw [hKU' (γ t) htU'] at htK
    simpa [hσ] using htK
  have hderiv_eq : deriv γ (x i) = deriv (fun t => gcurve i' η' (σ t)) (x i) :=
    Filter.EventuallyEq.deriv_eq hev
  have hxσ : σ (x i) = x i' := by
    rw [hσ]; simp only; rw [hxγ]
  have h1 : deriv γ (x i) = tanVec i η x := by
    rw [hγ]; exact (tanVec_eq_deriv hη x).symm
  have h2 : deriv (fun t => gcurve i' η' (σ t)) (x i) = deriv σ (x i) • tanVec i' η' x := by
    have hσd : HasDerivAt σ (deriv σ (x i)) (x i) :=
      ((hσ_smooth.differentiable (by simp)).differentiableAt).hasDerivAt
    have hcd : HasDerivAt (gcurve i' η')
        (EuclideanSpace.single i' (1 : ℝ) + deriv η' (σ (x i))) (σ (x i)) :=
      hasDerivAt_gcurve hη' (σ (x i))
    have hcomp := hcd.scomp (x i) hσd
    have hcomp' : HasDerivAt (fun t => gcurve i' η' (σ t))
        (deriv σ (x i) • (EuclideanSpace.single i' (1 : ℝ) + deriv η' (σ (x i)))) (x i) := hcomp
    rw [hcomp'.deriv, hxσ, tanVec_eq_deriv hη' x]
    rw [(hasDerivAt_gcurve hη' (x i')).deriv]
  refine ⟨deriv σ (x i), ?_, ?_⟩
  · intro hc
    rw [h1, h2, hc, zero_smul] at hderiv_eq
    exact tanVec_ne_zero hη hηi x hderiv_eq
  · rw [h1, h2] at hderiv_eq
    exact hderiv_eq

/-- **The requested lemma.**  A compact `K ⊆ ℝⁿ` which is locally the graph of a smooth `η` over a
coordinate axis admits a smooth compactly supported `V` with `V x ≠ 0` and `V x` parallel to
`eᵢ + η'(x i)(1)` for every local graph representation at `x`; equivalently (`tanVec_proportional`)
`V x` is a non-zero element of the tangent line `T_x K` of the `1`-manifold `K`. -/
theorem graph_tangent_field {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
          (∀ t, (η t) i = 0) ∧
          ∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    : ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧
        (∀ x ∈ K, V x ≠ 0) ∧
        (∀ x ∈ K, ∀ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
            (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η →
          (∀ t, (η t) i = 0) →
          (∀ y ∈ U, (y ∈ K ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
          ∃ c : ℝ, c ≠ 0 ∧
            V x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) :=
  Work.ManifoldParity.graph_tangent_field K hK hgra

end

end Work.Drive.TParity
