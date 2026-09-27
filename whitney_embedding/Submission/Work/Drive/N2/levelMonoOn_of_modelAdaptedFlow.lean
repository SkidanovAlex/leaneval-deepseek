import Mathlib
import Submission.Work.Drive.N2.level_mono_of_modelAdaptedFlow
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.hmono_of_chartODE

namespace Work.Drive.N2

open scoped Manifold Topology
open Set

/-- **The orbit function of a model-adapted flow is non-decreasing.**

This is the `MonotoneOn` companion of `Work.Drive.N2.level_mono_of_modelAdaptedFlow`: the two use
exactly the same hypotheses, and the conclusion here is the monotonicity of `f` along the orbits of
`Φ` that several consumers need (e.g. the ordering arguments on the `f`-level sets).

The proof is short because the analytic work is in `Work.Drive.N2.hmono_of_chartODE`:

* `Work.Drive.N2.orbit_deriv_nonneg` (with `β i = chartMult (r i)`) gives that the orbit function
  `σ ↦ f (Φ (σ, y))` has non-negative derivative everywhere: inside a model ball the chart ODE gives
  `2 * chartMult (r i) (‖u‖ ^ 2) * ‖u‖ ^ 2 ≥ 0` and off the model balls the level law gives slope
  `1`;
* `σ ↦ f (Φ (σ, y))` is `C¹` along the orbit because `f` and `Φ` are `C^∞`;
* `monotone_of_deriv_nonneg` therefore makes it non-decreasing on all of `ℝ`, hence on `Set.Ici 0`. -/
theorem levelMonoOn_of_modelAdaptedFlow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hval : ∀ i y, y ∈ (φ i).source →
      f y = f (x i) + Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) y)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, Work.Drive.N2.modelBall (φ i) (r i) ⊆ C i)
    (Φ : ℝ × M → M)
    (hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hlevel : ∀ (y : M) (t : ℝ), (∀ i, y ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i,
        Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    (hODE : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) *
          (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) *
          (s₂ i * φ i (Φ (t, y)) 1)) t) :
    ∀ y : M, MonotoneOn (fun t : ℝ => f (Φ (t, y))) (Set.Ici 0) := by
  -- the orbit function is `C¹`
  have hFcd : ∀ y : M, ContDiff ℝ 1 (fun σ : ℝ => f (Φ (σ, y))) := by
    intro y
    have hcur : ContMDiff (modelWithCornersSelf ℝ ℝ)
        ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => (σ, y)) :=
      ContMDiff.prodMk contMDiff_id contMDiff_const
    have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun σ : ℝ => Φ (σ, y)) := hΦsm.comp hcur
    have h2 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => f (Φ (σ, y))) := hf.comp h1
    have h3 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) (1 : ℕ)
        (fun σ : ℝ => f (Φ (σ, y))) := (contMDiff_infty.mp h2) 1
    have h4 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun σ : ℝ => f (Φ (σ, y))) :=
      (contMDiff_iff_contDiff).mp h3
    simpa using h4
  -- the level law in the form consumed by `orbit_deriv_nonneg` (no condition on the base point)
  have hlevel' : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i,
        Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t := by
    intro y t h
    exact hlevel y t (fun i => hΦ0 y ▸ h (0 : ℝ) ⟨min_le_left (0 : ℝ) t, le_max_left (0 : ℝ) t⟩ i) h
  intro y
  have hderivnn : ∀ σ : ℝ, 0 ≤ deriv (fun τ : ℝ => f (Φ (τ, y))) σ :=
    orbit_deriv_nonneg hΦsm.continuous hΦcomp x φ s₁ s₂ r (fun i => chartMult (r i))
      hCball (fun i σ => chartMult_nonneg (r i) σ) hval hlevel' hODE hsgn y (hFcd y)
  have hmono : Monotone (fun t : ℝ => f (Φ (t, y))) :=
    monotone_of_deriv_nonneg ((hFcd y).differentiable (by norm_num)) hderivnn
  exact fun a _ b _ hab => hmono hab

end Work.Drive.N2
