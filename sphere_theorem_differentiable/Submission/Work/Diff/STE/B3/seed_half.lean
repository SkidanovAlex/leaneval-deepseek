import Mathlib
import Submission.Work.Diff.STE.B3.seed_margin
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

/-- **The seed margin with the explicit constant `1/2`.**

`Work.Diff.STE.B3.seed_margin` proves
`∃ ε₀ > 0, ∃ lam > 0, ∀ ε ∈ Ioc 0 ε₀, ∀ x v, lam * g₀.inner x v v ≤ (D.J ρ ε g₀.inner) x v v` — and
its proof *in fact* produces `lam = 1/2` (its last line is
`refine ⟨ε₀, hε₀pos, 1 / 2, by norm_num, ?_⟩`).  But the *statement* only exposes an existential
`lam`, so no consumer can extract `1/2` from it.

The final assembly of `Work.Diff.STE.Lead.gal_uniform_v2` needs exactly `1/2`: it is the hypothesis
`hseed` of `Work.Diff.STE.Lead.GalTame.galerkin_trapped_strong`, where the positivity margin `1/4`
is obtained as `1/2 − (the C⁰ drift)`.  Hence this restatement with the constant hardcoded.

**Proof**: copy the proof of `Work.Diff.STE.B3.seed_margin` verbatim out of
`Submission/Work/Diff/STE/B3/seed_margin.lean` and drop its `∃ lam` binder (replacing
`refine ⟨ε₀, hε₀pos, 1 / 2, by norm_num, ?_⟩` by `refine ⟨ε₀, hε₀pos, ?_⟩`).  All the auxiliary
material (`seed_lower`, `seed_term_id`, `seed_term_bound`, `dens_bound_sigma`, `densGood_noT2`) is in
that file and is sorry-free. -/
theorem seed_half
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJT : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, ∀ (x : M) (v : TangentSpace I x),
        (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v := by
  classical
  obtain ⟨c, C, hc, hC, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  have hdensb : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ D.σ i → c ≤ D.dens i z :=
    fun i z hz => (hdens i z hz).1
  have hdg : ∀ i : ι₀, D.DensGood i := fun i => Work.Diff.STE.B3.densGood_noT2 D i
  have hmat : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i g₀.inner a b) (extChartAt I (D.x₀ i)).target :=
    fun i a b => Work.Diff.STE.B3.matChart_metric_contDiffOn D i a b
  have hρc : ContinuousAt ρ 0 := hρs.continuous.continuousAt
  set K : ℝ := (Real.sqrt c)⁻¹ * (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  set δ : ℝ := 1 / (2 * (K + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδK : δ * K ≤ 1 / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
    nlinarith [hKnn]
  have hdef := Work.Diff.STE.B3.STruncR_R_sub_le_uniform D ρ hρ0 hρ hρc hρ1 hdg hmat δ hδpos
  obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y
            - D.R i g₀.inner a b y| ≤ δ := by
    rw [eventually_nhdsWithin_iff] at hdef
    rw [Metric.eventually_nhds_iff] at hdef
    obtain ⟨η, hηpos, hη⟩ := hdef
    refine ⟨η / 2, by linarith, fun ε hε => hη ?_ hε.1⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]
    linarith [hε.2]
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hε x v
  refine seed_lower D ρ ε δ c hc hδpos hdensb ?_ ?_ x v
  · intro i a b y hy
    exact hε₀ ε hε i a b y hy
  · rw [← hK]
    exact hδK

end Work.Diff.STE.B3
