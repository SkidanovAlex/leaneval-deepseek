import Mathlib
import Submission.Work.Diff.STE.Lead.STruncR_sup_le
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.Lead.Rstar_abs_le
import Submission.Work.Diff.STE.Lead.STrunc_component_sup_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- The Friedrichs mollifier `D.J ρ ε` is bounded on the pointwise sup-norm: a section `X` which is
pointwise dominated by `K √(g₀(u,u)) √(g₀(v,v))` has `D.J ρ ε X` pointwise dominated by
`C K √(g₀(u,u)) √(g₀(v,v))`, uniformly in `ε ∈ (0,1]`.  (Sup route: the kernel of the Friedrichs
truncation is bounded in `L¹`; the reconstruction `Rstar` uses a `g₀`-orthonormal frame.)

Route: `D.J ρ ε X = Σ_i Rstar i (fun a b z => STruncR ρ ε (D.R i X a b) z)`.  For each `i`,
`|D.R i X a b w| ≤ √Cdens · K` (`R_abs_le`, from the pointwise bound of `X` with `dens_bound_sigma`
giving both a lower and an upper bound for `dens` on the `σ i`-ball), and `D.R i X a b` is supported
in the open cube, so `|STruncR ρ ε (D.R i X a b) z| ≤ Cstl · √Cdens · K`
(`STruncR_sup_le`).  Finally unfold `Rstar`: at a point `x` with `D.ζ i x ≠ 0` one has
`‖coord i x‖ < σ i`, hence `D.χ i (coord i x) = 1` (`B3Data.hχ1`),
`d₀ ≤ D.dens i (coord i x)` (`B3Data.hζsupp` + `dens_bound_sigma`) and the frame `e i` is
`g₀`-orthonormal at `x` (`B3Data.heON`), so
`(D.Rstar i u) x v w = Σ_a Σ_b ⟨e i a x, v⟩ · (ζ i x · χ i (coord i x) · (√(dens i (coord i x)))⁻¹ · u a b (coord i x)) · ⟨e i b x, w⟩`
and `Σ_a |⟨e i a x, v⟩| ≤ √n √(g₀.inner x v v)` (`B3Data.sum_abs_inner_le`), while the coefficient is
bounded by `(√d₀)⁻¹ · Cstl √Cdens · K`.  When `D.ζ i x = 0` the whole `i`-term vanishes. -/
theorem J_pointwise_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ENat) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
      (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ) (hK : 0 ≤ K),
      (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      ∀ (x : M) (u v : TangentSpace I x),
        |(D.J ρ ε X) x u v|
          ≤ C * K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  classical
  -- Uniform two-sided bounds for the chart densities on the `σ`-balls, and the uniform `L^∞`
  -- bound for the Friedrichs truncation of the localised components.
  obtain ⟨c₀, Cu, hc₀, hCu, hdensb⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  obtain ⟨C₁, hC₁, hC₁b⟩ := STrunc_component_sup_le D ρ hρ hρ0 hρs
  refine ⟨(Fintype.card ι₀ : ℝ) * (Real.sqrt c₀)⁻¹ * (Module.finrank ℝ E : ℝ) * C₁,
    by positivity, ?_⟩
  intro ε hε X K hK hX x u v
  -- Every component family `STruncR ρ ε (R i X a b)` is dominated by `C₁ * K`.
  have hcomp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z| ≤ C₁ * K :=
    fun i a b z => hC₁b ε hε X K hK hX i a b z
  have hMnn : 0 ≤ C₁ * K := mul_nonneg hC₁ hK
  -- The per-chart reconstruction bound.
  have hper : ∀ i : ι₀,
      |(D.Rstar i (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z)) x u v|
        ≤ (Real.sqrt c₀)⁻¹ * (C₁ * K) * (Module.finrank ℝ E : ℝ)
            * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) :=
    fun i => Rstar_abs_le D i (fun a b z =>
        Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z) (C₁ * K) hMnn
      (fun a b z => hcomp i a b z) c₀ hc₀ (fun z hz => (hdensb i z hz).1) x u v
  -- `J` is the pointwise sum of the reconstructions of the localised components.
  have hJ : (D.J ρ ε X) x u v
      = ∑ i : ι₀, (D.Rstar i (fun a b z =>
          Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z)) x u v := by
    simp only [Work.Diff.STE.B3Data.J, Finset.sum_apply, sum_apply]
  rw [hJ]
  calc |∑ i : ι₀, (D.Rstar i (fun a b z =>
          Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z)) x u v|
      ≤ ∑ i : ι₀, |(D.Rstar i (fun a b z =>
          Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z)) x u v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι₀, ((Real.sqrt c₀)⁻¹ * (C₁ * K) * (Module.finrank ℝ E : ℝ)
          * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (Fintype.card ι₀ : ℝ) * ((Real.sqrt c₀)⁻¹ * (C₁ * K) * (Module.finrank ℝ E : ℝ)
          * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((Fintype.card ι₀ : ℝ) * (Real.sqrt c₀)⁻¹ * (Module.finrank ℝ E : ℝ) * C₁)
          * K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by ring

end Work.Diff.STE.Lead
