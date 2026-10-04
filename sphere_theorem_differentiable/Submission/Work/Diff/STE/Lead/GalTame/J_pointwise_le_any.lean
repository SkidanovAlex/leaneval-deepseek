import Mathlib
import Submission.Work.Diff.STE.Lead.J_pointwise_le
import Submission.Work.Diff.STE.Lead.STruncR_sup_le
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.Rstar_abs_le
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.Lead.KSBP.Defs
import Submission.Work.Diff.STE.Lead.GalTame.STruncR_sup_le_any
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-! ## The `ε₁`-uniform sup bound for the localised components

`Work.Diff.STE.Lead.STrunc_component_sup_le` bounds `STruncR ρ ε (D.R i X a b)` uniformly in
`ε ∈ (0,1]`, using the `L¹` (kernel) bound `STruncR_sup_le` for the Friedrichs truncation.  Here we
extend the range of `ε` to `(0, ε₁]` for an arbitrary `ε₁ > 0`, replacing the kernel bound by
`Work.Diff.STE.Lead.GalTame.STruncR_sup_le_any` (the finite-box bound for `ε ≥ 1`). -/

/-- The Friedrichs truncation of a localised component of a section `X` which is pointwise
dominated by `K √(g₀(u,u)) √(g₀(v,v))` is bounded uniformly in `ε ∈ (0, ε₁]`: for every `ε` in that
range, every chart `i`, every `(a,b)` and every flat coordinate `z`,
`|STruncR ρ ε (D.R i X a b) z| ≤ C * K` for a constant `C ≥ 0` independent of `ε`, `X`, `K`, `i`,
`a`, `b`, `z`. -/
theorem STrunc_component_sup_le_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ENat) ρ)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) ε₁)
      (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ) (hK : 0 ≤ K),
      (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ),
        |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z| ≤ C * K := by
  -- The Friedrichs truncation is bounded on `L^∞` uniformly in `ε ∈ (0,ε₁]`
  -- (`STruncR_sup_le_any`), and the localised component is bounded by `√Cdens * K`
  -- (`R_abs_le`, with the uniform upper bound `Cdens` for the chart densities provided by
  -- `dens_bound_sigma`) and supported in the open unit cube (`B3Data.R_support`).
  obtain ⟨C₀, hC₀, hstl⟩ :=
    STruncR_sup_le_any (E := E) ρ hρ hρ0 hρs ε₁ hε₁
  obtain ⟨c, Cd, hc, hCd, hdens⟩ :=
    Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  refine ⟨C₀ * Real.sqrt Cd, mul_nonneg hC₀ (Real.sqrt_nonneg _), ?_⟩
  intro ε hε X K hK hbound i a b z
  have hR : ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i X a b w| ≤ Real.sqrt Cd * K :=
    R_abs_le D X K Cd hK hCd (fun i z hz => (hdens i z hz).2) hbound i a b
  have hmain := hstl ε hε (D.R i X a b) (Real.sqrt Cd * K)
    (mul_nonneg (Real.sqrt_nonneg _) hK) hR (D.R_support i X a b) z
  calc |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i X a b) z|
      ≤ C₀ * (Real.sqrt Cd * K) := hmain
    _ = C₀ * Real.sqrt Cd * K := by ring

/-! `J_pointwise_le_any`: the Friedrichs mollifier `D.J ρ ε` is bounded on the pointwise metric sup-norm
with a constant uniform in `ε ∈ (0, ε₁]` (any `ε₁ > 0`): a section `X` dominated pointwise by
`K √(g₀(u,u)) √(g₀(v,v))` has `D.J ρ ε X` dominated by `C K √(g₀(u,u)) √(g₀(v,v))`.

ROUTE (confirmed by the reviewers): for `ε ≤ 1` this is `Work.Diff.STE.Lead.J_pointwise_le`
verbatim. For `1 ≤ ε` use the crude finite-box bound: `STruncR ρ ε f z` is the finite sum
`Σ_{m ∈ truncBox ε} (trunc ρ ε (perCoeff f) m · e_m z).re` (`Work.Diff.STE.B3.STruncR_eq_sum`),
`truncBox ε ⊆ ∏ [-2,2]` for `ε ≥ 1` (so at most `5 ^ n` terms), `|trunc ρ ε c m| ≤ |c m|` (`hρ`), and
`|perCoeff f m| ≤ sup |f|` when `f` is supported in the open unit cube (the periodisation has at most
one non-zero term: `Work.Diff.STE.Lead.KSBP.stl_perFun_norm_le`), hence
`|STruncR ρ ε f z| ≤ 5^n · sup |f|`. Combine with `Work.Diff.STE.Lead.R_abs_le` (which turns the
pointwise domination of `X` into `|D.R i X a b w| ≤ √Cdens · K`, using
`Work.Diff.STE.B3.dens_bound_sigma` for the density upper bound and `D.R_support` for the support)
and with `Work.Diff.STE.Lead.Rstar_abs_le` exactly as in the proof of `J_pointwise_le`. -/

theorem J_pointwise_le_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (X : Work.Diff.STE.Bil (I := I) (M := M))
      (K : ℝ), 0 ≤ K → (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      ∀ (x : M) (u v : TangentSpace I x),
        |(D.J ρ ε X) x u v| ≤ C * K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  classical
  -- Uniform two-sided bounds for the chart densities on the `σ`-balls, and the uniform `L^∞`
  -- bound for the Friedrichs truncation of the localised components.
  obtain ⟨c₀, Cu, hc₀, hCu, hdensb⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  obtain ⟨C₁, hC₁, hC₁b⟩ := STrunc_component_sup_le_any D ρ hρ hρ0 hρs ε₁ hε₁
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

end Work.Diff.STE.Lead.GalTame
