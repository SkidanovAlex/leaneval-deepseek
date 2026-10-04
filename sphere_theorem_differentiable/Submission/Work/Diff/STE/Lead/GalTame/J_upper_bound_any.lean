import Mathlib
import Submission.Work.Diff.STE.Lead.J_pointwise_le
import Submission.Work.Diff.STE.Lead.STrunc_component_sup_le
import Submission.Work.Diff.STE.Lead.J_norm_le
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform_nodim
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.Lead.Rstar_abs_le
import Submission.Work.Diff.STE.Lead.KSBP.Defs
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.JPrelim
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.CSq_trunc_le
import Submission.Work.Diff.STE.Lead.GalTame.STruncR_Rper_le_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.Diff.STE.Lead.GalTame

/-! `J_upper_bound_any`: the upper pinching bound for the Friedrichs mollifier, uniform in
`ε ∈ (0, ε₁]` (any `ε₁ > 0`): if `h` has smooth chart data and `BNorm k h ≤ Bnd`, then
`(D.J ρ ε h) x v v ≤ C √Bnd · g₀(x)(v,v)`.

ROUTE (per the reviewers; note that no `hρ0`/`hρs` is needed for this one): for `ε ≤ 1` this is
`Work.Diff.STE.Lead.J_upper_bound` (proved in `Diff/STE/Lead/deTurck_limit.lean`), which is exactly
this estimate with `hdens` (derivable from `Work.Diff.STE.B3.dens_bound_sigma`) and `hJN` (the uniform
`BNorm` bound `BNorm k (J ρ ε h) ≤ C BNorm k h`, available from
`Diff/STE/Lead/GalTame/BNorm_J_le_any` or `Work.Diff.STE.B3.BNorm_J_le_uniform_nodim`) as explicit
hypotheses.

For arbitrary `ε > 0` the following ε-free route works directly: unfold
`D.J ρ ε h = Σ_i D.Rstar i (fun a b z => B3Data.STruncR ρ ε (D.R i h a b) z)`; for the per-chart
component bound `|STruncR ρ ε (Rper i h a b) z| ≤ Σ_m |(Rper i h a b)^_m| ≤
√(Σ_m wt(m)^{-k}) · √(CSq k (fourierCoeff (Rper i h a b)))` (Cauchy–Schwarz with the weights `wt ^ k`,
using only `‖ρ‖ ≤ 1`); then `Work.Diff.STE.Lead.Rstar_abs_le` turns `|STruncR … z| ≤ K_i` into
`|D.Rstar i … x v v| ≤ √Cdens⁻¹ · K_i · n · √(g₀ v v)²`, and Cauchy–Schwarz over the finite index set
`(i,a,b)` gives `≤ C · √(BNorm k h) · g₀(x)(v,v) ≤ C · √Bnd · g₀(x)(v,v)`. -/

/-- **Cauchy–Schwarz over a finite type**: `Σ_i √(X i) ≤ √(card) · √(Σ_i X i)` for a nonnegative
family `X`.  This is the step that converts the per-chart bounds (one square root per chart) into a
single square root of the *sum* of the per-chart energies, which is what `D.BNorm k h` is. -/
private lemma sum_sqrt_le_sqrt_card_mul_sqrt_sum {ι : Type*} [Fintype ι] (X : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) :
    ∑ i, Real.sqrt (X i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, X i) := by
  have h2 : (∑ i, Real.sqrt (X i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, X i := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => Real.sqrt (X i))
    have h3 : ∑ i, (Real.sqrt (X i)) ^ 2 = ∑ i, X i :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hX i))
    rw [h3] at h
    simpa only [Finset.card_univ] using h
  have h0 : 0 ≤ ∑ i, Real.sqrt (X i) := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc ∑ i, Real.sqrt (X i) = Real.sqrt ((∑ i, Real.sqrt (X i)) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, X i) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, X i) := Real.sqrt_mul (Nat.cast_nonneg _) _

/-- The background metric `g₀` is positive semidefinite on the diagonal. -/
private lemma smet_inner_nonneg'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {g : Submission.Diff.SMet I M} {x : M} (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp
  · exact (g.pos x v hv).le

theorem J_upper_bound_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (Bnd : ℝ), 0 ≤ Bnd →
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k h ≤ Bnd →
      ∀ (x : M) (v : TangentSpace I x),
        (D.J ρ ε h) x v v ≤ C * Real.sqrt Bnd * g₀.inner x v v := by
  classical
  -- *** TODO: replace by the delegated lemma ***
  have hCS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z|
          ≤ C * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))) := by
    exact Work.Diff.STE.Lead.GalTame.STruncR_Rper_le_CSq (I := I) (M := M) D ρ hρ k hk
  obtain ⟨C₁, hC₁, hC₁b⟩ := hCS
  -- The uniform two-sided bound for the chart densities on the closed `σ`-balls.
  obtain ⟨c₀, Cu, hc₀, hCu, hdensb⟩ :=
    Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  have hKnn : 0 ≤ (Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ)
      * Real.sqrt (Fintype.card ι₀) :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c₀)) hC₁)
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg (Fintype.card ι₀))
  have hrootnn : 0 ≤ (Real.sqrt c₀)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg c₀)
  refine ⟨(Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ) * Real.sqrt (Fintype.card ι₀),
    hKnn, ?_⟩
  intro ε hε h Bnd hBnd hsm hB x v
  have hvvsq : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
    mul_nonneg (Real.sqrt_nonneg (g₀.inner x v v)) (Real.sqrt_nonneg (g₀.inner x v v))
  -- The per-chart energy `X i = Σ_{a,b} CSq k (fourierCoeff (Rper i h a b))`; the total energy is
  -- `D.BNorm k h` by definition.
  set X : ι₀ → ℝ := fun i => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) with hXdef
  have hXnn : ∀ i, 0 ≤ X i := fun i => by
    rw [hXdef]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Work.Diff.STE.CSq_nonneg k _
  have hXsum : ∑ i, X i = D.BNorm k h := by
    rw [hXdef]
    rfl
  -- The uniform componentwise bound: `|STruncR ρ ε (R i h a b) z| ≤ C₁ √(X i)`.
  have hcomp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z| ≤ C₁ * Real.sqrt (X i) := by
    intro i a b z
    refine (hC₁b ε h hsm i a b z).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC₁
    rw [hXdef]
    exact (Finset.single_le_sum
        (f := fun b' : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b')))
        (fun b' _ => Work.Diff.STE.CSq_nonneg k _) (Finset.mem_univ b)).trans
      (Finset.single_le_sum
        (f := fun a' : Fin (Module.finrank ℝ E) =>
          ∑ b' : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')))
        (fun a' _ => Finset.sum_nonneg fun b' _ => Work.Diff.STE.CSq_nonneg k _)
        (Finset.mem_univ a))
  -- The per-chart reconstruction bound.
  have hRstar : ∀ i : ι₀,
      |(D.Rstar i (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)) x v v|
        ≤ (Real.sqrt c₀)⁻¹ * (C₁ * Real.sqrt (X i)) * (Module.finrank ℝ E : ℝ)
            * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
    fun i => Work.Diff.STE.Lead.Rstar_abs_le (I := I) (M := M) D i
      (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)
      (C₁ * Real.sqrt (X i)) (mul_nonneg hC₁ (Real.sqrt_nonneg (X i)))
      (fun a b z => hcomp i a b z) c₀ hc₀ (fun z hz => (hdensb i z hz).1) x v v
  -- `D.J ρ ε h` is the pointwise sum of the per-chart reconstructions.
  have hJ : (D.J ρ ε h) x v v = ∑ i : ι₀,
      (D.Rstar i (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)) x v v := by
    simp only [Work.Diff.STE.B3Data.J, Finset.sum_apply, sum_apply]
  have hvv : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
    Real.mul_self_sqrt (smet_inner_nonneg' (g := g₀) v)
  calc (D.J ρ ε h) x v v
      ≤ |(D.J ρ ε h) x v v| := le_abs_self _
    _ = |∑ i : ι₀,
          (D.Rstar i (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)) x v v| := by
        rw [hJ]
    _ ≤ ∑ i : ι₀,
          |(D.Rstar i (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R i h a b) z)) x v v| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι₀, (Real.sqrt c₀)⁻¹ * (C₁ * Real.sqrt (X i)) * (Module.finrank ℝ E : ℝ)
          * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
        Finset.sum_le_sum (fun i _ => hRstar i)
    _ = ((Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ)
            * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)))
          * (∑ i : ι₀, Real.sqrt (X i)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ ≤ ((Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ)
            * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)))
          * (Real.sqrt (Fintype.card ι₀) * Real.sqrt (∑ i, X i)) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_le_sqrt_card_mul_sqrt_sum X hXnn)
          (mul_nonneg (mul_nonneg (mul_nonneg hrootnn hC₁) (Nat.cast_nonneg _)) hvvsq)
    _ = ((Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ) * Real.sqrt (Fintype.card ι₀))
          * Real.sqrt (D.BNorm k h) * g₀.inner x v v := by
        rw [hXsum, hvv]
        ring
    _ ≤ ((Real.sqrt c₀)⁻¹ * C₁ * (Module.finrank ℝ E : ℝ) * Real.sqrt (Fintype.card ι₀))
          * Real.sqrt Bnd * g₀.inner x v v :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) hKnn)
          (smet_inner_nonneg' (g := g₀) v)

end Work.Diff.STE.Lead.GalTame
