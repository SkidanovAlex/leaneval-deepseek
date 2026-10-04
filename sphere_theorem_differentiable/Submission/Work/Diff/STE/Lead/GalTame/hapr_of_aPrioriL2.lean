import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Contracts
import Submission.Work.Diff.STE.Lead.GalTame.galE_apriori_L2
import Submission.Work.Diff.STE.Lead.deTurck_limit
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.B3.J_finite_rank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

/-- The physical energy `ENormSq` is nonnegative (a sum of integrals of squares). -/
private lemma ENormSq_nonneg_hapr {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq k f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => by positivity

/-- **The a priori estimate `hapr` of the trapping result, at level `k₀`.**

`Work.Diff.STE.Lead.GalTame.galE_apriori_L2` (proved, axiom-clean) bounds
`galE D k ε (c t)` for *any* solution `c` of the span-form Galerkin ODE on `[0, T)` that keeps
`u~(c) = J ρ ε (galState D ε (c ·))` between `lam · g₀` and `K · g₀` and whose `J`-image has
`ENormB`-level-`k₀` bound `B₀`, by `(galE D k ε (c 0) + 1) · exp (C t) - 1` — with `C` independent
of `ε`, of the level-`k` energy and of the solution.

The trapping result `Work.Diff.STE.Lead.GalTame.galerkin_trapped_solution_clean` needs this estimate
at level `k₀` in the *weak* shape whose hypotheses are the ones the trap actually provides: only
`lam · g₀ ≤ u~(c)` (the trap's margin), and only `galE D k₀ ε (c t) ≤ B` (the trap's energy bound)
— no explicit `K`, no explicit `B₀`, no explicit smoothness of the section.  The present statement
produces the missing data internally:

* `B₀ := (A k₀ * CJN k₀ + A 0 * CJN 0) * (Cb * B)`, where `Cb` is the constant of
  `Work.Diff.STE.Lead.BNorm_le_ENormB_uniform D k₀`, `A m` that of
  `Work.Diff.STE.Lead.ENormB_le_BNorm_uniform D m` and `CJN m` that of the hypothesis `hJN` at
  level `m`.  Indeed
  `ENormB k₀ (J ρ ε h) ≤ A k₀ * BNorm k₀ (J ρ ε h) ≤ A k₀ * CJN k₀ * BNorm k₀ h`,
  `BNorm k₀ h ≤ Cb * (ENormB k₀ h + ENormB 0 h) ≤ Cb * B` (since `galE k₀ ε (c t) = ENormB k₀ h +
  ENormB 0 h`), and the same at level `0`; the smoothness hypotheses of `ENormB_le_BNorm_uniform`
  come from `ChartData (D.J ρ ε h)` (`Work.Diff.STE.Lead.chartData_J_props`) via
  `Work.Diff.STE.B3.R_contDiff_of_chartData` and
  `Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff` plus `ContDiff.of_le le_top`.
* `K := max Khub 1`, where `Work.Diff.STE.Lead.J_upper_bound D ρ hρ k₀ hk₀' hdens hJN` gives `C` with
  `(D.J ρ ε h) x v v ≤ C * √Bnd * g₀.inner x v v` for `D.BNorm k₀ h ≤ Bnd`; with
  `h := galState D ε (c t)` and `Bnd := Cb * B` this is the `hub` needed for `u~`, and
  `hdens : ∃ d₀ > 0, ∀ i z, ‖z‖ ≤ 2 D.σ i → d₀ ≤ D.dens i z` comes from
  `Work.Diff.STE.B3.dens_lower_bound D (fun i => Work.Diff.STE.B3.densGood_noT2 D i)`.
* `hComm : CommData D ρ k₀` gives the `hJ` of `galE_apriori_L2` at level `k₀`, and
  `hG : GardingData D hLC k₀ k₀`, `hLow : LowEnergyData D hLC k₀ k₀` are its `hG`/`hLow`.

The resulting `Cof : ℝ → ℝ` is the constant produced by `galE_apriori_L2` at `lam` for `lam > 0`
and `0` otherwise; it is `≥ 0` on `lam > 0` by the nonnegativity clause of `galE_apriori_L2`.

Note the exact shapes: `ε ≤ 1` (not `≤ ε₁`), `Ico 0 T`, `HasDerivAt`, and the conclusion written
with `Work.Diff.STE.Lead.galE`; the caller instantiates `ε₁ := min ε_seed 1` and shrinks `ε ≤ ε₁`
to `ε ≤ 1`. -/
theorem hapr_of_aPrioriL2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (k₀ : ℕ) (hk₀ : Module.finrank ℝ E + 12 < 2 * k₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hJN : Work.Diff.STE.Lead.GalTame.JNBound (I := I) (M := M) D ρ)
    (hComm : Work.Diff.STE.Lead.GalTame.CommData (I := I) (M := M) D ρ k₀)
    (hG : Work.Diff.STE.Lead.GalTame.GardingData (I := I) (M := M) D hLC k₀ k₀)
    (hLow : Work.Diff.STE.Lead.GalTame.LowEnergyData (I := I) (M := M) D hLC k₀ k₀) :
    ∃ Cof : ℝ → ℝ, (∀ lam : ℝ, 0 < lam → 0 ≤ Cof lam) ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k₀ ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1 := by
  classical
  -- ## The constants produced by the statement
  -- the two composite-norm bounds of the physical energy, at level `k₀` and at level `0`
  obtain ⟨Cbk, hCbk, hCbk_b⟩ :=
    Work.Diff.STE.Lead.BNorm_le_ENormB_uniform (I := I) (M := M) D k₀
  obtain ⟨Cb0, hCb0, hCb0_b⟩ :=
    Work.Diff.STE.Lead.BNorm_le_ENormB_uniform (I := I) (M := M) D 0
  -- the two physical-energy bounds of the composite norm
  obtain ⟨Ak, hAk, hAk_b⟩ :=
    Work.Diff.STE.Lead.ENormB_le_BNorm_uniform (I := I) (M := M) D k₀
  obtain ⟨A0, hA0, hA0_b⟩ :=
    Work.Diff.STE.Lead.ENormB_le_BNorm_uniform (I := I) (M := M) D 0
  -- the `ε`-uniform mollifier bound `hJN`, in the raw form
  let CJN : ℕ → ℝ := fun m => Classical.choose (hJN m)
  have hCJNspec : ∀ m : ℕ, 0 ≤ CJN m ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        D.BNorm m (D.J ρ ε h) ≤ CJN m * D.BNorm m h :=
    fun m => Classical.choose_spec (hJN m)
  -- the adjointness constant of the mollifier
  obtain ⟨CJ, hCJ, hCommf⟩ := hComm
  -- the uniform positivity of the chart densities
  have hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood_noT2 (I := I) (M := M) D i)
  have hkcard : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k₀ := by
    rw [Fintype.card_fin]; omega
  -- the `ε`-uniform upper pinching bound for the mollified section
  obtain ⟨CJub, hCJub0, hCJub⟩ :=
    Work.Diff.STE.Lead.J_upper_bound (I := I) (M := M) D ρ hρ k₀ hkcard hdens hJN
  -- a single composite-norm bound `Bnd` valid at both levels, the resulting pinching
  -- constant `K` and the energy bound `B₀`
  set Bnd : ℝ := max (Cbk * B) (2 * Cb0 * B) with hBnddef
  have hBnd0 : 0 ≤ Bnd := by
    rw [hBnddef]
    exact le_trans (mul_nonneg hCbk hB) (le_max_left _ _)
  set K : ℝ := max (CJub * Real.sqrt Bnd) 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set B₀ : ℝ := (Ak * CJN k₀ + A0 * CJN 0) * Bnd with hB₀def
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀def]
    exact mul_nonneg (add_nonneg (mul_nonneg hAk (hCJNspec k₀).1)
      (mul_nonneg hA0 (hCJNspec 0).1)) hBnd0
  -- ## The estimate for each `lam`
  have key : ∀ lam : ℝ, 0 < lam →
      ∃ Clam : ℝ, 0 ≤ Clam ∧
        ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
        ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
        (∀ t ∈ Set.Ico (0 : ℝ) T,
          HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
          0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
          lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
        (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) →
        ∀ t ∈ Set.Ico (0 : ℝ) T,
          Work.Diff.STE.Lead.galE D k₀ ε (c t)
            ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Clam * t) - 1 := by
    intro lam hlam
    -- the Gårding and low-order data at this `lam`, `K`, `B₀`
    obtain ⟨lam', Cg, hlam', hCg, hG'⟩ := hG lam K B₀ hlam hKpos hB₀0
    obtain ⟨Cl, hCl, hLow'⟩ := hLow lam K B₀ hlam hKpos hB₀0
    have hk₀' : Module.finrank ℝ E + 4 < 2 * k₀ := by omega
    obtain ⟨Clam, hClam, hCf⟩ :=
      Work.Diff.STE.Lead.GalTame.galE_apriori_L2 (I := I) (M := M) D hLC ρ hρ hρ0 hρs hρ1 hg
        k₀ k₀ hk₀ hk₀' lam K B₀ hlam hKpos hB₀0 CJ hCJ
        (fun ε hε hε1 f u hf hu => hCommf ε hε hε1 f u hf hu)
        CJN (fun m => (hCJNspec m).1)
        (fun m ε hε hε1 h hcd => (hCJNspec m).2 ε ⟨hε, hε1⟩ h hcd)
        lam' Cg Cl hlam' hCg hCl hG' hLow'
    refine ⟨Clam, hClam, ?_⟩
    intro ε hε hε1 c T hT hder hpos hlow hEu t ht
    -- ## the two bounds that the trap supplies, converted into the data of `galE_apriori_L2`
    -- composite-norm bound of the state at level `k₀`
    have hBNk : ∀ t' ∈ Set.Ico (0 : ℝ) T,
        D.BNorm k₀ (Submission.Diff.STEGal.galState D ε (c t')) ≤ Bnd := by
      intro t' ht'
      have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (Submission.Diff.STEGal.galState D ε (c t')) :=
        Work.Diff.STE.Lead.chartData_galState (I := I) (M := M) D ε hg (c t')
      have hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ k₀ (D.Rper i (Submission.Diff.STEGal.galState D ε (c t')) a b) :=
        fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M)
          D i _ a b (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
            hcd i a b)).1.of_le (WithTop.coe_le_coe.mpr le_top)
      have hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.Periodic1
            (D.Rper i (Submission.Diff.STEGal.galState D ε (c t')) a b) :=
        fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M)
          D i _ a b (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
            hcd i a b)).2
      have hE : D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t'))
          + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t')) ≤ B := hEu t' ht'
      calc D.BNorm k₀ (Submission.Diff.STEGal.galState D ε (c t'))
          ≤ Cbk * (D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t'))
              + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t'))) := hCbk_b _ hsm hper
        _ ≤ Cbk * B := mul_le_mul_of_nonneg_left hE hCbk
        _ ≤ Bnd := le_max_left _ _
    -- composite-norm bound of the state at level `0`
    have hBN0 : ∀ t' ∈ Set.Ico (0 : ℝ) T,
        D.BNorm 0 (Submission.Diff.STEGal.galState D ε (c t')) ≤ Bnd := by
      intro t' ht'
      have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (Submission.Diff.STEGal.galState D ε (c t')) :=
        Work.Diff.STE.Lead.chartData_galState (I := I) (M := M) D ε hg (c t')
      have hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ 0 (D.Rper i (Submission.Diff.STEGal.galState D ε (c t')) a b) :=
        fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M)
          D i _ a b (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
            hcd i a b)).1.of_le (WithTop.coe_le_coe.mpr le_top)
      have hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.Periodic1
            (D.Rper i (Submission.Diff.STEGal.galState D ε (c t')) a b) :=
        fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M)
          D i _ a b (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
            hcd i a b)).2
      have hE : D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t'))
          + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t')) ≤ B := hEu t' ht'
      have hnn : 0 ≤ D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t')) :=
        Work.Diff.STE.B3Data.ENormB_nonneg (I := I) (M := M) D k₀ _
          (fun i a b => ENormSq_nonneg_hapr k₀ _)
      calc D.BNorm 0 (Submission.Diff.STEGal.galState D ε (c t'))
          ≤ Cb0 * (D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t'))
              + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t'))) := hCb0_b _ hsm hper
        _ ≤ Cb0 * (2 * (D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t'))
              + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t')))) :=
            mul_le_mul_of_nonneg_left (by linarith) hCb0
        _ = 2 * Cb0 * (D.ENormB k₀ (Submission.Diff.STEGal.galState D ε (c t'))
              + D.ENormB 0 (Submission.Diff.STEGal.galState D ε (c t'))) := by ring
        _ ≤ 2 * Cb0 * B := mul_le_mul_of_nonneg_left hE (by linarith)
        _ ≤ Bnd := le_max_right _ _
    -- ## the upper pinching bound `hub` for the mollified state
    have hupfun : ∀ t' ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) x v v ≤ K * g₀.inner x v v := by
      intro t' ht' x v
      have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (Submission.Diff.STEGal.galState D ε (c t')) :=
        Work.Diff.STE.Lead.chartData_galState (I := I) (M := M) D ε hg (c t')
      have hub := hCJub ε ⟨hε, hε1⟩ (Submission.Diff.STEGal.galState D ε (c t')) hcd
        Bnd hBnd0 (hBNk t' ht') x v
      calc (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) x v v
          ≤ CJub * Real.sqrt Bnd * g₀.inner x v v := hub
        _ ≤ K * g₀.inner x v v := by
            refine mul_le_mul_of_nonneg_right ?_
              (Work.Diff.STE.Lead.smet_inner_nonneg (I := I) (g₀ := g₀) v)
            rw [hKdef]; exact le_max_left _ _
    -- ## the energy bound `B₀` for the mollified state
    have hB0fun : ∀ t' ∈ Set.Ico (0 : ℝ) T,
        D.ENormB k₀ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t')))
          + D.ENormB 0 (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) ≤ B₀ := by
      intro t' ht'
      have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (Submission.Diff.STEGal.galState D ε (c t')) :=
        Work.Diff.STE.Lead.chartData_galState (I := I) (M := M) D ε hg (c t')
      have hcdJ : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) :=
        Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε _ hcd
      have hsmJ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞)
            (D.R i (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) a b) :=
        fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hcdJ i a b
      have hEk := hAk_b _ hsmJ
      have hE0 := hA0_b _ hsmJ
      have hBk := (hCJNspec k₀).2 ε ⟨hε, hε1⟩ _ hcd
      have hB0 := (hCJNspec 0).2 ε ⟨hε, hε1⟩ _ hcd
      have h1 : D.ENormB k₀ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t')))
          ≤ Ak * CJN k₀ * Bnd := by
        calc D.ENormB k₀ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t')))
            ≤ Ak * D.BNorm k₀ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) := hEk
          _ ≤ Ak * (CJN k₀ * D.BNorm k₀ (Submission.Diff.STEGal.galState D ε (c t'))) :=
              mul_le_mul_of_nonneg_left hBk hAk
          _ ≤ Ak * (CJN k₀ * Bnd) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hBNk t' ht') (hCJNspec k₀).1) hAk
          _ = Ak * CJN k₀ * Bnd := by ring
      have h2 : D.ENormB 0 (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t')))
          ≤ A0 * CJN 0 * Bnd := by
        calc D.ENormB 0 (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t')))
            ≤ A0 * D.BNorm 0 (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t'))) := hE0
          _ ≤ A0 * (CJN 0 * D.BNorm 0 (Submission.Diff.STEGal.galState D ε (c t'))) :=
              mul_le_mul_of_nonneg_left hB0 hA0
          _ ≤ A0 * (CJN 0 * Bnd) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hBN0 t' ht') (hCJNspec 0).1) hA0
          _ = A0 * CJN 0 * Bnd := by ring
      rw [hB₀def]
      have hid : Ak * CJN k₀ * Bnd + A0 * CJN 0 * Bnd
          = (Ak * CJN k₀ + A0 * CJN 0) * Bnd := by ring
      linarith [h1, h2]
    exact hCf ε hε hε1 c T hT hder hpos hlow hupfun hB0fun t ht
  -- ## Assembly: choose the constant `Cof lam` for `lam > 0`, and `0` otherwise
  let Cof : ℝ → ℝ := fun lam => if h : 0 < lam then Classical.choose (key lam h) else 0
  refine ⟨Cof, ?_, ?_⟩
  · intro lam hlam
    have hCof : Cof lam = Classical.choose (key lam hlam) := dif_pos hlam
    rw [hCof]
    exact (Classical.choose_spec (key lam hlam)).1
  · intro lam hlam
    have hCof : Cof lam = Classical.choose (key lam hlam) := dif_pos hlam
    rw [hCof]
    exact (Classical.choose_spec (key lam hlam)).2

end

end Work.Diff.STE.Lead.GalTame
