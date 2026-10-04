import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.Lead.GalTame.Contracts
import Submission.Work.Diff.STE.Lead.GalTame.galE_apriori_L2
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Lead.GalTame.Level
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.BNorm_le_ENormB_unif
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.Lead.mat_jet_uniform_bound
import Submission.Work.Diff.STE.Lead.GalTame.J_upper_bound_any
import Submission.Work.Diff.STE.Lead.GalTame.deTurck_low_energy
import Submission.Work.Diff.STE.Lead.galState_J_props
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The final assembly of `Work.Diff.STE.Lead.gal_uniform_v2`

The statement of the target is

`GalUniform hLC D ρ = ∃ ε₀ > 0, ∃ τ₀ > 0, ∃ lam > 0, ∃ B : ℕ → ℝ, ∀ ε ∈ Ioc 0 ε₀, ∃ c,
   IsGalSol hLC D ρ ε τ₀ c ∧ (∀ t ∈ Icc 0 τ₀, (∀ k, D.BNorm k (galState D ε (c t)) ≤ B k)
     ∧ ∀ x v, lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v)`.

This module contains the whole assembly, with the *analytic* inputs as explicit hypotheses whose
shapes are the conclusions of the corresponding (possibly still in-flight) lemmas.  The glue is:

1. **Seed margin**: the hypothesis `hseed` (supplied by `Work.Diff.STE.B3.seed_margin` with
   `hJT`): `(1/2) g₀ ≤ J ρ ε g₀` for `ε ≤ εs`.
2. **Level**: `k₀` with `n + 12 < 2 k₀` (take `k₀ = n + 13`).
3. **Trapping** (hypothesis `hTrap`, supplied by `GalTame/galerkin_trapped_strong`): one `τ₀ > 0`,
   and for every `ε ∈ (0, min εs 1]` a curve `c` with `IsGalSol`, the coefficient-level ODE
   `HasDerivAt c (galVF2 … (c t)) t` on `[0, τ₀)`, the margin `(1/4)·g₀ ≤ J ρ ε (galState D ε (c t))`
   on `[0, τ₀]` and `galE D k₀ ε (c t) ≤ B` on `[0, τ₀)`.
4. **Trap bounds** (`trapBounds`, proved here): from `galE D k₀ ε c ≤ B` alone one gets `K > 0`,
   `B₀ ≥ 0` with `(D.J ρ ε (galState D ε c)) x v v ≤ K · g₀.inner x v v` pointwise and
   `D.ENormB k₀ (D.J ρ ε (galState D ε c)) + D.ENormB 0 (⋯) ≤ B₀`.  These are the `hub` and the
   level-`k₀` hypothesis of `galE_apriori_L2` at *every* level.
5. **Level-by-level a priori estimate**: `galE_apriori_L2` at level `k` with the sharp Gårding datum
   `GardingData k k₀` (from `gardingSharp_hG_of_jet` and the defect), the low-energy datum
   `LowEnergyData k k₀` (from `lowEnergy_of_transport`), and `CommData ρ k`.
6. **Conversion**: `D.BNorm k h ≤ Cb k · galE D k ε (c t)`
   (`Work.Diff.STE.B3.BNorm_le_ENormB_unif`); for the finitely many `k` with `2k ≤ n + 12` (hence
   `k ≤ k₀`) the monotonicity `D.ENormB m h ≤ Cm · D.ENormB k₀ h`
   (`GalTame/ENormB_mono_level`) and the trap give the bound.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **`IsGalSol` is monotone in the time interval.** -/
lemma isGalSol_mono {hLC : LCSmooth I M} {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀}
    {ρ : (Idx → ℝ) → ℝ} {ε τ τ' : ℝ} {c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)}
    (h : IsGalSol hLC D ρ ε τ c) (hτ' : τ' ≤ τ) : IsGalSol hLC D ρ ε τ' c := by
  refine ⟨h.1, ?_, ?_⟩
  · intro t ht x v hv
    exact h.2.1 t ⟨ht.1, le_trans ht.2 hτ'⟩ x v hv
  · intro t ht hsym hsm hpos x u v
    exact (h.2.2 t ⟨ht.1, le_trans ht.2 hτ'⟩ hsym hsm hpos x u v).mono
      (fun y hy => ⟨hy.1, le_trans hy.2 hτ'⟩)

/-- The energy `ENormSq` is nonnegative. -/
private lemma ENormSq_nonneg_asm {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => by positivity

/-- `ENormB` is nonnegative. -/
private lemma ENormB_nonneg_asm (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (m : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : 0 ≤ D.ENormB m h := by
  rw [Work.Diff.STE.B3Data.ENormB]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => ENormSq_nonneg_asm m _

/-- **`ENormB ≤ C · BNorm`, uniformly in the section** — a private copy of
`Work.Diff.STE.Lead.ENormB_le_BNorm_uniform` (so that this module does not depend on the live target
`Lead/deTurck_limit`).  The proof only uses the section through the smoothness of the localised
components, which is exactly the hypothesis here. -/
private theorem enormb_le_bnorm_uniform_asm
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Idx), ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)),
      D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hCb⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Idx) k
  refine ⟨C, hC, fun h hh => ?_⟩
  simp only [Work.Diff.STE.B3Data.ENormB, Work.Diff.STE.B3Data.BNorm]
  calc ∑ i : ι₀, ∑ a : Idx, ∑ b : Idx, Work.Diff.STE.ENormSq k (D.Rper i h a b)
      ≤ ∑ i : ι₀, ∑ a : Idx, ∑ b : Idx,
          C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => ?_
        obtain ⟨hsm, hper⟩ :=
          Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b
            (hh i a b)
        exact hCb _ hsm hper
    _ = C * ∑ i : ι₀, ∑ a : Idx, ∑ b : Idx,
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- **The uniform bounds implied by the trap.**  From the level-`k₀` energy bound
`galE D k₀ ε c = D.ENormB k₀ (galState D ε c) + D.ENormB 0 (galState D ε c) ≤ B` alone one gets

* a pointwise upper bound `D.J ρ ε (galState D ε c) ≤ K · g₀` (the `hub` of `galE_apriori_L2`),
  from `Work.Diff.STE.Lead.J_upper_bound` applied to `galState D ε c` (whose `BNorm k₀` is
  `≤ Cb · B` by `BNorm_le_ENormB_unif`), and
* the level-`k₀` energy bound for the *mollified* state `D.J ρ ε (galState D ε c)` (the `B₀` of
  `galE_apriori_L2`), from `ENormB_le_BNorm_uniform` and the level-`k₀`/level-`0` constants `CJN`,
  `CJNz` of `hJN`.

All constants are independent of `ε ∈ (0, 1]`, of the curve and of `B` except through the displayed
formulas. -/
theorem trapBounds
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Idx → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (hJN : Work.Diff.STE.Lead.GalTame.JNBound (I := I) (M := M) D ρ)
    (k₀ : ℕ) (hk₀ : Module.finrank ℝ E + 12 < 2 * k₀)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 ≤ B₀ ∧
      ∀ (ε : ℝ), ε ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
          Work.Diff.STE.Lead.galE D k₀ ε c ≤ B →
          (∀ (x : M) (v : TangentSpace I x),
              (D.J ρ ε (galState D ε c)) x v v ≤ K * g₀.inner x v v) ∧
          (D.ENormB k₀ (D.J ρ ε (galState D ε c)) + D.ENormB 0 (D.J ρ ε (galState D ε c)) ≤ B₀) := by
  classical
  -- the level-`k₀` and level-`0` constants of `BNorm ≤ C (ENormB + ENormB 0)`
  obtain ⟨Cb, hCb0, hCbb⟩ := Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k₀
  obtain ⟨Cbz, hCbz0, hCbzb⟩ := Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D 0
  -- the level-`k₀` and level-`0` constants of `ENormB ≤ C BNorm`
  obtain ⟨A, hA0, hAb⟩ := enormb_le_bnorm_uniform_asm (I := I) (M := M) D k₀
  obtain ⟨A₀, hA₀0, hA₀b⟩ := enormb_le_bnorm_uniform_asm (I := I) (M := M) D 0
  obtain ⟨CJN, hCJN0, hCJNb⟩ := hJN k₀
  obtain ⟨CJNz, hCJNz0, hCJNzb⟩ := hJN 0
  -- the uniform density lower bound on the `2σ`-balls
  obtain ⟨d₀, hd₀pos, hd₀b⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood_noT2 (I := I) (M := M) D i)
  have hhk : Fintype.card (Idx) < 2 * k₀ := by
    rw [Fintype.card_fin]; omega
  obtain ⟨CJ, hCJ0, hCJb⟩ :=
    Work.Diff.STE.Lead.GalTame.J_upper_bound_any (I := I) (M := M) D ρ hρ k₀ hhk 1 one_pos
  -- the composite norm of the state is bounded by `Bnd`
  set Bnd : ℝ := max (Cb * B) (Cbz * (2 * B)) with hBnd
  have hBnd0 : 0 ≤ Bnd := by
    rw [hBnd]
    exact le_trans (mul_nonneg hCb0 hB) (le_max_left _ _)
  refine ⟨max (CJ * Real.sqrt Bnd) 1,
    A * CJN * Bnd + A₀ * CJNz * Bnd,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), by positivity, ?_⟩
  intro ε hε c hEc
  obtain ⟨hε0, hε1⟩ := hε
  -- smoothness of the state and of its mollification
  have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D ε c) :=
    chartData_galState (I := I) (M := M) D ε hg c
  have hsm : ∀ (i : ι₀) (a b : Idx),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (galState D ε c) a b) :=
    fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hcd i a b
  have hlev : ((k₀ : ℕ) : (WithTop ℕ∞)) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simpa using (le_top : ((k₀ : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hlev0 : ((0 : ℕ) : (WithTop ℕ∞)) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simpa using (le_top : ((0 : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hRper : ∀ (i : ι₀) (a b : Idx),
      ContDiff ℝ ((k₀ : ℕ) : (WithTop ℕ∞)) (D.Rper i (galState D ε c) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i _ a b
      (hsm i a b)).1.of_le hlev
  have hRper0 : ∀ (i : ι₀) (a b : Idx),
      ContDiff ℝ ((0 : ℕ) : (WithTop ℕ∞)) (D.Rper i (galState D ε c) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i _ a b
      (hsm i a b)).1.of_le hlev0
  have hRperper : ∀ (i : ι₀) (a b : Idx),
      Work.Diff.STE.Periodic1 (D.Rper i (galState D ε c) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i _ a b
      (hsm i a b)).2
  have hEc' : D.ENormB k₀ (galState D ε c) + D.ENormB 0 (galState D ε c) ≤ B := hEc
  -- the composite-norm bounds of the state
  have hBNk : D.BNorm k₀ (galState D ε c) ≤ Cb * B := by
    calc D.BNorm k₀ (galState D ε c)
        ≤ Cb * (D.ENormB k₀ (galState D ε c) + D.ENormB 0 (galState D ε c)) :=
          hCbb _ hRper hRperper
      _ ≤ Cb * B := mul_le_mul_of_nonneg_left hEc' hCb0
  have hBN0 : D.BNorm 0 (galState D ε c) ≤ Cbz * (2 * B) := by
    have h2 : 0 ≤ D.ENormB k₀ (galState D ε c) := ENormB_nonneg_asm D k₀ _
    calc D.BNorm 0 (galState D ε c)
        ≤ Cbz * (D.ENormB 0 (galState D ε c) + D.ENormB 0 (galState D ε c)) :=
          hCbzb _ hRper0 hRperper
      _ = Cbz * (2 * D.ENormB 0 (galState D ε c)) := by ring
      _ ≤ Cbz * (2 * B) := by
          refine mul_le_mul_of_nonneg_left ?_ hCbz0
          linarith
  constructor
  · -- the pointwise upper bound
    have h1 := hCJb ε ⟨hε0, hε1⟩ (galState D ε c) Bnd hBnd0 hcd
      (le_trans hBNk (le_max_left _ _))
    refine fun x v => le_trans (h1 x v) ?_
    have hvnn : 0 ≤ g₀.inner x v v := by
      rcases eq_or_ne v 0 with hv | hv
      · rw [hv]; simp
      · exact le_of_lt (g₀.pos x v hv)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hvnn
  · -- the level-`k₀` energy of the mollified state
    have hsmJ : ∀ (i : ι₀) (a b : Idx),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε (galState D ε c)) a b) :=
      fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
        (Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε _
          hcd) i a b
    have hsmJ' : ∀ (i : ι₀) (a b : Idx),
        ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.J ρ ε (galState D ε c)) a b) := hsmJ
    have h3 : D.BNorm k₀ (D.J ρ ε (galState D ε c)) ≤ CJN * Bnd := by
      calc D.BNorm k₀ (D.J ρ ε (galState D ε c))
          ≤ CJN * D.BNorm k₀ (galState D ε c) := hCJNb ε ⟨hε0, hε1⟩ _ hcd
        _ ≤ CJN * Bnd := mul_le_mul_of_nonneg_left (le_trans hBNk (le_max_left _ _)) hCJN0
    have h4 : D.BNorm 0 (D.J ρ ε (galState D ε c)) ≤ CJNz * Bnd := by
      calc D.BNorm 0 (D.J ρ ε (galState D ε c))
          ≤ CJNz * D.BNorm 0 (galState D ε c) := hCJNzb ε ⟨hε0, hε1⟩ _ hcd
        _ ≤ CJNz * Bnd :=
            mul_le_mul_of_nonneg_left (le_trans hBN0 (le_max_right _ _)) hCJNz0
    calc D.ENormB k₀ (D.J ρ ε (galState D ε c)) + D.ENormB 0 (D.J ρ ε (galState D ε c))
        ≤ A * D.BNorm k₀ (D.J ρ ε (galState D ε c))
          + A₀ * D.BNorm 0 (D.J ρ ε (galState D ε c)) :=
          add_le_add (hAb _ hsmJ') (hA₀b _ hsmJ')
      _ ≤ A * (CJN * Bnd) + A₀ * (CJNz * Bnd) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 hA0) (mul_le_mul_of_nonneg_left h4 hA₀0)
      _ = A * CJN * Bnd + A₀ * CJNz * Bnd := by ring

/-- **The low-energy datum `hLow` of `galE_apriori_L2`, from `GalTame/deTurck_low_energy`.**

`Work.Diff.STE.Lead.GalTame.deTurck_low_energy` is *unconditional* in the level-`k₀` energy: for
`1 ≤ k` and `n + 4 ≤ k`, `0 < lam`, `0 < K` it produces `C ≥ 0` with

  `ENormB (k-1) (P h) + ENormB 0 (P h) ≤ C * (1 + ENormB (k+1) h)`

for every section `h` that is `lam`-elliptic, `K`-bounded, smooth **and** whose chart-matrix first
jet is bounded by `K`.  Its `hjet` (with the *same* constant `K` as `hub`) is discharged here from
the level-`k₀` energy bound, exactly as in `gardingSharp_hG_of_jet`: apply the lemma at
`Kmax := max K Kjet`, where `Kjet` is the section-independent bound of
`Work.Diff.STE.Lead.mat_jet_uniform_bound D k₀ hk₀ (Cb · B₀)` (with `Cb` the constant of
`Work.Diff.STE.B3.BNorm_le_ENormB_unif D k₀`).  `hub` survives the passage to `Kmax`, and `hjet`
holds with `Kmax` because `Kjet ≤ Kmax`.  The resulting constant is allowed to depend on `B₀`,
which `LowEnergyData` permits (it is quantified inside). -/
theorem lowEnergyData_of
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ)
    (hk : 1 ≤ k) (hk2 : Module.finrank ℝ E + 4 ≤ k)
    (hk₀ : Module.finrank ℝ E + 4 < 2 * k₀) :
    Work.Diff.STE.Lead.GalTame.LowEnergyData (I := I) (M := M) D hLC k k₀ := by
  intro lam K B₀ hlam hK hB₀
  obtain ⟨Cb, hCb0, hCbb⟩ := Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k₀
  have hBnd0 : 0 ≤ Cb * B₀ := mul_nonneg hCb0 hB₀
  obtain ⟨Kjet, hKjetpos, hKjetb⟩ :=
    Work.Diff.STE.Lead.mat_jet_uniform_bound (I := I) (M := M) D k₀ hk₀ (Cb * B₀) hBnd0
  obtain ⟨C, hC0, hCb⟩ := Work.Diff.STE.Lead.GalTame.deTurck_low_energy (I := I) (M := M) D hLC k
    hk hk2 lam (max K Kjet) hlam (lt_of_lt_of_le hK (le_max_left _ _))
  refine ⟨C, hC0, fun h hsym hpos hsmooth hell hub hB => ?_⟩
  have hlev : ((k₀ : ℕ) : (WithTop ℕ∞)) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simpa using (le_top : ((k₀ : ℕ) : WithTop ℕ∞) ≤ ⊤)
  have hRper : ∀ (i : ι₀) (a b : Idx),
      ContDiff ℝ ((k₀ : ℕ) : (WithTop ℕ∞)) (D.Rper i h a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth i a b)).1.of_le hlev
  have hRperper : ∀ (i : ι₀) (a b : Idx), Work.Diff.STE.Periodic1 (D.Rper i h a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth i a b)).2
  have hLe : D.BNorm k₀ h ≤ Cb * B₀ := by
    calc D.BNorm k₀ h ≤ Cb * (D.ENormB k₀ h + D.ENormB 0 h) := hCbb h hRper hRperper
      _ ≤ Cb * B₀ := mul_le_mul_of_nonneg_left hB hCb0
  refine hCb h hsym hpos hsmooth hell ?_ ?_
  · intro x v
    have hvnn : 0 ≤ g₀.inner x v v := by
      rcases eq_or_ne v 0 with hv | hv
      · rw [hv]; simp
      · exact le_of_lt (g₀.pos x v hv)
    exact le_trans (hub x v) (mul_le_mul_of_nonneg_right (le_max_left _ _) hvnn)
  · intro i c d r z hz
    exact le_trans (hKjetb h hsmooth hLe i c d r z hz) (le_max_right _ _)

/-- **The final assembly.**  All the analytic inputs are hypotheses:

* `hJN` is the target's own `hJN`;
* `hseed` is the conclusion of `Work.Diff.STE.B3.seed_margin` (with `hJT`), stated here;
* `hGS k _` is `Work.Diff.STE.Lead.GalTame.GardingSharpData` (from `galTame/gardingSharp`, with the
  defect `DefectData` supplied);
* `hComm k` is `Work.Diff.STE.Lead.GalTame.CommData` (from `Work.Diff.STE.Lead.Gal.galE_comm`);
* `hGk`/`hLowk` are the level-`k` Gårding and low-energy data (from `GalTame/gardingSharp_hG_of_jet`
  and `GalTame/lowEnergyData_of` respectively);
* `hApr` is the conclusion of `GalTame/hapr_of_aPrioriL2`;
* `hTrap` is the conclusion of `GalTame/galerkin_trapped_strong` (with `ε₁ := min εs 1`).

The conclusion is `GalUniform hLC D ρ`, on the interval `[0, τ₀/2]` (shrinking the trap interval
makes the *closed* endpoint available, which is what `GalUniform` asks for). -/

theorem galUniform_of
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : LCSmooth I M)
    (ρ : (Idx → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Idx → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (hJN : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h)
    (εs : ℝ) (hεs : 0 < εs)
    (hseed : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ εs → ∀ (x : M) (v : TangentSpace I x),
      (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v)
    (k₀ : ℕ) (hk₀ : Module.finrank ℝ E + 12 < 2 * k₀)
    (hk₀4 : Module.finrank ℝ E + 4 ≤ k₀)
    (B : ℝ) (hB : D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) + 1 ≤ B)
    (hGS : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.GardingSharpData (I := I) (M := M) D hLC k k₀)
    (hComm : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.CommData (I := I) (M := M) D ρ k)
    (hGk : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.GardingData (I := I) (M := M) D hLC k k₀)
    (hLowk : ∀ k : ℕ, Module.finrank ℝ E + 4 ≤ k →
      Work.Diff.STE.Lead.GalTame.LowEnergyData (I := I) (M := M) D hLC k k₀)
    (hApr : ∃ Cof : ℝ → ℝ, (∀ lam : ℝ, 0 < lam → 0 ≤ Cof lam) ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k₀ ε (c t) ≤ (galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1)
    (hTrap : ∀ (Cof : ℝ → ℝ), (∀ lam : ℝ, 0 < lam → 0 ≤ Cof lam) →
      (∀ (lam : ℝ), 0 < lam → ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ min εs 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k₀ ε (c t) ≤ (galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1) →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ min εs 1 → ∃ c :
        ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
      IsGalSol hLC D ρ ε τ₀ c ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
        (1 / 4 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, galE D k₀ ε (c t) ≤ B)) :
    GalUniform hLC D ρ := by
  classical
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ D.ENormB k₀ (g₀.inner) := ENormB_nonneg_asm D k₀ _
    have h2 : 0 ≤ D.ENormB 0 (g₀.inner) := ENormB_nonneg_asm D 0 _
    linarith
  have hk₀' : Module.finrank ℝ E + 4 < 2 * k₀ := by omega
  -- the trap bounds
  obtain ⟨K, B₀, hKpos, hB₀0, hbnd⟩ := trapBounds D ρ hρ hg
    (fun k => hJN k) k₀ hk₀ B hB0
  -- the level constants of `ENormB_mono_level` and of `BNorm_le_ENormB_unif`
  obtain ⟨CW, hCW0, hCWb⟩ := Work.Diff.STE.Lead.GalTame.ENormB_mono_level (I := I) (M := M) D k₀
  let Cβ : ℕ → ℝ := fun (k : ℕ) =>
    (Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k).choose
  have hCβ0 : ∀ (k : ℕ), 0 ≤ Cβ k := fun (k : ℕ) =>
    (Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k).choose_spec.1
  have hCβb : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Idx), ContDiff ℝ k (D.Rper i h a b))
      (hper : ∀ (i : ι₀) (a b : Idx), Work.Diff.STE.Periodic1 (D.Rper i h a b)),
      D.BNorm k h ≤ Cβ k * (D.ENormB k h + D.ENormB 0 h) := fun (k : ℕ) =>
    (Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k).choose_spec.2
  -- the level-`k` data of `hJN`
  let hJNd : ℕ → ℝ := fun (m : ℕ) => (hJN m).choose
  have hJNd0 : ∀ (m : ℕ), 0 ≤ hJNd m := fun (m : ℕ) => (hJN m).choose_spec.1
  have hJNdb : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      D.BNorm m (D.J ρ ε h) ≤ hJNd m * D.BNorm m h :=
    fun (m : ℕ) ε hε hε1 h hsm => (hJN m).choose_spec.2 ε ⟨hε, hε1⟩ h hsm
  -- the per-level a priori estimates
  have hlev : ∀ (k : ℕ), Module.finrank ℝ E + 4 ≤ k → Module.finrank ℝ E + 12 < 2 * k →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (1 / 4 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k ε (c t) ≤ (galE D k ε (c 0) + 1) * Real.exp (C * t) - 1 := by
    intro (k : ℕ) hk4 hk
    obtain ⟨lam', Cg, hlam', hCg, hGbody⟩ := hGk k hk4 (1 / 4) K B₀ (by norm_num) hKpos hB₀0
    obtain ⟨Cl, hCl, hLowbody⟩ := hLowk k hk4 (1 / 4) K B₀ (by norm_num) hKpos hB₀0
    obtain ⟨CJ, hCJ, hJbody⟩ := hComm k hk4
    obtain ⟨C, hC0, hCmain⟩ :=
      Work.Diff.STE.Lead.GalTame.galE_apriori_L2 (I := I) (M := M) D hLC ρ hρ hρ0 hρs hρ1 hg
        k k₀ hk hk₀' (1 / 4) K B₀ (by norm_num) hKpos hB₀0 CJ hCJ hJbody hJNd hJNd0 hJNdb
        lam' Cg Cl hlam' hCg hCl hGbody hLowbody
    exact ⟨C, hC0, fun ε hε hε1 c T hT hode hpos hlow hE =>
      hCmain ε hε hε1 c T hT hode hpos hlow
        (fun t ht x v => (hbnd ε ⟨hε, hε1⟩ (c t) (hE t ht)).1 x v)
        (fun t ht => (hbnd ε ⟨hε, hε1⟩ (c t) (hE t ht)).2)⟩
  -- the level constant, relaxed so that it is defined for *every* `k` (the implication in
  -- the body is vacuous when the level conditions fail, in which case the constant is `0`)
  have hlevEx : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ((Module.finrank ℝ E + 4 ≤ k ∧ Module.finrank ℝ E + 12 < 2 * k) →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (1 / 4 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k ε (c t) ≤ (galE D k ε (c 0) + 1) * Real.exp (C * t) - 1) := by
    intro k
    by_cases h : (Module.finrank ℝ E + 4 ≤ k ∧ Module.finrank ℝ E + 12 < 2 * k)
    · obtain ⟨hk4, hk⟩ := h
      obtain ⟨C, hC0, hCb⟩ := hlev k hk4 hk
      exact ⟨C, hC0, fun _ => hCb⟩
    · exact ⟨0, le_refl 0, fun hh => absurd hh h⟩
  let ClevAll : ℕ → ℝ := fun k => (hlevEx k).choose
  have hClevAll0 : ∀ k : ℕ, 0 ≤ ClevAll k := fun k => (hlevEx k).choose_spec.1
  have hClevAllb : ∀ k : ℕ, (Module.finrank ℝ E + 4 ≤ k ∧ Module.finrank ℝ E + 12 < 2 * k) →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (1 / 4 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k ε (c t) ≤ (galE D k ε (c 0) + 1) * Real.exp (ClevAll k * t) - 1 :=
    fun k => (hlevEx k).choose_spec.2
  -- the trapping
  obtain ⟨Cof, hCof, hapri⟩ := hApr
  have hap : ∀ (lam : ℝ), 0 < lam → ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ min εs 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k₀ ε (c t) ≤ (galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1 :=
    fun lam hlam ε hε hε1 => hapri lam hlam ε hε (le_trans hε1 (min_le_right _ _))
  obtain ⟨τ₀, hτ₀pos, hsol⟩ := hTrap Cof hCof hap
  -- the output interval and the output level function
  set τ : ℝ := τ₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτle : τ ≤ τ₀ := by rw [hτdef]; linarith
  set Bk : ℕ → ℝ := fun k => max
    (Cβ k * ((D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1)
      * Real.exp (ClevAll k * τ₀) - 1))
    (Cβ k * ((CW + 3) * B)) with hBk
  refine ⟨min εs 1, lt_min hεs one_pos, τ, hτpos, 1 / 4, by norm_num, Bk, ?_⟩
  intro ε hεIoc
  obtain ⟨hε0, hε1⟩ := hεIoc
  obtain ⟨c, hIsGal, hode, hmargin, hEtrap⟩ := hsol ε hε0 hε1
  have hpos' : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε (c t))) x v v := fun t ht x v hv =>
    hIsGal.2.1 t ⟨ht.1, le_of_lt ht.2⟩ x v hv
  have hlow' : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      (1 / 4 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v := fun t ht x v =>
    hmargin t ⟨ht.1, le_of_lt ht.2⟩ x v
  have hc0 : galState D ε (c 0) = g₀.inner := by
    rw [hIsGal.1]
    ext x u v
    simp [galState, Work.Diff.STE.D.addSec_apply, Work.Diff.STE.D.genMap]
  refine ⟨c, isGalSol_mono hIsGal hτle, ?_⟩
  intro t ht
  have htIco : t ∈ Set.Ico (0 : ℝ) τ₀ :=
    ⟨ht.1, lt_of_le_of_lt ht.2 (by rw [hτdef]; linarith [hτ₀pos])⟩
  refine ⟨fun k => ?_, fun x v => hmargin t ⟨ht.1, le_trans ht.2 hτle⟩ x v⟩
  have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D ε (c t)) :=
    chartData_galState (I := I) (M := M) D ε hg (c t)
  have hsm : ∀ (i : ι₀) (a b : Idx), ContDiff ℝ k (D.Rper i (galState D ε (c t)) a b) := by
    intro i a b
    refine (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i
      (galState D ε (c t)) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hcd i a b)).1.of_le ?_
    simpa using (le_top : ((k : ℕ) : (WithTop ℕ∞)) ≤ ⊤)
  have hper : ∀ (i : ι₀) (a b : Idx),
      Work.Diff.STE.Periodic1 (D.Rper i (galState D ε (c t)) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i
      (galState D ε (c t)) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hcd i a b)).2
  have h7 := hCβb k (galState D ε (c t)) hsm hper
  by_cases hbig : Module.finrank ℝ E + 4 ≤ k ∧ Module.finrank ℝ E + 12 < 2 * k
  · obtain ⟨hk4, hk⟩ := hbig
    have h1 := hClevAllb k ⟨hk4, hk⟩ ε hε0 (le_trans hε1 (min_le_right _ _)) c τ₀ hτ₀pos
      hode hpos' hlow' hEtrap t htIco
    have h2 : galE D k ε (c 0) = D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) := by
      simp only [galE, hc0]
    have h3 : Real.exp (ClevAll k * t) ≤ Real.exp (ClevAll k * τ₀) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans ht.2 hτle) (hClevAll0 k))
    have h5 : 0 ≤ D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1 := by
      have h6 : 0 ≤ D.ENormB k (g₀.inner) := ENormB_nonneg_asm D k _
      have h7' : 0 ≤ D.ENormB 0 (g₀.inner) := ENormB_nonneg_asm D 0 _
      linarith
    have h6 : galE D k ε (c t) ≤ (D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1)
        * Real.exp (ClevAll k * τ₀) - 1 := by
      rw [h2] at h1
      have h8 : (D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1) * Real.exp (ClevAll k * t)
          ≤ (D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1) * Real.exp (ClevAll k * τ₀) :=
        mul_le_mul_of_nonneg_left h3 h5
      linarith
    calc D.BNorm k (galState D ε (c t))
        ≤ Cβ k * (D.ENormB k (galState D ε (c t)) + D.ENormB 0 (galState D ε (c t))) := h7
      _ = Cβ k * galE D k ε (c t) := rfl
      _ ≤ Cβ k * ((D.ENormB k (g₀.inner) + D.ENormB 0 (g₀.inner) + 1)
            * Real.exp (ClevAll k * τ₀) - 1) := mul_le_mul_of_nonneg_left h6 (hCβ0 k)
      _ ≤ Bk k := by rw [hBk]; exact le_max_left _ _
  · -- small `k`: monotonicity of the levels plus the trap
    have hk0 : k ≤ k₀ := by
      by_cases h4 : Module.finrank ℝ E + 4 ≤ k
      · omega
      · omega
    have hE0 : D.ENormB 0 (galState D ε (c t)) ≤ B := by
      have h1 : D.ENormB k₀ (galState D ε (c t)) + D.ENormB 0 (galState D ε (c t)) ≤ B :=
        hEtrap t htIco
      have h2 : 0 ≤ D.ENormB k₀ (galState D ε (c t)) := ENormB_nonneg_asm D k₀ _
      linarith
    have hBle : B ≤ (CW + 3) * B := by
      have h11 : (1 : ℝ) ≤ CW + 3 := by linarith
      calc B = 1 * B := by ring
        _ ≤ (CW + 3) * B := mul_le_mul_of_nonneg_right h11 hB0
    have h8 : D.ENormB k (galState D ε (c t)) + D.ENormB 0 (galState D ε (c t)) ≤ (CW + 3) * B := by
      have hmid : CW * B + B ≤ (CW + 3) * B := by nlinarith [hB0]
      rcases Nat.eq_zero_or_pos k with hkz | hkp
      · rw [hkz]
        have hmid2 : (2 : ℝ) * B ≤ (CW + 3) * B := by
          have h12 : (2 : ℝ) ≤ CW + 3 := by linarith
          exact mul_le_mul_of_nonneg_right h12 hB0
        linarith [hE0, hmid2]
      · have h1 := hCWb (galState D ε (c t)) hcd k hkp hk0
        have h2 : D.ENormB k₀ (galState D ε (c t)) ≤ B := by
          have h3 : D.ENormB k₀ (galState D ε (c t)) + D.ENormB 0 (galState D ε (c t)) ≤ B :=
            hEtrap t htIco
          have h4 : 0 ≤ D.ENormB 0 (galState D ε (c t)) := ENormB_nonneg_asm D 0 _
          linarith
        have h3 : D.ENormB k (galState D ε (c t)) ≤ CW * B :=
          le_trans h1 (mul_le_mul_of_nonneg_left h2 hCW0)
        linarith [h3, hE0, hmid]
    calc D.BNorm k (galState D ε (c t))
        ≤ Cβ k * (D.ENormB k (galState D ε (c t)) + D.ENormB 0 (galState D ε (c t))) := h7
      _ = Cβ k * galE D k ε (c t) := rfl
      _ ≤ Cβ k * ((CW + 3) * B) := mul_le_mul_of_nonneg_left h8 (hCβ0 k)
      _ ≤ Bk k := by rw [hBk]; exact le_max_right _ _

end

end Work.Diff.STE.Lead
