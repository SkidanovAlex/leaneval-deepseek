import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.BoseBand.NeuBilAux
import Submission.Work.Analysis.BoseBand.exists_finrank_partition_approx
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.neuFrac_offdiag_integral` — the off-diagonal `u`-integral of the
Neumann fraction

The target is

`∫_{y ∈ Λ} [ Q(c + G(·,y)) − Q(c − G(·,y)) ] dy = 0`,   `Q := neuFrac ℓ a² 0`, `Λ = acube ℓ`,

for `c` smooth and `G` continuous with `∫_{y∈Λ} G(z,y) dy = 0` for every `z` (and pointwise
bounds `R`).

## The argument

`Q(c+G) − Q(c−G) = 4·B(c, G)` for the polar (bilinear) form `B := Work.BoseFixB2.DvApriori.neuBil` of `Q`, so the task
is to show `∫_y B(c, G(·,y)) dy = 0`, i.e. that the linear functional `L := B(c, ·)` commutes
with the `y`-integral; the mean-zero hypothesis says that the *function* `z ↦ ∫_y G(z,y) dy`
vanishes.

1. **Finite-rank approximation** (`exists_finrank_partition_approx`): for every `ε > 0` there
   are continuous weights `θ i` and smooth `p i` with
   `|G(z,y) − ∑_i θ_i(y) p_i(z)| ≤ ε` on `Λ × Λ`  (three-variable Stone–Weierstrass on the
   compact cube together with a partition of unity).
2. **Finite-rank values** (`neuBil_sum_expansion`): `L` is additive and `ℝ`-homogeneous on
   smooth states, so `L(∑_i θ_i(y) p_i) = ∑_i θ_i(y) L(p_i)`, and integrating in `y` gives
   `∫_y L(P(·,y)) dy = L(∑_i (∫_y θ_i) p_i) = L(∫_y P(·,y) dy)` for `P = ∑_i θ_i p_i`.
3. **Estimates** (`neuBil_sup_lipschitz`, `continuousOn_neuBil_family`): `L` is Lipschitz for
   the sup norm on `Λ`, with a constant `K` uniform in the states, and `y ↦ L(G(·,y))` is
   integrable.  Hence `|∫_y L(G(·,y)) dy − L(∫_y P(·,y) dy)| ≤ K ε |Λ|`, while the mean-zero
   hypothesis gives `L(∫_y P(·,y) dy) = L(∫_y (P−G)(·,y) dy)`, also `≤ K ε |Λ|`.  The integral
   is therefore `≤ 2Kε|Λ|` for every `ε ∈ (0,1]`, hence `0`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.Analysis.BoseBand

set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-- The zero function vanishes. -/
lemma zero_fun_apply (x : EuclideanSpace ℝ (Fin 3)) :
    (0 : EuclideanSpace ℝ (Fin 3) → ℝ) x = 0 := rfl

/-- `|0| ≤ S` for the zero function, for `0 ≤ S`. -/
lemma abs_zero_fun_le {S : ℝ} (hS : 0 ≤ S) (x : EuclideanSpace ℝ (Fin 3)) :
    |(0 : EuclideanSpace ℝ (Fin 3) → ℝ) x| ≤ S := by
  rw [zero_fun_apply x, abs_zero]; exact hS

/-- **The key estimate.**  For every `ε ∈ (0,1]` the integral over the cube of
`Work.BoseFixB2.DvApriori.neuBil ℓ a² 0 c (G · y)` is bounded by `2Kε|Λ|`, with the constant
`K = 3(2S√(ℓ³)+1)√(ℓ³)`, `S = 2R + 1 + |Λ|`, of `neuBil_sup_lipschitz`. -/
lemma neuBil_integral_le {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    {c : EuclideanSpace ℝ (Fin 3) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2)
    (hcR : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ R)
    (hGR : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ, |G z y| ≤ R)
    (hmean : ∀ z, ∫ y in Submission.BoseGases.acube ℓ, G z y = 0)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)|
      ≤ 2 * (3 * (2 * (2 * R + 1 + acubeVol ℓ) * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3))
          * acubeVol ℓ * ε := by
  classical
  have hΛm : MeasurableSet (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_measurable ℓ
  have hΛc : IsCompact (Submission.BoseGases.acube ℓ) := Work.BoseFixB2.Polar.isCompact_acube_all ℓ
  have hΛfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.acube ℓ) < ⊤ :=
    Submission.BoseGases.acube_lt_top ℓ (le_of_lt hℓ)
  have hvr : 0 ≤ acubeVol ℓ := acubeVol_nonneg ℓ
  set S : ℝ := 2 * R + 1 + acubeVol ℓ with hSdef
  set K : ℝ := 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3) with hKdef
  have hSpos : 0 < S := by rw [hSdef]; linarith
  -- the finite-rank approximation
  obtain ⟨n, θ, p, hθc, hpc, happrox⟩ := exists_finrank_partition_approx (ℓ := ℓ) hℓ hG hε0
  set P : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun z y => ∑ i, θ i y * p i z with hPdef
  have hSc : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ S := by
    intro z hz; rw [hSdef]; linarith [hcR z hz]
  have hSG : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ,
      |G z y| ≤ S := by
    intro z hz y hy; rw [hSdef]; linarith [hGR z hz y hy]
  have hPG : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ,
      |G z y - P z y| ≤ ε := by
    intro z hz y hy
    simpa only [hPdef] using happrox z hz y hy
  have hPS : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ,
      |P z y| ≤ S := by
    intro z hz y hy
    have h1 : |P z y - G z y| ≤ ε := by
      simpa only [abs_sub_comm] using hPG z hz y hy
    have h2 := hGR z hz y hy
    have h3 : P z y = G z y + (P z y - G z y) := by ring
    rw [h3]
    calc |G z y + (P z y - G z y)| ≤ |G z y| + |P z y - G z y| := abs_add_le _ _
      _ ≤ R + ε := add_le_add h2 h1
      _ ≤ S := by rw [hSdef]; linarith
  -- the pointwise finite-sum expansion of `Work.BoseFixB2.DvApriori.neuBil` in the approximant
  have hexp : ∀ y, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)
      = ∑ i, θ i y * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (p i) := by
    intro y
    have h := neuBil_sum_expansion (ℓ := ℓ) (a2 := a2) hℓ ha2
      (Finset.univ : Finset (Fin n)) (fun i => θ i y) p hc (fun i _ => hpc i)
    simpa only [hPdef] using h
  have hQval : Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c
        (fun z => ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z)
      = ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (p i) :=
    neuBil_sum_expansion (ℓ := ℓ) (a2 := a2) hℓ ha2 (Finset.univ : Finset (Fin n))
      (fun i => ∫ y in Submission.BoseGases.acube ℓ, θ i y) p hc (fun i _ => hpc i)
  -- continuity in `y` of the two families
  have hcontGy : ∀ z : EuclideanSpace ℝ (Fin 3), Continuous (fun y => G z y) := by
    intro z
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin 3) => (z, p) :=
      continuous_const.prodMk continuous_id
    exact hG.comp h2
  have hcontGz : ∀ y : EuclideanSpace ℝ (Fin 3), Continuous (fun z => G z y) := by
    intro y
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin 3) => (p, y) :=
      continuous_id.prodMk continuous_const
    exact hG.comp h2
  have hcontPy : ∀ z : EuclideanSpace ℝ (Fin 3), Continuous (fun y => P z y) := by
    intro z
    rw [show (fun y => P z y) = fun y => ∑ i, θ i y * p i z from by
      funext y; simp only [hPdef]]
    exact continuous_finsetSum _ (fun i _ => (hθc i).mul continuous_const)
  have hcontPz : ∀ y : EuclideanSpace ℝ (Fin 3), Continuous (fun z => P z y) := by
    intro y
    rw [show (fun z => P z y) = fun z => ∑ i, θ i y * p i z from by
      funext z; simp only [hPdef]]
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hpc i).continuous)
  have hinteq : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube ℓ, P z y)
        = ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z := by
    intro z
    rw [show (∫ y in Submission.BoseGases.acube ℓ, P z y)
        = ∫ y in Submission.BoseGases.acube ℓ, ∑ i, θ i y * p i z from by
      refine MeasureTheory.setIntegral_congr_fun hΛm (fun y _ => ?_)
      simp only [hPdef]]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ =>
        MeasureTheory.integral_mul_const (p i z) (fun y => θ i y))
    · intro i _
      exact ((hθc i).mul continuous_const).continuousOn.integrableOn_compact hΛc
  have hint_const : Integrable
      (fun _ : EuclideanSpace ℝ (Fin 3) => ε) (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    refine (MeasureTheory.integrable_const_iff).mpr (Or.inr ?_)
    exact ⟨by rw [Measure.restrict_apply_univ]; exact hΛfin⟩
  -- the value of the approximant's integral is small
  have hQbound : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z| ≤ ε * acubeVol ℓ := by
    intro z hz
    rw [← hinteq z]
    have hsplit : (∫ y in Submission.BoseGases.acube ℓ, (P z y - G z y))
        = ∫ y in Submission.BoseGases.acube ℓ, P z y := by
      rw [MeasureTheory.integral_sub ((hcontPy z).continuousOn.integrableOn_compact hΛc)
        ((hcontGy z).continuousOn.integrableOn_compact hΛc), hmean z, sub_zero]
    rw [← hsplit]
    calc |∫ y in Submission.BoseGases.acube ℓ, (P z y - G z y)|
        ≤ ∫ y in Submission.BoseGases.acube ℓ, |P z y - G z y| := by
          simpa only [Real.norm_eq_abs] using
            MeasureTheory.norm_integral_le_integral_norm (fun y => P z y - G z y)
      _ ≤ ∫ y in Submission.BoseGases.acube ℓ, ε := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hint_const
            (MeasureTheory.ae_restrict_of_forall_mem hΛm (fun y hy => ?_))
          simpa only [abs_sub_comm] using hPG z hz y hy
      _ = ε * acubeVol ℓ := by
          rw [MeasureTheory.setIntegral_const, acubeVol, smul_eq_mul]
          ring
  have hLQ : |Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c
        (fun z => ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z)|
      ≤ K * (ε * acubeVol ℓ) := by
    have hcont : Continuous
        (fun z => ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z) :=
      continuous_finsetSum _ (fun i _ => continuous_const.mul (hpc i).continuous)
    have hb := neuBil_sup_lipschitz (ℓ := ℓ) (a2 := a2) (S := S) (δ := ε * acubeVol ℓ)
      (c := c) (f := fun z => ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z)
      (g := 0) hℓ ha2 hSpos (by positivity) hc.continuous hcont continuous_const hSc
      (fun z hz => by
        rw [hSdef]
        nlinarith [hQbound z hz, hvr, hε1, hε0.le, hR])
      (fun z hz => abs_zero_fun_le hSpos.le z)
      (fun z hz => by rw [zero_fun_apply z, sub_zero]; exact hQbound z hz)
    have hzero : Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (0 : EuclideanSpace ℝ (Fin 3) → ℝ) = 0 :=
      Work.BoseFixB2.DvApriori.neuBil_zero_right ℓ a2 0 c
    simpa only [hKdef, hzero, sub_zero] using hb
  -- integrability of the two families of `y`
  have hIntF : Integrable (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    refine MeasureTheory.IntegrableOn.of_bound hΛfin ?_ (K * S) ?_
    · exact (continuousOn_neuBil_family (ℓ := ℓ) (a2 := a2) (R := R) hℓ ha2 hR
        hc.continuous hG hcR hGR).aestronglyMeasurable hΛm
    · refine MeasureTheory.ae_restrict_of_forall_mem hΛm (fun y hy => ?_)
      have hb := neuBil_sup_lipschitz (ℓ := ℓ) (a2 := a2) (S := S) (δ := S)
        (c := c) (f := fun z => G z y) (g := 0)
        hℓ ha2 hSpos hSpos.le hc.continuous (hcontGz y) continuous_const hSc
        (fun z hz => hSG z hz y hy)
        (fun z hz => abs_zero_fun_le hSpos.le z)
        (fun z hz => by rw [zero_fun_apply z, sub_zero]; exact hSG z hz y hy)
      have hzero : Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (0 : EuclideanSpace ℝ (Fin 3) → ℝ) = 0 :=
        Work.BoseFixB2.DvApriori.neuBil_zero_right ℓ a2 0 c
      rw [Real.norm_eq_abs]
      simpa only [hzero, sub_zero, hKdef] using hb
  have hIntP : Integrable (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have hcont : Continuous (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)) := by
      rw [show (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
          = fun y => ∑ i, θ i y * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (p i) from funext hexp]
      exact continuous_finsetSum _ (fun i _ => (hθc i).mul continuous_const)
    exact hcont.continuousOn.integrableOn_compact hΛc
  -- the value of the approximant's integral
  have hPval : (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
      = ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (p i) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
        = ∫ y in Submission.BoseGases.acube ℓ,
            ∑ i, θ i y * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (p i) from
      MeasureTheory.setIntegral_congr_fun hΛm (fun y _ => hexp y)]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ =>
        MeasureTheory.integral_mul_const _ (fun y => θ i y))
    · intro i _
      exact ((hθc i).mul continuous_const).continuousOn.integrableOn_compact hΛc
  have hPval' : (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
      = Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c
          (fun z => ∑ i, (∫ y in Submission.BoseGases.acube ℓ, θ i y) * p i z) :=
    hPval.trans hQval.symm
  -- the difference of the two integrals
  have hintK : Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => K * ε)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    refine (MeasureTheory.integrable_const_iff).mpr (Or.inr ?_)
    exact ⟨by rw [Measure.restrict_apply_univ]; exact hΛfin⟩
  have hdiff : |(∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
      - (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))|
      ≤ K * ε * acubeVol ℓ := by
    rw [← MeasureTheory.integral_sub hIntF hIntP]
    calc |∫ y in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y) - Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))|
        ≤ ∫ y in Submission.BoseGases.acube ℓ,
            |Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y) - Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)| := by
          simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
            (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y) - Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))
      _ ≤ ∫ y in Submission.BoseGases.acube ℓ, (K * ε) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hintK
            (MeasureTheory.ae_restrict_of_forall_mem hΛm (fun y hy => ?_))
          have hb := neuBil_sup_lipschitz (ℓ := ℓ) (a2 := a2) (S := S) (δ := ε)
            (c := c) (f := fun z => G z y) (g := fun z => P z y)
            hℓ ha2 hSpos hε0.le hc.continuous (hcontGz y) (hcontPz y) hSc
            (fun z hz => hSG z hz y hy) (fun z hz => hPS z hz y hy) (fun z hz => hPG z hz y hy)
          simpa only [hKdef] using hb
      _ = acubeVol ℓ * (K * ε) := by
          rw [MeasureTheory.setIntegral_const, acubeVol, smul_eq_mul]
      _ = K * ε * acubeVol ℓ := by ring
  -- assembly
  have hfinal : |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)|
      ≤ 2 * K * acubeVol ℓ * ε := by
    have hsplit : (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
        = ((∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
            - (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)))
          + (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)) := by ring
    calc |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)|
        = |((∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
            - (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)))
          + (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))| :=
          congrArg abs hsplit
      _ ≤ |(∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
            - (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y))|
          + |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => P z y)| :=
          abs_add_le _ _
      _ ≤ K * ε * acubeVol ℓ + K * (ε * acubeVol ℓ) :=
          add_le_add hdiff (by rw [hPval']; exact hLQ)
      _ = 2 * K * acubeVol ℓ * ε := by ring
  exact hfinal

/-- **The off-diagonal integral vanishes.**  With `c` smooth, `G` continuous and bounded by `R`
on the cube, with vanishing `y`-mean in the sense `∫_{Λ} G(z,y) dy = 0` for every `z`, the
integral over `Λ` of the antisymmetric combination `Q(c+G) − Q(c−G)` of the box
Neumann-resolvent fraction vanishes. -/
theorem neuFrac_offdiag_integral {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    {c : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hG : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2)
    (hcR : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ R)
    (hGR : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ, |G z y| ≤ R)
    (hmean : ∀ z, ∫ y in Submission.BoseGases.acube ℓ, G z y = 0) :
    (∫ y in Submission.BoseGases.acube ℓ,
      (Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z + G z y)
        - Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z - G z y))) = 0 := by
  classical
  -- the pointwise polarisation identity
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin 3),
      (Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z + G z y)
        - Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z - G z y))
      = 4 * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y) := by
    intro y
    simp only [Work.BoseFixB2.DvApriori.neuBil]
    ring
  have hstep : (∫ y in Submission.BoseGases.acube ℓ,
        (Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z + G z y)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z - G z y)))
      = 4 * (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)) := by
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          (Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z + G z y)
            - Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => c z - G z y)))
        = ∫ y in Submission.BoseGases.acube ℓ, 4 * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y) from
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun y _ => hpoint y)]
    exact MeasureTheory.integral_const_mul 4 _
  rw [hstep]
  have hJ : (∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)) = 0 := by
    set C : ℝ := 2 * (3 * (2 * (2 * R + 1 + acubeVol ℓ) * Real.sqrt (ℓ ^ 3) + 1)
      * Real.sqrt (ℓ ^ 3)) * acubeVol ℓ with hCdef
    have hCnn : 0 ≤ C := by
      rw [hCdef]
      have hsqrt : 0 ≤ Real.sqrt (ℓ ^ 3) := Real.sqrt_nonneg _
      have hvrn : 0 ≤ acubeVol ℓ := acubeVol_nonneg ℓ
      have h1 : 0 ≤ 2 * (2 * R + 1 + acubeVol ℓ) * Real.sqrt (ℓ ^ 3) + 1 := by
        nlinarith [hsqrt, hvrn, hR]
      have h2 : (0 : ℝ) ≤ 3 * (2 * (2 * R + 1 + acubeVol ℓ) * Real.sqrt (ℓ ^ 3) + 1)
          * Real.sqrt (ℓ ^ 3) := mul_nonneg (mul_nonneg (by norm_num) h1) hsqrt
      exact mul_nonneg (mul_nonneg (by norm_num) h2) hvrn
    have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)| ≤ C * ε := by
      intro ε h0 h1
      have h := neuBil_integral_le hℓ ha2 hR hc hG hcR hGR hmean h0 h1
      rw [hCdef]
      exact h
    have hbound : |∫ y in Submission.BoseGases.acube ℓ, Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)| ≤ 0 := by
      refine le_of_forall_pos_le_add (fun η hη => ?_)
      set ε : ℝ := min (1 / 2) (η / (C + 1)) with hεdef
      have hε0 : 0 < ε := by
        rw [hεdef]
        exact lt_min (by norm_num) (div_pos hη (by linarith))
      have hε1 : ε ≤ 1 := by
        rw [hεdef]
        exact le_trans (min_le_left _ _) (by norm_num)
      have hle : C * ε ≤ η := by
        have h1 : ε ≤ η / (C + 1) := by rw [hεdef]; exact min_le_right _ _
        have h2 : 0 < C + 1 := by linarith
        have h3 : C * (η / (C + 1)) = C * η / (C + 1) := mul_div_assoc' C η (C + 1)
        have h4 : C * η / (C + 1) ≤ η := by
          rw [div_le_iff₀ h2]
          nlinarith [hη.le, hCnn]
        calc C * ε ≤ C * (η / (C + 1)) := mul_le_mul_of_nonneg_left h1 hCnn
          _ = C * η / (C + 1) := h3
          _ ≤ η := h4
      linarith [key ε hε0 hε1, hle]
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  rw [hJ, mul_zero]

end Work.Analysis.BoseBand
