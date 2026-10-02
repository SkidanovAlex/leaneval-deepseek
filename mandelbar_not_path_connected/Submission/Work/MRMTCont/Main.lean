/-
Work.MRMTCont — **continuity of the principal solution of the Beltrami equation under a.e.
convergence of the coefficients** (item S1 of `Submission/Work/NOTES_LEAD_mandelbar_simple.md`,
§3.1).

The measurable Riemann mapping theorem associates to an admissible Beltrami coefficient `μ` a
normalised homeomorphism `principal μ` of `ℂ`.  This file proves that the map `μ ↦ principal μ`
is continuous along an a.e.-convergent sequence of coefficients which is uniformly bounded by
`k < 1` and uniformly supported in a fixed ball:

`Work.MRMT.Found.principal_tendsto_of_ae`.

The proof is the classical diagonal argument:

1. For each `j`, `exists_approx_of_admissible` produces a *uniform* approximating family
   `ν j n → μs j` (smooth, compactly supported, bounded by `max k 0`, supported in the fixed ball
   of radius `max R 0 + 1`) together with `C¹` solutions `F j n` of the Beltrami equation, and
   `F j n → principal (μs j)` locally uniformly (`tendsto_principal_of_approx`).
2. Choose `n j` so that, on the disc of radius `j`, `F j (n j)` is within `1/(j+1)` of
   `principal (μs j)`, and so that the measure of the set where `ν j (n j)` differs from `μs j`
   by more than `1/(j+1)` is at most `2^{-(j+1)}` (a.e. convergence implies convergence in
   measure on the fixed ball, which has finite volume).
3. By Borel–Cantelli, `ν j (n j) → μ` a.e.
4. The key identity `tendsto_principal_of_approx` applied to the diagonal family gives
   `F j (n j) → principal μ` locally uniformly.
5. The triangle inequality upgrades this to `principal (μs j) → principal μ` locally uniformly.

The last two steps consume the four independent analytic lemmas in this directory
(`Work.MRMTCont.of_eventually_dist_le`, `…eventually_forall_dist_le_of_tendstoLocallyUniformly`,
`…eventually_volume_lt_of_tendstoInMeasure`, `…ae_tendsto_of_ae_tendsto_and_measure_bound`).
-/
import Mathlib
import Submission.Work.MRMTCont.ExistsApprox
import Submission.Work.MRMTCont.of_eventually_dist_le
import Submission.Work.MRMTCont.eventually_forall_dist_le_of_tendstoLocallyUniformly
import Submission.Work.MRMTCont.eventually_volume_lt_of_tendstoInMeasure
import Submission.Work.MRMTCont.ae_tendsto_of_ae_tendsto_and_measure_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

open Work.MRMT

/-- **S1 (MRMT-CONT), the strong form.**  The principal solutions of a sequence of Beltrami
coefficients converge locally uniformly to the principal solution of the limit coefficient, as
soon as the coefficients are admissible, uniformly bounded by a common `k < 1`, uniformly
supported in a fixed ball, and converge almost everywhere.

Note that no support hypothesis on the *limit* coefficient is needed: the limit enters only through
its a.e. bound. -/
theorem principal_tendsto_of_ae_of_bound {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}
    (hμs : ∀ j, Admissible (μs j)) (hμ : Admissible μ) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂MeasureTheory.volume, ‖μs j z‖ ≤ k)
    (hbμ : ∀ᵐ z ∂MeasureTheory.volume, ‖μ z‖ ≤ k)
    (hT : ∀ᵐ z ∂MeasureTheory.volume, Tendsto (fun j => μs j z) atTop (𝓝 (μ z))) :
    TendstoLocallyUniformly (fun j => (principal (μs j) : ℂ → ℂ)) (principal μ) atTop := by
  classical
  -- ## 0. common constants
  have hk0 : (0 : ℝ) ≤ max k 0 := le_max_right _ _
  have hk1 : max k 0 < 1 := max_lt hk zero_lt_one
  have hR0 : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hsupp' : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 (max R 0) :=
    fun j => (hsupp j).trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  have hb' : ∀ j, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖μs j z‖ ≤ max k 0 :=
    fun j => (hb j).mono fun z hz => hz.trans (le_max_left k 0)
  have hbμ' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ max k 0 :=
    hbμ.mono fun z hz => hz.trans (le_max_left k 0)
  -- ## 1. a uniform approximating family for each coefficient
  have hex : ∀ j, ∃ (ν : ℕ → ℂ → ℂ) (F : ℕ → ℂ ≃ₜ ℂ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ν n)) ∧
      (∀ n, HasCompactSupport (ν n)) ∧
      (∀ n z, ‖ν n z‖ ≤ max k 0) ∧
      (∀ n z, ν n z ≠ 0 → ‖z‖ ≤ max R 0 + 1) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Tendsto (fun n => ν n z) atTop (𝓝 (μs j z))) ∧
      (∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ)) ∧
      (∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ)) ∧
      (∀ n z, dzbar (F n : ℂ → ℂ) z = ν n z * dz (F n : ℂ → ℂ) z) ∧
      (∀ n, ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖F n z - z‖ ≤ C / ‖z‖) ∧
      TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) (principal (μs j) : ℂ → ℂ) atTop :=
    fun j => exists_approx_of_admissible (hμs j) hk0 hk1 hR0 (hsupp' j) (hb' j)
  choose ν F hν1 hν2 hν3 hν4 hν5 hF1 hF2 hF3 hF4 hFconv using hex
  -- ## 2. the two eventual selection facts
  have hev1 : ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ (j : ℝ) →
      dist (F j n z) (principal (μs j) z) ≤ 1 / ((j : ℝ) + 1) :=
    fun j => Work.MRMTCont.eventually_forall_dist_le_of_tendstoLocallyUniformly
      (F := fun j n => (F j n : ℂ → ℂ))
      (g := fun j => (principal (μs j) : ℂ → ℂ)) hFconv j
  have hev2 : ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - μs j z‖} ≤ (1 / 2 : ENNReal) ^ (j + 1) := by
    intro j
    haveI : IsFiniteMeasure
        ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict
          (Metric.closedBall 0 (max R 0 + 1))) :=
      isFiniteMeasure_restrict.mpr
        (isCompact_closedBall (0 : ℂ) (max R 0 + 1)).measure_lt_top.ne
    refine Work.MRMTCont.eventually_volume_lt_of_tendstoInMeasure
      (ν := ν) (g := μs) (B := Metric.closedBall 0 (max R 0 + 1)) ?_ ?_ ?_ ?_ j
    · exact (isCompact_closedBall (0 : ℂ) (max R 0 + 1)).isClosed.measurableSet
    · intro j' n
      exact ((hν1 j' n).continuous.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · intro j'
      exact Filter.Eventually.filter_mono (ae_mono Measure.restrict_le_self) (hν5 j')
    · intro j' n z hz
      have hne : ν j' n z ≠ 0 ∨ μs j' z ≠ 0 := by
        by_contra h
        push_neg at h
        exact hz (by simp [h.1, h.2])
      rw [Metric.mem_closedBall, dist_zero_right]
      rcases hne with h1 | h1
      · have h2 := hν4 j' n z h1
        linarith [le_max_left R 0]
      · have h2 := hsupp' j' h1
        rw [Metric.mem_closedBall, dist_zero_right] at h2
        linarith [le_max_left R 0]
  -- ## 3. the diagonal choice
  have hsel : ∀ j : ℕ, ∃ n : ℕ,
      (∀ z : ℂ, ‖z‖ ≤ (j : ℝ) → dist (F j n z) (principal (μs j) z) ≤ 1 / ((j : ℝ) + 1)) ∧
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ)
        {z : ℂ | 1 / ((j : ℝ) + 1) < ‖ν j n z - μs j z‖} ≤ (1 / 2 : ENNReal) ^ (j + 1)) :=
    fun j => ((hev1 j).and (hev2 j)).exists
  choose n hn using hsel
  -- ## 4. Borel–Cantelli: the diagonal coefficients converge to `μ` a.e.
  have ha : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : (tsum fun j : ℕ => (1 / 2 : ENNReal) ^ (j + 1)) ≠ ⊤ := by
    have hhalf : (1 / 2 : ENNReal) = 2⁻¹ := by norm_num
    have h2 : (tsum fun j : ℕ => (1 / 2 : ENNReal) ^ (j + 1)) = 1 := by
      rw [hhalf, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [h2]
    exact ENNReal.one_ne_top
  have hdiagT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun j => ν j (n j) z) atTop (𝓝 (μ z)) :=
    Work.MRMTCont.ae_tendsto_of_ae_tendsto_and_measure_bound
      (f := fun j => ν j (n j)) (g := μs) (w := μ) (a := fun j : ℕ => 1 / ((j : ℝ) + 1))
      (c := fun j : ℕ => (1 / 2 : ENNReal) ^ (j + 1)) hT ha hc fun j => (hn j).2
  -- ## 5. the key identity applied to the diagonal family
  have hdiagF : TendstoLocallyUniformly (fun j => (F j (n j) : ℂ → ℂ))
      (principal μ : ℂ → ℂ) atTop :=
    tendsto_principal_of_approx (μ := μ) (k := max k 0) (M := max R 0 + 1) hμ hk0 hk1
      (by linarith)
      (fun j => hν1 j (n j)) (fun j => hν2 j (n j)) (fun j z => hν3 j (n j) z)
      (fun j z => hν4 j (n j) z) hdiagT hbμ'
      (fun j => hF1 j (n j)) (fun j => hF2 j (n j)) (fun j z => hF3 j (n j) z)
      (fun j => hF4 j (n j))
  -- ## 6. triangle inequality
  exact Work.MRMTCont.of_eventually_dist_le
    (F := fun j => (F j (n j) : ℂ → ℂ))
    (G := fun j => (principal (μs j) : ℂ → ℂ))
    (f := (principal μ : ℂ → ℂ)) (a := fun j : ℕ => 1 / ((j : ℝ) + 1))
    hdiagF ha (Filter.Eventually.of_forall fun j z hz => by
      rw [dist_comm]
      exact (hn j).1 z hz)

/-- **S1 (MRMT-CONT)**, exactly as stated in `Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3.1
(whose `hsuppμ` hypothesis is superfluous, see `principal_tendsto_of_ae_of_bound`): the principal
solutions of a sequence of Beltrami coefficients converge locally uniformly to the principal
solution of the limit coefficient whenever the coefficients are admissible, uniformly bounded by a
common `k < 1`, uniformly supported in a fixed ball, and converge almost everywhere. -/
theorem principal_tendsto_of_ae {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}
    (hμs : ∀ j, Admissible (μs j)) (hμ : Admissible μ) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hsuppμ : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂MeasureTheory.volume, ‖μs j z‖ ≤ k)
    (hbμ : ∀ᵐ z ∂MeasureTheory.volume, ‖μ z‖ ≤ k)
    (hT : ∀ᵐ z ∂MeasureTheory.volume, Tendsto (fun j => μs j z) atTop (𝓝 (μ z))) :
    TendstoLocallyUniformly (fun j => (principal (μs j) : ℂ → ℂ)) (principal μ) atTop :=
  principal_tendsto_of_ae_of_bound hμs hμ hk hsupp hb hbμ hT

/-- **The pointwise form of `principal_tendsto_of_ae`.**  This is the form consumed downstream:
`z ↦ principal (μs j) z → principal μ z` for every `z`. -/
theorem principal_tendsto_of_ae_apply {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}
    (hμs : ∀ j, Admissible (μs j)) (hμ : Admissible μ) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hsuppμ : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂MeasureTheory.volume, ‖μs j z‖ ≤ k)
    (hbμ : ∀ᵐ z ∂MeasureTheory.volume, ‖μ z‖ ≤ k)
    (hT : ∀ᵐ z ∂MeasureTheory.volume, Tendsto (fun j => μs j z) atTop (𝓝 (μ z)))
    (z : ℂ) :
    Tendsto (fun j => principal (μs j) z) atTop (𝓝 (principal μ z)) :=
  (tendstoLocallyUniformlyOn_univ.mpr
    (principal_tendsto_of_ae hμs hμ hk hsupp hsuppμ hb hbμ hT)).tendsto_at (Set.mem_univ z)

/-- The pointwise form of `principal_tendsto_of_ae`, quantified over all `z`. -/
theorem principal_tendsto_of_ae_pointwise {μs : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}
    (hμs : ∀ j, Admissible (μs j)) (hμ : Admissible μ) {R k : ℝ} (hk : k < 1)
    (hsupp : ∀ j, Function.support (μs j) ⊆ Metric.closedBall 0 R)
    (hsuppμ : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ j, ∀ᵐ z ∂MeasureTheory.volume, ‖μs j z‖ ≤ k)
    (hbμ : ∀ᵐ z ∂MeasureTheory.volume, ‖μ z‖ ≤ k)
    (hT : ∀ᵐ z ∂MeasureTheory.volume, Tendsto (fun j => μs j z) atTop (𝓝 (μ z))) :
    ∀ z : ℂ, Tendsto (fun j => principal (μs j) z) atTop (𝓝 (principal μ z)) :=
  fun z => principal_tendsto_of_ae_apply hμs hμ hk hsupp hsuppμ hb hbμ hT z

end Work.MRMT.Found
