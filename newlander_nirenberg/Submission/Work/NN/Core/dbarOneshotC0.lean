import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.dbarOneshotCk
import Submission.Work.NN.Final.oneshotClosedOnSelf

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set Filter
open Work.CR.Flat
open Work.CR.Flat.Cauchy

set_option maxHeartbeats 1000000

/-! ## A cutoff product of a locally `C¹` function is globally `C¹`

If `η` is smooth and vanishes as soon as one coordinate distance `‖z j - c j‖` reaches `r j`,
while `v` is `C¹` only on the polydisc of multiradius `ρ` with `r < ρ`, then `η · v` (continued
by `0` outside the support of `η`) is `C¹` on all of `ℂⁿ`: near every point either `η` is `1`-like
and `v` is `C¹` (inside the closed polydisc of multiradius `r`, which is contained in the open
polydisc of multiradius `ρ`), or `η` vanishes on a neighbourhood. -/
private lemma contDiff_one_mul_of_contDiffOn {n : ℕ} {c : Fin n → ℂ} {ρ r : Fin n → ℝ}
    (hrρ : ∀ j, r j < ρ j) {η : (Fin n → ℂ) → ℝ}
    (hηsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hη0 : ∀ z, (∃ j, r j ≤ ‖z j - c j‖) → η z = 0)
    {v : (Fin n → ℂ) → ℂ} (hv : ContDiffOn ℝ 1 v (polydisc c ρ)) :
    ContDiff ℝ 1 (fun z => (η z : ℂ) * v z) := by
  have hηC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (η z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηsm
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hcover : ∀ i, ‖z i - c i‖ ≤ r i
  · have hzρ : z ∈ polydisc c ρ := fun i => lt_of_le_of_lt (hcover i) (hrρ i)
    have h1 : ContDiffAt ℝ 1 (fun y => (η y : ℂ)) z := (hηC.contDiffAt).of_le (by simp)
    have h2 : ContDiffAt ℝ 1 v z := hv.contDiffAt ((isOpen_polydisc c ρ).mem_nhds hzρ)
    simpa using h1.mul h2
  · push Not at hcover
    obtain ⟨i, hi⟩ := hcover
    have hev : (fun y => (η y : ℂ) * v y) =ᶠ[nhds z] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hi)] with y hy
      have hyi : r i ≤ ‖y i - c i‖ := by
        have h1 : ‖y i - z i‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) i
        have h2 : ‖z i - c i‖ ≤ ‖y i - c i‖ + ‖y i - z i‖ := by
          calc ‖z i - c i‖ = ‖(z i - y i) + (y i - c i)‖ := by ring_nf
            _ ≤ ‖z i - y i‖ + ‖y i - c i‖ := norm_add_le _ _
            _ = ‖y i - c i‖ + ‖y i - z i‖ := by
                rw [norm_sub_rev (z i) (y i), add_comm]
        have h3 : ‖y - z‖ < ‖z i - c i‖ - r i := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hy
        linarith
      simp only [hη0 y ⟨i, hyi⟩, Complex.ofReal_zero, zero_mul]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

theorem dbarOneshotC0 {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc c ρo) →
      (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc c ρo)) →
      (∀ j l (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc c ρo →
        Work.CR.Flat.dbarCoord l (f j) z = Work.CR.Flat.dbarCoord j (f l) z) →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) →
        Work.CR.Flat.dbarCoord j u z = f j z) →
      Work.CR.Flat.holderNorm 1 α u (Work.CR.Flat.polydisc c ρi)
        ≤ ENNReal.ofReal C *
            ((∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc c ρo))
              + Work.CR.Flat.holderNorm 0 α u (Work.CR.Flat.polydisc c ρo)) := by
  classical
  -- ### intermediate multiradii: `ρi < ρs < A < B < ρo`
  set M : Fin n → ℝ := fun j => max (ρi j) 0 with hM
  set ρs : Fin n → ℝ := fun j => M j + (ρo j - M j) / 4 with hρs
  set A : Fin n → ℝ := fun j => M j + (ρo j - M j) / 2 with hA
  set B : Fin n → ℝ := fun j => M j + 3 * (ρo j - M j) / 4 with hB
  have hMlt : ∀ j, M j < ρo j := fun j => max_lt (hlt j) (hρo j)
  have hd : ∀ j, 0 < ρo j - M j := fun j => by linarith [hMlt j]
  have hMnn : ∀ j, 0 ≤ M j := fun j => le_max_right _ _
  have hρs_pos : ∀ j, 0 < ρs j := by
    intro j; have h := hd j; simp only [hρs]; linarith [hMnn j]
  have hA_pos : ∀ j, 0 < A j := by
    intro j; have h := hd j; simp only [hA]; linarith [hMnn j]
  have hB_pos : ∀ j, 0 < B j := by
    intro j; have h := hd j; simp only [hB]; linarith [hMnn j]
  have hρiρs : ∀ j, ρi j < ρs j := by
    intro j; have h1 : ρi j ≤ M j := le_max_left _ _; have h := hd j
    simp only [hρs]; linarith
  have hρsA : ∀ j, ρs j < A j := by
    intro j; have h := hd j; simp only [hρs, hA]; linarith
  have hAB : ∀ j, A j < B j := by
    intro j; have h := hd j; simp only [hA, hB]; linarith
  have hAρo : ∀ j, A j < ρo j := by
    intro j; have h := hd j; simp only [hA]; linarith [hMnn j]
  have hBρo : ∀ j, B j < ρo j := by
    intro j; have h := hd j; simp only [hB]; linarith [hMnn j]
  have hρsρo : ∀ j, ρs j < ρo j := fun j => lt_trans (hρsA j) (hAρo j)
  have hρiA : ∀ j, ρi j < A j := fun j => lt_trans (hρiρs j) (hρsA j)
  -- ### the interior Schauder estimate for the pair `P(ρi) ⊂ P(ρs)`
  obtain ⟨C, hCpos, hC⟩ :=
    Work.NN.Final.oneshotClosedOnSelf hn (c := c) (ρi := ρi) (ρo := ρs)
      hρiρs hρs_pos hα hα1 0
  refine ⟨C, hCpos, ?_⟩
  intro u f hu hf hfcl heq
  -- ### a cutoff which is `1` on `P(A)` and vanishes beyond `B`
  obtain ⟨η, hηsm, _hη01, hη1, hη0, _hηcs, _hηdsm, _hηdcs⟩ :=
    polydiscCutoff (n := n) (c := c) (r₁ := A) (r₂ := B) 0 hA_pos hAB
  have hηA : ∀ z, (∀ i, ‖z i - c i‖ < A i) → η z = 1 :=
    fun z hz => hη1 z (fun i => le_of_lt (hz i))
  set ηC : (Fin n → ℂ) → ℂ := fun z => (η z : ℂ) with hηC
  set ut : (Fin n → ℂ) → ℂ := fun z => ηC z * u z with hut
  set ft : Fin n → (Fin n → ℂ) → ℂ := fun j z => ηC z * f j z with hft
  -- ### the localised data is globally `C¹`
  have hut_sm : ContDiff ℝ 1 ut := by
    have h := contDiff_one_mul_of_contDiffOn (c := c) (ρ := ρo) (r := B) hBρo hηsm hη0 hu
    simpa only [hut, hηC] using h
  have hft_sm : ∀ j, ContDiff ℝ 1 (ft j) := by
    intro j
    have h := contDiff_one_mul_of_contDiffOn (c := c) (ρ := ρo) (r := B) hBρo hηsm hη0 (hf j)
    simpa only [hft, hηC] using h
  -- ### the localised data satisfies the equation on `P(ρs)`
  have heq' : ∀ j z, z ∈ polydisc c ρs → dbarCoord j ut z = ft j z := by
    intro j z hz
    have hzA : z ∈ polydisc c A := fun i => lt_trans (hz i) (hρsA i)
    have hev : ut =ᶠ[nhds z] u := by
      filter_upwards [(isOpen_polydisc c A).mem_nhds hzA] with y hy
      simp only [hut, hηC, hηA y hy, Complex.ofReal_one, one_mul]
    rw [dbarCoord_congr hev j, heq j z (fun i => lt_trans (hz i) (hρsρo i))]
    simp only [hft, hηC, hηA z hzA, Complex.ofReal_one, one_mul]
  -- ### the localised data is closed on the closure of `P(ρs)`
  have hfcl' : ∀ j l z, z ∈ closure (polydisc c ρs) →
      dbarCoord l (ft j) z = dbarCoord j (ft l) z := by
    intro j l z hz
    have hzle : ∀ i, ‖z i - c i‖ ≤ ρs i := by
      intro i
      have h2 : z ∈ closure {w : Fin n → ℂ | ‖w i - c i‖ ≤ ρs i} :=
        closure_mono (fun w (hw : w ∈ polydisc c ρs) => le_of_lt (hw i)) hz
      have hcont : Continuous fun w : Fin n → ℂ => ‖w i - c i‖ :=
        ((continuous_apply i).sub continuous_const).norm
      exact (isClosed_le hcont continuous_const).closure_subset h2
    have hzA : z ∈ polydisc c A := fun i => lt_of_le_of_lt (hzle i) (hρsA i)
    have hevj : ft j =ᶠ[nhds z] f j := by
      filter_upwards [(isOpen_polydisc c A).mem_nhds hzA] with y hy
      simp only [hft, hηC, hηA y hy, Complex.ofReal_one, one_mul]
    have hevl : ft l =ᶠ[nhds z] f l := by
      filter_upwards [(isOpen_polydisc c A).mem_nhds hzA] with y hy
      simp only [hft, hηC, hηA y hy, Complex.ofReal_one, one_mul]
    rw [dbarCoord_congr hevj l, dbarCoord_congr hevl j]
    exact hfcl j l z (fun i => lt_trans (hzA i) (hAρo i))
  -- ### the `C^{0,α}` norms of the localised data are bounded by those of the data
  have hleft : holderNorm 1 α ut (polydisc c ρi) = holderNorm 1 α u (polydisc c ρi) :=
    holderNorm_congr (fun z hz => by
      simp only [hut, hηC, hηA z (fun i => lt_trans (hz i) (hρiA i)), Complex.ofReal_one,
        one_mul])
  have hfs : ∀ j, holderNorm 0 α (ft j) (polydisc c ρs) ≤ holderNorm 0 α (f j) (polydisc c ρo) := by
    intro j
    calc holderNorm 0 α (ft j) (polydisc c ρs)
        = holderNorm 0 α (f j) (polydisc c ρs) :=
          holderNorm_congr (fun z hz => by
            simp only [hft, hηC, hηA z (fun i => lt_trans (hz i) (hρsA i)), Complex.ofReal_one,
              one_mul])
      _ ≤ holderNorm 0 α (f j) (polydisc c ρo) :=
          holderNorm_mono_set (isOpen_polydisc c ρo) (isOpen_polydisc c ρs)
            (fun z hz i => lt_trans (hz i) (hρsρo i)) 0 α (f j)
  have hus : holderNorm 0 α ut (polydisc c ρs) ≤ holderNorm 0 α u (polydisc c ρo) := by
    calc holderNorm 0 α ut (polydisc c ρs)
        = holderNorm 0 α u (polydisc c ρs) :=
          holderNorm_congr (fun z hz => by
            simp only [hut, hηC, hηA z (fun i => lt_trans (hz i) (hρsA i)), Complex.ofReal_one,
              one_mul])
      _ ≤ holderNorm 0 α u (polydisc c ρo) :=
          holderNorm_mono_set (isOpen_polydisc c ρo) (isOpen_polydisc c ρs)
            (fun z hz i => lt_trans (hz i) (hρsρo i)) 0 α u
  have hsum : (∑ j, holderNorm 0 α (ft j) (polydisc c ρs)) + holderNorm 0 α ut (polydisc c ρs)
      ≤ (∑ j, holderNorm 0 α (f j) (polydisc c ρo)) + holderNorm 0 α u (polydisc c ρo) :=
    add_le_add (Finset.sum_le_sum fun j _ => hfs j) hus
  -- ### assemble
  calc holderNorm 1 α u (polydisc c ρi)
      = holderNorm 1 α ut (polydisc c ρi) := hleft.symm
    _ ≤ ENNReal.ofReal C * ((∑ j, holderNorm 0 α (ft j) (polydisc c ρs))
          + holderNorm 0 α ut (polydisc c ρs)) := hC ut ft hut_sm hft_sm hfcl' heq'
    _ ≤ ENNReal.ofReal C * ((∑ j, holderNorm 0 α (f j) (polydisc c ρo))
          + holderNorm 0 α u (polydisc c ρo)) := mul_le_mul_right hsum _

end Work.NN.Core
