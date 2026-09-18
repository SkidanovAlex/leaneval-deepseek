import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.LevelMass

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Work.MassTransferenceAlt.Tree.Hausdorff

noncomputable section

/-! ## The mass distribution on the Cantor tree

The level measures `Hausdorff.levelMeasure d c ρ η T N` are probability measures on `ℝ`,
supported on the level sets `levSet T N ⊆ [0,1]`.  Their weak limit along a subsequence is a
probability measure `μ` supported on the Cantor set `cantor T`, and the portmanteau theorem
together with the level estimate `Hausdorff.meetMass_le_of_small` gives the Frostman bound. -/

/-- The minimal radius of a ball of level `0` is `< 1`. -/
lemma rmin0_lt_one (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    rmin0 d c ρ η T < 1 := by
  obtain ⟨j, hj⟩ := rootLev_nonempty d c ρ η T
  have h1 : rmin0 d c ρ η T ≤ ρ j := rmin0_le d c ρ η T hj
  have h2 : ρ j ≤ Rabs d := (T.good 0 j hj).2.1
  have h3 : Rabs d < 1 := by
    rw [Rabs]
    refine Real.rpow_lt_one (by positivity) (by norm_num) ?_
    rw [one_div_pos]; linarith
  linarith

/-- The `N`-th level measure, viewed as a probability measure on `ℝ`. -/
def levProb (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨levelMeasure d c ρ η T N, IsProbabilityMeasure.mk (levelMeasure_univ d c ρ η T N)⟩

lemma levProb_toMeasure (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ) :
    (levProb d c ρ η T N : Measure ℝ) = levelMeasure d c ρ η T N := rfl

/-- The level measures are supported in the compact interval `[0,1]`. -/
lemma levProb_compl_Icc_eq_zero (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) (N : ℕ) :
    (levProb d c ρ η T N : Measure ℝ) (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
  have h1 : levelMeasure d c ρ η T N (levSet T 0) = 1 :=
    levelMeasure_levSet d hd1 c ρ η T (Nat.zero_le N)
  have hsub : levSet T 0 ⊆ Set.Icc (0:ℝ) 1 := levSet_subset_Icc d c ρ η T 0
  have h2 : levelMeasure d c ρ η T N (Set.Icc (0:ℝ) 1) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← levelMeasure_univ d c ρ η T N]; exact measure_mono (Set.subset_univ _)
    · rw [← h1]; exact measure_mono hsub
  have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1) := measurableSet_Icc
  have h3 := measure_compl (μ := levelMeasure d c ρ η T N) hmeas (by rw [h2]; exact ENNReal.one_ne_top)
  rw [h2, levelMeasure_univ d c ρ η T N, tsub_self] at h3
  exact h3

/-- **Existence of a weak limit of the level measures.**  The level measures form a sequence in
the compact set of probability measures supported in `[0,1]`; hence some subsequence converges
to a probability measure `μ` on `ℝ`. -/
lemma exists_weakLimit (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => levProb d c ρ η T (φ k)) atTop (𝓝 μ) := by
  classical
  have hsupp : ∀ N, (levProb d c ρ η T N : Measure ℝ) (Set.Icc (0:ℝ) 1)ᶜ ≤ (0:ℝ≥0) :=
    fun N => le_of_eq (levProb_compl_Icc_eq_zero d hd1 c ρ η T N)
  have hcomp : IsCompact {μ : ProbabilityMeasure ℝ |
      ∀ _ : ℕ, (μ : Measure ℝ) (Set.Icc (0:ℝ) 1)ᶜ ≤ (0:ℝ≥0)} := by
    convert isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (E := ℝ) (u := fun _ : ℕ => (0:ℝ≥0)) (K := fun _ : ℕ => Set.Icc (0:ℝ) 1)
      tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inr monotone_const) using 1
    ext μ; simp [forall_const]
  have hmem : ∀ N, levProb d c ρ η T N ∈ {μ : ProbabilityMeasure ℝ |
      ∀ _ : ℕ, (μ : Measure ℝ) (Set.Icc (0:ℝ) 1)ᶜ ≤ (0:ℝ≥0)} := fun N => by
    simpa using hsupp N
  obtain ⟨μ, _hμ, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hmem
  exact ⟨μ, φ, hφ, hlim⟩

/-- **The weak limit gives full mass to the Cantor set.** -/
lemma levProb_limit_cantor_eq_one (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hlim : Tendsto (fun k => levProb d c ρ η T (φ k)) atTop (𝓝 μ)) :
    (μ : Measure ℝ) (cantor T) = 1 := by
  classical
  have hlev : ∀ m, (μ : Measure ℝ) (levSet T m) = 1 := by
    intro m
    have hcl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim
      (isClosed_levSet d c ρ η T m)
    have hev : ∀ᶠ k in Filter.atTop,
        (levProb d c ρ η T (φ k) : Measure ℝ) (levSet T m) = 1 :=
      (hφ.tendsto_atTop.eventually (eventually_ge_atTop m)).mono (fun k hk => by
        show levelMeasure d c ρ η T (φ k) (levSet T m) = 1
        exact levelMeasure_levSet d hd1 c ρ η T hk)
    have h1 : Filter.atTop.limsup
        (fun k => (levProb d c ρ η T (φ k) : Measure ℝ) (levSet T m)) = 1 := by
      rw [Filter.limsup_congr hev]; simp
    rw [h1] at hcl
    refine le_antisymm ?_ hcl
    calc (μ : Measure ℝ) (levSet T m) ≤ (μ : Measure ℝ) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hcompl : ∀ m, (μ : Measure ℝ) (levSet T m)ᶜ = 0 := by
    intro m
    have hmeas : MeasurableSet (levSet T m) := (isClosed_levSet d c ρ η T m).measurableSet
    have h := measure_compl (μ := (μ : Measure ℝ)) hmeas (by rw [hlev m]; exact ENNReal.one_ne_top)
    rw [hlev m, show (μ : Measure ℝ) Set.univ = 1 from by simp, tsub_self] at h
    exact h
  have hnull : (μ : Measure ℝ) (⋃ m, (levSet T m)ᶜ) = 0 := measure_iUnion_null hcompl
  have hcc : (μ : Measure ℝ) (cantor T)ᶜ = 0 := by
    rw [cantor, Set.compl_iInter]; exact hnull
  have hmeasC : MeasurableSet (cantor T) := (isClosed_cantor d c ρ η T).measurableSet
  have h := measure_add_measure_compl (μ := (μ : Measure ℝ)) hmeasC
  rw [hcc, add_zero, show (μ : Measure ℝ) Set.univ = 1 from by simp] at h
  exact h

/-- **The Frostman bound for the weak limit.**  For `2 r ≤ rmin0`, the weak limit of the level
measures gives at most `400 (2 r)^d / η` to the interval `Iv x r`. -/
lemma levProb_limit_Iv_le (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (hη : 0 < η) (T : TreeData d c ρ η) {μ : ProbabilityMeasure ℝ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hlim : Tendsto (fun k => levProb d c ρ η T (φ k)) atTop (𝓝 μ))
    {x r : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ rmin0 d c ρ η T) :
    (μ : Measure ℝ) (Iv x r) ≤ ENNReal.ofReal (400 * (2 * r) ^ d / η) := by
  classical
  have hrmin0 : 0 < rmin0 d c ρ η T := rmin0_pos d c ρ η T
  have hrmin0lt : rmin0 d c ρ η T < 1 := rmin0_lt_one d hd1 c ρ η T
  set ε₀ : ℝ := min (rmin0 d c ρ η T - r) ((1 - 2 * r) / 2) with hε₀def
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def, lt_min_iff]
    exact ⟨by linarith, by linarith⟩
  -- the bound for every small positive `ε`
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (μ : Measure ℝ) (Iv x r) ≤ ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num) hε₀] with ε hε hεpos
    have hε0' : 0 < ε := hεpos
    have hεlt : ε < ε₀ := hε.2
    have hle_rmin0 : r + ε ≤ rmin0 d c ρ η T := by
      have : ε < rmin0 d c ρ η T - r := lt_of_lt_of_le hεlt (min_le_left _ _)
      linarith
    have h2r' : 2 * (r + ε) ≤ 1 := by
      have : ε < (1 - 2 * r) / 2 := lt_of_lt_of_le hεlt (min_le_right _ _)
      linarith
    have hr' : 0 < r + ε := by linarith
    have huniq0 : ∀ j ∈ T.lev 0, ∀ j' ∈ T.lev 0, j ≠ j' →
        ¬ (hits c ρ x (r + ε) j ∧ hits c ρ x (r + ε) j') :=
      fun j hj j' hj' hne => hits_unique_level0 d hd1 c ρ η T hle_rmin0 hj hj' hne
    obtain ⟨N, hN1, hNbd⟩ :=
      meetMass_le_of_small d hd0 hd1 c ρ η hη T hr'.le h2r' huniq0 hε0'
    -- the portmanteau bound
    have hIvsub : Iv x r ⊆ interior (Iv x (r + ε)) := by
      intro z hz
      rw [mem_Iv] at hz
      rw [abs_le] at hz
      rw [show Iv x (r + ε) = Set.Icc (x - (r + ε)) (x + (r + ε)) from rfl, interior_Icc,
        Set.mem_Ioo]
      constructor <;> linarith
    have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (isOpen_interior : IsOpen (interior (Iv x (r + ε))))
    have hmain : (μ : Measure ℝ) (Iv x r) ≤ Filter.atTop.liminf (fun k =>
        (levProb d c ρ η T (φ k) : Measure ℝ) (interior (Iv x (r + ε)))) :=
      (measure_mono hIvsub).trans hport
    have hevk : ∀ᶠ k in Filter.atTop,
        (levProb d c ρ η T (φ k) : Measure ℝ) (interior (Iv x (r + ε)))
          ≤ ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε) := by
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
      calc (levProb d c ρ η T (φ k) : Measure ℝ) (interior (Iv x (r + ε)))
          ≤ (levProb d c ρ η T (φ k) : Measure ℝ) (Iv x (r + ε)) :=
            measure_mono interior_subset
        _ = levelMeasure d c ρ η T (φ k) (Iv x (r + ε)) := rfl
        _ ≤ ENNReal.ofReal (meetMass d c ρ η T (φ k) x (r + ε)) :=
            levelMeasure_le_meetMass d c ρ η T (φ k) hr'.le
        _ ≤ ENNReal.ofReal (meetMass d c ρ η T N x (r + ε)) :=
            ENNReal.ofReal_le_ofReal (massMono d hd0 hd1 c ρ η T
              (x := x) (r := r + ε) (n := N) (N := φ k) hN1 hk)
        _ ≤ ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε) :=
            ENNReal.ofReal_le_ofReal hNbd
    have hliminf_le : Filter.atTop.liminf (fun k =>
        (levProb d c ρ η T (φ k) : Measure ℝ) (interior (Iv x (r + ε))))
        ≤ ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε) := by
      refine Filter.liminf_le_of_le
        (u := fun k => (levProb d c ρ η T (φ k) : Measure ℝ) (interior (Iv x (r + ε))))
        ⟨0, Eventually.of_forall (fun k => zero_le)⟩ (fun b hb => ?_)
      obtain ⟨n, hbn, hgn⟩ := (hb.and hevk).exists
      exact le_trans hbn hgn
    exact hmain.trans hliminf_le
  -- let `ε → 0⁺`
  have hcont : Tendsto (fun ε : ℝ => ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε))
      (𝓝[>] (0:ℝ)) (𝓝 (ENNReal.ofReal (400 * (2 * r) ^ d / η))) := by
    have hca : ContinuousAt (fun ε : ℝ => ENNReal.ofReal (400 * (2 * (r + ε)) ^ d / η + ε)) 0 := by
      have h1 : ContinuousAt (fun ε : ℝ => (2 * (r + ε)) ^ d) 0 := by
        apply ContinuousAt.rpow_const
        · fun_prop
        · left; simp; linarith
      have h2 : ContinuousAt (fun ε : ℝ => 400 * (2 * (r + ε)) ^ d) 0 := h1.const_mul 400
      have h3 : ContinuousAt (fun ε : ℝ => 400 * (2 * (r + ε)) ^ d / η) 0 := h2.div_const η
      have h4 : ContinuousAt (fun ε : ℝ => 400 * (2 * (r + ε)) ^ d / η + ε) 0 :=
        h3.add continuousAt_id
      exact ENNReal.continuous_ofReal.continuousAt.comp h4
    have := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  exact ge_of_tendsto hcont hev

end

/-- **The mass distribution on the Cantor tree.**  There is a probability measure `μ` supported
on the Cantor set `cantor T` whose measure of any interval `Iv x r` of radius `2 r ≤ rmin0` is at
most `400 (2 r)^d / η` (a Frostman-type bound).

Route (the material is in `Submission.Work.MassTransferenceAlt.Tree.LevelMass`): the level measures
`Hausdorff.levelMeasure d c ρ η T N` are probability measures on `ℝ`
(`Hausdorff.levelMeasure_univ`), supported on the level sets
(`Hausdorff.levelMeasure_levSet`), and satisfy
`Hausdorff.levelMeasure_le_meetMass : levelMeasure … N (Iv x r) ≤ ofReal (meetMass … N x r)` for
`0 ≤ r`.  For `2 * r ≤ rmin0` the interval meets at most one ball of level `0`
(`Hausdorff.hits_unique_level0`), so `Hausdorff.meetMass_le_of_small` bounds the meeting mass of a
deep enough level by `400 (2 r)^d / η` up to `δ`.  A weak limit `μ` of the level measures along a
subsequence (`IsCompact.tendsto_subseq` applied to the compact set of probability measures
supported in the compact set `levSet T 0`, using
`MeasureTheory.isCompact_setOfPred_finiteMeasure_le_of_isCompact` and the embedding
`ProbabilityMeasure.toFiniteMeasure_isEmbedding`), together with the portmanteau theorems
(`MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`,
`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto`) and the monotonicity of
`meetMass` in the level (`Hausdorff.massMono_le`-style: the meeting mass of `Iv x r` is
non-increasing in the level, from `levelBound`/`massAncestor`), gives the bound for `Iv x r` after
enlarging to `Iv x (r + δ')` with `δ' → 0` (possible because `2 r ≤ rmin0`), and `μ (cantor T) = 1`
by continuity from above along the decreasing closed level sets. -/
lemma frostmanMeasure (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (hη : 0 < η) (T : Work.MassTransferenceAlt.TreeData d c ρ η) : ∃ μ : MeasureTheory.Measure ℝ, μ Set.univ = 1 ∧ μ (Work.MassTransferenceAlt.cantor T) = 1 ∧ ∀ x r : ℝ, 0 < r → 2 * r ≤ Work.MassTransferenceAlt.Tree.Hausdorff.rmin0 d c ρ η T → μ (Work.MassTransferenceAlt.Iv x r) ≤ ENNReal.ofReal (400 * (2 * r) ^ d / η) := by
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_weakLimit d hd1 c ρ η T
  refine ⟨(μ : Measure ℝ), ?_, ?_, ?_⟩
  · simp
  · exact levProb_limit_cantor_eq_one d hd1 c ρ η T hφ hlim
  · intro x r hr hr2
    exact levProb_limit_Iv_le d hd0 hd1 c ρ η hη T hφ hlim hr hr2

end Work.MassTransferenceAlt.Tree
