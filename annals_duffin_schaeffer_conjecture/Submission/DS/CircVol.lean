import Submission.DS.CircLift

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# Volume transfer: `volume (W ψ) = volume (Eapprox ψ)`

Chain (all pieces already proved):

* `W_measure_eq_inter_Ioo ψ` : `volume (W ψ) = volume (W ψ ∩ (0,1))`;
* `W_ae_eq_lift_Eapprox ψ hδ` : ae on `(0,1)`: `x ∈ W ψ ↔ mk x ∈ Eapprox ψ`, so
  `(W ψ ∩ (0,1))` and `mk⁻¹ (Eapprox ψ) ∩ (0,1)` are equal a.e. (equal volumes);
* dropping the endpoint `1` does not change the measure of the lift
  (`mk⁻¹ E ∩ (0,1]` vs `mk⁻¹ E ∩ (0,1)`, `{1}` null);
* `volume_circle_eq_lift hE` : `volume E = volume (mk⁻¹ E ∩ (0,1])` for measurable `E`.

All four measure-equality steps can be done without measurability, using
`S ⊆ T ∪ (S Δ T)`-style subset arguments with `measure_mono`, `measure_union_le` and the
known zero of the symmetric differences / singletons.
-/

namespace Submission.DS

/-- Sets whose symmetric difference is null have equal measures (no measurability
needed: outer-measure subadditivity and monotonicity suffice). -/
lemma measure_eq_of_symmDiff_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : Set α} (h : μ (symmDiff A B) = 0) : μ A = μ B := by
  classical
  apply le_antisymm
  · calc
      μ A ≤ μ (symmDiff A B ∪ B) := measure_mono (by
        intro x hxA
        by_cases hxB : x ∈ B
        · exact Or.inr hxB
        · exact Or.inl (Or.inl ⟨hxA, hxB⟩))
      _ ≤ μ (symmDiff A B) + μ B := measure_union_le _ _
      _ = μ B := by simp [h]
  · calc
      μ B ≤ μ (symmDiff A B ∪ A) := measure_mono (by
        intro x hxB
        by_cases hxA : x ∈ A
        · exact Or.inr hxA
        · exact Or.inl (Or.inr ⟨hxB, hxA⟩))
      _ ≤ μ (symmDiff A B) + μ A := measure_union_le _ _
      _ = μ A := by simp [h]

/-- Intersecting both arguments with a common set restricts the symmetric difference
to the points of the common set where membership differs. -/
lemma symmDiff_inter_eq_of_common {α : Type*} (W B J : Set α) :
    symmDiff (W ∩ J) (B ∩ J) = {x | x ∈ J ∧ ¬ (x ∈ W ↔ x ∈ B)} := by
  ext x
  rw [Set.symmDiff_def]
  by_cases hJ : x ∈ J
  · simp [hJ]
    tauto
  · simp [hJ]

/-- Dropping the right endpoint `1` from the lift's fundamental domain `(0,1]` down to
`(0,1)` does not change the volume (`{1}` is null). -/
lemma volume_lift_Ioo_eq_Ioc {E : Set (AddCircle (1 : ℝ))} :
    volume ((QuotientAddGroup.mk ⁻¹' E : Set ℝ) ∩ Set.Ioo (0 : ℝ) 1) =
    volume ((QuotientAddGroup.mk ⁻¹' E : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) := by
  classical
  let L : Set ℝ := QuotientAddGroup.mk ⁻¹' E
  let J : Set ℝ := Set.Ioo (0 : ℝ) 1
  let K : Set ℝ := Set.Ioc (0 : ℝ) 1
  have hdecomp : L ∩ K = (L ∩ J) ∪ (L ∩ ({1} : Set ℝ)) := by
    ext x
    simp only [L, J, K, Set.mem_inter_iff, Set.mem_union, Set.mem_Ioo, Set.mem_Ioc,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases hx with ⟨hL, h0, h1⟩
      by_cases h : x < 1
      · exact Or.inl ⟨hL, h0, h⟩
      · exact Or.inr ⟨hL, le_antisymm h1 (le_of_not_gt h)⟩
    · intro hx
      rcases hx with ⟨hL, h0, hlt⟩ | ⟨hL, hx1⟩
      · exact ⟨hL, h0, le_of_lt hlt⟩
      · subst x
        exact ⟨hL, by norm_num, by norm_num⟩
  have hmono : volume (L ∩ J) ≤ volume (L ∩ K) := measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.1, le_of_lt hx.2.2⟩)
  have hrev : volume (L ∩ K) ≤ volume (L ∩ J) := by
    calc
      volume (L ∩ K) = volume ((L ∩ J) ∪ (L ∩ ({1} : Set ℝ))) := by rw [hdecomp]
      _ ≤ volume (L ∩ J) + volume (L ∩ ({1} : Set ℝ)) := measure_union_le _ _
      _ = volume (L ∩ J) := by
        have hL1 : volume (L ∩ ({1} : Set ℝ)) = 0 := by
          apply le_antisymm _ bot_le
          calc
            volume (L ∩ ({1} : Set ℝ)) ≤ volume ({1} : Set ℝ) := measure_mono inter_subset_right
            _ = 0 := measure_singleton (1 : ℝ)
        simp [hL1]
  simpa [L, J, K] using (le_antisymm hrev hmono).symm

/-- For `ψ` with all radii `ψ(q)/q ≤ 1/2`, the `[0,1]`-volume of `W ψ` equals the
circle volume of `Eapprox ψ`. -/
lemma volume_W_eq_volume_E (ψ : ℕ+ → ℝ≥0) (hδ : ∀ q, (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    volume (W ψ) = volume (Eapprox ψ) := by
  classical
  -- Step A: `W ψ ⊆ [0,1]` loses nothing on dropping the endpoints
  have hA : volume (W ψ) = volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) :=
    W_measure_eq_inter_Ioo ψ
  -- Step B: on `(0,1)` the set `W ψ` coincides a.e. with the lift of `Eapprox ψ`
  have hB : volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) =
      volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioo (0 : ℝ) 1) := by
    let bad : Set ℝ := {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧
      ¬ (x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ)}
    have hbad : volume bad = 0 := by
      have hz : volume {x : ℝ | ¬ (x ∈ Set.Ioo (0 : ℝ) 1 →
          (x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ))} = 0 :=
        MeasureTheory.ae_iff.mp (W_ae_eq_lift_Eapprox ψ hδ)
      have hset : {x : ℝ | ¬ (x ∈ Set.Ioo (0 : ℝ) 1 →
          (x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ))} = bad := by
        ext x
        simp [bad]
        tauto
      rw [← hset]
      exact hz
    apply measure_eq_of_symmDiff_zero
    have hmid : symmDiff (W ψ ∩ Set.Ioo (0 : ℝ) 1)
        ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioo (0 : ℝ) 1) =
        {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧
          ¬ (x ∈ W ψ ↔ x ∈ (QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ))} :=
      symmDiff_inter_eq_of_common (W ψ) (QuotientAddGroup.mk ⁻¹' (Eapprox ψ))
        (Set.Ioo (0 : ℝ) 1)
    have hbadEq : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧
        ¬ (x ∈ W ψ ↔ x ∈ (QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ))} = bad := by
      ext x
      simp [bad, Set.mem_preimage]
    rw [hmid, hbadEq]
    exact hbad
  -- Step C: drop the endpoint `1` from the lift
  have hC : volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioo (0 : ℝ) 1) =
      volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) :=
    volume_lift_Ioo_eq_Ioc
  -- Step D: the lift to `(0,1]` is measure-preserving for measurable `Eapprox ψ`
  have hD : volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) =
      volume (Eapprox ψ) := (volume_circle_eq_lift (E_measurableSet ψ)).symm
  calc
    volume (W ψ) = volume (W ψ ∩ Set.Ioo (0 : ℝ) 1) := hA
    _ = volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioo (0 : ℝ) 1) := hB
    _ = volume ((QuotientAddGroup.mk ⁻¹' (Eapprox ψ) : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) := hC
    _ = volume (Eapprox ψ) := hD



/-- **Gallagher zero-one law (decaying-radii regime)**: if the radii `ψ(q)/q → 0`
(and are `≤ 1/2`), then `W ψ` is null or full. -/
theorem gallagher_zero_one_decay (ψ : ℕ+ → ℝ≥0)
    (hδ0 : Tendsto (radSeq ψ) atTop (nhds (0 : ℝ)))
    (hδ : ∀ q, (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    volume (W ψ) = 0 ∨ volume (W ψ) = 1 := by
  classical
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hEmeas : MeasurableSet (Eapprox ψ) := E_measurableSet ψ
  have hvolE : volume (W ψ) = volume (Eapprox ψ) := volume_W_eq_volume_E ψ hδ
  have hGal := AddCircle.addWellApproximable_ae_empty_or_univ (T := (1 : ℝ)) (radSeq ψ) hδ0
  rcases hGal with hn | hy
  · left
    have hE0 : volume (Eapprox ψ) = 0 := by
      have hnull : volume (addWellApproximable (AddCircle (1 : ℝ)) (radSeq ψ)) = 0 := by
        simpa using (ae_iff.mp hn)
      simpa [Eapprox] using hnull
    exact hvolE.trans hE0
  · right
    have hc : volume ((Eapprox ψ)ᶜ : Set (AddCircle (1 : ℝ))) = 0 := by
      have hnull : volume ((addWellApproximable (AddCircle (1 : ℝ)) (radSeq ψ))ᶜ : Set (AddCircle (1 : ℝ))) = 0 := by
        change volume {a : AddCircle (1 : ℝ) | a ∉ addWellApproximable (AddCircle (1 : ℝ)) (radSeq ψ)} = 0
        exact ae_iff.mp hy
      simpa [Eapprox] using hnull
    have hE1 : volume (Eapprox ψ) = 1 := by
      apply le_antisymm ?_ ?_
      · calc
          volume (Eapprox ψ) ≤ volume (univ : Set (AddCircle (1 : ℝ))) :=
            measure_mono (Set.subset_univ (Eapprox ψ))
          _ = 1 := by
            rw [AddCircle.measure_univ (1 : ℝ)]
            norm_num
      · calc
          (1 : ℝ≥0∞) = volume (univ : Set (AddCircle (1 : ℝ))) := by
            rw [AddCircle.measure_univ (1 : ℝ)]
            norm_num
          _ ≤ volume ((Eapprox ψ) ∪ (Eapprox ψ)ᶜ) := measure_mono (by intro x; by_cases hx : x ∈ Eapprox ψ <;> simp [hx])
          _ ≤ volume (Eapprox ψ) + volume ((Eapprox ψ)ᶜ) := measure_union_le _ _
          _ = volume (Eapprox ψ) := by rw [hc]; simp
    exact hvolE.trans hE1



end Submission.DS
