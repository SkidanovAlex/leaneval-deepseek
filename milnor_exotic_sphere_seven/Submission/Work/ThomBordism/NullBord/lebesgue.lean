import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Lebesgue number of a finite open cover of a compact metric space

`Work.ThomBordism.NullBord.exists_lebesgue_number`: for a finite open cover of a compact metric
space there is `η > 0` such that any two points at distance `< η` lie in a common member of the
cover.  The proof uses the continuous function `z ↦ maxᵢ infDist z (Uᵢᶜ)`, positive because the `Uᵢ`
cover `Z`, whose minimum `η` over the compact space is positive. -/

open Set Metric Filter
open scoped Topology

namespace Work.ThomBordism.NullBord

noncomputable section

/-- **The Lebesgue number lemma** for a finite open cover of a compact metric space. -/
theorem exists_lebesgue_number {Z : Type*} [MetricSpace Z] [CompactSpace Z] {ι : Type*}
    [Finite ι] (U : ι → Set Z) (hU : ∀ i, IsOpen (U i)) (hcov : ∀ z, ∃ i, z ∈ U i) :
    ∃ η : ℝ, 0 < η ∧ ∀ z z' : Z, dist z z' < η → ∃ i, z ∈ U i ∧ z' ∈ U i := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact ⟨1, one_pos, fun z => isEmptyElim z⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : IsEmpty Z := ⟨fun z => by obtain ⟨i⟩ := hcov z; exact isEmptyElim i⟩
    exact ⟨1, one_pos, fun z => isEmptyElim z⟩
  by_cases huniv : ∃ i, U i = univ
  · obtain ⟨i, hi⟩ := huniv
    exact ⟨1, one_pos, fun z z' _ =>
      ⟨i, by rw [hi]; exact mem_univ z, by rw [hi]; exact mem_univ z'⟩⟩
  push_neg at huniv
  -- the continuous function `z ↦ maxᵢ infDist z (Uᵢᶜ)`
  let g : ι → C(Z, ℝ) := fun i =>
    ⟨fun z => Metric.infDist z (U i)ᶜ, continuous_infDist_pt _⟩
  let w : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => Metric.infDist (Classical.arbitrary Z)
    (U i)ᶜ)
  let f : C(Z, ℝ) := Finset.univ.sup' Finset.univ_nonempty g
  have hfval : ∀ z, f z = Finset.univ.sup' Finset.univ_nonempty
      (fun i => Metric.infDist z (U i)ᶜ) :=
    fun z => ContinuousMap.sup'_apply Finset.univ_nonempty g z
  have hfpos : ∀ z, 0 < f z := by
    intro z
    obtain ⟨j, hj⟩ := hcov z
    have hne : (U j)ᶜ.Nonempty := Set.nonempty_compl.mpr (huniv j)
    have hpos : 0 < Metric.infDist z (U j)ᶜ := by
      refine (Metric.infDist_pos_iff_notMem_closure hne).mp fun hc => ?_
      rw [((hU j).isClosed_compl).closure_eq] at hc
      exact hc hj
    have hle : Metric.infDist z (U j)ᶜ ≤ f z := by
      rw [hfval z]
      exact Finset.le_sup' (fun i => Metric.infDist z (U i)ᶜ) (Finset.mem_univ j)
    linarith
  -- the minimum
  obtain ⟨z₀, -, hmin⟩ := (show IsCompact (Set.univ : Set Z) from isCompact_univ).exists_isMinOn
    Set.univ_nonempty f.continuous.continuousOn
  refine ⟨f z₀, hfpos z₀, fun z z' hzz' => ?_⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => Metric.infDist z (U i)ᶜ)
  have hfz : f z = Metric.infDist z (U i)ᶜ := by rw [hfval z, hi]
  have hile : f z₀ ≤ Metric.infDist z (U i)ᶜ := by rw [← hfz]; exact hmin (mem_univ z)
  have hzi : z ∈ U i := by
    by_contra hz
    have hzero : Metric.infDist z (U i)ᶜ = 0 :=
      Metric.infDist_zero_of_mem_closure (subset_closure hz)
    rw [hzero] at hile
    linarith [hfpos z₀]
  refine ⟨i, hzi, ?_⟩
  by_contra hz'
  have hbound : Metric.infDist z (U i)ᶜ ≤ dist z z' :=
    Metric.infDist_le_dist_of_mem hz'
  linarith

end

end Work.ThomBordism.NullBord
