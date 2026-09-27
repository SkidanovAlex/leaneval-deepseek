import Mathlib
import Submission.Work.Geo.Radial.Basic

namespace Work.Geo.Radial

open Set Metric

/-- In a metric space, given a closed set `K` contained in an open set `U`, there is a continuous
`f : α → ℝ` with `0 ≤ f ≤ 1`, `f = 0` off `U`, `f > 0` on `U` and `f = 1` on `K`.

Witness: if `Uᶜ = ∅` take `f ≡ 1`; otherwise take
`f u = infDist u Uᶜ / (infDist u Uᶜ + infDist u K + c)` with the constant `c = 1` when `K = ∅`
(in which case the bound `f = 1` on `K` is vacuous) and `c = 0` otherwise. -/
theorem exists_continuous_separator {α : Type*} [MetricSpace α] {U K : Set α} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) :
    ∃ f : α → ℝ, Continuous f ∧ (∀ u, 0 ≤ f u) ∧ (∀ u, f u ≤ 1) ∧
      (∀ u, u ∉ U → f u = 0) ∧ (∀ u, u ∈ U → 0 < f u) ∧ (∀ u, u ∈ K → f u = 1) := by
  by_cases hUc : Uᶜ = ∅
  · -- `U = univ`, so the constant `1` works.
    refine ⟨fun _ => 1, continuous_const, fun u => by norm_num, fun u => by norm_num,
      fun u hu => ?_, fun u hu => by norm_num, fun u hu => rfl⟩
    exfalso
    have : u ∈ Uᶜ := hu
    rw [hUc] at this
    exact notMem_empty u this
  · have hneU : Uᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr hUc
    -- `infDist · Uᶜ` is positive on the open set `U`
    have hdpos : ∀ u ∈ U, 0 < infDist u Uᶜ := fun u hu =>
      (Metric.infDist_pos_iff_notMem_closure hneU).mp (by
        rw [hU.isClosed_compl.closure_eq]
        intro h; exact h hu)
    rcases Set.eq_empty_or_nonempty K with hK0 | hneK
    · -- `K = ∅`: the constraint `f = 1` on `K` is vacuous, so add `1` to the denominator.
      refine ⟨fun u => infDist u Uᶜ / (infDist u Uᶜ + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Continuous.div (continuous_infDist_pt _)
          (Continuous.add (continuous_infDist_pt _) continuous_const)
          (fun u => ne_of_gt (by have := infDist_nonneg (x := u) (s := Uᶜ); linarith))
      · intro u
        exact div_nonneg infDist_nonneg (by have := infDist_nonneg (x := u) (s := Uᶜ); linarith)
      · intro u
        rw [div_le_one (by have := infDist_nonneg (x := u) (s := Uᶜ); linarith)]
        linarith [infDist_nonneg (x := u) (s := Uᶜ)]
      · intro u hu
        change infDist u Uᶜ / (infDist u Uᶜ + 1) = 0
        rw [infDist_zero_of_mem (show u ∈ Uᶜ from hu)]
        norm_num
      · intro u hu
        exact div_pos (hdpos u hu) (by linarith [hdpos u hu])
      · intro u hu; exact absurd (hK0 ▸ hu) (notMem_empty u)
    · -- `K ≠ ∅`: the denominator `infDist · Uᶜ + infDist · K` never vanishes, because a point
      -- where both terms vanish lies in `Uᶜ` and in `K`, while `K ⊆ U`.
      have hdenpos : ∀ u : α, 0 < infDist u Uᶜ + infDist u K := by
        intro u
        refine lt_of_le_of_ne ?_ (Ne.symm ?_)
        · have hA := infDist_nonneg (x := u) (s := Uᶜ)
          have hB := infDist_nonneg (x := u) (s := K)
          linarith
        · intro h
          have h1 : infDist u Uᶜ = 0 := by
            have hA := infDist_nonneg (x := u) (s := Uᶜ)
            have hB := infDist_nonneg (x := u) (s := K)
            linarith
          have h2 : infDist u K = 0 := by
            have hA := infDist_nonneg (x := u) (s := Uᶜ)
            have hB := infDist_nonneg (x := u) (s := K)
            linarith
          have hm1 : u ∈ closure Uᶜ := (Metric.mem_closure_iff_infDist_zero hneU).mpr h1
          have hm2 : u ∈ closure K := (Metric.mem_closure_iff_infDist_zero hneK).mpr h2
          have hm1' : u ∈ Uᶜ := by rwa [hU.isClosed_compl.closure_eq] at hm1
          have hm2' : u ∈ K := by rwa [hK.closure_eq] at hm2
          exact absurd (hKU hm2') hm1'
      refine ⟨fun u => infDist u Uᶜ / (infDist u Uᶜ + infDist u K), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Continuous.div (continuous_infDist_pt _)
          (Continuous.add (continuous_infDist_pt _) (continuous_infDist_pt _))
          (fun u => ne_of_gt (hdenpos u))
      · intro u; exact div_nonneg infDist_nonneg (le_of_lt (hdenpos u))
      · intro u
        rw [div_le_one (hdenpos u)]
        linarith [infDist_nonneg (x := u) (s := K)]
      · intro u hu
        change infDist u Uᶜ / (infDist u Uᶜ + infDist u K) = 0
        rw [infDist_zero_of_mem (show u ∈ Uᶜ from hu)]
        simp
      · intro u hu
        exact div_pos (hdpos u hu) (hdenpos u)
      · intro u hu
        change infDist u Uᶜ / (infDist u Uᶜ + infDist u K) = 1
        rw [infDist_zero_of_mem hu, add_zero]
        exact div_self (ne_of_gt (hdpos u (hKU hu)))

end Work.Geo.Radial
