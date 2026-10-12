import ChallengeDeps
import Submission.Work.BoseFixB1.Q1FormDefs
import Submission.Work.BoseFixB1.q1pair_peel_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem wSmall1Pair_fibre_indicator {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : EuclideanSpace ℝ (Fin 3)) :
    (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
          * Submission.BoseGases.wSmall1Pair h M ℓ d u y z)
      = Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z := by
  -- The first-slot kernel `y ↦ w₁(y,z)` is supported in the sliding box `B(u) = dlBox ℓ d u`
  -- (the `chiSmallB`-factor vanishes off it), so the indicator of `dlBox` is redundant;
  -- the resulting first-slot integral is the fibre of the symmetric kernel `w₁` (FS's
  -- `w₁(x,y) = w₁(y,x)`), which is `w1Fibre ℓ w₁ z`.
  have hvan : ∀ y : EuclideanSpace ℝ (Fin 3),
      y ∉ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.wSmall1Pair h M ℓ d u y z = 0 :=
    fun y hy => Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hy)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
        * Submission.BoseGases.wSmall1Pair h M ℓ d u y z
      = Submission.BoseGases.wSmall1Pair h M ℓ d u y z := by
    intro y
    by_cases hy : y ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Set.indicator_of_mem hy]
      simp
    · rw [Set.indicator_of_notMem hy, zero_mul]
      exact (hvan y hy).symm
  calc (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
          * Submission.BoseGases.wSmall1Pair h M ℓ d u y z)
      = (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u y z) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z :=
        wSmallPair_fibre_eq hM u (Submission.BoseGases.g0_even hvrad h) z

end Work.BoseFixB1
