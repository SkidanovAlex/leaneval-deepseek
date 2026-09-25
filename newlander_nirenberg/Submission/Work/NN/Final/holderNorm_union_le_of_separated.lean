import Mathlib
import Submission.Work.CR.Flat.Holder

/-!
# Hölder norm on a union of two separated open sets

If `A` and `B` are open subsets of a real normed space whose *outer* parts
`A \ B` and `B \ A` stay at distance at least `η` from one another, then on the
union `A ∪ B` the `C^{k,α}`-Hölder norm (as defined in
`Work.CR.Flat.Holder`) is controlled by the two norms on `A` and on `B` alone.

The point is that the within-derivatives relative to the union agree, on `A`,
with the within-derivatives relative to `A` (because `A` is open, hence agrees
with `A ∪ B` in a neighbourhood of each of its points), and similarly for `B`.
The only genuinely new terms on the union are the "cross" Hölder quotients with
`x ∈ A \ B` and `y ∈ B \ A`; there `‖x - y‖ ≥ η`, so the derivative difference
is bounded by `iterDerivNorm ⋯ A + iterDerivNorm ⋯ B` and the factor
`‖x - y‖ ^ (-α)` by `η ^ (-α)`.

This is a small, self-contained statement about the Hölder-norm glossary; it
does not use any regularity (`ContDiffOn`) hypothesis, only the openness of the
two sets and the separation.
-/

noncomputable section

open scoped NNReal ENNReal Topology
open Set

namespace Work.NN.Final

open Work.CR.Flat

/-- On the part `A` of `A ∪ B`, the within-`i`-th-derivative relative to the
union coincides with the within-derivative relative to `A` (as `A` is open). -/
private lemma iteratedFDerivWithin_union_eq_left {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {A B : Set X} (hA : IsOpen A) {x : X} (hx : x ∈ A) (i : ℕ)
    (f : X → ℂ) :
    iteratedFDerivWithin ℝ i f (A ∪ B) x = iteratedFDerivWithin ℝ i f A x :=
  (iteratedFDerivWithin_congr_set (by
    filter_upwards [hA.mem_nhds hx] with y hy
    exact propext ⟨fun h => Or.inl h, fun h => h.elim id (fun _ => hy)⟩) i).symm

/-- On the part `B` of `A ∪ B`, the within-`i`-th-derivative relative to the
union coincides with the within-derivative relative to `B`. -/
private lemma iteratedFDerivWithin_union_eq_right {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {A B : Set X} (hB : IsOpen B) {x : X} (hx : x ∈ B) (i : ℕ)
    (f : X → ℂ) :
    iteratedFDerivWithin ℝ i f (A ∪ B) x = iteratedFDerivWithin ℝ i f B x :=
  (iteratedFDerivWithin_congr_set (by
    filter_upwards [hB.mem_nhds hx] with y hy
    exact propext ⟨fun h => Or.inr h, fun h => h.elim (fun _ => hy) id⟩) i).symm

/-- The iterated-derivative norm on `A ∪ B` is bounded by the sum of the norms
on `A` and on `B`. -/
private lemma iterDerivNorm_union_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (i : ℕ) (f : X → ℂ) :
    iterDerivNorm i f (A ∪ B) ≤ iterDerivNorm i f A + iterDerivNorm i f B := by
  refine iSup₂_le fun x hx => ?_
  rcases hx with hx | hx
  · rw [iteratedFDerivWithin_union_eq_left hA hx i f]
    exact le_trans (le_iterDerivNorm i f A hx) le_self_add
  · rw [iteratedFDerivWithin_union_eq_right hB hx i f]
    exact le_trans (le_iterDerivNorm i f B hx) le_add_self

/-- The Hölder seminorm on `A ∪ B` is bounded by the seminorms on `A` and on
`B`, plus a correction `η^{-α} (N_A + N_B)` coming from the "cross" pairs of
points of `A \ B` and `B \ A`, which are at distance `≥ η`. -/
private lemma holderSeminorm_union_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hsep : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → η ≤ ‖x - y‖) (i : ℕ) (f : X → ℂ) :
    holderSeminorm i α f (A ∪ B) ≤ holderSeminorm i α f A + holderSeminorm i α f B
      + ENNReal.ofReal ((η^α)⁻¹) * (iterDerivNorm i f A + iterDerivNorm i f B) := by
  refine iSup₂_le fun x hx => ?_
  refine iSup₂_le fun y hy => ?_
  refine iSup_le fun hxy => ?_
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · -- both points in `A`
    rw [iteratedFDerivWithin_union_eq_left hA hxA i f,
        iteratedFDerivWithin_union_eq_left hA hyA i f]
    exact le_trans (le_holderSeminorm i α f A hxA hyA hxy) (le_add_right le_self_add)
  · -- `x ∈ A`, `y ∈ B`
    by_cases hxB' : x ∈ B
    · rw [iteratedFDerivWithin_union_eq_right hB hxB' i f,
          iteratedFDerivWithin_union_eq_right hB hyB i f]
      exact le_trans (le_holderSeminorm i α f B hxB' hyB hxy) (le_add_right le_add_self)
    · by_cases hyA' : y ∈ A
      · rw [iteratedFDerivWithin_union_eq_left hA hxA i f,
            iteratedFDerivWithin_union_eq_left hA hyA' i f]
        exact le_trans (le_holderSeminorm i α f A hxA hyA' hxy) (le_add_right le_self_add)
      · -- genuinely separated pair
        have hxy_sep : η ≤ ‖x - y‖ := hsep x hxA hxB' y hyB hyA'
        have hpow_pos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (lt_of_lt_of_le hη hxy_sep) α
        have hηpow_pos : 0 < η ^ α := Real.rpow_pos_of_pos hη α
        have hpow_le : η ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hη.le hxy_sep hα.le
        have hinv : (‖x - y‖ ^ α)⁻¹ ≤ (η ^ α)⁻¹ := (inv_le_inv₀ hpow_pos hηpow_pos).mpr hpow_le
        have hbd : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f (A ∪ B) x
            - iteratedFDerivWithin ℝ i f (A ∪ B) y‖
            ≤ iterDerivNorm i f A + iterDerivNorm i f B := by
          rw [iteratedFDerivWithin_union_eq_left hA hxA i f,
              iteratedFDerivWithin_union_eq_right hB hyB i f]
          refine le_trans (ENNReal.ofReal_le_ofReal (norm_sub_le _ _)) ?_
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact add_le_add (le_iterDerivNorm i f A hxA) (le_iterDerivNorm i f B hyB)
        calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f (A ∪ B) x
                - iteratedFDerivWithin ℝ i f (A ∪ B) y‖ / ‖x - y‖ ^ α)
            = ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f (A ∪ B) x
                - iteratedFDerivWithin ℝ i f (A ∪ B) y‖ * ENNReal.ofReal ((‖x - y‖ ^ α)⁻¹) := by
              rw [div_eq_mul_inv, ENNReal.ofReal_mul (norm_nonneg _)]
          _ ≤ (iterDerivNorm i f A + iterDerivNorm i f B) * ENNReal.ofReal ((η ^ α)⁻¹) :=
              mul_le_mul' hbd (ENNReal.ofReal_le_ofReal hinv)
          _ = ENNReal.ofReal ((η ^ α)⁻¹) * (iterDerivNorm i f A + iterDerivNorm i f B) :=
              mul_comm _ _
          _ ≤ holderSeminorm i α f A + holderSeminorm i α f B
                + ENNReal.ofReal ((η ^ α)⁻¹) * (iterDerivNorm i f A + iterDerivNorm i f B) :=
              le_add_left le_rfl
  · -- `x ∈ B`, `y ∈ A`
    by_cases hyB' : y ∈ B
    · rw [iteratedFDerivWithin_union_eq_right hB hxB i f,
          iteratedFDerivWithin_union_eq_right hB hyB' i f]
      exact le_trans (le_holderSeminorm i α f B hxB hyB' hxy) (le_add_right le_add_self)
    · by_cases hxA' : x ∈ A
      · rw [iteratedFDerivWithin_union_eq_left hA hxA' i f,
            iteratedFDerivWithin_union_eq_left hA hyA i f]
        exact le_trans (le_holderSeminorm i α f A hxA' hyA hxy) (le_add_right le_self_add)
      · have hxy_sep : η ≤ ‖x - y‖ := by
          have h := hsep y hyA hyB' x hxB hxA'
          rwa [norm_sub_rev] at h
        have hpow_pos : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (lt_of_lt_of_le hη hxy_sep) α
        have hηpow_pos : 0 < η ^ α := Real.rpow_pos_of_pos hη α
        have hpow_le : η ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow hη.le hxy_sep hα.le
        have hinv : (‖x - y‖ ^ α)⁻¹ ≤ (η ^ α)⁻¹ := (inv_le_inv₀ hpow_pos hηpow_pos).mpr hpow_le
        have hbd : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f (A ∪ B) x
            - iteratedFDerivWithin ℝ i f (A ∪ B) y‖
            ≤ iterDerivNorm i f A + iterDerivNorm i f B := by
          rw [iteratedFDerivWithin_union_eq_right hB hxB i f,
              iteratedFDerivWithin_union_eq_left hA hyA i f]
          refine le_trans (ENNReal.ofReal_le_ofReal (norm_sub_le _ _)) ?_
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact le_trans (add_le_add (le_iterDerivNorm i f B hxB) (le_iterDerivNorm i f A hyA))
            (le_of_eq (add_comm _ _))
        calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i f (A ∪ B) x
                - iteratedFDerivWithin ℝ i f (A ∪ B) y‖ / ‖x - y‖ ^ α)
            = ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f (A ∪ B) x
                - iteratedFDerivWithin ℝ i f (A ∪ B) y‖ * ENNReal.ofReal ((‖x - y‖ ^ α)⁻¹) := by
              rw [div_eq_mul_inv, ENNReal.ofReal_mul (norm_nonneg _)]
          _ ≤ (iterDerivNorm i f A + iterDerivNorm i f B) * ENNReal.ofReal ((η ^ α)⁻¹) :=
              mul_le_mul' hbd (ENNReal.ofReal_le_ofReal hinv)
          _ = ENNReal.ofReal ((η ^ α)⁻¹) * (iterDerivNorm i f A + iterDerivNorm i f B) :=
              mul_comm _ _
          _ ≤ holderSeminorm i α f A + holderSeminorm i α f B
                + ENNReal.ofReal ((η ^ α)⁻¹) * (iterDerivNorm i f A + iterDerivNorm i f B) :=
              le_add_left le_rfl
  · -- both points in `B`
    rw [iteratedFDerivWithin_union_eq_right hB hxB i f,
        iteratedFDerivWithin_union_eq_right hB hyB i f]
    exact le_trans (le_holderSeminorm i α f B hxB hyB hxy) (le_add_right le_add_self)

/-- Elementary `ℝ≥0∞` bound used to assemble the per-order estimate: with
`rE = η^{-α}` it absorbs the correction term into the factor `1 + rE`. -/
private lemma holderNorm_term_le (rE NA NB SA SB : ℝ≥0∞) :
    (NA + NB) + (SA + SB + rE * (NA + NB)) ≤ (1 + rE) * ((NA + SA) + (NB + SB)) := by
  have h1 : (NA + NB) + (SA + SB + rE * (NA + NB))
      = (NA + SA) + (NB + SB) + rE * (NA + NB) := by abel
  rw [h1]
  have h2 : NA + NB ≤ (NA + SA) + (NB + SB) := add_le_add le_self_add le_self_add
  calc (NA + SA) + (NB + SB) + rE * (NA + NB)
      ≤ (NA + SA) + (NB + SB) + rE * ((NA + SA) + (NB + SB)) :=
        add_le_add le_rfl (mul_le_mul' le_rfl h2)
    _ = (1 + rE) * ((NA + SA) + (NB + SB)) := by rw [add_mul, one_mul]

theorem holderNorm_union_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (f : E → ℂ) (A B : Set E),
      IsOpen A →
      IsOpen B →
      ContDiffOn ℝ (k : WithTop ENat) f (A ∪ B) →
      (∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → η ≤ ‖x - y‖) →
      Work.CR.Flat.holderNorm k α f (A ∪ B)
        ≤ ENNReal.ofReal (C k) * (Work.CR.Flat.holderNorm k α f A
            + Work.CR.Flat.holderNorm k α f B) := by
  refine ⟨fun _ => 1 + (η^α)⁻¹, ?_, ?_⟩
  · intro k
    have hηα : 0 < η ^ α := Real.rpow_pos_of_pos hη α
    have hpos : 0 < (η^α)⁻¹ := inv_pos.mpr hηα
    linarith
  · intro k f A B hA hB _hcont hsep
    have hηα : 0 ≤ η ^ α := Real.rpow_nonneg hη.le α
    have hC : ENNReal.ofReal (1 + (η^α)⁻¹) = 1 + ENNReal.ofReal ((η^α)⁻¹) := by
      rw [ENNReal.ofReal_add zero_le_one (inv_nonneg.mpr hηα), ENNReal.ofReal_one]
    rw [hC]
    have hsum : Work.CR.Flat.holderNorm k α f (A ∪ B) ≤
        ∑ i ∈ Finset.range (k + 1), (1 + ENNReal.ofReal ((η^α)⁻¹)) *
          ((Work.CR.Flat.iterDerivNorm i f A + Work.CR.Flat.holderSeminorm i α f A)
            + (Work.CR.Flat.iterDerivNorm i f B
                + Work.CR.Flat.holderSeminorm i α f B)) := by
      rw [Work.CR.Flat.holderNorm]
      apply Finset.sum_le_sum
      intro i _
      refine le_trans (add_le_add (iterDerivNorm_union_le hA hB i f)
        (holderSeminorm_union_le hA hB hα hη hsep i f)) ?_
      exact holderNorm_term_le _ _ _ _ _
    rw [show (1 + ENNReal.ofReal ((η^α)⁻¹)) *
          (Work.CR.Flat.holderNorm k α f A + Work.CR.Flat.holderNorm k α f B)
        = ∑ i ∈ Finset.range (k + 1), (1 + ENNReal.ofReal ((η^α)⁻¹)) *
          ((Work.CR.Flat.iterDerivNorm i f A + Work.CR.Flat.holderSeminorm i α f A)
            + (Work.CR.Flat.iterDerivNorm i f B
                + Work.CR.Flat.holderSeminorm i α f B)) from ?_]
    exact hsum
    rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, ← Finset.sum_add_distrib,
      Finset.mul_sum]

end Work.NN.Final
