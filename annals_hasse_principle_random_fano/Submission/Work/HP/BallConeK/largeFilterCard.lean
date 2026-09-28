import Mathlib
import Submission.Work.HP.BallConeK.Defs

namespace Work.HP.BallConeK

/-- `largeFilterCard`: the elements of `largeSet L v w γ Y T` of norm `≤ t` (with
`Y ≤ t ≤ T`) are exactly the lattice points in the cone slice with `Y < ‖a‖ ≤ t`; counting
them is the same as the difference `coneCount · t - coneCount · Y` of the two counting
functions, where the `≤ Y` part cancels. -/
theorem largeFilterCard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ Y T : ℝ)
    (hfin : (largeSet L v w γ Y T).Finite) {t : ℝ} (ht : t ∈ Set.Icc Y T) (hY0 : 0 ≤ Y) :
    (((hfin.toFinset.filter (fun a => eNorm a ≤ t)).card : ℕ) : ℝ)
      = coneCount L v w γ t - coneCount L v w γ Y := by
  classical
  -- The filtered `largeSet` is exactly the shell `Y < ‖a‖ ≤ t` of the two cones.
  have hcoe : ((hfin.toFinset.filter (fun a => eNorm a ≤ t) : Finset (ι → ℤ)) : Set (ι → ℤ))
      = {a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} := by
    ext a
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      largeSet]
    constructor
    · rintro ⟨⟨hL, hne, hYlt, hTle, hc1, hc2⟩, hlt⟩
      exact ⟨hL, hYlt, hlt, hc1, hc2⟩
    · rintro ⟨hL, hYlt, hlt, hc1, hc2⟩
      refine ⟨⟨hL, ?_, hYlt, le_trans hlt ht.2, hc1, hc2⟩, hlt⟩
      intro h0
      have hpos : (0 : ℝ) < eNorm a := lt_of_le_of_lt hY0 hYlt
      rw [h0] at hpos
      simp [eNorm] at hpos
  have hcard : (hfin.toFinset.filter (fun a => eNorm a ≤ t)).card
      = ({a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).ncard := by
    rw [← Set.ncard_coe_finset, hcoe]
  -- `coneCount · t` decomposes as `coneCount · Y` plus the shell.
  have huni : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ))
      = {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}
        ∪ {a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hL, ht', hc1, hc2⟩
      rcases le_or_gt (eNorm a) Y with h | h
      · exact Or.inl ⟨hL, h, hc1, hc2⟩
      · exact Or.inr ⟨hL, h, ht', hc1, hc2⟩
    · rintro (⟨hL, hY, hc1, hc2⟩ | ⟨hL, hY, ht', hc1, hc2⟩)
      · exact ⟨hL, le_trans hY ht.1, hc1, hc2⟩
      · exact ⟨hL, ht', hc1, hc2⟩
  have hdisj : Disjoint ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ))
      {a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} := by
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [Set.mem_ofPred_eq] at ha hb
    exact absurd ha.2.1 (not_le.mpr hb.2.1)
  have hSYfin : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).Finite :=
    finite_coneBall L v w γ Y
  have hStfin : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).Finite :=
    finite_coneBall L v w γ t
  have hDfin : ({a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).Finite :=
    hStfin.subset (fun a ha => ⟨ha.1, ha.2.2.1, ha.2.2.2⟩)
  have hadd : ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).ncard : ℕ) : ℝ)
      = ((({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).ncard : ℕ) : ℝ)
        + ((({a : ι → ℤ | a ∈ L ∧ Y < eNorm a ∧ eNorm a ≤ t ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ} : Set (ι → ℤ)).ncard : ℕ) : ℝ) := by
    have h := Set.ncard_union_eq hdisj hSYfin hDfin
    rw [← huni] at h
    rw [h, Nat.cast_add]
  rw [hcard]
  simp only [coneCount]
  linarith [hadd]

end Work.HP.BallConeK
