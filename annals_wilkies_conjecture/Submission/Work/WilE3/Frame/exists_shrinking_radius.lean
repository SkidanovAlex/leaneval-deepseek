import Mathlib

namespace Work.WilE3.Frame

set_option autoImplicit false
-- `hsel_card` (and `N`) are part of the fixed statement but not needed for this lemma.
set_option linter.unusedVariables false
noncomputable section
open Classical

variable {k : ℕ}

/-- The supremum of the distances `‖Z z - x‖` over the finite set `sel ε`; it is set to `0`
when `sel ε` is empty. -/
def supDist (Z : ℂ → Fin k → ℂ) (x : Fin k → ℂ) (sel : ℂ → Finset ℂ) (ε : ℂ) : ℝ :=
  if h : (sel ε).Nonempty then (sel ε).sup' h (fun z => ‖Z z - x‖) else 0

lemma supDist_nonneg (Z : ℂ → Fin k → ℂ) (x : Fin k → ℂ) (sel : ℂ → Finset ℂ) (ε : ℂ) :
    0 ≤ supDist Z x sel ε := by
  unfold supDist
  split_ifs with h
  · obtain ⟨z, hz⟩ := h
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun z => ‖Z z - x‖) hz)
  · exact le_refl 0

lemma le_supDist (Z : ℂ → Fin k → ℂ) (x : Fin k → ℂ) (sel : ℂ → Finset ℂ) (ε : ℂ) {z : ℂ}
    (hz : z ∈ sel ε) : ‖Z z - x‖ ≤ supDist Z x sel ε := by
  have hne : (sel ε).Nonempty := ⟨z, hz⟩
  unfold supDist
  rw [dif_pos hne]
  exact Finset.le_sup' (fun z => ‖Z z - x‖) hz

theorem exists_shrinking_radius {k : ℕ} {N : ℕ} {δ rr : ℝ}
    (G : ℂ → ℂ) (Z : ℂ → Fin k → ℂ) (x : Fin k → ℂ) (sel : ℂ → Finset ℂ)
    (hsel_card : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → (sel ε).card = N)
    (hsel_sub : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ →
      ∀ z ∈ sel ε, G z = ε ∧ ‖z‖ < rr)
    (hsel_empty : ∀ ε : ℂ, ¬ (0 < ‖ε‖ ∧ ‖ε‖ < δ) → sel ε = ∅)
    (hconv : ∀ η : ℝ, 0 < η → ∀ᶠ ε in nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0},
      ∀ z : ℂ, G z = ε → ‖z‖ < rr → ‖z‖ < η)
    (hZcont : ContinuousAt Z 0) (hZ0 : Z 0 = x) :
    ∃ ρ : ℂ → ℝ, (∀ ε, 0 < ρ ε) ∧
      Filter.Tendsto ρ (nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}) (nhds 0) ∧
      (∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → ∀ z ∈ sel ε, ‖Z z - x‖ < ρ ε) := by
  classical
  -- ### Step 1: the supremum of `‖Z z - x‖` over `sel ε` tends to `0`.
  have hbound : Filter.Tendsto (supDist Z x sel)
      (nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}) (nhds 0) := by
    rw [tendsto_order]
    refine ⟨?_, ?_⟩
    · -- lower bound: the supremum is always `≥ 0`
      intro b hb
      exact Filter.Eventually.of_forall fun ε =>
        lt_of_lt_of_le hb (supDist_nonneg Z x sel ε)
    · -- upper bound: eventually the supremum is `< b`
      intro b hb
      -- continuity of `Z` at `0` gives a radius `δZ` on which `‖Z z - x‖ < b`
      rw [Metric.continuousAt_iff] at hZcont
      obtain ⟨δZ, hδZpos, hδZ⟩ := hZcont b hb
      have hδZ' : ∀ z : ℂ, dist z 0 < δZ → ‖Z z - x‖ < b := by
        intro z hz
        have := hδZ hz
        rw [hZ0, dist_eq_norm] at this
        exact this
      -- `hconv` gives a punctured neighbourhood where the elements near level `ε` are small
      have hc := hconv δZ hδZpos
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hc
      obtain ⟨m, hmpos, hm⟩ := hc
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨m, hmpos, ?_⟩
      rintro ε hε hεne
      rw [supDist]
      split_ifs with hne
      · -- `sel ε ≠ ∅`: bound each element
        have hpos : 0 < ‖ε‖ := norm_pos_iff.mpr (by simpa using hεne)
        by_cases hltδ : ‖ε‖ < δ
        · rw [Finset.sup'_lt_iff]
          intro z hz
          obtain ⟨hGz, hzr⟩ := hsel_sub ε hpos hltδ z hz
          have hzsmall : ‖z‖ < δZ := hm hε hεne z hGz hzr
          exact hδZ' z (by simpa [dist_eq_norm] using hzsmall)
        · -- otherwise `sel ε = ∅`, contradicting nonemptiness
          exact absurd hne (by
            rw [hsel_empty ε (by rintro ⟨h1, h2⟩; exact hltδ h2)]
            exact Finset.not_nonempty_empty)
      · exact hb
  -- ### Step 2: define `ρ ε = supDist ε + ‖ε‖` (with a harmless bump at `ε = 0`).
  let ρ : ℂ → ℝ := fun ε => if ε = 0 then 1 else supDist Z x sel ε + ‖ε‖
  have hρpos : ∀ ε, 0 < ρ ε := by
    intro ε
    dsimp only [ρ]
    by_cases h : ε = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
      have h1 := supDist_nonneg Z x sel ε
      have h2 : 0 < ‖ε‖ := norm_pos_iff.mpr h
      linarith
  have hρbound : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → ∀ z ∈ sel ε, ‖Z z - x‖ < ρ ε := by
    intro ε hpos hltδ z hz
    dsimp only [ρ]
    rw [if_neg (norm_pos_iff.mp hpos)]
    have h1 : ‖Z z - x‖ ≤ supDist Z x sel ε := le_supDist Z x sel ε hz
    linarith
  -- ### Step 3: `ρ` tends to `0`.
  have hnorm_tend : Filter.Tendsto (fun ε : ℂ => ‖ε‖)
      (nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}) (nhds 0) := by
    have := continuous_norm.tendsto (0 : ℂ)
    simp only [norm_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hg : Filter.Tendsto (fun ε : ℂ => supDist Z x sel ε + ‖ε‖)
      (nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}) (nhds 0) := by
    have := hbound.add hnorm_tend
    simpa using this
  have hρeq : ρ =ᶠ[nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}]
      (fun ε : ℂ => supDist Z x sel ε + ‖ε‖) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    dsimp only [ρ]
    rw [if_neg (by simpa using hε)]
  have hρtend : Filter.Tendsto ρ (nhdsWithin (0 : ℂ) {x : ℂ | x ≠ 0}) (nhds 0) :=
    Filter.Tendsto.congr' hρeq.symm hg
  exact ⟨ρ, hρpos, hρtend, hρbound⟩

end

end Work.WilE3.Frame
