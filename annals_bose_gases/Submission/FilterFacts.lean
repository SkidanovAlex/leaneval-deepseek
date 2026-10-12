import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 0: filter facts behind `BoseGases.e`.

`e ρ v = (jointFilter ρ).limUnder (fun (L,N) ↦ L⁻³ · box energy)`.  To extract bounds
on `e` we need the standard `Tendsto → limUnder` API and basic facts about the filter.
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Every nonnegative real has a natural number within distance `< 1` above it. -/
lemma exists_nat_within_one (x : ℝ) (hx : 0 ≤ x) :
    ∃ N : ℕ, (N : ℝ) ≤ x ∧ x < (N : ℝ) + 1 := by
  let z : ℤ := Int.floor x
  have hz0 : 0 ≤ z := Int.floor_nonneg.mpr hx
  have hztoNat : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz0)
  refine ⟨z.toNat, ?_, ?_⟩
  · calc
      (z.toNat : ℝ) = (z : ℝ) := hztoNat
      _ ≤ x := Int.floor_le x
  · calc
      x < (z : ℝ) + 1 := Int.lt_floor_add_one x
      _ = (z.toNat : ℝ) + 1 := by rw [hztoNat]

/-- For `0 ≤ ρ`, for a sufficiently large side length `L ≥ 1` there is a particle number
`N` with `|N / L³ − ρ| < ε`.  The only size condition on `L` is `1 / ε < L`. -/
lemma exists_particle_number (ρ : ℝ) (hρ : 0 ≤ ρ) {ε L : ℝ} (hε : 0 < ε) (hL1 : 1 ≤ L)
    (hbig : 1 / ε < L) : ∃ N : ℕ, |(N : ℝ) / L ^ 3 - ρ| < ε := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let x : ℝ := ρ * L ^ 3
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hρ (pow_nonneg (by linarith) 3)
  obtain ⟨N, hN1, hN2⟩ := exists_nat_within_one x hx0
  refine ⟨N, ?_⟩
  have hxn : 0 ≤ x - (N : ℝ) := by linarith
  have hxn1 : x - (N : ℝ) < 1 := by linarith
  have h_abs1 : |(N : ℝ) - x| < 1 := by
    have h' : |x - (N : ℝ)| < 1 := by
      rw [abs_of_nonneg hxn]
      exact hxn1
    simpa [abs_sub_comm] using h'
  have hL3pos : 0 < L ^ 3 := pow_pos hLpos 3
  have hL3ne : L ^ 3 ≠ 0 := ne_of_gt hL3pos
  have hEq : (N : ℝ) / L ^ 3 - ρ = ((N : ℝ) - x) / L ^ 3 := by
    dsimp [x]
    field_simp [hL3ne]
  have hmain1 : |(N : ℝ) / L ^ 3 - ρ| = |(N : ℝ) - x| / L ^ 3 := by
    rw [hEq]
    rw [abs_div]
    rw [abs_of_pos hL3pos]
  rw [hmain1]
  have h_le1 : |(N : ℝ) - x| / L ^ 3 ≤ 1 / L ^ 3 :=
    div_le_div_of_nonneg_right h_abs1.le hL3pos.le
  have hLL3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by decide : 3 ≠ 0)
  have h_1L3_le : 1 / L ^ 3 ≤ 1 / L := one_div_le_one_div_of_le hLpos hLL3
  have h_1L_lt : 1 / L < ε := (one_div_lt hε hLpos).mp hbig
  exact lt_of_le_of_lt h_le1 (lt_of_le_of_lt h_1L3_le h_1L_lt)

/-- The joint filter is nontrivial for densities `ρ ≥ 0`. -/
lemma jointFilter_neBot {ρ : ℝ} (hρ : 0 ≤ ρ) : (jointFilter ρ).NeBot := by
  rw [Filter.neBot_iff]
  by_contra h
  have hbot : jointFilter ρ = ⊥ := h
  unfold jointFilter at hbot
  rcases (Filter.inf_eq_bot_iff.mp hbot) with ⟨U, hU, V, hV, hdisj⟩
  rcases (Filter.mem_comap.mp hU) with ⟨s, hs, hsubU⟩
  rcases (Filter.mem_atTop_sets.mp hs) with ⟨a, ha⟩
  rcases (Filter.mem_comap.mp hV) with ⟨t, ht, hsubV⟩
  rcases (Metric.mem_nhds_iff.mp ht) with ⟨ε, hε, hball⟩
  -- choose a natural `k` with `k ≥ a`, `k ≥ 1` and `k > 1 / ε`, and put `L = k`
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge (max a 1)
  obtain ⟨k₂, hk₂⟩ := exists_nat_gt (1 / ε)
  let k : ℕ := max k₁ k₂
  let L : ℝ := k
  have hk₁k : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_max_left k₁ k₂
  have hk₂k : (k₂ : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_max_right k₁ k₂
  have haL : a ≤ L := by
    dsimp [L, k]
    exact le_trans (le_max_left a 1) (le_trans hk₁ hk₁k)
  have hL1 : 1 ≤ L := by
    dsimp [L, k]
    exact le_trans (le_max_right a 1) (le_trans hk₁ hk₁k)
  have hbig : 1 / ε < L := by
    dsimp [L, k]
    exact lt_of_lt_of_le hk₂ hk₂k
  obtain ⟨N, hN⟩ := exists_particle_number ρ hρ hε hL1 hbig
  let p : ℝ × ℕ := (L, N)
  -- `p` lies in the horizontal-ray part `U`
  have pU : p ∈ U := by
    exact hsubU (by simpa [p, L] using ha L haL)
  -- `p` lies in the density part `V`
  have pV : p ∈ V := by
    exact hsubV (by
      have hNmem : (N : ℝ) / L ^ 3 ∈ Metric.ball ρ ε := by
        simpa [Real.dist_eq] using hN
      exact hball hNmem)
  have hp : p ∈ U ∩ V := ⟨pU, pV⟩
  rw [hdisj] at hp
  exact hp

/-- Along the joint filter at density `ρ`, the side length diverges. -/
lemma tendsto_fst_atTop (ρ : ℝ) : Tendsto (fun (p : ℝ × ℕ) => p.1) (jointFilter ρ) atTop := by
  unfold jointFilter
  refine Filter.Tendsto.mono_left ?_ inf_le_left
  exact Filter.tendsto_comap

/-- Along the joint filter at density `ρ`, the density `N / L³` tends to `ρ`. -/
lemma tendsto_density (ρ : ℝ) : Tendsto (fun (p : ℝ × ℕ) => (p.2 : ℝ) / p.1 ^ 3) (jointFilter ρ) (𝓝 ρ) := by
  unfold jointFilter
  refine Filter.Tendsto.mono_left ?_ inf_le_right
  exact Filter.tendsto_comap

/-- Consequence of the two: along the joint filter, `L` is eventually positive. -/
lemma eventually_pos_L (ρ : ℝ) (_hρ : 0 ≤ ρ) :
    ∀ᶠ (p : ℝ × ℕ) in jointFilter ρ, 0 < p.1 := by
  have hL : ∀ᶠ L : ℝ in atTop, 0 < L := Filter.eventually_gt_atTop (0 : ℝ)
  exact (tendsto_fst_atTop ρ).eventually hL

end BoseGases

end Submission
