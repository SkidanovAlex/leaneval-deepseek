import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Analysis.InnerProductSpace

theorem exists_lyz_crossings {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {Γ : ℝ → F} {xS aF : F} {n₀ n : ℕ} {τ : ℝ} (hn : n₀ ≤ n) (hτ : 0 ≤ τ) (hcont : ContinuousOn Γ (Set.Icc 0 τ)) (haF : ‖aF‖ = 1) (hΓτ : Γ τ = xS + (2:ℝ) ^ n • aF) (h0lt : ‖Γ 0 - xS‖ < (2:ℝ) ^ n₀) : ∃ σ τhat : ℕ → ℝ, σ n = τ ∧ (∀ i, n₀ ≤ i → i ≤ n → σ i ∈ Set.Icc 0 τ ∧ ‖Γ (σ i) - xS‖ = (2:ℝ) ^ i ∧ (∀ t ∈ Set.Icc (σ i) τ, (2:ℝ) ^ i ≤ ‖Γ t - xS‖)) ∧ (∀ i, n₀ ≤ i → i < n → σ i ≤ σ (i + 1)) ∧ (∀ i, n₀ ≤ i → i < n → τhat i ∈ Set.Icc (σ i) (σ (i + 1)) ∧ ‖Γ (τhat i) - xS‖ = ‖Γ (τhat i) - Γ (σ (i + 1))‖ ∧ (2:ℝ) ^ i ≤ ‖Γ (τhat i) - xS‖) := by
  have h2le : (1:ℝ) ≤ 2 := by norm_num
  have h2lt : (1:ℝ) < 2 := by norm_num
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hpow_mono : ∀ i j : ℕ, i ≤ j → (2:ℝ)^i ≤ (2:ℝ)^j := fun i j h => pow_le_pow_right₀ h2le h
  have hpow_pos : ∀ i : ℕ, (0:ℝ) < (2:ℝ)^i := fun i => pow_pos h2pos i
  have hcontf : ContinuousOn (fun t => ‖Γ t - xS‖) (Set.Icc (0:ℝ) τ) :=
    (hcont.sub continuousOn_const).norm
  have hnormτ : ‖Γ τ - xS‖ = (2:ℝ)^n := by
    have hsub : Γ τ - xS = (2:ℝ)^n • aF := by rw [hΓτ]; abel
    rw [hsub, norm_smul, haF, mul_one, Real.norm_of_nonneg (pow_nonneg h2pos.le n)]
  -- the set of times at which ‖Γ t - xS‖ ≤ 2^i
  set S : ℕ → Set ℝ := fun i => {t : ℝ | t ∈ Set.Icc (0:ℝ) τ ∧ ‖Γ t - xS‖ ≤ (2:ℝ)^i} with hS
  have hS_mem : ∀ i t, t ∈ S i ↔ t ∈ Set.Icc (0:ℝ) τ ∧ ‖Γ t - xS‖ ≤ (2:ℝ)^i := by
    intro i t; simp only [hS]
    exact Iff.rfl
  have hS_ne : ∀ i, n₀ ≤ i → (S i).Nonempty := by
    intro i hi
    refine ⟨0, ?_⟩
    rw [hS_mem i]
    exact ⟨⟨le_refl 0, hτ⟩, le_of_lt (lt_of_lt_of_le h0lt (hpow_mono n₀ i hi))⟩
  have hS_bdd : ∀ i, BddAbove (S i) := by
    intro i
    refine ⟨τ, fun t ht => ?_⟩
    rw [hS_mem i] at ht
    exact ht.1.2
  have hS_closed : ∀ i, IsClosed (S i) := by
    intro i
    have hset : S i = Set.Icc (0:ℝ) τ ∩ (fun t => ‖Γ t - xS‖) ⁻¹' Set.Iic ((2:ℝ)^i) := by
      ext t
      rw [hS_mem i]
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    rw [hset]
    exact hcontf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  -- σ: the last time at which the curve is inside the ball of radius 2^i
  have hσ_mem : ∀ i, n₀ ≤ i → sSup (S i) ∈ S i := by
    intro i hi
    exact (hS_closed i).csSup_mem (hS_ne i hi) (hS_bdd i)
  have hσval : ∀ i, n₀ ≤ i → i ≤ n → ‖Γ (sSup (S i)) - xS‖ = (2:ℝ)^i := by
    intro i hi hile
    have hmem := hσ_mem i hi
    rw [hS_mem i] at hmem
    obtain ⟨hmemIcc, hle⟩ := hmem
    refine le_antisymm hle ?_
    by_contra hcon
    simp only [not_le] at hcon
    rcases lt_or_eq_of_le hmemIcc.2 with hσlt | hσeq
    · -- σ i < τ : a small step to the right stays inside S i
      have hε : 0 < (2:ℝ)^i - ‖Γ (sSup (S i)) - xS‖ := sub_pos.mpr hcon
      have hcwa := (hcontf.continuousWithinAt hmemIcc)
      rw [Metric.continuousWithinAt_iff] at hcwa
      obtain ⟨δ, hδpos, hδ⟩ := hcwa ((2:ℝ)^i - ‖Γ (sSup (S i)) - xS‖) hε
      set t : ℝ := sSup (S i) + min δ (τ - sSup (S i)) / 2 with ht
      have hminpos : 0 < min δ (τ - sSup (S i)) := lt_min hδpos (sub_pos.mpr hσlt)
      have ht_gt : sSup (S i) < t := by rw [ht]; linarith
      have ht_le : t ≤ τ := by
        rw [ht]; have := min_le_right δ (τ - sSup (S i)); linarith
      have ht_ge : 0 ≤ t := le_trans hmemIcc.1 ht_gt.le
      have hdist : dist t (sSup (S i)) < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht_gt), ht]
        have := min_le_left δ (τ - sSup (S i)); linarith
      have hδt := hδ ⟨ht_ge, ht_le⟩ hdist
      rw [Real.dist_eq, abs_lt] at hδt
      have hlt2 : ‖Γ t - xS‖ < (2:ℝ)^i := by linarith [hδt.2]
      have htS : t ∈ S i := by
        rw [hS_mem i]; exact ⟨⟨ht_ge, ht_le⟩, hlt2.le⟩
      have htle : t ≤ sSup (S i) := le_csSup (hS_bdd i) htS
      linarith
    · -- σ i = τ : then necessarily i = n
      have hleτ : ‖Γ τ - xS‖ ≤ (2:ℝ)^i := by rw [hσeq] at hle; exact hle
      rw [hnormτ] at hleτ
      have hni : n ≤ i := (pow_le_pow_iff_right₀ h2lt).mp hleτ
      have heq : ‖Γ (sSup (S i)) - xS‖ = (2:ℝ)^i := by
        rw [hσeq, hnormτ, le_antisymm hni hile]
      linarith
  have hσle : ∀ i, n₀ ≤ i → i ≤ n → ∀ t ∈ Set.Icc (sSup (S i)) τ, (2:ℝ)^i ≤ ‖Γ t - xS‖ := by
    intro i hi hile t ht
    have hmem := hσ_mem i hi
    rw [hS_mem i] at hmem
    obtain ⟨hmemIcc, _⟩ := hmem
    by_contra hcon
    simp only [not_le] at hcon
    have htS : t ∈ S i := by
      rw [hS_mem i]
      exact ⟨⟨le_trans hmemIcc.1 ht.1, ht.2⟩, hcon.le⟩
    have htle : t ≤ sSup (S i) := le_csSup (hS_bdd i) htS
    have hteq : t = sSup (S i) := le_antisymm htle ht.1
    rw [hteq] at hcon
    exact absurd (hσval i hi hile) (ne_of_lt hcon)
  have hσn : sSup (S n) = τ := by
    have hmemτ : τ ∈ S n := by
      rw [hS_mem n]
      exact ⟨⟨hτ, le_refl τ⟩, le_of_eq hnormτ⟩
    have hbdd := hS_bdd n
    have hne := hS_ne n hn
    have hle : sSup (S n) ≤ τ := (csSup_le_iff hbdd hne).mpr (by
      intro b hb; rw [hS_mem n] at hb; exact hb.1.2)
    exact le_antisymm hle (le_csSup hbdd hmemτ)
  have hσmono : ∀ i, n₀ ≤ i → i < n → sSup (S i) ≤ sSup (S (i + 1)) := by
    intro i hi _
    refine csSup_le_csSup (hS_bdd (i + 1)) (hS_ne i hi) ?_
    intro t ht
    rw [hS_mem i] at ht
    rw [hS_mem (i + 1)]
    exact ⟨ht.1, le_trans ht.2 (hpow_mono i (i + 1) (Nat.le_succ i))⟩
  -- τhat: a crossing point equidistant from xS and Γ (σ (i+1))
  have hex : ∀ i, n₀ ≤ i → i < n → ∃ t : ℝ, t ∈ Set.Icc (sSup (S i)) (sSup (S (i + 1))) ∧ ‖Γ t - xS‖ = ‖Γ t - Γ (sSup (S (i + 1)))‖ ∧ (2:ℝ)^i ≤ ‖Γ t - xS‖ := by
    intro i hi hin
    have hile : i ≤ n := le_of_lt hin
    have hi1 : n₀ ≤ i + 1 := le_trans hi (Nat.le_succ i)
    have hi1n : i + 1 ≤ n := Nat.succ_le_of_lt hin
    have hmono := hσmono i hi hin
    have hmem := hσ_mem i hi
    rw [hS_mem i] at hmem
    obtain ⟨hmemIcc, _⟩ := hmem
    have hmem1 := hσ_mem (i + 1) hi1
    rw [hS_mem (i + 1)] at hmem1
    obtain ⟨hmemIcc1, _⟩ := hmem1
    have hsub : Set.Icc (sSup (S i)) (sSup (S (i + 1))) ⊆ Set.Icc (0:ℝ) τ :=
      fun t ht => ⟨le_trans hmemIcc.1 ht.1, le_trans ht.2 hmemIcc1.2⟩
    have hgcont : ContinuousOn (fun t => ‖Γ t - xS‖ - ‖Γ t - Γ (sSup (S (i + 1)))‖)
        (Set.Icc (sSup (S i)) (sSup (S (i + 1)))) := by
      have h1 : ContinuousOn (fun t => ‖Γ t - xS‖) (Set.Icc (sSup (S i)) (sSup (S (i + 1)))) :=
        hcontf.mono hsub
      have h2 : ContinuousOn (fun t => ‖Γ t - Γ (sSup (S (i + 1)))‖)
          (Set.Icc (sSup (S i)) (sSup (S (i + 1)))) :=
        ((hcont.sub continuousOn_const).mono hsub).norm
      exact h1.sub h2
    have hgb : 0 ≤ ‖Γ (sSup (S (i + 1))) - xS‖ - ‖Γ (sSup (S (i + 1))) - Γ (sSup (S (i + 1)))‖ := by
      rw [sub_self, norm_zero, sub_zero, hσval (i + 1) hi1 hi1n]
      exact (hpow_pos (i + 1)).le
    have hga : ‖Γ (sSup (S i)) - xS‖ - ‖Γ (sSup (S i)) - Γ (sSup (S (i + 1)))‖ ≤ 0 := by
      have htri := norm_sub_norm_le (Γ (sSup (S (i + 1))) - xS) (Γ (sSup (S i)) - xS)
      rw [sub_sub_sub_cancel_right] at htri
      rw [hσval (i + 1) hi1 hi1n, hσval i hi hile] at htri
      have hpow : (2:ℝ)^(i + 1) - (2:ℝ)^i = (2:ℝ)^i := by rw [pow_succ]; ring
      rw [hpow] at htri
      have hsym : ‖Γ (sSup (S (i + 1))) - Γ (sSup (S i))‖ = ‖Γ (sSup (S i)) - Γ (sSup (S (i + 1)))‖ := by
        rw [← neg_sub, norm_neg]
      rw [hsym] at htri
      have hAi : ‖Γ (sSup (S i)) - xS‖ = (2:ℝ)^i := hσval i hi hile
      linarith
    have hIVT := intermediate_value_Icc hmono hgcont ⟨hga, hgb⟩
    rw [Set.mem_image] at hIVT
    obtain ⟨c, hc, hc0⟩ := hIVT
    refine ⟨c, hc, sub_eq_zero.mp hc0, ?_⟩
    exact hσle i hi hile c ⟨hc.1, le_trans hc.2 hmemIcc1.2⟩
  have hexall : ∀ i, ∃ t : ℝ, n₀ ≤ i → i < n → t ∈ Set.Icc (sSup (S i)) (sSup (S (i + 1))) ∧ ‖Γ t - xS‖ = ‖Γ t - Γ (sSup (S (i + 1)))‖ ∧ (2:ℝ)^i ≤ ‖Γ t - xS‖ := by
    intro i
    by_cases h : n₀ ≤ i ∧ i < n
    · obtain ⟨t, ht⟩ := hex i h.1 h.2
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  refine ⟨fun i => sSup (S i), fun i => Classical.choose (hexall i), hσn, ?_, hσmono, ?_⟩
  · intro i hi hile
    have hmem := hσ_mem i hi
    rw [hS_mem i] at hmem
    exact ⟨hmem.1, hσval i hi hile, hσle i hi hile⟩
  · intro i h1 h2
    exact Classical.choose_spec (hexall i) h1 h2

end Commons.Analysis.InnerProductSpace