import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

namespace Work.Oscillation.Lacunary

open Finset

/-- `lacScale ρ j` is at most `ρ ^ j`. -/
lemma lacScale_le_pow {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) :
    (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) ≤ ρ ^ j :=
  Nat.floor_le (pow_nonneg hρ j)

/-- `lacScale ρ j ≥ 1` for `ρ ≥ 1`. -/
lemma one_le_lacScale {ρ : ℝ} (hρ : 1 ≤ ρ) (j : ℕ) :
    1 ≤ Work.BourgainPlan.Oscillation.lacScale ρ j := by
  have h : 0 < Work.BourgainPlan.Oscillation.lacScale ρ j :=
    Nat.floor_pos.mpr (one_le_pow₀ (n := j) hρ)
  omega

/-- For `ρ^j ≥ 2`, the lacunary scale is at least half of `ρ^j`. -/
lemma half_le_lacScale {ρ : ℝ} (j : ℕ) (h : 2 ≤ ρ ^ j) :
    ρ ^ j / 2 ≤ (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) := by
  have h1 : ρ ^ j < ((⌊ρ ^ j⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : ρ ^ j < (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) + 1 := h1
  linarith

/-- The first half of the window condition: `t · ρ^{-j} < θ` implies `t/θ < ρ^j`. -/
lemma cond_lt {ρ : ℝ} (hρ0 : 0 < ρ) {t θ : ℝ} (hθ : 0 < θ) {j : ℕ}
    (h : t * ρ ^ (-(j:ℤ)) < θ) : t / θ < ρ ^ j := by
  have hρj : (0:ℝ) < ρ ^ j := pow_pos hρ0 j
  have h1 : t / ρ ^ j < θ := by
    rw [zpow_neg, zpow_natCast] at h
    simpa [div_eq_mul_inv] using h
  have h2 : t < θ * ρ ^ j := (div_lt_iff₀ hρj).mp h1
  rw [div_lt_iff₀ hθ]
  linarith

/-- The second half of the window condition: `θ ≤ t / lacScale ρ j` together with `ρ^j ≥ 2`
implies `ρ^j ≤ 2 · (t/θ)`. -/
lemma cond_ge {ρ : ℝ} (hρ : 1 < ρ) {t θ : ℝ} (hθ : 0 < θ) {j : ℕ} (hj : 2 ≤ ρ ^ j)
    (h : θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ)) :
    ρ ^ j ≤ 2 * (t / θ) := by
  have hLj : (0:ℝ) < (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) :=
    Nat.cast_pos.mpr (by have := one_le_lacScale hρ.le j; omega)
  have hLhalf : ρ ^ j / 2 ≤ (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) :=
    half_le_lacScale j hj
  have h2' : θ * (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ) ≤ t :=
    (le_div_iff₀ hLj).mp h
  have h3 : θ * (ρ ^ j / 2) ≤ t :=
    le_trans (mul_le_mul_of_nonneg_left hLhalf hθ.le) h2'
  have h4 : θ * ρ ^ j ≤ 2 * t := by linarith
  have h5 : ρ ^ j ≤ 2 * t / θ := (le_div_iff₀ hθ).mpr (by linarith)
  rwa [mul_div_assoc] at h5

theorem gap_count (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t θ : ℝ) (s : Finset ℕ), 0 ≤ t →
      ∑ j ∈ s, (if t * ρ ^ (-(j:ℤ)) < θ ∧
          θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ)
        then (1:ℝ) else 0) ≤ M := by
  have hρ0 : (0:ℝ) < ρ := lt_trans zero_lt_one hρ
  have hρ1 : (1:ℝ) ≤ ρ := hρ.le
  -- a fixed lacunary index at which the scale is already `≥ 2`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (2:ℝ) ≤ ρ ^ n := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2:ℝ) hρ
    exact ⟨k, hk.le⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hn
    · exact h
  have hMpos : (0:ℝ) < ((2 * n : ℕ) : ℝ) := by
    have : 0 < 2 * n := by omega
    exact_mod_cast this
  refine ⟨((2 * n : ℕ) : ℝ), hMpos, ?_⟩
  intro t θ s ht
  by_cases hθ : 0 < θ
  · -- the window is non-empty; count the contributing indices
    rw [Finset.sum_boole]
    set T : Finset ℕ := s.filter (fun j =>
      t * ρ ^ (-(j:ℤ)) < θ ∧ θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ))
      with hT
    set T₂ : Finset ℕ := T.filter (fun j => n ≤ j) with hT2def
    -- the two consequences of the window condition at a large index
    have key : ∀ j : ℕ, 2 ≤ ρ ^ j →
        (t * ρ ^ (-(j:ℤ)) < θ ∧
          θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ)) →
        (ρ ^ j ≤ 2 * (t / θ) ∧ t / θ < ρ ^ j) :=
      fun j hj hcon =>
        ⟨cond_ge hρ hθ hj hcon.2, cond_lt hρ0 hθ hcon.1⟩
    have hT1 : (T.filter (fun j => j < n)).card ≤ n := by
      calc (T.filter (fun j => j < n)).card ≤ (Finset.range n).card :=
            Finset.card_le_card (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
        _ = n := Finset.card_range n
    have hT2 : T₂.card ≤ n := by
      rcases Finset.eq_empty_or_nonempty T₂ with hemp | hne
      · rw [hemp]; simp
      · obtain ⟨m, hm_mem, hmin⟩ : ∃ m ∈ T₂, ∀ j ∈ T₂, m ≤ j :=
          ⟨T₂.min' hne, Finset.min'_mem T₂ hne, fun j hj => Finset.min'_le T₂ j hj⟩
        have hmT : m ∈ T := (Finset.mem_filter.mp (hT2def ▸ hm_mem)).1
        have hmn : n ≤ m := (Finset.mem_filter.mp (hT2def ▸ hm_mem)).2
        have hconm := (Finset.mem_filter.mp (hT ▸ hmT)).2
        have hpm2 : (2:ℝ) ≤ ρ ^ m := le_trans hn (pow_le_pow_right₀ hρ1 hmn)
        have hfm := key m hpm2 hconm
        have hcont : T₂ ⊆ Finset.Ico m (m + n) := by
          intro j hj
          have hjT : j ∈ T := (Finset.mem_filter.mp (hT2def ▸ hj)).1
          refine Finset.mem_Ico.mpr ⟨hmin j hj, ?_⟩
          by_cases hjm : j = m
          · omega
          · have hmj : m < j := lt_of_le_of_ne (hmin j hj) (Ne.symm hjm)
            have hconj := (Finset.mem_filter.mp (hT ▸ hjT)).2
            have hpj2 : (2:ℝ) ≤ ρ ^ j := le_trans hpm2 (pow_le_pow_right₀ hρ1 hmj.le)
            have hfj := key j hpj2 hconj
            have hpmpos : (0:ℝ) < ρ ^ m := pow_pos hρ0 m
            have hC : ρ ^ j < 2 * ρ ^ m := by
              have hB : 2 * (t/θ) < 2 * ρ ^ m := by linarith [hfm.2]
              linarith [hfj.1]
            have hD : ρ ^ (j - m) < 2 := by
              have h1 : ρ ^ (j - m) * ρ ^ m < 2 * ρ ^ m := by
                rw [← pow_add, Nat.sub_add_cancel hmj.le]; exact hC
              exact (mul_lt_mul_iff_of_pos_right hpmpos).mp h1
            have hE : j - m < n := by
              by_contra hcon
              have hnle : n ≤ j - m := Nat.le_of_not_lt hcon
              have : ρ ^ n ≤ ρ ^ (j - m) := pow_le_pow_right₀ hρ1 hnle
              linarith
            omega
        calc T₂.card ≤ (Finset.Ico m (m + n)).card := Finset.card_le_card hcont
          _ = n := by simp
    have hTcard : T.card ≤ 2 * n := by
      have hunion : T = T.filter (fun j => j < n) ∪ T₂ := by
        rw [hT2def]
        ext j
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro h
          rcases Nat.lt_or_ge j n with h' | h'
          · exact Or.inl ⟨h, h'⟩
          · exact Or.inr ⟨h, h'⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hle := Finset.card_union_le (T.filter (fun j => j < n)) T₂
      rw [← hunion] at hle
      calc T.card ≤ (T.filter (fun j => j < n)).card + T₂.card := hle
        _ ≤ n + n := Nat.add_le_add hT1 hT2
        _ = 2 * n := by ring
    exact_mod_cast hTcard
  · -- `θ ≤ 0`: the condition fails for every index
    have hθ' : θ ≤ 0 := not_lt.mp hθ
    have hfalse : ∀ j : ℕ,
        ¬ (t * ρ ^ (-(j:ℤ)) < θ ∧
            θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ)) := by
      intro j hcon
      have hpos : 0 ≤ t * ρ ^ (-(j:ℤ)) := mul_nonneg ht (zpow_pos hρ0 _).le
      linarith [hcon.1, hθ']
    have hzero : (∑ j ∈ s, (if t * ρ ^ (-(j:ℤ)) < θ ∧
        θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ j : ℝ)
        then (1:ℝ) else 0)) = 0 :=
      Finset.sum_eq_zero (fun j _ => by rw [if_neg (hfalse j)])
    rw [hzero]
    exact hMpos.le

end Work.Oscillation.Lacunary
