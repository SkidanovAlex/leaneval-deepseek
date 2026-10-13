import Mathlib
import Submission.Work.WilC4.ProfileDefs

namespace Work.WilC4

open Set

/-- Pigeonhole for dyadic slots: a finite set `B` of at most `P` reals misses at least one of
the `P + 1` dyadic open intervals `(2 ^ j, 2 ^ (j + 1))`, `j = 0, …, P`. -/
lemma base_est_slot_free (B : Finset ℝ) (P : ℕ) (hB : B.card ≤ P) :
    ∃ j ∈ Finset.range (P + 1), ∀ b ∈ B, ¬ ((2 : ℝ) ^ j < b ∧ b < (2 : ℝ) ^ (j + 1)) := by
  by_contra hcon
  push Not at hcon
  let f : ℕ → ℝ := fun j =>
    if h : ∃ b ∈ B, (2 : ℝ) ^ j < b ∧ b < (2 : ℝ) ^ (j + 1) then h.choose else 0
  have hspec : ∀ j ∈ Finset.range (P + 1),
      f j ∈ B ∧ (2 : ℝ) ^ j < f j ∧ f j < (2 : ℝ) ^ (j + 1) := by
    intro j hj
    have h : ∃ b ∈ B, (2 : ℝ) ^ j < b ∧ b < (2 : ℝ) ^ (j + 1) := hcon j hj
    have hfj : f j = h.choose := by
      dsimp only [f]
      exact dite_eq_left h
    rw [hfj]
    exact h.choose_spec
  have hinj : Set.InjOn f ↑(Finset.range (P + 1)) := by
    intro j hj j' hj' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : f j < (2 : ℝ) ^ (j + 1) := (hspec j hj).2.2
      have h2 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ j' :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      have h3 : (2 : ℝ) ^ j' < f j' := (hspec j' hj').2.1
      rw [← heq] at h3
      linarith
    · have h1 : f j' < (2 : ℝ) ^ (j' + 1) := (hspec j' hj').2.2
      have h2 : (2 : ℝ) ^ (j' + 1) ≤ (2 : ℝ) ^ j :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      have h3 : (2 : ℝ) ^ j < f j := (hspec j hj).2.1
      rw [heq] at h3
      linarith
  have hcard : (Finset.range (P + 1)).card ≤ B.card :=
    Finset.card_le_card_of_injOn f (fun j hj => (hspec j hj).1) hinj
  rw [Finset.card_range] at hcard
  omega

/-- Monotonicity or antitonicity on the open interval `(a,b)` extends to the closed interval
`[a,b]` for a function continuous on `[a,b]` (with `a < b`). -/
lemma base_est_monoOrAnti_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b)) (hc : ContinuousOn f (Icc a b)) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  have hne : (Ioo a b).Nonempty := nonempty_Ioo.2 hab
  have ha_close : a ∈ closure (Ioo a b) := (isGLB_Ioo hab).mem_closure hne
  have hb_close : b ∈ closure (Ioo a b) := (isLUB_Ioo hab).mem_closure hne
  have hsub : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  have key : ∀ g : ℝ → ℝ, MonotoneOn g (Ioo a b) → ContinuousOn g (Icc a b) →
      MonotoneOn g (Icc a b) := by
    intro g hg hgc
    have h1 : MonotoneOn g (insert a (Ioo a b)) :=
      hg.insert_of_continuousWithinAt
        (by rw [← mem_closure_iff_clusterPt]; exact ha_close)
        ((hgc a (left_mem_Icc.mpr hab.le)).mono hsub)
    have hsub2 : insert a (Ioo a b) ⊆ Icc a b := by
      intro x hx
      rcases hx with rfl | hx
      · exact left_mem_Icc.mpr hab.le
      · exact hsub hx
    have h2 : MonotoneOn g (insert b (insert a (Ioo a b))) :=
      h1.insert_of_continuousWithinAt
        (by rw [← mem_closure_iff_clusterPt]
            exact closure_mono (subset_insert a (Ioo a b)) hb_close)
        ((hgc b (right_mem_Icc.mpr hab.le)).mono hsub2)
    refine h2.mono ?_
    intro x hx
    rcases lt_or_eq_of_le hx.1 with h1 | h1
    · rcases lt_or_eq_of_le hx.2 with h2 | h2
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · exact Or.inl h2
    · exact Or.inr (Or.inl h1.symm)
  rcases h with hmono | hanti
  · exact Or.inl (key f hmono hc)
  · refine Or.inr ?_
    have hneg : MonotoneOn (fun x => -f x) (Ioo a b) := by
      intro x hx y hy hxy
      have := hanti hx hy hxy
      linarith
    have hk := key (fun x => -f x) hneg hc.neg
    intro x hx y hy hxy
    have := hk hx hy hxy
    linarith

theorem base_est (P : ℕ) (ρ τ : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ) (hτρ : τ < ρ) :
    ∀ (β : ℝ) (G : ℝ → ℝ), (2 : ℝ) ^ (P + 1) ≤ β →
      ContinuousOn G (Set.Icc 1 β) →
      (∀ s ∈ Set.Icc 1 β, 0 < G s) →
      Work.WilC4.PieceMono G P →
      (∀ s ∈ Set.Icc 1 (β / 2), |G (2 * s) / G s - ρ| ≤ τ) →
      ∀ t ∈ Set.Icc 1 2,
        G t ≤ max (ρ + τ) 1 * ((ρ + τ) / (ρ - τ)) ^ P * G 1 := by
  intro β G hβ hcont hpos hpm hdbl t ht
  obtain ⟨B, hBcard, hBanti⟩ := hpm
  obtain ⟨j, hjmem, hfree⟩ := base_est_slot_free B P hBcard
  have hjle : j ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
  have hρτ : 0 < ρ - τ := sub_pos.mpr hτρ
  have hratio_ge1 : 1 ≤ (ρ + τ) / (ρ - τ) := by
    rw [le_div_iff₀ hρτ]
    linarith
  have hratio_nonneg : 0 ≤ (ρ + τ) / (ρ - τ) := le_trans zero_le_one hratio_ge1
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h1le2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have h2j_lt : (2 : ℝ) ^ j < (2 : ℝ) ^ (j + 1) := by
    have h : (2 : ℝ) ^ j * 1 < (2 : ℝ) ^ j * 2 :=
      mul_lt_mul_of_pos_left (by norm_num : (1 : ℝ) < 2) h2pos
    rw [mul_one] at h
    rw [pow_succ]
    exact h
  have h2j1_le : (2 : ℝ) ^ (j + 1) ≤ β := by
    have h1 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (P + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    linarith
  have h2j_le : (2 : ℝ) ^ j ≤ β := le_trans h2j_lt.le h2j1_le
  have h1β : (1 : ℝ) ≤ β := le_trans h1le2j h2j_le
  have ht_le : (2 : ℝ) ^ j * t ≤ (2 : ℝ) ^ (j + 1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left ht.2 h2pos.le
  have ht_ge : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j * t := by
    simpa using mul_le_mul_of_nonneg_left ht.1 h2pos.le
  have h2jt_le_β : (2 : ℝ) ^ j * t ≤ β := le_trans ht_le h2j1_le
  obtain ⟨hlo, _hhi⟩ :=
    chain_bound G ρ τ β hτ hτρ.le hpos hdbl j t ht.1 h2jt_le_β
  have hfree' : ∀ x ∈ Ioo ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)), x ∉ B :=
    fun x hx hxB => hfree x hxB ⟨hx.1, hx.2⟩
  have hmono := hBanti ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)) h2j_lt hfree'
  have hcontIcc : ContinuousOn G (Icc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1))) :=
    hcont.mono (fun x hx => ⟨le_trans h1le2j hx.1, le_trans hx.2 h2j1_le⟩)
  have hmonoIcc := base_est_monoOrAnti_Icc h2j_lt hmono hcontIcc
  have hG1pos : 0 < G 1 := hpos 1 ⟨le_refl 1, h1β⟩
  have hpj : 0 < (ρ - τ) ^ j := pow_pos hρτ j
  have hmax_nonneg : (0 : ℝ) ≤ max (ρ + τ) 1 := le_trans zero_le_one (le_max_right _ _)
  rcases hmonoIcc with hinc | hdec
  · have hstep1 : G ((2 : ℝ) ^ j * t) ≤ G ((2 : ℝ) ^ (j + 1)) :=
      hinc ⟨ht_ge, ht_le⟩ (right_mem_Icc.mpr h2j_lt.le) ht_le
    have hstep2 : G ((2 : ℝ) ^ (j + 1)) ≤ (ρ + τ) ^ (j + 1) * G 1 := by
      have h := (chain_bound G ρ τ β hτ hτρ.le hpos hdbl (j + 1) 1 le_rfl
        (by simpa using h2j1_le)).2
      simpa using h
    have hGt : G t ≤ (ρ + τ) ^ (j + 1) * G 1 / (ρ - τ) ^ j := by
      rw [le_div_iff₀' hpj]
      calc (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) := hlo
        _ ≤ G ((2 : ℝ) ^ (j + 1)) := hstep1
        _ ≤ (ρ + τ) ^ (j + 1) * G 1 := hstep2
    have hkey : (ρ + τ) ^ (j + 1) * G 1 / (ρ - τ) ^ j
        = (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ j * G 1 := by
      rw [pow_succ, div_pow]
      ring
    calc G t ≤ (ρ + τ) ^ (j + 1) * G 1 / (ρ - τ) ^ j := hGt
      _ = (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ j * G 1 := hkey
      _ ≤ max (ρ + τ) 1 * ((ρ + τ) / (ρ - τ)) ^ P * G 1 := by
          have hA : (ρ + τ) * ((ρ + τ) / (ρ - τ)) ^ j
              ≤ max (ρ + τ) 1 * ((ρ + τ) / (ρ - τ)) ^ P :=
            mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hratio_ge1 hjle)
              (pow_nonneg hratio_nonneg j) hmax_nonneg
          exact mul_le_mul hA le_rfl hG1pos.le (mul_nonneg hmax_nonneg
            (pow_nonneg hratio_nonneg P))
  · have hstep : G ((2 : ℝ) ^ j * t) ≤ G ((2 : ℝ) ^ j) :=
      hdec (left_mem_Icc.mpr h2j_lt.le) ⟨ht_ge, ht_le⟩ ht_ge
    have hstep2 : G ((2 : ℝ) ^ j) ≤ (ρ + τ) ^ j * G 1 := by
      have h := (chain_bound G ρ τ β hτ hτρ.le hpos hdbl j 1 le_rfl
        (by simpa using h2j_le)).2
      simpa using h
    have hGt : G t ≤ (ρ + τ) ^ j * G 1 / (ρ - τ) ^ j := by
      rw [le_div_iff₀' hpj]
      calc (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) := hlo
        _ ≤ G ((2 : ℝ) ^ j) := hstep
        _ ≤ (ρ + τ) ^ j * G 1 := hstep2
    have hkey : (ρ + τ) ^ j * G 1 / (ρ - τ) ^ j
        = ((ρ + τ) / (ρ - τ)) ^ j * G 1 := by
      rw [div_pow, div_mul_eq_mul_div]
    calc G t ≤ (ρ + τ) ^ j * G 1 / (ρ - τ) ^ j := hGt
      _ = ((ρ + τ) / (ρ - τ)) ^ j * G 1 := hkey
      _ ≤ max (ρ + τ) 1 * ((ρ + τ) / (ρ - τ)) ^ P * G 1 := by
          have hA : ((ρ + τ) / (ρ - τ)) ^ j
              ≤ max (ρ + τ) 1 * ((ρ + τ) / (ρ - τ)) ^ P :=
            le_trans (pow_le_pow_right₀ hratio_ge1 hjle)
              (le_mul_of_one_le_left (pow_nonneg hratio_nonneg P) (le_max_right _ _))
          exact mul_le_mul hA le_rfl hG1pos.le (mul_nonneg hmax_nonneg
            (pow_nonneg hratio_nonneg P))

end Work.WilC4
