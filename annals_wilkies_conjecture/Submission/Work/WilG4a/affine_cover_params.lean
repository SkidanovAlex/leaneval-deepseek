import Mathlib
import Submission.Work.WilG4a.f1affine1_defs

set_option autoImplicit false

namespace Work.WilG4a

/-- If `0 < w` and the open interval `(a, a+w)` meets the `ε`-neighbourhood `(t-ε, t+ε)`
of `t`, then some `τ ∈ (0,1)` has `|a + w * τ - t| < ε`. -/
theorem exists_tau_I_of_lt {a w t ε : ℝ} (hw : 0 < w) (hε : 0 < ε)
    (h1 : a < t + ε) (h2 : t - ε < a + w) :
    ∃ τ ∈ Set.Ioo (0 : ℝ) 1, |a + w * τ - t| < ε := by
  have hlt : max a (t - ε) < min (a + w) (t + ε) :=
    max_lt (lt_min (by linarith) h1) (lt_min h2 (by linarith))
  obtain ⟨y, hy1, hy2⟩ := exists_between hlt
  have hay : a < y := lt_of_le_of_lt (le_max_left _ _) hy1
  have hyb : y < a + w := lt_of_lt_of_le hy2 (min_le_left _ _)
  have hty : t - ε < y := lt_of_le_of_lt (le_max_right _ _) hy1
  have hyt : y < t + ε := lt_of_lt_of_le hy2 (min_le_right _ _)
  refine ⟨(y - a) / w, ⟨?_, ?_⟩, ?_⟩
  · exact div_pos (sub_pos.mpr hay) hw
  · rw [div_lt_one hw]; linarith
  · have hwne : w ≠ 0 := ne_of_gt hw
    have hval : a + w * ((y - a) / w) = y := by
      rw [mul_div_cancel₀ (y - a) hwne]; ring
    rw [hval, abs_lt]
    exact ⟨by linarith, by linarith⟩

theorem affine_cover_params
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2)))
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Finset (ℝ × ℝ),
      (∀ q ∈ s, 0 < q.2 ∧ 0 ≤ q.1 ∧ q.1 + q.2 ≤ 1 ∧
        q.2 * ((r : ℝ) + 1) ≤ min q.1 (1 - (q.1 + q.2))) ∧
      (s.card : ℝ) ≤ 8 * ((r : ℝ) + 1) * (-Real.log ε + 4) + 2 ∧
      ∀ t ∈ Work.WilG4a.I, ∃ q ∈ s, ∃ τ ∈ Work.WilG4a.I, |q.1 + q.2 * τ - t| < ε := by
  obtain ⟨s₀, hcard₀, hmem₀, hcov₀⟩ := hG3b r ε hε hε1
  set w : ℝ := min (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3)) / 2 with hwdef
  have hwpos : 0 < w := by
    rw [hwdef]
    have h1 : 0 < ε / ((r : ℝ) + 1) := by positivity
    have h2 : 0 < 1 / (2 * (r : ℝ) + 3) := by positivity
    positivity
  have hwle1 : ((r : ℝ) + 1) * w ≤ ε := by
    rw [hwdef]
    have h2 : min (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3)) / 2
        ≤ (ε / ((r : ℝ) + 1)) / 2 := by
      linarith [min_le_left (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3))]
    calc ((r : ℝ) + 1) * (min (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3)) / 2)
        ≤ ((r : ℝ) + 1) * ((ε / ((r : ℝ) + 1)) / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 2 := by
          have hr1 : ((r : ℝ) + 1) ≠ 0 := by positivity
          field_simp
      _ ≤ ε := by linarith [hε]
  have hwle2 : (2 * (r : ℝ) + 3) * w ≤ 1 := by
    rw [hwdef]
    have h2 : min (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3)) / 2
        ≤ (1 / (2 * (r : ℝ) + 3)) / 2 := by
      linarith [min_le_right (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3))]
    calc (2 * (r : ℝ) + 3) * (min (ε / ((r : ℝ) + 1)) (1 / (2 * (r : ℝ) + 3)) / 2)
        ≤ (2 * (r : ℝ) + 3) * ((1 / (2 * (r : ℝ) + 3)) / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / 2 := by
          have h2 : 2 * (r : ℝ) + 3 ≠ 0 := by positivity
          field_simp
      _ ≤ 1 := by norm_num
  let qL : ℝ × ℝ := (((r : ℝ) + 1) * w, w)
  let qR : ℝ × ℝ := (1 - ((r : ℝ) + 2) * w, w)
  let s₁ : Finset (ℝ × ℝ) := s₀.image (fun p => (p.1, p.2 - p.1))
  refine ⟨insert qL (insert qR s₁), ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · simp only [qL]
      refine ⟨hwpos, ?_, ?_, ?_⟩
      · exact mul_nonneg (by positivity) (le_of_lt hwpos)
      · have h : ((r : ℝ) + 1) * w + w = ((r : ℝ) + 2) * w := by ring
        rw [h]
        calc ((r : ℝ) + 2) * w ≤ (2 * (r : ℝ) + 3) * w := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hwpos)
              linarith
          _ ≤ 1 := hwle2
      · apply le_min
        · exact le_of_eq (mul_comm w ((r : ℝ) + 1))
        · have h : 1 - (((r : ℝ) + 1) * w + w) = 1 - ((r : ℝ) + 2) * w := by ring
          rw [h]
          nlinarith [hwle2]
    · rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · simp only [qR]
        have hle : ((r : ℝ) + 2) * w ≤ 1 := by
          calc ((r : ℝ) + 2) * w ≤ (2 * (r : ℝ) + 3) * w := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hwpos)
                linarith
            _ ≤ 1 := hwle2
        refine ⟨hwpos, by linarith, ?_, ?_⟩
        · have h : 1 - ((r : ℝ) + 2) * w + w = 1 - ((r : ℝ) + 1) * w := by ring
          rw [h]
          have hnn : 0 ≤ ((r : ℝ) + 1) * w := mul_nonneg (by positivity) (le_of_lt hwpos)
          linarith
        · apply le_min
          · nlinarith [hwle2]
          · have h : 1 - ((1 - ((r : ℝ) + 2) * w) + w) = ((r : ℝ) + 1) * w := by ring
            rw [h]
            exact le_of_eq (mul_comm w ((r : ℝ) + 1))
      · simp only [s₁] at hq
        rw [Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        obtain ⟨hp1, hp12, hp2, hpcon⟩ := hmem₀ p hp
        change 0 < p.2 - p.1 ∧ 0 ≤ p.1 ∧ p.1 + (p.2 - p.1) ≤ 1 ∧
          (p.2 - p.1) * ((r : ℝ) + 1) ≤ min p.1 (1 - (p.1 + (p.2 - p.1)))
        refine ⟨by linarith, by linarith, by linarith, ?_⟩
        apply le_min
        · have h := le_trans hpcon (min_le_left p.1 (1 - p.2))
          push_cast at h
          linarith
        · have h := le_trans hpcon (min_le_right p.1 (1 - p.2))
          push_cast at h
          linarith
  · have hrec : (insert qL (insert qR s₁)).card ≤ (insert qR s₁).card + 1 :=
      Finset.card_insert_le qL (insert qR s₁)
    have hrec2 : (insert qR s₁).card ≤ s₁.card + 1 := Finset.card_insert_le qR s₁
    have himg : s₁.card ≤ s₀.card := Finset.card_image_le
    have hnat : (insert qL (insert qR s₁)).card ≤ s₀.card + 2 := by omega
    have hreal : ((insert qL (insert qR s₁)).card : ℝ) ≤ (s₀.card : ℝ) + 2 := by
      exact_mod_cast hnat
    calc ((insert qL (insert qR s₁)).card : ℝ)
        ≤ (s₀.card : ℝ) + 2 := hreal
      _ ≤ 8 * ((r : ℝ) + 1) * (-Real.log ε + 2) + 2 := by
          have h := hcard₀
          push_cast at h
          linarith
      _ ≤ 8 * ((r : ℝ) + 1) * (-Real.log ε + 4) + 2 := by
          have hr : (0 : ℝ) ≤ 8 * ((r : ℝ) + 1) := by positivity
          have hle : -Real.log ε + 2 ≤ -Real.log ε + 4 := by norm_num
          have h2 := mul_le_mul_of_nonneg_left hle hr
          linarith
  · intro t ht
    simp only [Work.WilG4a.I, Set.mem_Ioo] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rcases lt_or_ge t ε with hlt | hge
    · refine ⟨qL, Finset.mem_insert_self qL (insert qR s₁), ?_⟩
      have h1 : ((r : ℝ) + 1) * w < t + ε := by linarith [hwle1, ht0]
      have h2 : t - ε < ((r : ℝ) + 1) * w + w := by
        have hnn : 0 ≤ ((r : ℝ) + 1) * w := mul_nonneg (by positivity) (le_of_lt hwpos)
        linarith [hlt, hwpos, hnn]
      obtain ⟨τ, hτ, hτabs⟩ := exists_tau_I_of_lt (a := ((r : ℝ) + 1) * w) hwpos hε h1 h2
      simp only [qL]
      exact ⟨τ, hτ, hτabs⟩
    · rcases lt_or_ge (1 - ε) t with hlt2 | hge2
      · refine ⟨qR, Finset.mem_insert_of_mem (Finset.mem_insert_self qR s₁), ?_⟩
        have h1 : 1 - ((r : ℝ) + 2) * w < t + ε := by
          have hle : 0 ≤ ((r : ℝ) + 2) * w := mul_nonneg (by positivity) (le_of_lt hwpos)
          linarith
        have h2 : t - ε < (1 - ((r : ℝ) + 2) * w) + w := by
          have h : (1 - ((r : ℝ) + 2) * w) + w = 1 - ((r : ℝ) + 1) * w := by ring
          rw [h]; linarith [hwle1, ht1]
        obtain ⟨τ, hτ, hτabs⟩ :=
          exists_tau_I_of_lt (a := 1 - ((r : ℝ) + 2) * w) hwpos hε h1 h2
        simp only [qR]
        exact ⟨τ, hτ, hτabs⟩
      · have htIcc : t ∈ Set.Icc ε (1 - ε) := ⟨hge, hge2⟩
        have hmem := hcov₀ htIcc
        simp only [Set.mem_iUnion] at hmem
        obtain ⟨p, hp, hpt⟩ := hmem
        have hpt' : p.1 ≤ t ∧ t ≤ p.2 := Set.mem_Icc.mp hpt
        refine ⟨(p.1, p.2 - p.1), ?_, ?_⟩
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_insert_of_mem
          simp only [s₁]
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
        · obtain ⟨_, hp12, _, _⟩ := hmem₀ p hp
          have h1 : p.1 < t + ε := by linarith [hpt'.1, hε]
          have h2 : t - ε < p.1 + (p.2 - p.1) := by linarith [hpt'.2, hε]
          obtain ⟨τ, hτ, hτabs⟩ :=
            exists_tau_I_of_lt (a := p.1) (w := p.2 - p.1) (by linarith) hε h1 h2
          exact ⟨τ, hτ, hτabs⟩

end Work.WilG4a
