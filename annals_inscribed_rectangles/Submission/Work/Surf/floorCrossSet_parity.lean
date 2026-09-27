import Mathlib
import Submission.Work.Drive.ncard_zeros_mod_four_eq_two

/-!
# Parity of the number of integer crossings of a lift of a circle map

For a continuous `F : ℝ → ℝ` with `F (x + 1) = F x + n` (a lift of a degree-`n` circle map),
whose integer values on `[0,1)` are finitely many and each is a transverse crossing, the number of
such crossings has the same parity as `n`.

The proof uses the elementary parity count `Work.Drive.even_ncard_zeros_iff` applied to the
continuous function `x ↦ sin (π * F x)`: its zeros are exactly the integer crossings of `F`, and at
each crossing the sign of `sin (π * F x)` flips (the floor of `F` jumps by `±1`).  The endpoint
values satisfy `sin (π F 1) = (-1)^n sin (π F 0)`, so the sign is the same iff `n` is even.
-/

namespace Work.Surf

open Set

/-- The integer-crossing set of `F` on `[0,1)`. -/
private def CrossSet (F : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}

/-- The auxiliary function whose zeros are the integer crossings. -/
private noncomputable def fSin (F : ℝ → ℝ) (x : ℝ) : ℝ := Real.sin (Real.pi * F x)

/-- `(-1 : ℝ) ^ k` is positive exactly for even `k`. -/
lemma neg_one_zpow_pos (k : ℤ) : (0 : ℝ) < (-1 : ℝ) ^ k ↔ Even k := by
  rw [neg_one_zpow_eq_ite]
  by_cases h : Even k
  · simp [h]
  · simp [h]

/-- `sin (π y) ≠ 0` when `y` is not an integer. -/
lemma sin_pi_ne_zero {y : ℝ} (hy : ∀ m : ℤ, y ≠ (m : ℝ)) : Real.sin (Real.pi * y) ≠ 0 := by
  intro h
  rw [Real.sin_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2 : (n : ℝ) * Real.pi = y * Real.pi := by rw [hn, mul_comm y]
  have h3 : (n : ℝ) = y := mul_right_cancel₀ Real.pi_ne_zero h2
  exact hy n h3.symm

/-- The sign of `sin (π y)`, for non-integer `y`, is the parity of `⌊y⌋`. -/
lemma sin_pi_pos_iff {y : ℝ} (hy : ∀ m : ℤ, y ≠ (m : ℝ)) :
    (0 < Real.sin (Real.pi * y) ↔ Even ⌊y⌋) := by
  have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have hne : y ≠ (⌊y⌋ : ℝ) := by intro h; exact hy ⌊y⌋ h
  have ht0 : 0 < y - (⌊y⌋ : ℝ) := sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm hne))
  have ht1 : y - (⌊y⌋ : ℝ) < 1 := by linarith
  have hsinpos : 0 < Real.sin (Real.pi * (y - ⌊y⌋)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi * y) = (-1 : ℝ) ^ ⌊y⌋ * Real.sin (Real.pi * (y - ⌊y⌋)) := by
    have hsplit : Real.pi * y = Real.pi * (y - ⌊y⌋) + (⌊y⌋ : ℤ) * Real.pi := by ring
    rw [hsplit, Real.sin_add_int_mul_pi]
  rw [hsin, mul_pos_iff_of_pos_right hsinpos, neg_one_zpow_pos]

/-- If two propositions on the two sides of `t` are inequivalent, and the sign of `sin (π F ·)`
is governed by them, then `t` is a sign change. -/
private lemma signChange_of_sign_data (F : ℝ → ℝ) (t : ℝ) {E : ℝ} (hE : 0 < E)
    {PL PR : Prop}
    (hleft : ∀ s, t - E < s → s < t → (0 < Real.sin (Real.pi * F s) ↔ PL))
    (hright : ∀ s, t < s → s < t + E → (0 < Real.sin (Real.pi * F s) ↔ PR))
    (hleftne : ∀ s, t - E < s → s < t → Real.sin (Real.pi * F s) ≠ 0)
    (hrightne : ∀ s, t < s → s < t + E → Real.sin (Real.pi * F s) ≠ 0)
    (hopp : ¬(PL ↔ PR)) :
    Work.Drive.SignChangeAt (fun x => Real.sin (Real.pi * F x)) t := by
  rcases em PL with hPL | hPL
  · have hR : ¬ PR := fun h => hopp ⟨fun _ => h, fun _ => hPL⟩
    right
    refine ⟨E, hE, ?_, ?_⟩
    · intro s h1 h2; exact (hleft s h1 h2).mpr hPL
    · intro s h1 h2
      have hne := hrightne s h1 h2
      have hnp : ¬(0 < Real.sin (Real.pi * F s)) := fun h => hR ((hright s h1 h2).mp h)
      exact lt_of_le_of_ne (le_of_not_gt hnp) hne
  · have hR : PR := by
      by_contra hR'
      exact hopp ⟨fun hp => absurd hp hPL, fun hr => absurd hr hR'⟩
    left
    refine ⟨E, hE, ?_, ?_⟩
    · intro s h1 h2
      have hne := hleftne s h1 h2
      have hnp : ¬(0 < Real.sin (Real.pi * F s)) := fun h => hPL ((hleft s h1 h2).mp h)
      exact lt_of_le_of_ne (le_of_not_gt hnp) hne
    · intro s h1 h2; exact (hright s h1 h2).mpr hR

theorem floorCrossSet_parity (F : ℝ → ℝ) (hF : Continuous F) (n : ℤ) (hper : ∀ x : ℝ, F (x + 1) = F x + (n : ℝ)) (hfin : {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}.Finite) (hzero : ¬ ∃ m : ℤ, F 0 = (m : ℝ)) (hjump : ∀ x ∈ {x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}, (∃ ε > 0, (∀ y ∈ Set.Ioo (x - ε) x, ⌊F y⌋ = ⌊F x⌋ - 1) ∧ (∀ y ∈ Set.Ioo x (x + ε), ⌊F y⌋ = ⌊F x⌋)) ∨ (∃ ε > 0, (∀ y ∈ Set.Ioo (x - ε) x, ⌊F y⌋ = ⌊F x⌋) ∧ (∀ y ∈ Set.Ioo x (x + ε), ⌊F y⌋ = ⌊F x⌋ - 1))) : Odd ({x : ℝ | x ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F x = (m : ℝ)}.ncard) ↔ Odd n := by
  change Odd (CrossSet F).ncard ↔ Odd n
  -- `F 1` is not an integer.
  have hF1 : ¬ ∃ m : ℤ, F 1 = (m : ℝ) := by
    rintro ⟨m, hm⟩
    refine hzero ⟨m - n, ?_⟩
    have h1 : F 1 = F 0 + (n : ℝ) := by simpa using hper 0
    have h0 : F 0 = (m : ℝ) - (n : ℝ) := by linarith
    rw [h0]
    push_cast
    ring
  -- endpoint values of `fSin F` are non-zero.
  have hf0 : fSin F 0 ≠ 0 := by
    intro h
    apply hzero
    simp only [fSin] at h
    rw [Real.sin_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have h3 : (k : ℝ) = F 0 := mul_right_cancel₀ Real.pi_ne_zero (by rw [hk, mul_comm])
    exact h3.symm
  have hf1 : fSin F 1 ≠ 0 := by
    intro h
    apply hF1
    simp only [fSin] at h
    rw [Real.sin_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have h3 : (k : ℝ) = F 1 := mul_right_cancel₀ Real.pi_ne_zero (by rw [hk, mul_comm])
    exact h3.symm
  -- the zero set of `fSin F` on `[0,1]` is `CrossSet F`.
  have hZS : {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ fSin F t = 0} = CrossSet F := by
    ext t
    constructor
    · rintro ⟨htIcc, ht0⟩
      have ht0' : Real.sin (Real.pi * F t) = 0 := ht0
      rw [Real.sin_eq_zero_iff] at ht0'
      obtain ⟨k, hk⟩ := ht0'
      have hFt : F t = (k : ℝ) := by
        have h3 : (k : ℝ) = F t := mul_right_cancel₀ Real.pi_ne_zero (by rw [hk, mul_comm])
        exact h3.symm
      have ht1 : t ≠ 1 := by intro h; rw [h] at hFt; exact hF1 ⟨k, hFt⟩
      exact ⟨⟨htIcc.1, lt_of_le_of_ne htIcc.2 ht1⟩, ⟨k, hFt⟩⟩
    · rintro ⟨htIco, ⟨k, hk⟩⟩
      refine ⟨⟨htIco.1, le_of_lt htIco.2⟩, ?_⟩
      simp only [fSin]
      rw [hk]
      rw [show Real.pi * (k : ℝ) = (k : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
  have hZfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ fSin F t = 0}).Finite := by
    rw [hZS]; exact hfin
  have hcont : ContinuousOn (fSin F) (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    exact Real.continuous_sin.comp (continuous_const.mul hF)
  -- every zero of `fSin F` in `[0,1]` is a sign change.
  have hsc : ∀ t ∈ Set.Icc (0 : ℝ) 1, fSin F t = 0 →
      Work.Drive.SignChangeAt (fSin F) t := by
    intro t htIcc ht0
    have ht0' : Real.sin (Real.pi * F t) = 0 := ht0
    rw [Real.sin_eq_zero_iff] at ht0'
    obtain ⟨m, hm⟩ := ht0'
    have hFt : F t = (m : ℝ) := by
      have h3 : (m : ℝ) = F t := mul_right_cancel₀ Real.pi_ne_zero (by rw [hm, mul_comm])
      exact h3.symm
    have ht1 : t ≠ 1 := by intro h; rw [h] at hFt; exact hF1 ⟨m, hFt⟩
    have htpos : 0 < t := by
      rcases lt_or_eq_of_le htIcc.1 with h | h
      · exact h
      · exfalso; rw [← h] at hFt; exact hzero ⟨m, hFt⟩
    have htlt1 : t < 1 := lt_of_le_of_ne htIcc.2 ht1
    have hfloor : ⌊F t⌋ = m := by rw [hFt, Int.floor_intCast]
    have htCross : t ∈ CrossSet F := ⟨⟨htIcc.1, htlt1⟩, ⟨m, hFt⟩⟩
    -- isolation of `t` among the crossings.
    obtain ⟨δ, hδpos, hiso⟩ : ∃ δ > 0, ∀ y, |y - t| < δ → y ∈ CrossSet F → y = t := by
      have hd : (CrossSet F \ {t}).Finite := hfin.subset Set.sdiff_subset
      have hop : IsOpen ((CrossSet F \ {t})ᶜ) := hd.isClosed.isOpen_compl
      have ht' : t ∈ ((CrossSet F \ {t})ᶜ) := by simp
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hop t ht'
      refine ⟨δ, hδ, ?_⟩
      intro y hy hyS
      by_contra hyne
      have hy' : y ∈ CrossSet F \ {t} := ⟨hyS, by simpa using hyne⟩
      have hb := hδsub (by rwa [Metric.mem_ball, Real.dist_eq])
      exact hb hy'
    rcases hjump t htCross with ⟨ε, hε, hl, hr⟩ | ⟨ε, hε, hl, hr⟩
    · -- increasing crossing: left floor `m-1`, right floor `m`
      set E : ℝ := min ε (min δ (min t (1 - t))) with hEdef
      have hEpos : 0 < E := by
        rw [hEdef]; exact lt_min hε (lt_min hδpos (lt_min htpos (by linarith)))
      have hEε : E ≤ ε := by rw [hEdef]; exact min_le_left _ _
      have hEδ : E ≤ δ := by rw [hEdef]; exact (min_le_right _ _).trans (min_le_left _ _)
      have hEt : E ≤ t := by
        rw [hEdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
      have hE1 : E ≤ 1 - t := by
        rw [hEdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
      have hnotintL : ∀ s, t - E < s → s < t → (∀ m' : ℤ, F s ≠ (m' : ℝ)) := by
        intro s h1 h2
        have hsIco : s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hsS : s ∉ CrossSet F := by
          intro hsS
          have hb := hiso s (by rw [abs_lt]; constructor <;> linarith [hEδ]) hsS
          linarith
        intro m' hm'
        exact hsS ⟨hsIco, ⟨m', hm'⟩⟩
      have hnotintR : ∀ s, t < s → s < t + E → (∀ m' : ℤ, F s ≠ (m' : ℝ)) := by
        intro s h1 h2
        have hsIco : s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hsS : s ∉ CrossSet F := by
          intro hsS
          have hb := hiso s (by rw [abs_lt]; constructor <;> linarith [hEδ]) hsS
          linarith
        intro m' hm'
        exact hsS ⟨hsIco, ⟨m', hm'⟩⟩
      refine signChange_of_sign_data F t (E := E) (PL := Even (m - 1)) (PR := Even m) hEpos ?_ ?_ ?_ ?_ ?_
      · intro s h1 h2
        have hsfloor : ⌊F s⌋ = m - 1 := by
          have h := hl s ⟨by linarith [hEε], h2⟩
          rwa [hfloor] at h
        rw [sin_pi_pos_iff (hnotintL s h1 h2), hsfloor]
      · intro s h1 h2
        have hsfloor : ⌊F s⌋ = m := by
          have h := hr s ⟨h1, by linarith [hEε]⟩
          rwa [hfloor] at h
        rw [sin_pi_pos_iff (hnotintR s h1 h2), hsfloor]
      · exact fun s h1 h2 => sin_pi_ne_zero (hnotintL s h1 h2)
      · exact fun s h1 h2 => sin_pi_ne_zero (hnotintR s h1 h2)
      · rw [Int.even_sub_one]
        intro h
        have hnp : ¬ Even m := fun p => (h.mpr p) p
        exact hnp (h.mp hnp)
    · -- decreasing crossing: left floor `m`, right floor `m-1`
      set E : ℝ := min ε (min δ (min t (1 - t))) with hEdef
      have hEpos : 0 < E := by
        rw [hEdef]; exact lt_min hε (lt_min hδpos (lt_min htpos (by linarith)))
      have hEε : E ≤ ε := by rw [hEdef]; exact min_le_left _ _
      have hEδ : E ≤ δ := by rw [hEdef]; exact (min_le_right _ _).trans (min_le_left _ _)
      have hEt : E ≤ t := by
        rw [hEdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
      have hE1 : E ≤ 1 - t := by
        rw [hEdef]; exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
      have hnotintL : ∀ s, t - E < s → s < t → (∀ m' : ℤ, F s ≠ (m' : ℝ)) := by
        intro s h1 h2
        have hsIco : s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hsS : s ∉ CrossSet F := by
          intro hsS
          have hb := hiso s (by rw [abs_lt]; constructor <;> linarith [hEδ]) hsS
          linarith
        intro m' hm'
        exact hsS ⟨hsIco, ⟨m', hm'⟩⟩
      have hnotintR : ∀ s, t < s → s < t + E → (∀ m' : ℤ, F s ≠ (m' : ℝ)) := by
        intro s h1 h2
        have hsIco : s ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have hsS : s ∉ CrossSet F := by
          intro hsS
          have hb := hiso s (by rw [abs_lt]; constructor <;> linarith [hEδ]) hsS
          linarith
        intro m' hm'
        exact hsS ⟨hsIco, ⟨m', hm'⟩⟩
      refine signChange_of_sign_data F t (E := E) (PL := Even m) (PR := Even (m - 1)) hEpos ?_ ?_ ?_ ?_ ?_
      · intro s h1 h2
        have hsfloor : ⌊F s⌋ = m := by
          have h := hl s ⟨by linarith [hEε], h2⟩
          rwa [hfloor] at h
        rw [sin_pi_pos_iff (hnotintL s h1 h2), hsfloor]
      · intro s h1 h2
        have hsfloor : ⌊F s⌋ = m - 1 := by
          have h := hr s ⟨h1, by linarith [hEε]⟩
          rwa [hfloor] at h
        rw [sin_pi_pos_iff (hnotintR s h1 h2), hsfloor]
      · exact fun s h1 h2 => sin_pi_ne_zero (hnotintL s h1 h2)
      · exact fun s h1 h2 => sin_pi_ne_zero (hnotintR s h1 h2)
      · rw [Int.even_sub_one]
        intro h
        have hnp : ¬ Even m := fun p => (h.mp p) p
        exact hnp (h.mpr hnp)
  have hmain := Work.Drive.even_ncard_zeros_iff (f := fSin F) (a := 0) (b := 1)
    (by norm_num) hcont hZfin hsc hf0 hf1
  rw [hZS] at hmain
  have hkey : (0 < fSin F 0 ↔ 0 < fSin F 1) ↔ Even n := by
    have hf1eq : fSin F 1 = (-1 : ℝ) ^ n * fSin F 0 := by
      have h1 : F 1 = F 0 + (n : ℝ) := by simpa using hper 0
      have h2 : Real.pi * F 1 = Real.pi * F 0 + (n : ℤ) * Real.pi := by
        rw [h1]; ring
      simp only [fSin]
      rw [h2, Real.sin_add_int_mul_pi]
    rw [hf1eq]
    rcases Int.even_or_odd n with he | ho
    · rw [he.neg_one_zpow, one_mul]
      exact ⟨fun _ => he, fun _ => Iff.rfl⟩
    · rw [ho.neg_one_zpow, neg_one_mul]
      have hno : ¬(0 < fSin F 0 ↔ 0 < -fSin F 0) := by
        intro h
        rcases lt_or_gt_of_ne hf0 with hl | hr
        · have hpos : 0 < -fSin F 0 := neg_pos.mpr hl
          exact absurd (h.mpr hpos) (not_lt.mpr hl.le)
        · have hneg : ¬(0 < -fSin F 0) := by linarith
          exact hneg (h.mp hr)
      exact ⟨fun h => absurd h hno, fun hn => absurd hn (Int.not_even_iff_odd.mpr ho)⟩
  rw [hkey] at hmain
  rw [← Nat.not_even_iff_odd, ← Int.not_even_iff_odd]
  rw [hmain]

end Work.Surf
