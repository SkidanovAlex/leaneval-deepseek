import Mathlib
import Submission.Work.WilE2.NextPoint

namespace Work.WilE2

open Set

/-- Iterating the period relation: for a `T`-periodic `φ` one has `φ (x + m T) = φ x` for every
integer `m` (this is where the negative powers of the period are needed). -/
theorem phi_add_int_mul {φ : ℝ → ℝ} {T : ℝ} (hper : ∀ t, φ (t + T) = φ t) (x : ℝ) :
    ∀ m : ℤ, φ (x + (m : ℝ) * T) = φ x := by
  intro m
  refine Int.induction_on m ?h0 ?hpos ?hneg
  · simp
  · intro n ih
    have hc : (((n : ℤ) + 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) + 1 := by push_cast; ring
    have hs : x + (((n : ℤ) : ℝ) + 1) * T = x + ((n : ℤ) : ℝ) * T + T := by ring
    rw [hc, hs, hper (x + ((n : ℤ) : ℝ) * T)]
    exact ih
  · intro n ih
    have hc : ((-(n : ℤ) - 1 : ℤ) : ℝ) = ((-(n : ℤ) : ℤ) : ℝ) - 1 := by push_cast; ring
    have hs : x + (((-(n : ℤ) : ℤ) : ℝ) - 1) * T + T = x + (((-(n : ℤ) : ℤ) : ℝ)) * T := by
      ring
    rw [hc, ← hper (x + (((-(n : ℤ) : ℤ) : ℝ) - 1) * T), hs]
    exact ih

/-- The zeros of a `T`-periodic `φ` whose zeros in the fundamental domain `[0, T)` are enumerated
by a strictly increasing `u : Fin p → ℝ` are exactly the points `u k + m T`, `k : Fin p`,
`m : ℤ`: the enumeration of the fundamental domain propagates to the whole line by periodicity,
and conversely any zero is a translate of a fundamental-domain zero. -/
theorem phi_eq_zero_iff {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hper : ∀ t, φ (t + T) = φ t) {p : ℕ} (_hp : 0 < p) (u : Fin p → ℝ)
    (hrange : {t : ℝ | 0 ≤ t ∧ t < T ∧ φ t = 0} = Set.range u) (x : ℝ) :
    (φ x = 0) ↔ ∃ k : Fin p, ∃ m : ℤ, x = u k + (m : ℝ) * T := by
  have hu : ∀ k : Fin p, 0 ≤ u k ∧ u k < T ∧ φ (u k) = 0 := by
    intro k
    have hk : u k ∈ Set.range u := Set.mem_range_self k
    rw [← hrange] at hk
    exact hk
  constructor
  · intro hx
    set m : ℤ := ⌊x / T⌋ with hmdef
    have hle : (m : ℝ) ≤ x / T := by rw [hmdef]; exact Int.floor_le (x / T)
    have hlt : x / T < (m : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one (x / T)
    have hm0 : 0 ≤ x - (m : ℝ) * T := by
      have h := mul_le_mul_of_nonneg_right hle (le_of_lt hT)
      rw [div_mul_cancel₀ x (ne_of_gt hT)] at h
      linarith
    have hm1 : x - (m : ℝ) * T < T := by
      have h := mul_lt_mul_of_pos_right hlt hT
      rw [div_mul_cancel₀ x (ne_of_gt hT)] at h
      rw [add_mul, one_mul] at h
      linarith
    have harg : x + ((-m : ℤ) : ℝ) * T = x - (m : ℝ) * T := by push_cast; ring
    have hyphi : φ (x - (m : ℝ) * T) = 0 := by
      have h := phi_add_int_mul hper x (-m)
      rw [harg] at h
      rw [h]; exact hx
    have hymem : x - (m : ℝ) * T ∈ Set.range u := by
      rw [← hrange]; exact ⟨hm0, hm1, hyphi⟩
    obtain ⟨k, hk⟩ := hymem
    exact ⟨k, m, by rw [hk]; ring⟩
  · rintro ⟨k, m, rfl⟩
    rw [phi_add_int_mul hper (u k) m]
    exact (hu k).2.2

theorem nextPt_ne_zero {φ : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hper : ∀ t, φ (t + T) = φ t)
    {p : ℕ} (hp : 0 < p) (u : Fin p → ℝ) (hmono : StrictMono u)
    (hrange : {t : ℝ | 0 ≤ t ∧ t < T ∧ φ t = 0} = Set.range u) (j : Fin p) :
    u j < nextPt hp T u j ∧ φ (nextPt hp T u j) = 0 ∧ φ (u j) = 0 ∧
      (∀ x : ℝ, u j < x → x < nextPt hp T u j → φ x ≠ 0) := by
  have hu : ∀ k : Fin p, 0 ≤ u k ∧ u k < T ∧ φ (u k) = 0 := by
    intro k
    have hk : u k ∈ Set.range u := Set.mem_range_self k
    rw [← hrange] at hk
    exact hk
  have hmin : ∀ k : Fin p, u ⟨0, hp⟩ ≤ u k :=
    fun k => hmono.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  have hchar : ∀ x : ℝ, φ x = 0 → ∃ k : Fin p, ∃ m : ℤ, x = u k + (m : ℝ) * T :=
    fun x => (phi_eq_zero_iff hT hper hp u hrange x).mp
  by_cases h : (j : ℕ) + 1 < p
  · -- the next zero is `u (j+1)`, still inside the fundamental domain
    rw [nextPt_of_lt hp T u j h]
    refine ⟨hmono (by simp [Fin.lt_def]), (hu _).2.2, (hu j).2.2, ?_⟩
    intro x h1 h2 hfx
    obtain ⟨k, m, hkm⟩ := hchar x hfx
    rcases lt_trichotomy m 0 with hm | hm | hm
    · -- a zero from the period *below* `[0, T)`
      have hmle : ((m : ℤ) : ℝ) ≤ -1 := by
        have : m ≤ -1 := by omega
        exact_mod_cast this
      have hmT : (m : ℝ) * T ≤ -T := by
        have := mul_le_mul_of_nonneg_right hmle (le_of_lt hT)
        simpa using this
      have hx0 : 0 < x := lt_of_le_of_lt (hu j).1 h1
      have hkT : T < u k := by linarith
      linarith [(hu k).2.1]
    · -- `x` is itself a fundamental-domain zero
      have hxk : x = u k := by rw [hkm, hm]; simp
      have hjk : j < k := (hmono.lt_iff_lt).mp (by rw [← hxk]; exact h1)
      have hkj : k < (⟨(j : ℕ) + 1, h⟩ : Fin p) :=
        (hmono.lt_iff_lt).mp (by rw [← hxk]; exact h2)
      have h1' : (j : ℕ) < (k : ℕ) := Fin.lt_def.mp hjk
      have h2' : (k : ℕ) < (j : ℕ) + 1 := by
        have := Fin.lt_def.mp hkj
        simpa using this
      omega
    · -- a zero from the period *above* `[0, T)`
      have hmge : (1 : ℝ) ≤ (m : ℝ) := by
        have : (1 : ℤ) ≤ m := by omega
        exact_mod_cast this
      have hmT : T ≤ (m : ℝ) * T := by
        have := mul_le_mul_of_nonneg_right hmge (le_of_lt hT)
        simpa using this
      have hxT : T ≤ x := by linarith [(hu k).1]
      have := (hu (⟨(j : ℕ) + 1, h⟩ : Fin p)).2.1
      linarith
  · -- the next zero wraps around: it is `u 0 + T`
    rw [nextPt_of_not_lt hp T u j h]
    refine ⟨by linarith [(hu j).2.1, (hu ⟨0, hp⟩).1], ?_, (hu j).2.2, ?_⟩
    · rw [hper]; exact (hu ⟨0, hp⟩).2.2
    · intro x h1 h2 hfx
      obtain ⟨k, m, hkm⟩ := hchar x hfx
      rcases lt_trichotomy m 0 with hm | hm | hm
      · -- below `[0, T)`
        have hmle : ((m : ℤ) : ℝ) ≤ -1 := by
          have : m ≤ -1 := by omega
          exact_mod_cast this
        have hmT : (m : ℝ) * T ≤ -T := by
          have := mul_le_mul_of_nonneg_right hmle (le_of_lt hT)
          simpa using this
        have hx0 : 0 < x := lt_of_le_of_lt (hu j).1 h1
        have hkT : u k < 0 := by linarith [(hu k).2.1]
        linarith
      · -- a fundamental-domain zero
        have hxk : x = u k := by rw [hkm, hm]; simp
        have hjk : j < k := (hmono.lt_iff_lt).mp (by rw [← hxk]; exact h1)
        have hkj : (k : ℕ) ≤ (j : ℕ) := by
          have := k.isLt
          omega
        have hle : k ≤ j := Fin.le_iff_val_le_val.mpr hkj
        exact absurd hjk (not_lt.mpr hle)
      · -- above `[0, T)`
        have hmge : (1 : ℝ) ≤ (m : ℝ) := by
          have : (1 : ℤ) ≤ m := by omega
          exact_mod_cast this
        have hle1 : (m : ℝ) ≤ 1 := by
          have hkey : (m : ℝ) * T ≤ (1 : ℝ) * T := by
            rw [one_mul]; linarith [hmin k]
          exact le_of_mul_le_mul_right hkey hT
        have hmeq : (m : ℝ) = 1 := le_antisymm hle1 hmge
        have hx' : x = u k + T := by rw [hkm, hmeq]; ring
        linarith [hmin k]

end Work.WilE2
