import Mathlib
import Submission.Work.RTOwed.jCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- **A point of an open quarter-wedge of `[0,1)` is pinned by the cut `cU = 0`.**  If
`a ∈ (k/4, (k+1)/4)` then `a ∈ [0,1)` and `Int.fract a = a` still lies in the same wedge, so the
pair `(0, k)` satisfies the pinning condition. -/
theorem jPin_wedge (a : ℝ) (k : Fin 4) (ha : a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4)) :
    a ∈ Set.Ico 0 1 ∧ Int.fract a ∈ Set.Ioo ((k : ℝ) / 4) (((k : ℝ) + 1) / 4) := by
  have hk3 : (k : ℝ) ≤ 3 := by
    have h : k.1 ≤ 3 := Nat.le_of_lt_succ k.isLt
    exact_mod_cast h
  have h0' : 0 ≤ a := by
    have : (0 : ℝ) ≤ (k : ℝ) / 4 := by positivity
    linarith [ha.1]
  have h1' : a < 1 := by linarith [ha.2, hk3]
  exact ⟨⟨h0', h1'⟩, by rw [Int.fract_eq_self.mpr ⟨h0', h1'⟩]; exact ha⟩

/-- **The eight perimeter pins cover `[0,1)`.**  For every `u ∈ [0,1)` there is a pin `i : Fin 8`
such that `u − (jPin i).1 ∈ [0,1)` and `Int.fract (u − (jPin i).1)` lies in the `(jPin i).2`-th
quarter of `[0,1)`.

The four wedges of the cut `cU = 0` cover `[0,1)` except the four quarter points
`0, 1/4, 1/2, 3/4`; each of these is shifted into the interior of its own wedge by the cut
`cU = −1/8`. -/
theorem jPin_cover (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) :
    ∃ i : Fin 8, u - (Work.RTOwed.jPin i).1 ∈ Set.Ico 0 1 ∧
      Int.fract (u - (Work.RTOwed.jPin i).1) ∈
        Set.Ioo (((Work.RTOwed.jPin i).2 : ℝ) / 4) ((((Work.RTOwed.jPin i).2 : ℝ) + 1) / 4) := by
  -- the cut `cU = 0`, for `u` strictly inside the `k`-th wedge
  have key : ∀ k : Fin 4, ((k : ℝ) / 4 < u) → (u < ((k : ℝ) + 1) / 4) →
      ∃ i : Fin 8, u - (Work.RTOwed.jPin i).1 ∈ Set.Ico 0 1 ∧
        Int.fract (u - (Work.RTOwed.jPin i).1) ∈
          Set.Ioo (((Work.RTOwed.jPin i).2 : ℝ) / 4) ((((Work.RTOwed.jPin i).2 : ℝ) + 1) / 4) := by
    intro k hk1 hk2
    have hw := jPin_wedge u k ⟨hk1, hk2⟩
    have hc : (Work.RTOwed.jPin (⟨k.1, by omega⟩ : Fin 8)).1 = 0 := by simp [Work.RTOwed.jPin]
    have hk : (Work.RTOwed.jPin (⟨k.1, by omega⟩ : Fin 8)).2 = k := by
      ext; simp [Work.RTOwed.jPin]
    exact ⟨⟨k.1, by omega⟩, by rw [hc]; simpa using hw.1, by rw [hc, hk]; simpa using hw.2⟩
  -- the shifted cut `cU = −1/8`, for `u = n/4` one of the four quarter points
  have key2 : ∀ n : Fin 4, u = (n : ℝ) / 4 →
      ∃ i : Fin 8, u - (Work.RTOwed.jPin i).1 ∈ Set.Ico 0 1 ∧
        Int.fract (u - (Work.RTOwed.jPin i).1) ∈
          Set.Ioo (((Work.RTOwed.jPin i).2 : ℝ) / 4) ((((Work.RTOwed.jPin i).2 : ℝ) + 1) / 4) := by
    intro n hn
    have hi1 : (Work.RTOwed.jPin (⟨n.1 + 4, by omega⟩ : Fin 8)).1 = -1/8 := by
      simp [Work.RTOwed.jPin]
    have hi2 : (Work.RTOwed.jPin (⟨n.1 + 4, by omega⟩ : Fin 8)).2 = n := by
      ext; simp [Work.RTOwed.jPin]
    have hmem : u + 1/8 ∈ Set.Ioo ((n : ℝ) / 4) (((n : ℝ) + 1) / 4) := by
      rw [hn]; constructor <;> linarith
    have hw := jPin_wedge (u + 1/8) n hmem
    have hsub : u - (-1/8) = u + 1/8 := by ring
    exact ⟨⟨n.1 + 4, by omega⟩, by rw [hi1, hsub]; exact hw.1,
      by rw [hi1, hi2, hsub]; exact hw.2⟩
  by_cases hq : ∃ n : Fin 4, u = (n : ℝ) / 4
  · obtain ⟨n, hn⟩ := hq
    exact key2 n hn
  · have hq' : ∀ n : Fin 4, u ≠ (n : ℝ) / 4 := fun n hn => hq ⟨n, hn⟩
    rcases lt_or_ge u (1/4) with hu | hu
    · -- `0 < u < 1/4`
      have hlo : ((0 : Fin 4) : ℝ) / 4 ≤ u := by
        have : ((0 : Fin 4) : ℝ) / 4 = 0 := by norm_num
        rw [this]; exact h0
      have hlt : ((0 : Fin 4) : ℝ) / 4 < u := lt_of_le_of_ne hlo (Ne.symm (hq' 0))
      have hup : u < (((0 : Fin 4) : ℝ) + 1) / 4 := by
        have : (((0 : Fin 4) : ℝ) + 1) / 4 = 1/4 := by norm_num
        rw [this]; exact hu
      exact key 0 hlt hup
    · rcases lt_or_ge u (1/2) with hu2 | hu2
      · -- `1/4 < u < 1/2`
        have hlo : ((1 : Fin 4) : ℝ) / 4 ≤ u := by
          have : ((1 : Fin 4) : ℝ) / 4 = 1/4 := by norm_num
          rw [this]; exact hu
        have hlt : ((1 : Fin 4) : ℝ) / 4 < u := lt_of_le_of_ne hlo (Ne.symm (hq' 1))
        have hup : u < (((1 : Fin 4) : ℝ) + 1) / 4 := by
          have : (((1 : Fin 4) : ℝ) + 1) / 4 = 1/2 := by norm_num
          rw [this]; exact hu2
        exact key 1 hlt hup
      · rcases lt_or_ge u (3/4) with hu3 | hu3
        · -- `1/2 < u < 3/4`
          have hlo : ((2 : Fin 4) : ℝ) / 4 ≤ u := by
            have : ((2 : Fin 4) : ℝ) / 4 = 1/2 := by norm_num
            rw [this]; exact hu2
          have hlt : ((2 : Fin 4) : ℝ) / 4 < u := lt_of_le_of_ne hlo (Ne.symm (hq' 2))
          have hup : u < (((2 : Fin 4) : ℝ) + 1) / 4 := by
            have : (((2 : Fin 4) : ℝ) + 1) / 4 = 3/4 := by norm_num
            rw [this]; exact hu3
          exact key 2 hlt hup
        · -- `3/4 < u < 1`
          have hlo : ((3 : Fin 4) : ℝ) / 4 ≤ u := by
            have : ((3 : Fin 4) : ℝ) / 4 = 3/4 := by norm_num
            rw [this]; exact hu3
          have hlt : ((3 : Fin 4) : ℝ) / 4 < u := lt_of_le_of_ne hlo (Ne.symm (hq' 3))
          have hup : u < (((3 : Fin 4) : ℝ) + 1) / 4 := by
            have : (((3 : Fin 4) : ℝ) + 1) / 4 = 1 := by norm_num
            rw [this]; exact h1
          exact key 3 hlt hup

end Work.RTOwed
