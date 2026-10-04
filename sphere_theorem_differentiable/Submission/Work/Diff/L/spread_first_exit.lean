import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

/-- **First exit time and last return to the top level.**

Let `f : ℝ → ℝ` be continuous on `[0,L]` with `L > 0`, `f 0 = S₀ > c` and `f L < c`.  Then there
are times `0 < r ≤ L` and `0 ≤ ρ ≤ r` with

* `f r = c` and `f > c` on `[0, r)` (`r` is the **first exit time** from the superlevel set
  `{f > c}`);
* `f ρ = S₀` and `f ≤ S₀` on `[ρ, r]` (`ρ` is the **last time `f` takes the value `S₀`** before the
  exit; the bound `f ≤ S₀` on `[ρ,r]` follows from the intermediate value theorem).

ROUTE.  `r := sInf {t ∈ Icc 0 L | f t = c}` (nonempty by the intermediate value theorem, closed and
bounded below, so the infimum belongs to the set); `ρ := sSup {t ∈ Icc 0 r | f t = S₀}` (nonempty
because `f 0 = S₀`, closed, bounded above).  Both "first/last" properties are the standard
intermediate-value arguments against the supremum/infimum. -/
theorem spread_first_exit {f : ℝ → ℝ} {L c S₀ : ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (h0 : f 0 = S₀) (hLc : f L < c) (hcs : c < S₀) :
    ∃ r ρ : ℝ, 0 < r ∧ r ≤ L ∧ f r = c ∧ (∀ t ∈ Set.Ico 0 r, c < f t) ∧
      ρ ∈ Set.Icc 0 r ∧ f ρ = S₀ ∧ (∀ t ∈ Set.Icc ρ r, f t ≤ S₀) := by
  have h0L : (0 : ℝ) ≤ L := le_of_lt hL
  -- The intermediate value theorem, in the orientation used below:
  -- on `[a,b] ⊆ [0,L]`, a value between `f b` and `f a` is attained.
  have ivt : ∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ L → f b ≤ y → y ≤ f a →
      ∃ x ∈ Set.Icc a b, f x = y := by
    intro a b y ha hab hbL hby hya
    have hsub : Set.Icc a b ⊆ Set.Icc 0 L := fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hbL⟩
    have hcont : ContinuousOn f (Set.Icc a b) := hf.mono hsub
    have hmem : y ∈ Set.Icc (f b) (f a) := ⟨hby, hya⟩
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hcont hmem
    exact ⟨x, hx, hfx⟩
  -- The set of times at which `f` leaves the superlevel set `{f > c}`.
  set T : Set ℝ := Set.Icc 0 L ∩ f ⁻¹' {c} with hTdef
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, hft⟩ :=
      ivt 0 L c (le_refl 0) h0L le_rfl (le_of_lt hLc) (by rw [h0]; exact le_of_lt hcs)
    exact ⟨t, by rw [hTdef]; exact ⟨ht, by simpa using hft⟩⟩
  have hTclosed : IsClosed T := by
    rw [hTdef]
    exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTbdd : BddBelow T := ⟨0, fun t ht => by rw [hTdef] at ht; exact ht.1.1⟩
  -- The first exit time.
  set r : ℝ := sInf T with hrdef
  have hr_mem : r ∈ T := by rw [hrdef]; exact hTclosed.csInf_mem hTne hTbdd
  have hr' : r ∈ Set.Icc 0 L ∧ f r = c := by
    have h := hr_mem
    rw [hTdef] at h
    exact ⟨h.1, by simpa using h.2⟩
  have hr_ge : 0 ≤ r := hr'.1.1
  have hr_le : r ≤ L := hr'.1.2
  have hrc : f r = c := hr'.2
  have hr_pos : 0 < r := by
    rcases eq_or_lt_of_le hr_ge with h | h
    · rw [← h, h0] at hrc; linarith
    · exact h
  -- `f > c` before `r`.
  have hexit : ∀ t ∈ Set.Ico 0 r, c < f t := by
    intro t ht
    rw [Set.mem_Ico] at ht
    by_contra hcon
    have hcon' : f t ≤ c := not_lt.mp hcon
    obtain ⟨x, hx, hfx⟩ :=
      ivt 0 t c (le_refl 0) ht.1 (le_trans ht.2.le hr_le) hcon' (by rw [h0]; exact le_of_lt hcs)
    have hxT : x ∈ T := by
      rw [hTdef]
      exact ⟨⟨hx.1, le_trans hx.2 (le_trans ht.2.le hr_le)⟩, by simpa using hfx⟩
    have hle : r ≤ x := by rw [hrdef]; exact csInf_le hTbdd hxT
    linarith [hx.2]
  -- The last time `f` takes the value `S₀` before the exit.
  set U : Set ℝ := Set.Icc 0 r ∩ f ⁻¹' {S₀} with hUdef
  have hUne : U.Nonempty :=
    ⟨0, by rw [hUdef]; exact ⟨⟨le_refl 0, hr_ge⟩, by simpa using h0⟩⟩
  have hUclosed : IsClosed U := by
    rw [hUdef]
    have hsub : Set.Icc 0 r ⊆ Set.Icc 0 L := fun x hx => ⟨hx.1, le_trans hx.2 hr_le⟩
    exact (hf.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hUbdd : BddAbove U := ⟨r, fun t ht => by rw [hUdef] at ht; exact ht.1.2⟩
  set ρ : ℝ := sSup U with hρdef
  have hρ_mem : ρ ∈ U := by rw [hρdef]; exact hUclosed.csSup_mem hUne hUbdd
  have hρ' : ρ ∈ Set.Icc 0 r ∧ f ρ = S₀ := by
    have h := hρ_mem
    rw [hUdef] at h
    exact ⟨h.1, by simpa using h.2⟩
  have hρ_ge : 0 ≤ ρ := hρ'.1.1
  have hρ_le : ρ ≤ r := hρ'.1.2
  have hρS : f ρ = S₀ := hρ'.2
  -- `f ≤ S₀` up to the exit.
  have hlast : ∀ t ∈ Set.Icc ρ r, f t ≤ S₀ := by
    intro t ht
    rw [Set.mem_Icc] at ht
    by_contra hcon
    have hcon' : S₀ < f t := not_le.mp hcon
    obtain ⟨x, hx, hfx⟩ :=
      ivt t r S₀ (le_trans hρ_ge ht.1) ht.2 hr_le (by rw [hrc]; exact le_of_lt hcs) hcon'.le
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨⟨le_trans hρ_ge (le_trans ht.1 hx.1), hx.2⟩, by simpa using hfx⟩
    have hxle : x ≤ ρ := by rw [hρdef]; exact le_csSup hUbdd hxU
    have hxt : x = t := le_antisymm (le_trans hxle ht.1) hx.1
    rw [hxt] at hfx
    linarith
  exact ⟨r, ρ, hr_pos, hr_le, hrc, hexit, ⟨hρ_ge, hρ_le⟩, hρS, hlast⟩

end Work.Diff.L
