import Mathlib

namespace Work.ZeroDensity.Montgomery

/-- If two real numbers are at distance at least `1`, then their floors (after the common
shift by `a`) differ. -/
lemma floor_sub_ne_of_abs_sub_ge_one {x y a : ℝ} (h : 1 ≤ |x - y|) :
    ⌊x - a⌋ ≠ ⌊y - a⌋ := by
  rcases lt_trichotomy x y with hlt | hxy | hgt
  · have h1 : 1 ≤ y - x := by
      have h3 : |x - y| = y - x := by
        rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < y - x)]
      linarith
    have h2 : (x - a) + 1 ≤ y - a := by linarith
    have h4 : ⌊x - a⌋ < ⌊y - a⌋ := by
      have h5 : ⌊(x - a) + 1⌋ ≤ ⌊y - a⌋ := Int.floor_le_floor h2
      rwa [Int.floor_add_one] at h5
    exact ne_of_lt h4
  · subst hxy; rw [sub_self, abs_zero] at h; linarith
  · have h1 : 1 ≤ x - y := by
      have h3 : |x - y| = x - y := by
        rw [abs_of_pos (by linarith : (0:ℝ) < x - y)]
      linarith
    have h2 : (y - a) + 1 ≤ x - a := by linarith
    have h4 : ⌊y - a⌋ < ⌊x - a⌋ := by
      have h5 : ⌊(y - a) + 1⌋ ≤ ⌊x - a⌋ := Int.floor_le_floor h2
      rwa [Int.floor_add_one] at h5
    exact ne_of_gt h4

theorem sepCardLe {Sp : Finset ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsep : ∀ s ∈ Sp, ∀ s' ∈ Sp, s ≠ s' → 1 ≤ |s - s'|)
    (hbd : ∀ s ∈ Sp, a ≤ s ∧ s ≤ b) :
    (Sp.card : ℝ) ≤ b - a + 1 := by
  -- The map `s ↦ ⌊s - a⌋` is injective on a `1`-separated set.
  have hinj : Set.InjOn (fun s : ℝ => ⌊s - a⌋) ↑Sp := by
    intro s hs s' hs' hfs
    by_contra hne
    exact floor_sub_ne_of_abs_sub_ge_one
      (hsep s (Finset.mem_coe.mp hs) s' (Finset.mem_coe.mp hs') hne) hfs
  -- ... and it maps `Sp` into the interval `{0, …, ⌊b - a⌋}`.
  have himg : Sp.image (fun s : ℝ => ⌊s - a⌋) ⊆ Finset.Icc (0:ℤ) ⌊b - a⌋ := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hbd s hs
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr (by linarith), Int.floor_le_floor (by linarith)⟩
  have hle : Sp.card ≤ (Finset.Icc (0:ℤ) ⌊b - a⌋).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card himg
  have h0 : (0:ℤ) ≤ ⌊b - a⌋ := Int.floor_nonneg.mpr (by linarith)
  calc (Sp.card : ℝ) ≤ ((Finset.Icc (0:ℤ) ⌊b - a⌋).card : ℝ) := by exact_mod_cast hle
    _ = ((⌊b - a⌋ : ℤ) : ℝ) + 1 := by
        have h1 : ((Finset.Icc (0:ℤ) ⌊b - a⌋).card : ℤ) = ⌊b - a⌋ + 1 := by
          rw [Int.card_Icc_of_le 0 ⌊b - a⌋ (by linarith)]
          ring
        rw [← Int.cast_natCast (R := ℝ) (Finset.Icc (0:ℤ) ⌊b - a⌋).card, h1]
        push_cast
        ring
    _ ≤ b - a + 1 := by
        have := Int.floor_le (b - a)
        linarith

end Work.ZeroDensity.Montgomery
