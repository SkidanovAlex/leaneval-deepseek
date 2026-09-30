import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- If `m ≤ n` and `m ≡ n [MOD q]`, then `q` divides the natural difference `n - m`. -/
private lemma dvd_sub_of_modEq {q m n : ℕ} (h : m ≡ n [MOD q]) (hmn : m ≤ n) : q ∣ n - m := by
  have h1 : (q : ℤ) ∣ (n : ℤ) - (m : ℤ) := h.dvd
  rw [← Nat.cast_sub hmn] at h1
  exact Int.natCast_dvd_natCast.mp h1

/-- A finite set of naturals lying in a window of half-width `W`, all of whose elements are
congruent mod `q` (`q ≥ 1`), has at most `2W/q + 1` elements. -/
lemma n4_window_modEq_card {A W : ℝ} {q : ℕ} (hq : 1 ≤ q) (hW0 : 0 ≤ W) {S : Finset ℕ}
    (hW : ∀ n ∈ S, |(n : ℝ) - A| ≤ W) (hmod : ∀ n ∈ S, ∀ n' ∈ S, n ≡ n' [MOD q]) :
    (S.card : ℝ) ≤ 2 * W / (q : ℝ) + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp only [Finset.card_empty, Nat.cast_zero]
    have : (0:ℝ) ≤ 2 * W / (q:ℝ) := by positivity
    linarith
  · -- `m` is the least element of `S`; every other element is `m + q * ((n - m)/q)`.
    set m := S.min' hS with hmdef
    have hmS : m ∈ S := S.min'_mem hS
    have hmin : ∀ n ∈ S, m ≤ n := fun n hn => S.min'_le n hn
    set k : ℕ → ℕ := fun n => (n - m) / q with hkdef
    -- on `S`, `n ↦ k n` is a genuine progress step: `n = m + q * k n`
    have hk_spec : ∀ n ∈ S, n = m + q * k n := by
      intro n hn
      have hmn : m ≤ n := hmin n hn
      have hdvd : q ∣ n - m := dvd_sub_of_modEq (hmod m hmS n hn) hmn
      have hmul : q * ((n - m) / q) = n - m := Nat.mul_div_cancel' hdvd
      have hk_eq : k n = (n - m) / q := rfl
      rw [hk_eq, hmul, Nat.add_sub_of_le hmn]
    -- hence `k` is injective on `S`
    have hk_inj : Set.InjOn k ↑S := by
      intro n hn n' hn' hkn
      have h1 := hk_spec n hn
      have h2 := hk_spec n' hn'
      rw [h1, h2, hkn]
    -- the window bounds the diameter of `S` by `2W`
    have hrel : ∀ n ∈ S, ((n - m : ℕ) : ℝ) ≤ 2 * W := by
      intro n hn
      have hmn : m ≤ n := hmin n hn
      have hn_le : (n : ℝ) ≤ A + W := by
        have := (abs_le.mp (hW n hn)).2; linarith
      have hm_le : A - W ≤ (m : ℝ) := by
        have := (abs_le.mp (hW m hmS)).1; linarith
      rw [Nat.cast_sub hmn]
      linarith
    -- so `k n ≤ 2W/q`
    have hk_le : ∀ n ∈ S, (k n : ℝ) ≤ 2 * W / (q : ℝ) := by
      intro n hn
      have hmn : m ≤ n := hmin n hn
      have hdvd : q ∣ n - m := dvd_sub_of_modEq (hmod m hmS n hn) hmn
      have hmul : q * k n = n - m := by
        have := Nat.mul_div_cancel' hdvd
        rwa [show k n = (n - m) / q from rfl]
      have hcast : ((q * k n : ℕ) : ℝ) = ((n - m : ℕ) : ℝ) := by rw [hmul]
      rw [Nat.cast_mul] at hcast
      have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
      rw [le_div_iff₀ hqpos]
      nlinarith [hcast, hrel n hn]
    -- the image of `k` lies in `{0, …, ⌊2W/q⌋}`
    have hsub : S.image k ⊆ Finset.range (Nat.floor (2 * W / (q:ℝ)) + 1) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨n, hn, rfl⟩ := hx
      rw [Finset.mem_range]
      have h1 : k n ≤ Nat.floor (2*W/(q:ℝ)) := by
        rw [Nat.le_floor_iff (by positivity)]
        exact hk_le n hn
      omega
    have hcard : S.card ≤ Nat.floor (2*W/(q:ℝ)) + 1 := by
      calc S.card = (S.image k).card := (Finset.card_image_of_injOn hk_inj).symm
        _ ≤ (Finset.range (Nat.floor (2*W/(q:ℝ))+1)).card := Finset.card_le_card hsub
        _ = Nat.floor (2*W/(q:ℝ)) + 1 := Finset.card_range _
    have hcast_card : (S.card : ℝ) ≤ (Nat.floor (2*W/(q:ℝ)) : ℝ) + 1 := by
      exact_mod_cast hcard
    have hfloor : (Nat.floor (2*W/(q:ℝ)) : ℝ) ≤ 2*W/(q:ℝ) := Nat.floor_le (by positivity)
    linarith

end Work.BMF
