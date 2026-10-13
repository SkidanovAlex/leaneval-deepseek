import Mathlib
import Submission.Work.WilG4c.EngineDefs

namespace Work.WilG4c

/-- **One-dimensional core of `tileN`.**  For `t ∈ (0,1)`, `lam ≥ 1` and
`K ≥ 2 * (lam - 1) + 2 = 2 * lam` there is a grid index `k < K` such that the point
`v = min (k/2) (lam - 1)` of the tile grid lies strictly between `lam * t - 1` and `lam * t`;
equivalently `y = lam * t - v` lies in `(0,1)`.

The index is `k = ⌈2 * lam * t⌉ - 1`: it is the largest integer with `k/2 < lam * t`, and
`k/2 ≥ lam * t - 1/2`. -/
theorem tile1_core (lam : ℝ) (hlam : 1 ≤ lam) (K : ℕ) (hK : 2 * (lam - 1) + 2 ≤ K) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ k : ℕ, k < K ∧ lam * t - 1 < min ((k : ℝ) / 2) (lam - 1) ∧
      min ((k : ℝ) / 2) (lam - 1) < lam * t := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have h2lam : 2 * lam ≤ (K : ℝ) := by
    have h : (2 * (lam - 1) + 2 : ℝ) = 2 * lam := by ring
    linarith [hK, h]
  set x : ℝ := 2 * lam * t with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hceil1 : 1 ≤ Nat.ceil x := Nat.succ_le_of_lt (Nat.ceil_pos.mpr hx0)
  have hcast : (((Nat.ceil x - 1 : ℕ)) : ℝ) = (Nat.ceil x : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
  have hceil_lt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (le_of_lt hx0)
  have hle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  refine ⟨Nat.ceil x - 1, ?_, ?_, ?_⟩
  · -- the index is below `K`
    have hlt : (((Nat.ceil x - 1 : ℕ)) : ℝ) < (K : ℝ) := by
      rw [hcast]
      have hxt : x < 2 * lam := by rw [hx]; nlinarith [ht1, hlam0]
      linarith
    exact_mod_cast hlt
  · -- lower bound
    refine lt_min ?_ ?_
    · rw [hcast]; linarith [hle, hx]
    · nlinarith [ht1, hlam0]
  · -- upper bound
    have hk : (((Nat.ceil x - 1 : ℕ)) : ℝ) / 2 < lam * t := by
      rw [hcast]; linarith [hceil_lt, hx]
    exact lt_of_le_of_lt (min_le_left _ _) hk

theorem tileN (N : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) (K : ℕ) (hK : 2 * (lam - 1) + 2 ≤ K)
    (t : Fin N → ℝ) (ht : t ∈ WilkiesDesign.openCube N) :
    ∃ (k : Fin N → Fin K) (y : Fin N → ℝ), y ∈ WilkiesDesign.openCube N ∧
      (∀ i, 0 ≤ min (((k i : ℕ) : ℝ) / 2) (lam - 1) ∧
        min (((k i : ℕ) : ℝ) / 2) (lam - 1) ≤ lam - 1) ∧
      (∀ i, (min (((k i : ℕ) : ℝ) / 2) (lam - 1) + y i) / lam = t i) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hkey : ∀ i : Fin N, ∃ k : ℕ, k < K ∧
      lam * t i - 1 < min ((k : ℝ) / 2) (lam - 1) ∧
      min ((k : ℝ) / 2) (lam - 1) < lam * t i := by
    intro i
    obtain ⟨ht0, ht1⟩ := ht i
    exact tile1_core lam hlam K hK ht0 ht1
  choose kk hkK hklo hkhi using hkey
  refine ⟨fun i => ⟨kk i, hkK i⟩, fun i => lam * t i - min ((kk i : ℝ) / 2) (lam - 1),
    ?_, ?_, ?_⟩
  · -- the remainder lies in the open cube
    intro i
    simp only []
    exact ⟨by linarith [hkhi i], by linarith [hklo i]⟩
  · -- the tile point is a legitimate grid point
    intro i
    refine ⟨le_min (by positivity) (by linarith), min_le_right _ _⟩
  · -- reconstruction
    intro i
    have h : min ((((fun j => (⟨kk j, hkK j⟩ : Fin K)) i : ℕ) : ℝ) / 2) (lam - 1) +
        (lam * t i - min ((((fun j => (⟨kk j, hkK j⟩ : Fin K)) i : ℕ) : ℝ) / 2) (lam - 1))
        = lam * t i := by ring
    rw [h, mul_div_cancel_left₀ (t i) (ne_of_gt hlam0)]

end Work.WilG4c
