import Mathlib

namespace Work.EKLComp

/-- Index of a real number in the grid of `k` intervals `[i/k, (i+1)/k)` cutting out `[0,1)`.
For `x ∈ [0,1)` this is the (nonnegative) integer `⌊x * k⌋`, reduced mod `k` only so that the
function is total. -/
private noncomputable def gridIdx (k : ℕ) (hk : 0 < k) (x : ℝ) : Fin k :=
  ⟨(⌊x * (k : ℝ)⌋).toNat % k, Nat.mod_lt _ hk⟩

/-- For `x ∈ [0,1)` the two facts we need about `⌊x * k⌋`: it is nonnegative (so `toNat` is the
identity) and it is `< k`. -/
private lemma floor_mul_toNat_spec (k : ℕ) (hk : 0 < k) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((⌊x * (k : ℝ)⌋).toNat : ℤ) = ⌊x * (k : ℝ)⌋ ∧ (⌊x * (k : ℝ)⌋).toNat < k := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hnn : 0 ≤ ⌊x * (k : ℝ)⌋ := Int.floor_nonneg.mpr (mul_nonneg hx0 (le_of_lt hkR))
  have hlt : ⌊x * (k : ℝ)⌋ < (k : ℤ) := by
    have hfloor : (⌊x * (k : ℝ)⌋ : ℝ) ≤ x * (k : ℝ) := Int.floor_le _
    have hxklt : x * (k : ℝ) < (k : ℝ) := by
      have := mul_lt_mul_of_pos_right hx1 hkR; simpa using this
    have : (⌊x * (k : ℝ)⌋ : ℝ) < (k : ℝ) := lt_of_le_of_lt hfloor hxklt
    exact_mod_cast this
  exact ⟨Int.toNat_of_nonneg hnn, (Int.toNat_lt hnn).mpr hlt⟩

/-- Two reals in `[0,1)` with the same grid index lie within `1/k` of each other. -/
private lemma abs_sub_lt_div_of_gridIdx_eq (k : ℕ) (hk : 0 < k) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (h : gridIdx k hk x = gridIdx k hk y) : |x - y| < (1 : ℝ) / k := by
  obtain ⟨hxcast, hxlt⟩ := floor_mul_toNat_spec k hk hx0 hx1
  obtain ⟨hycast, hylt⟩ := floor_mul_toNat_spec k hk hy0 hy1
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hval : (⌊x * (k:ℝ)⌋).toNat = (⌊y * (k:ℝ)⌋).toNat := by
    have hv := congrArg Fin.val h; simp only [gridIdx] at hv
    rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hv
  have hfl : ⌊x * (k:ℝ)⌋ = ⌊y * (k:ℝ)⌋ := by rw [← hxcast, ← hycast, hval]
  have hflR : (⌊x * (k:ℝ)⌋ : ℝ) = (⌊y * (k:ℝ)⌋ : ℝ) := by exact_mod_cast hfl
  have hxy : x * (k:ℝ) - y * (k:ℝ) < 1 := by
    have h1 := Int.lt_floor_add_one (x * (k:ℝ)); have h2 := Int.floor_le (y * (k:ℝ)); linarith
  have hyx : y * (k:ℝ) - x * (k:ℝ) < 1 := by
    have h1 := Int.lt_floor_add_one (y * (k:ℝ)); have h2 := Int.floor_le (x * (k:ℝ)); linarith
  have habs : |x * (k:ℝ) - y * (k:ℝ)| < 1 := abs_lt.mpr ⟨by linarith, hxy⟩
  have habsfac : |x - y| * (k:ℝ) < 1 := by
    have hkabs : |(k:ℝ)| = (k:ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    have h1 : |x * (k:ℝ) - y * (k:ℝ)| = |x - y| * (k:ℝ) := by rw [← sub_mul, abs_mul, hkabs]
    rwa [h1] at habs
  exact (lt_div_iff₀ hkR).mpr habsfac

/-- Pigeonhole / grid extraction: a finite set of points of the unit square `[0,1)²` contains a
subsquare-cluster `G` of points that are pairwise within distance `ε₀`, accounting for all but a
factor `⌈2/ε₀⌉²` of the points. -/
theorem subsquare_extract (ε₀ : ℝ) (hε₀ : 0 < ε₀) (F : Finset (ℝ × ℝ))
    (hF : ∀ x ∈ F, 0 ≤ x.1 ∧ x.1 < 1 ∧ 0 ≤ x.2 ∧ x.2 < 1) :
    ∃ G : Finset (ℝ × ℝ), G ⊆ F ∧
      (∀ x ∈ G, ∀ y ∈ G, dist x y ≤ ε₀) ∧
      F.card ≤ (Nat.ceil (2 / ε₀)) ^ 2 * G.card := by
  classical
  let k : ℕ := Nat.ceil (2 / ε₀)
  have hk_pos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have h1k_le : (1 : ℝ) / k ≤ ε₀ := by
    rw [div_le_iff₀ hkR]
    have hceil : (2 : ℝ) / ε₀ ≤ (k : ℝ) := Nat.le_ceil (2 / ε₀)
    have h2 : (2 : ℝ) ≤ ε₀ * (k : ℝ) := by
      have := (div_le_iff₀ hε₀).mp hceil; linarith
    linarith
  let idx : ℝ × ℝ → Fin k × Fin k := fun p => (gridIdx k hk_pos p.1, gridIdx k hk_pos p.2)
  obtain ⟨c0, -, hc0max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k × Fin k))
      (fun c => (F.filter (fun p => idx p = c)).card)
      ⟨(⟨0, hk_pos⟩, ⟨0, hk_pos⟩), Finset.mem_univ _⟩
  refine ⟨F.filter (fun p => idx p = c0), Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨hxmem, hxidx⟩ := hx
    obtain ⟨hymem, hyidx⟩ := hy
    have hidx : idx x = idx y := by rw [hxidx, hyidx]
    have hxb := hF x hxmem
    have hyb := hF y hymem
    have h1 : gridIdx k hk_pos x.1 = gridIdx k hk_pos y.1 := by
      have := congrArg Prod.fst hidx; simpa [idx] using this
    have h2 : gridIdx k hk_pos x.2 = gridIdx k hk_pos y.2 := by
      have := congrArg Prod.snd hidx; simpa [idx] using this
    have ha := abs_sub_lt_div_of_gridIdx_eq k hk_pos hxb.1 hxb.2.1 hyb.1 hyb.2.1 h1
    have hb := abs_sub_lt_div_of_gridIdx_eq k hk_pos hxb.2.2.1 hxb.2.2.2 hyb.2.2.1 hyb.2.2.2 h2
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    calc max |x.1 - y.1| |x.2 - y.2| ≤ (1 : ℝ) / k := max_le ha.le hb.le
      _ ≤ ε₀ := h1k_le
  · have hsum := Finset.card_eq_sum_card_image idx F
    rw [hsum]
    have himg : (F.image idx).card ≤ k ^ 2 := by
      calc (F.image idx).card ≤ Fintype.card (Fin k × Fin k) := Finset.card_le_univ _
        _ = k * k := by rw [Fintype.card_prod, Fintype.card_fin]
        _ = k ^ 2 := by rw [pow_two]
    calc ∑ b ∈ F.image idx, (F.filter (fun p => idx p = b)).card
        ≤ ∑ _b ∈ F.image idx, (F.filter (fun p => idx p = c0)).card := by
          apply Finset.sum_le_sum
          intro b hb
          exact hc0max b (Finset.mem_univ b)
      _ = (F.image idx).card * (F.filter (fun p => idx p = c0)).card :=
          Finset.sum_const_nat (fun _ _ => rfl)
      _ ≤ k ^ 2 * (F.filter (fun p => idx p = c0)).card := Nat.mul_le_mul_right _ himg

end Work.EKLComp
