import Mathlib

/-!
# Counting the "good residues" of `Weil`'s arithmetic

For `q ≥ 1` and `k ≥ 1` call `s ∈ [1, q-1]` *good* when
`min s (q - s) ≤ q/(2k) + 1/2`, i.e. when `s` is within `q/(2k) + 1/2` of one of the two
endpoints `0` and `q` of the interval.  This is exactly the size of the union of the two
"endpoint windows" `{s : s ≤ T}` and `{s : q - s ≤ T}` with `T = q/(2k) + 1/2`, each of which
contains at most `⌊T⌋₊` integers of `[1, q-1]`.  Hence the number of good residues is at most
`2⌊T⌋₊`, and since `T ≤ q/k` when `k ≤ q` while `T < 1` when `q < k`, we have
`⌊T⌋₊ ≤ ⌊q/k⌋₊`.

The result is the elementary counting input of the Weyl-sum estimates in
`Work.A3.Weil` (the "near the endpoint" residues are exactly the ones that fall in a small
set of denominators).
-/

namespace Work.A3.Weil

/-- Arithmetic part: `⌊q/(2k) + 1/2⌋₊ ≤ ⌊q/k⌋₊` for `q ≥ 1`, `k ≥ 1`. -/
lemma card_goodResidues_floor {q : ℤ} (hq : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    ⌊(q : ℝ) / (2 * (k : ℝ)) + 1 / 2⌋₊ ≤ ⌊(q : ℝ) / (k : ℝ)⌋₊ := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hT0 : (0 : ℝ) ≤ (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 := by positivity
  refine Nat.le_of_lt_succ ?_
  rw [Nat.floor_lt hT0]
  push_cast
  have hTeq : (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 = ((q : ℝ) / (k : ℝ)) / 2 + 1 / 2 := by
    rw [div_div]; ring_nf
  rcases le_or_gt (k : ℝ) (q : ℝ) with hkq | hqk
  · have h1 : (1 : ℝ) ≤ (q : ℝ) / (k : ℝ) := by rw [le_div_iff₀ hk0]; linarith
    calc (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 = ((q : ℝ) / (k : ℝ)) / 2 + 1 / 2 := hTeq
      _ ≤ (q : ℝ) / (k : ℝ) := by linarith
      _ < (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  · have h1 : (q : ℝ) / (k : ℝ) < 1 := by rw [div_lt_one hk0]; exact hqk
    have h2 : (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 < 1 := by rw [hTeq]; linarith
    have h3 : (0 : ℝ) ≤ (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith

/-- Counting the lower window: at most `⌊T⌋₊` integers `s ∈ [1, q-1]` satisfy `s ≤ T`. -/
lemma card_goodResidues_lower {q : ℤ} (T : ℝ) :
    ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T)).card ≤ ⌊T⌋₊ := by
  have hsub : (Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T)
      ⊆ Finset.Icc (1 : ℤ) ((⌊T⌋₊ : ℕ) : ℤ) := by
    intro s hs
    obtain ⟨hsS, hsT⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs1, _⟩ := Finset.mem_Icc.mp hsS
    refine Finset.mem_Icc.mpr ⟨hs1, ?_⟩
    have hz : (0 : ℤ) ≤ s := by omega
    have hzr : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
    have h1 : s.toNat ≤ ⌊T⌋₊ := Nat.le_floor (by rw [hzr]; exact hsT)
    have h2 : (s.toNat : ℤ) ≤ (⌊T⌋₊ : ℤ) := by exact_mod_cast h1
    rwa [Int.toNat_of_nonneg hz] at h2
  calc ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T)).card
      ≤ (Finset.Icc (1 : ℤ) ((⌊T⌋₊ : ℕ) : ℤ)).card := Finset.card_le_card hsub
    _ = ⌊T⌋₊ := by rw [Int.card_Icc]; simp

/-- Counting the upper window: at most `⌊T⌋₊` integers `s ∈ [1, q-1]` satisfy `q - s ≤ T`. -/
lemma card_goodResidues_upper {q : ℤ} (T : ℝ) :
    ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T)).card
      ≤ ⌊T⌋₊ := by
  have hsub : (Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T)
      ⊆ Finset.Icc (q - ((⌊T⌋₊ : ℕ) : ℤ)) (q - 1) := by
    intro s hs
    obtain ⟨hsS, hsT⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hsS
    refine Finset.mem_Icc.mpr ⟨?_, hs2⟩
    have hz : (0 : ℤ) ≤ q - s := by omega
    have hzr : (((q - s).toNat : ℕ) : ℝ) = ((q - s : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]
    have h1 : (q - s).toNat ≤ ⌊T⌋₊ := Nat.le_floor (by rw [hzr]; exact hsT)
    have h2 : ((q - s).toNat : ℤ) ≤ (⌊T⌋₊ : ℤ) := by exact_mod_cast h1
    have h3 : q - s ≤ ((⌊T⌋₊ : ℕ) : ℤ) := by rwa [Int.toNat_of_nonneg hz] at h2
    omega
  calc ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T)).card
      ≤ (Finset.Icc (q - ((⌊T⌋₊ : ℕ) : ℤ)) (q - 1)).card := Finset.card_le_card hsub
    _ = ⌊T⌋₊ := by
        rw [Int.card_Icc]
        have h : q - 1 + 1 - (q - ((⌊T⌋₊ : ℕ) : ℤ)) = ((⌊T⌋₊ : ℕ) : ℤ) := by ring
        rw [h, Int.toNat_natCast]

theorem card_goodResidues_le {q : ℤ} (hq : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    (((Finset.Icc (1 : ℤ) (q - 1)).filter
        (fun s : ℤ => ((min s (q - s) : ℤ) : ℝ) ≤ (q : ℝ) / (2 * (k : ℝ)) + 1 / 2)).card : ℝ)
      ≤ 2 * (⌊(q : ℝ) / (k : ℝ)⌋₊ : ℝ) := by
  set T : ℝ := (q : ℝ) / (2 * (k : ℝ)) + 1 / 2 with hT
  have hAcard := card_goodResidues_lower (q := q) T
  have hBcard := card_goodResidues_upper (q := q) T
  have hsub : (Finset.Icc (1 : ℤ) (q - 1)).filter
        (fun s : ℤ => ((min s (q - s) : ℤ) : ℝ) ≤ T)
      ⊆ ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T))
        ∪ ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T)) := by
    intro s hs
    obtain ⟨hsS, hsmin⟩ := Finset.mem_filter.mp hs
    rw [Int.cast_min] at hsmin
    rw [Finset.mem_union]
    rcases min_le_iff.mp hsmin with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hsS, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hsS, h⟩)
  have hcard : ((Finset.Icc (1 : ℤ) (q - 1)).filter
        (fun s : ℤ => ((min s (q - s) : ℤ) : ℝ) ≤ T)).card ≤ 2 * ⌊T⌋₊ := by
    calc ((Finset.Icc (1 : ℤ) (q - 1)).filter
            (fun s : ℤ => ((min s (q - s) : ℤ) : ℝ) ≤ T)).card
        ≤ (((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T))
            ∪ ((Finset.Icc (1 : ℤ) (q - 1)).filter
                (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T))).card :=
          Finset.card_le_card hsub
      _ ≤ ((Finset.Icc (1 : ℤ) (q - 1)).filter (fun s : ℤ => (s : ℝ) ≤ T)).card
          + ((Finset.Icc (1 : ℤ) (q - 1)).filter
              (fun s : ℤ => ((q - s : ℤ) : ℝ) ≤ T)).card :=
          Finset.card_union_le _ _
      _ ≤ ⌊T⌋₊ + ⌊T⌋₊ := add_le_add hAcard hBcard
      _ = 2 * ⌊T⌋₊ := by ring
  have hfloor : ⌊T⌋₊ ≤ ⌊(q : ℝ) / (k : ℝ)⌋₊ := by
    rw [hT]; exact card_goodResidues_floor hq hk
  exact_mod_cast (le_trans hcard (Nat.mul_le_mul_left 2 hfloor))

end Work.A3.Weil
