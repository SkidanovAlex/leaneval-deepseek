import Mathlib
import Submission.Work.Peluse.Basic

/-!
## The residue-class cardinality bounds of the ladder's P2 node

For `c > 0` and each residue `r ∈ [0, c)`, the class `r` of the symmetric window
`symIcc N = [-N, N]` has cardinality between `N / c` and `4 (N / c + 1)`.

The proof splits `symIcc N` into the residue classes of the integers in `[0, 2N]` (a
translation by `N`), whose counts are given exactly by `Nat.count_modEq_card`
(the class cardinality in `[0, K)` is `K / c` or `K / c + 1`).
-/

namespace Work.Peluse.LadderP

/-- The residue condition `(y - N) % c = r` on a *natural* number `y` is the `Nat` congruence
`y ≡ r + N [MOD c.natAbs]`, for `r < c.natAbs`. -/
lemma key_emod_iff_modEq {c : ℤ} (hc : 0 < c) (N r y : ℕ) (hr : r < c.natAbs) :
    (((y : ℤ) - (N : ℤ)) % c = (r : ℤ)) ↔ y ≡ (r + N) [MOD c.natAbs] := by
  have hrnonneg : (0 : ℤ) ≤ (r : ℤ) := by positivity
  have hrlt : (r : ℤ) < c := by
    have h1 : (r : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast hr
    rwa [Int.natCast_natAbs, abs_of_pos hc] at h1
  have hmcast : ((c.natAbs : ℕ) : ℤ) = c := by rw [Int.natCast_natAbs, abs_of_pos hc]
  have hrem : (r : ℤ) % c = (r : ℤ) := Int.emod_eq_of_lt hrnonneg hrlt
  have hL : (((y : ℤ) - (N : ℤ)) % c = (r : ℤ)) ↔ (c ∣ (r : ℤ) - ((y : ℤ) - (N : ℤ))) := by
    rw [show (((y : ℤ) - (N : ℤ)) % c = (r : ℤ)) ↔ ((y : ℤ) - (N : ℤ)) ≡ (r : ℤ) [ZMOD c] by
        simp only [Int.ModEq, hrem]]
    exact Int.modEq_iff_dvd
  have hR : (y ≡ (r + N) [MOD c.natAbs]) ↔ (c ∣ ((r + N : ℕ) : ℤ) - (y : ℤ)) := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, hmcast]
  rw [hL, hR]
  have heq : (r : ℤ) - ((y : ℤ) - (N : ℤ)) = ((r + N : ℕ) : ℤ) - (y : ℤ) := by push_cast; ring
  rw [heq]

/-- The cardinality of the residue class `r` of `symIcc N` equals the number of `y ∈ [0, 2N]`
with `y ≡ r + N [MOD c]`. -/
lemma class_card_eq_count {c : ℤ} (hc : 0 < c) (N r : ℕ) (hr : r < c.natAbs) :
    ((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card
      = Nat.count (fun y : ℕ => y ≡ (r + N) [MOD c.natAbs]) (2 * N + 1) := by
  rw [Nat.count_eq_card_filter_range]
  have hfs : (Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))
      = ((Finset.range (2 * N + 1)).filter (fun y : ℕ => ((y : ℤ) - (N : ℤ)) % c = (r : ℤ))).image
          (fun y : ℕ => (y : ℤ) - (N : ℤ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, Work.Peluse.symIcc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hx3⟩
      have hge : 0 ≤ x + (N : ℤ) := by omega
      refine ⟨(x + (N : ℤ)).toNat, ⟨?_, ?_⟩, ?_⟩
      · have hh : (((x + (N : ℤ)).toNat : ℤ)) < ((2 * N + 1 : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg hge]; push_cast; omega
        exact_mod_cast hh
      · have hto : (((x + (N : ℤ)).toNat : ℤ)) = x + (N : ℤ) := Int.toNat_of_nonneg hge
        show ((((x + (N : ℤ)).toNat : ℤ)) - (N : ℤ)) % c = (r : ℤ)
        rw [hto]; ring_nf; exact hx3
      · have hto : (((x + (N : ℤ)).toNat : ℤ)) = x + (N : ℤ) := Int.toNat_of_nonneg hge
        rw [hto]; ring
    · rintro ⟨y, ⟨hy1, hy2⟩, hy3⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · rw [← hy3]; exact hy2
  rw [hfs]
  rw [Finset.card_image_of_injective]
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨h.1, (key_emod_iff_modEq hc N r y hr).mp h.2⟩,
           fun h => ⟨h.1, (key_emod_iff_modEq hc N r y hr).mpr h.2⟩⟩
  · intro a b h
    have h' : (a : ℤ) = (b : ℤ) := by
      have := congrArg (fun z : ℤ => z + (N : ℤ)) h
      simpa using this
    exact_mod_cast h'

theorem p2classCard {c : ℤ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ∀ r ∈ Finset.range c.natAbs,
      ((N / c.natAbs : ℕ) : ℝ)
          ≤ (((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
        ∧ (((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card : ℝ)
          ≤ 4 * ((N : ℝ) / (c : ℝ) + 1) := by
  intro r hr
  rw [Finset.mem_range] at hr
  have hm : 0 < c.natAbs := by omega
  have hval : ((Work.Peluse.symIcc N).filter (fun x : ℤ => x % c = (r : ℤ))).card
      = (2 * N + 1) / c.natAbs + (if (r + N) % c.natAbs < (2 * N + 1) % c.natAbs then 1 else 0) :=
    (class_card_eq_count hc N r hr).trans (Nat.count_modEq_card (2 * N + 1) hm (r + N))
  have hmR : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
    have h1 : ((c.natAbs : ℕ) : ℤ) = c := by rw [Int.natCast_natAbs, abs_of_pos hc]
    have h2 : (((c.natAbs : ℕ) : ℤ) : ℝ) = (c : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) h1
    simpa using h2
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    have : (1 : ℤ) ≤ c := by omega
    exact_mod_cast this
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  constructor
  · rw [hval]
    have h1 : N / c.natAbs ≤ (2 * N + 1) / c.natAbs := Nat.div_le_div_right (by omega)
    have h2 : N / c.natAbs ≤ (2 * N + 1) / c.natAbs
        + (if (r + N) % c.natAbs < (2 * N + 1) % c.natAbs then 1 else 0) :=
      le_trans h1 (Nat.le_add_right _ _)
    exact_mod_cast h2
  · rw [hval, Nat.cast_add]
    have hK : (((2 * N + 1) / c.natAbs : ℕ) : ℝ) ≤ (2 * (N : ℝ) + 1) / (c : ℝ) := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 * N + 1) (n := c.natAbs)
      rw [hmR] at this
      calc (((2 * N + 1) / c.natAbs : ℕ) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) / (c : ℝ) := this
        _ = (2 * (N : ℝ) + 1) / (c : ℝ) := by push_cast; ring
    have he : (((if (r + N) % c.natAbs < (2 * N + 1) % c.natAbs then 1 else 0 : ℕ)) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
    have hfin : (2 * (N : ℝ) + 1) / (c : ℝ) + 1 ≤ 4 * ((N : ℝ) / (c : ℝ) + 1) := by
      have hne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
      rw [div_add_one hne, div_add_one hne]
      rw [← mul_div_assoc]
      rw [div_le_div_iff₀ hcpos hcpos]
      nlinarith [hc1, hN0]
    linarith

end Work.Peluse.LadderP
