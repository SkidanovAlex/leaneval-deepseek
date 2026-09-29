import Mathlib

namespace Work.TMC16Core.Trig

theorem sum_emod_coprime {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (F : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc 1 q, F (((k : ℤ) * p) % q) = ∑ j ∈ Finset.range q, F j := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  -- The map sending `k` to `(k * p) % q`, viewed as a function `ℕ → ℤ`.
  let g : ℕ → ℤ := fun k => ((k : ℤ) * p) % (q : ℤ)
  change (∑ k ∈ Finset.Icc 1 q, F (g k)) = ∑ j ∈ Finset.range q, F ((j : ℤ))
  -- `g` is injective on `{1, …, q}`: two values in `[1,q]` with equal residues differ by a
  -- multiple of `q`, hence by `0`, since they lie in an interval of length `< q`.
  have hinj : Set.InjOn g ↑(Finset.Icc 1 q) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Icc] at ha hb
    obtain ⟨ha1, haq⟩ := ha
    obtain ⟨hb1, hbq⟩ := hb
    have hdvd : (q : ℤ) ∣ ((a : ℤ) - (b : ℤ)) * p := by
      have h1 : (q : ℤ) ∣ (a : ℤ) * p - (b : ℤ) * p := by
        rw [Int.dvd_iff_emod_eq_zero]
        rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
        exact hab
      rwa [← sub_mul] at h1
    -- `q` divides `(a-b) * p`, and `q` is coprime to `p`, so `q` divides `a - b`.
    have hnat0 : (q : ℤ).natAbs ∣ (((a : ℤ) - (b : ℤ)) * p).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hdvd
    rw [Int.natAbs_natCast, Int.natAbs_mul] at hnat0
    have hq_dvd : q ∣ ((a : ℤ) - (b : ℤ)).natAbs :=
      hcop.symm.dvd_of_dvd_mul_left (by simpa [mul_comm] using hnat0)
    -- and `|a - b| < q`, so the only possibility is `a - b = 0`.
    have hlt : ((a : ℤ) - (b : ℤ)).natAbs < q := by
      have hb1' : |(a : ℤ) - (b : ℤ)| < (q : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      rw [Int.abs_eq_natAbs] at hb1'
      exact_mod_cast hb1'
    have hzero : ((a : ℤ) - (b : ℤ)).natAbs = 0 := by
      have h1 : ((a : ℤ) - (b : ℤ)).natAbs % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd
      rwa [Nat.mod_eq_of_lt hlt] at h1
    have h2 : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp (Int.natAbs_eq_zero.mp hzero)
    exact_mod_cast h2
  -- Hence `g` is a bijection from `{1, …, q}` onto the residues `{0, …, q-1}`.
  have himg : (Finset.Icc 1 q).image g = (Finset.range q).image (fun j : ℕ => (j : ℤ)) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      have hy0 : 0 ≤ g k := Int.emod_nonneg _ hq0
      have hylt : g k < (q : ℤ) := Int.emod_lt_of_pos _ hqpos
      exact Finset.mem_image.mpr ⟨(g k).toNat, Finset.mem_range.mpr ((Int.toNat_lt hy0).mpr hylt),
        Int.toNat_of_nonneg hy0⟩
    · have ht : ((Finset.range q).image (fun j : ℕ => (j : ℤ))).card = q := by
        rw [Finset.card_image_of_injective (Finset.range q) (Nat.cast_injective (R := ℤ)),
          Finset.card_range]
      have hs : ((Finset.Icc 1 q).image g).card = q := by
        rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]
        omega
      omega
  rw [← Finset.sum_image (f := F) (g := g) (s := Finset.Icc 1 q) hinj]
  rw [himg]
  exact Finset.sum_image (f := F) (g := fun j : ℕ => (j : ℤ)) (s := Finset.range q)
    (fun a _ b _ h => Nat.cast_injective h)

end Work.TMC16Core.Trig
