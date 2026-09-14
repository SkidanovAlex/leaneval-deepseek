import Mathlib

namespace Commons.NumberTheory.Int

/-- The number of integers `d` with `|d| ≤ N` lying in a fixed residue class modulo `r`
(here expressed as `r ∣ (y - d)`) is at most `2*N/r + 1`. -/
private lemma ncard_int_residue_le (N r : ℕ) (y : ℤ) :
    (({d : ℤ | |d| ≤ (N : ℤ) ∧ (r : ℤ) ∣ (y - d)} : Set ℤ).ncard) ≤ 2 * N / r + 1 := by
  have hf : ∀ d ∈ ({d : ℤ | |d| ≤ (N : ℤ) ∧ (r : ℤ) ∣ (y - d)} : Set ℤ),
      (d + N).toNat / r ∈ Set.Iic (2 * N / r) := by
    intro d hd
    rw [Set.mem_Iic]
    have hb : d ≤ (N : ℤ) := (abs_le.mp hd.1).2
    have hub : d + (N : ℤ) ≤ ((2 * N : ℕ) : ℤ) := by push_cast; linarith
    have hnat : (d + N).toNat ≤ 2 * N := Int.toNat_le.mpr hub
    exact Nat.div_le_div_right hnat
  have hinj : Set.InjOn (fun d : ℤ => (d + N).toNat / r)
      ({d : ℤ | |d| ≤ (N : ℤ) ∧ (r : ℤ) ∣ (y - d)} : Set ℤ) := by
    intro d hd d' hd' heq
    have hmod1 : d ≡ y [ZMOD (r : ℤ)] := (Int.modEq_iff_dvd).mpr hd.2
    have hmod2 : d' ≡ y [ZMOD (r : ℤ)] := (Int.modEq_iff_dvd).mpr hd'.2
    have hmod : d + (N : ℤ) ≡ d' + (N : ℤ) [ZMOD (r : ℤ)] :=
      (hmod1.trans hmod2.symm).add_right (N : ℤ)
    have h0 : (0 : ℤ) ≤ d + (N : ℤ) := by have := (abs_le.mp hd.1).1; linarith
    have h0' : (0 : ℤ) ≤ d' + (N : ℤ) := by have := (abs_le.mp hd'.1).1; linarith
    have hnat : (d + N).toNat ≡ (d' + N).toNat [MOD r] := by
      rw [← Int.natCast_modEq_iff, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h0']
      exact hmod
    have hmod_eq : (d + N).toNat % r = (d' + N).toNat % r := hnat
    have key1 : (d + N).toNat = r * ((d + N).toNat / r) + (d + N).toNat % r :=
      (Nat.div_add_mod _ _).symm
    have key1' : (d' + N).toNat = r * ((d' + N).toNat / r) + (d' + N).toNat % r :=
      (Nat.div_add_mod _ _).symm
    have heq' : (d + N).toNat / r = (d' + N).toNat / r := heq
    have hnat_eq : (d + N).toNat = (d' + N).toNat := by rw [key1, key1', heq', hmod_eq]
    have : d + (N : ℤ) = d' + (N : ℤ) := by
      rw [← Int.toNat_of_nonneg h0, ← Int.toNat_of_nonneg h0', hnat_eq]
    linarith
  have hle := Set.ncard_le_ncard_of_injOn (fun d : ℤ => (d + N).toNat / r) hf hinj
  rwa [Set.ncard_Iic_nat] at hle

/-- The number of integers `c` with `|c| ≤ K` and `r ∣ (y - 2*c)` is at most `4*K/r + 1`:
the values `2*c` lie in the interval `[-2K, 2K]`, and an interval of that length meets a
fixed residue class modulo `r` in at most `2*(2K)/r + 1` points. -/
theorem ncard_two_mul_residue_le (r K : ℕ) (hr : 1 ≤ r) (y : ℤ) :
    ((({c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)} : Set ℤ)).ncard : ℕ)
      ≤ 4 * K / r + 1 := by
  have _hle := hr
  have hinjS : Set.InjOn (fun c : ℤ => 2 * c)
      ({c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)} : Set ℤ) := by
    intro a _ b _ h; linarith
  have himg : (({c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)} : Set ℤ).ncard)
      = ((fun c : ℤ => 2 * c) '' {c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)}).ncard :=
    (Set.InjOn.ncard_image hinjS).symm
  have hsub : (fun c : ℤ => 2 * c) '' {c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)}
      ⊆ {d : ℤ | |d| ≤ ((2 * K : ℕ) : ℤ) ∧ (r : ℤ) ∣ (y - d)} := by
    rintro d ⟨c, hc, rfl⟩
    refine ⟨?_, hc.2⟩
    have h2 : |2 * c| = 2 * |c| := by rw [abs_mul]; norm_num
    rw [h2]
    have := hc.1
    push_cast
    linarith
  have hfinT : ({d : ℤ | |d| ≤ ((2 * K : ℕ) : ℤ) ∧ (r : ℤ) ∣ (y - d)} : Set ℤ).Finite :=
    (Set.finite_Icc (-((2 * K : ℕ) : ℤ)) ((2 * K : ℕ) : ℤ)).subset (fun d hd => abs_le.mp hd.1)
  have hle2 : ((fun c : ℤ => 2 * c) '' {c : ℤ | |c| ≤ (K : ℤ) ∧ (r : ℤ) ∣ (y - 2 * c)}).ncard
      ≤ 4 * K / r + 1 := by
    refine le_trans (Set.ncard_le_ncard hsub hfinT) ?_
    have h3 := ncard_int_residue_le (2 * K) r y
    have h4 : 2 * (2 * K) / r + 1 = 4 * K / r + 1 := by
      congr 1
      rw [show 2 * (2 * K) = 4 * K by ring]
    rwa [h4] at h3
  rw [himg]
  exact hle2

end Commons.NumberTheory.Int
