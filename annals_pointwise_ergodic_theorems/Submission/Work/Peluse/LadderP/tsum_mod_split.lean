import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.LadderP

/-- The statement: if `v : ℤ → ℂ` vanishes outside `[-N, N]`, then its total sum over `ℤ` splits
as the sum over the residue classes modulo `c` of the sums of `v` along the arithmetic
progressions `z ↦ c * z + r`, `r = 0, …, |c| - 1`. -/
theorem tsum_mod_split {c : ℤ} (hc : c ≠ 0) {N : ℕ} {v : ℤ → ℂ}
    (hv : ∀ x : ℤ, N < x.natAbs → v x = 0) :
    ∑' x : ℤ, v x = ∑ r ∈ Finset.range c.natAbs, ∑' z : ℤ, v (c * z + (r : ℤ)) := by
  set C : ℕ := c.natAbs with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact Int.natAbs_pos.mpr hc
  have hC1 : 1 ≤ C := hCpos
  have hcast : (C : ℤ) = |c| := by rw [hCdef]; exact Int.natCast_natAbs c
  -- The (slightly enlarged) comparison window `[-N-1, N+1]`.
  set S : Finset ℤ := Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1) with hSdef
  have hnotmem : ∀ x : ℤ, x ∉ S → (N : ℤ) < |x| := by
    intro x hx
    have hmem : ¬ (-(N:ℤ) - 1 ≤ x ∧ x ≤ (N:ℤ) + 1) := by
      simpa [hSdef, Finset.mem_Icc] using hx
    have hN : (0:ℤ) ≤ (N:ℤ) := Int.natCast_nonneg N
    rcases not_and_or.mp hmem with h | h
    · have hxlt : x < -(N:ℤ) - 1 := not_le.mp h
      have hx0 : x < 0 := by linarith
      rw [abs_of_neg hx0]; linarith
    · have hxgt : (N:ℤ) + 1 < x := not_le.mp h
      have : (N:ℤ) < x := by linarith
      linarith [le_abs_self x]
  have hconv : ∀ x : ℤ, (N:ℤ) < |x| → N < x.natAbs := by
    intro x h
    rw [← Int.natCast_natAbs x] at h
    exact_mod_cast h
  have hinner : ∀ r : ℕ, r < C → ∀ z : ℤ, z ∉ S → v (c * z + (r : ℤ)) = 0 := by
    intro r hr z hz
    apply hv
    apply hconv
    have hz' : (N:ℤ) < |z| := hnotmem z hz
    have htri : |c*z| - |(r:ℤ)| ≤ |c*z + (r:ℤ)| := by
      have h := abs_add_le (c*z + (r:ℤ)) (-(r:ℤ))
      rw [add_neg_cancel_right, abs_neg] at h
      linarith
    have hcz : |c * z| = (C:ℤ) * |z| := by rw [abs_mul, hcast]
    have hrz : |(r:ℤ)| = (r:ℤ) := abs_of_nonneg (Int.natCast_nonneg r)
    have hrle : (r:ℤ) ≤ (C:ℤ) - 1 := by
      have : (r:ℤ) < (C:ℤ) := by exact_mod_cast hr
      linarith
    have hzge : (N:ℤ) + 1 ≤ |z| := by linarith
    have hCz : (C:ℤ) * ((N:ℤ)+1) ≤ (C:ℤ) * |z| :=
      mul_le_mul_of_nonneg_left hzge (Int.natCast_nonneg C)
    rw [hcz, hrz] at htri
    nlinarith [htri, hCz, hrle]
  have hvS : ∀ x : ℤ, x ∉ S → v x = 0 := fun x hx => hv x (hconv x (hnotmem x hx))
  have hL : ∑' x : ℤ, v x = ∑ x ∈ S, v x := tsum_eq_sum (s := S) (f := v) hvS
  have hR : (∑ r ∈ Finset.range C, ∑' z : ℤ, v (c * z + (r : ℤ)))
      = ∑ r ∈ Finset.range C, ∑ z ∈ S, v (c * z + (r : ℤ)) :=
    Finset.sum_congr rfl (fun r hr =>
      tsum_eq_sum (s := S) (f := fun z : ℤ => v (c * z + (r : ℤ)))
        (fun z hz => hinner r (Finset.mem_range.mp hr) z hz))
  -- The map `(r, z) ↦ c * z + r` is injective on `range C × S`.
  have hinj : Set.InjOn (fun p : ℕ × ℤ => c * p.2 + (p.1 : ℤ))
      ↑((Finset.range C).product S) := by
    intro p hp q hq hpq
    have hp' : p ∈ (Finset.range C).product S := Finset.mem_coe.mp hp
    have hq' : q ∈ (Finset.range C).product S := Finset.mem_coe.mp hq
    obtain ⟨hp1, _hp2⟩ := Finset.mem_product.mp hp'
    obtain ⟨hq1, _hq2⟩ := Finset.mem_product.mp hq'
    have hp1' : p.1 < C := Finset.mem_range.mp hp1
    have hq1' : q.1 < C := Finset.mem_range.mp hq1
    have hkey : ((c * (p.2 - q.2)).natAbs) = (((q.1 : ℤ) - (p.1 : ℤ))).natAbs := by
      congr 1
      have h : c * p.2 + (p.1:ℤ) = c * q.2 + (q.1:ℤ) := hpq
      linarith
    rw [Int.natAbs_mul, ← hCdef] at hkey
    have hle : (((q.1 : ℤ) - (p.1 : ℤ))).natAbs ≤ C - 1 :=
      Int.natAbs_coe_sub_coe_le_of_le (by omega) (by omega)
    have hsmall : C * (p.2 - q.2).natAbs < C := by omega
    have h2 : (p.2 - q.2).natAbs = 0 := by
      have h := Nat.lt_of_mul_lt_mul_left
        (show C * (p.2 - q.2).natAbs < C * 1 by simpa using hsmall)
      omega
    have hp2q2 : p.2 = q.2 := by
      have := Int.natAbs_eq_zero.mp h2
      omega
    have h12 : (p.1 : ℤ) = (q.1 : ℤ) := by
      have h : c * p.2 + (p.1:ℤ) = c * q.2 + (q.1:ℤ) := hpq
      rw [hp2q2] at h
      linarith
    exact Prod.ext (by exact_mod_cast h12) hp2q2
  -- Every point of `S` is in the image of `range C × S`.
  have hsub : S ⊆ ((Finset.range C).product S).image
      (fun p : ℕ × ℤ => c * p.2 + (p.1 : ℤ)) := by
    intro x hx
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    rw [Finset.mem_image]
    refine ⟨((x % c).toNat, x / c), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (by
          have h0 : 0 ≤ x % c := Int.emod_nonneg x hc
          have hlt : x % c < (C : ℤ) := by rw [hcast]; exact Int.emod_lt_abs x hc
          exact (Int.toNat_lt h0).mpr hlt)
      · rw [hSdef, Finset.mem_Icc]
        have hxmem : -(N:ℤ) - 1 ≤ x ∧ x ≤ (N:ℤ) + 1 := by
          rw [hSdef, Finset.mem_Icc] at hxS; exact hxS
        have habsx : |x| ≤ (N:ℤ) + 1 := by
          rw [abs_le]; exact ⟨by linarith [hxmem.1], hxmem.2⟩
        have h0 : 0 ≤ x % c := Int.emod_nonneg x hc
        have h1 : x % c < (C:ℤ) := by rw [hcast]; exact Int.emod_lt_abs x hc
        have habsr : |x % c| ≤ (C:ℤ) - 1 := by
          rw [abs_of_nonneg h0]; linarith
        have hspl : c * (x / c) = x - x % c := by
          have h := Int.mul_ediv_add_emod x c; linarith
        have habsz : (C:ℤ) * |x / c| ≤ (N:ℤ) + (C:ℤ) := by
          have h2 : |c * (x/c)| = (C:ℤ) * |x/c| := by rw [abs_mul, hcast]
          rw [hspl] at h2
          calc (C:ℤ) * |x/c| = |x - x % c| := h2.symm
            _ ≤ |x| + |x % c| := by
                have h := abs_add_le x (-(x % c))
                simpa only [sub_eq_add_neg, abs_neg] using h
            _ ≤ ((N:ℤ)+1) + ((C:ℤ)-1) := add_le_add habsx habsr
            _ = (N:ℤ) + (C:ℤ) := by ring
        have hbound : (C:ℤ) * (|x/c| - 1) ≤ (N:ℤ) := by linarith
        have hle : |x/c| ≤ (N:ℤ) + 1 := by
          by_cases hz0 : |x/c| = 0
          · linarith
          · have hz1 : (1:ℤ) ≤ |x/c| := by
              have hnn : (0:ℤ) ≤ |x/c| := abs_nonneg _
              omega
            have hmul : (1:ℤ) * (|x/c| - 1) ≤ (C:ℤ) * (|x/c| - 1) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hC1) (by linarith)
            linarith
        exact ⟨by linarith [(abs_le.mp hle).1], (abs_le.mp hle).2⟩
    · have h0 : 0 ≤ x % c := Int.emod_nonneg x hc
      have hto : (((x % c).toNat : ℕ) : ℤ) = x % c := Int.toNat_of_nonneg h0
      rw [hto, Int.mul_ediv_add_emod]
  rw [hL, hR]
  calc ∑ x ∈ S, v x
      = ∑ x ∈ ((Finset.range C).product S).image
            (fun p : ℕ × ℤ => c * p.2 + (p.1 : ℤ)), v x :=
          Finset.sum_subset hsub (fun x _ hx => hvS x hx)
    _ = ∑ p ∈ (Finset.range C).product S, v (c * p.2 + (p.1 : ℤ)) :=
          Finset.sum_image hinj
    _ = ∑ r ∈ Finset.range C, ∑ z ∈ S, v (c * z + (r : ℤ)) :=
          Finset.sum_product (Finset.range C) S (fun p : ℕ × ℤ => v (c * p.2 + (p.1 : ℤ)))

end Work.Peluse.LadderP
