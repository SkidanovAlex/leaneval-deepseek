import Mathlib
import Submission.Work.GM.Trace.Spart_defs

/-!
# The weighted count `Σ_{m ∈ s} |rho m|^{-j}` (GM §4/5 combinatorial input)

For `m : ℤ³` with `nzCount m = 1` let `rho m` be the unique non-zero coordinate
(`Submission.Work.GM.Trace.Spart_defs`).  This file proves

`∑_{m ∈ s} 1/|rho m|^j ≤ 24 / X^{j-1}`

for any finite set `s` of such `m` whose `rho`-values all exceed `X ≥ 1` in absolute
value, and any `j ≥ 2`.

The arithmetic content is that `rho` is at most `6`-to-`1` on the `nzCount = 1` locus
(three families `(n,0,0)`, `(0,n,0)`, `(0,0,n)` times the two signs), so the sum is
dominated by the tail of the `p`-series `Σ |n|^{-j}`, which converges geometrically
fast.  The tail is handled by reduction to the `j = 2` estimate already in Mathlib
(`sum_Ioo_inv_sq_le`) after peeling off `j - 2` factors of `1/|rho m| ≤ 1/X`.
-/

namespace Work.GM.Trace

open Submission.GM

/-- The inverse of `m ↦ (fam m, rho m)` on the `nzCount = 1` locus: from the family and
the value of the non-zero coordinate, reconstruct `m`. -/
def unrho (p : Fin 3 × ℤ) : ℤ × ℤ × ℤ :=
  if p.1 = 0 then (p.2, 0, 0) else if p.1 = 1 then (0, p.2, 0) else (0, 0, p.2)

/-- On the `nzCount = 1` locus, `(fam, rho)` is a left inverse of `unrho`. -/
theorem unrho_fam_rho (m : ℤ × ℤ × ℤ) (h : nzCount m = 1) :
    unrho (fam m, rho m) = m := by
  obtain ⟨a, b, c⟩ := m
  rcases nzCount_one_cases (a, b, c) h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · simp only at h1 h2 h3
    rw [fam_eq_zero h1, rho_of_ne_zero h1, unrho]
    simp [h2, h3]
  · simp only at h1 h2 h3
    rw [fam_eq_one h1 h2, rho_of_fst_eq_zero h1 h2, unrho]
    simp [h1, h3]
  · simp only at h1 h2 h3
    rw [fam_eq_two h1 h2, rho_of_fst_snd_eq_zero h1 h2, unrho]
    simp [h1, h2]

/-- `rho` is at most `6`-to-`1` on `s` (when `nzCount = 1` there): for every
`k : ℕ`, at most six `m ∈ s` have `|rho m| = k`. -/
theorem fiber_card_le (s : Finset (ℤ × ℤ × ℤ)) (hs : ∀ m ∈ s, nzCount m = 1) (k : ℕ) :
    (s.filter (fun m => (rho m).natAbs = k)).card ≤ 6 := by
  set t := s.filter (fun m => (rho m).natAbs = k) with ht
  have hinj : Set.InjOn (fun m => (fam m, rho m)) ↑t := by
    intro m hm m' hm' heq
    have hs_m : nzCount m = 1 := hs m (Finset.mem_of_mem_filter m hm)
    have hs_m' : nzCount m' = 1 := hs m' (Finset.mem_of_mem_filter m' hm')
    have h2 := congrArg unrho heq
    rwa [unrho_fam_rho m hs_m, unrho_fam_rho m' hs_m'] at h2
  have hsub : t.image (fun m => (fam m, rho m)) ⊆
      ((Finset.univ : Finset (Fin 3)) ×ˢ ({(k:ℤ), -(k:ℤ)} : Finset ℤ)) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_univ, true_and]
    have hk : (rho m).natAbs = k := (Finset.mem_filter.mp hm).2
    rcases Int.natAbs_eq_iff.mp hk with h | h <;> simp [h]
  have hcard2 : ((Finset.univ : Finset (Fin 3)) ×ˢ ({(k:ℤ), -(k:ℤ)} : Finset ℤ)).card ≤ 6 := by
    rw [Finset.card_product]
    have h2 : ({(k:ℤ), -(k:ℤ)} : Finset ℤ).card ≤ 2 := by
      calc ({(k:ℤ), -(k:ℤ)} : Finset ℤ).card
          ≤ (({-(k:ℤ)} : Finset ℤ)).card + 1 := Finset.card_insert_le (k:ℤ) {-(k:ℤ)}
        _ = 2 := by simp
    have huniv : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
    rw [huniv]
    calc 3 * ({(k:ℤ), -(k:ℤ)} : Finset ℤ).card ≤ 3 * 2 := Nat.mul_le_mul_left 3 h2
      _ = 6 := by norm_num
  calc t.card = (t.image (fun m => (fam m, rho m))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ 6 := hcard2

/-- Tail bound for the `p`-series: a finite set of naturals above `N ≥ 1` contributes at
most `2/N` to `Σ 1/k²`.  Immediate from Mathlib's `sum_Ioo_inv_sq_le`. -/
theorem sum_inv_sq_tail_le (N : ℕ) (hN : 1 ≤ N) (v : Finset ℕ) (hv : ∀ k ∈ v, N ≤ k) :
    ∑ k ∈ v, (1:ℝ) / (k:ℝ)^2 ≤ 2 / (N:ℝ) := by
  rcases v.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty]
    positivity
  · have hsub : v ⊆ Finset.Ioo (N-1) (v.max' hne + 1) := by
      intro k hk
      simp only [Finset.mem_Ioo]
      have h1 : N ≤ k := hv k hk
      have h2 : k ≤ v.max' hne := Finset.le_max' v k hk
      omega
    calc ∑ k ∈ v, (1:ℝ) / (k:ℝ)^2
        ≤ ∑ k ∈ Finset.Ioo (N-1) (v.max' hne + 1), (1:ℝ) / (k:ℝ)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro i hi hni
          positivity
      _ ≤ 2 / (N:ℝ) := by
          have h := sum_Ioo_inv_sq_le (α := ℝ) (N-1) (v.max' hne + 1)
          have hcast : ((N-1 : ℕ) : ℝ) + 1 = (N:ℝ) := by
            rw [Nat.cast_sub hN, Nat.cast_one]; ring
          simpa [one_div, hcast] using h

/-- Peeling off `j - 2` factors: for `0 < N ≤ a` and `j ≥ 2`,
`1/a^j ≤ (1/N^{j-2}) · (1/a^2)`. -/
theorem one_div_pow_le (a N : ℝ) (hN : 0 < N) (hNa : N ≤ a) (j : ℕ) (hj : 2 ≤ j) :
    (1:ℝ)/a^j ≤ (1/N^(j-2)) * (1/a^2) := by
  have hpow : a^j = a^(j-2) * a^2 := by
    calc a^j = a^((j-2)+2) := by congr 1; omega
      _ = a^(j-2) * a^2 := by rw [pow_add]
  rw [hpow, ← one_div_mul_one_div]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact one_div_le_one_div_of_le (pow_pos hN _) (pow_le_pow_left₀ (le_of_lt hN) hNa _)

theorem rho_sum_pow_le (j : ℕ) (hj : 2 ≤ j) (X : ℝ) (hX : 1 ≤ X) (s : Finset (ℤ × ℤ × ℤ))
    (hs : ∀ m ∈ s, Submission.GM.nzCount m = 1)
    (hXm : ∀ m ∈ s, X < |(Work.GM.Trace.rho m : ℝ)|) :
    ∑ m ∈ s, (1 : ℝ) / |(Work.GM.Trace.rho m : ℝ)| ^ j ≤ 24 / X ^ (j - 1) := by
  set N : ℕ := ⌊X⌋₊ + 1 with hNdef
  have hNpos : 1 ≤ N := by omega
  have hNposR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hNX : X < (N:ℝ) := by
    rw [hNdef]
    push_cast
    exact Nat.lt_floor_add_one X
  have habs : ∀ m : ℤ × ℤ × ℤ, |(rho m : ℝ)| = ((rho m).natAbs : ℝ) := by
    intro m
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNm_nat : ∀ m ∈ s, N ≤ (rho m).natAbs := by
    intro m hm
    have h0 : (0:ℝ) ≤ X := le_trans (by norm_num) hX
    have hlt : ⌊X⌋₊ < (rho m).natAbs := by
      rw [Nat.floor_lt h0]
      rw [← habs m]
      exact hXm m hm
    omega
  have hNmR : ∀ m ∈ s, (N:ℝ) ≤ |(rho m:ℝ)| := by
    intro m hm
    rw [habs m]
    exact_mod_cast hNm_nat m hm
  have stepA : ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^j ≤
      (1/(N:ℝ)^(j-2)) * ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact one_div_pow_le _ _ hNposR (hNmR m hm) j hj
  have stepB : ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^2 ≤ 12/(N:ℝ) := by
    have hconv : ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^2
        = ∑ m ∈ s, (1:ℝ)/(((rho m).natAbs : ℝ))^2 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [habs m]
    rw [hconv]
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := s) (t := s.image (fun m => (rho m).natAbs))
      (g := fun m => (rho m).natAbs)
      (fun m hm => Finset.mem_image_of_mem _ hm)
      (f := fun m => (1:ℝ)/(((rho m).natAbs : ℝ))^2)]
    calc ∑ k ∈ s.image (fun m => (rho m).natAbs),
            ∑ m ∈ s.filter (fun m => (rho m).natAbs = k), (1:ℝ)/(((rho m).natAbs : ℝ))^2
        ≤ ∑ k ∈ s.image (fun m => (rho m).natAbs), 6 * (1/(k:ℝ)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hcong : ∑ m ∈ s.filter (fun m => (rho m).natAbs = k), (1:ℝ)/(((rho m).natAbs : ℝ))^2
              = ∑ m ∈ s.filter (fun m => (rho m).natAbs = k), (1:ℝ)/((k:ℝ))^2 :=
            Finset.sum_congr rfl (fun m hm => by rw [(Finset.mem_filter.mp hm).2])
          rw [hcong, Finset.sum_const, nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hc : (s.filter (fun m => (rho m).natAbs = k)).card ≤ 6 := fiber_card_le s hs k
          exact_mod_cast hc
      _ = 6 * ∑ k ∈ s.image (fun m => (rho m).natAbs), (1:ℝ)/(k:ℝ)^2 := by
          rw [Finset.mul_sum]
      _ ≤ 6 * (2/(N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sum_inv_sq_tail_le N hNpos
          intro k hk
          rw [Finset.mem_image] at hk
          obtain ⟨m, hm, rfl⟩ := hk
          exact hNm_nat m hm
      _ = 12/(N:ℝ) := by ring
  calc ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^j
      ≤ (1/(N:ℝ)^(j-2)) * ∑ m ∈ s, (1:ℝ)/|(rho m:ℝ)|^2 := stepA
    _ ≤ (1/(N:ℝ)^(j-2)) * (12/(N:ℝ)) := by
        apply mul_le_mul_of_nonneg_left stepB (by positivity)
    _ = 12/(N:ℝ)^(j-1) := by
        rw [div_mul_div_comm]
        have hp : (N:ℝ)^(j-1) = (N:ℝ)^(j-2) * (N:ℝ) := by
          have h : j - 1 = (j-2) + 1 := by omega
          rw [h, pow_succ]
        rw [one_mul, ← hp]
    _ ≤ 24/X^(j-1) := by
        have hXpos : (0:ℝ) < X := lt_of_lt_of_le (by norm_num) hX
        have hle : X^(j-1) ≤ (N:ℝ)^(j-1) :=
          pow_le_pow_left₀ (le_of_lt hXpos) (le_of_lt hNX) _
        exact div_le_div₀ (by norm_num) (by norm_num) (pow_pos hXpos _) hle

end Work.GM.Trace
