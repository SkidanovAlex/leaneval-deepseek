import Mathlib
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.bpD_pair_mul_le
import Submission.Work.BW.prod_one_add_le_inv_one_sub_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The odd integers in `[-(2m), 2m]` split into the positive odds `2i+1` and their negatives,
for `i < m`. -/
private lemma oddIdx_two_mul (m : ℕ) :
    oddIdx (2*m) = ((Finset.range m).image (fun i : ℕ => (2*(i:ℤ)+1)))
      ∪ ((Finset.range m).image (fun i : ℕ => -(2*(i:ℤ)+1))) := by
  ext k
  rw [mem_oddIdx_iff, Finset.mem_union, Finset.mem_image, Finset.mem_image]
  simp only [Finset.mem_range]
  push_cast
  constructor
  · rintro ⟨⟨j, rfl⟩, h1, h2⟩
    rcases le_or_gt 0 j with hj | hj
    · left
      refine ⟨j.toNat, ?_, ?_⟩
      · have : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
        omega
      · have : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
        omega
    · right
      refine ⟨(-j-1).toNat, ?_, ?_⟩
      · have : ((-j-1).toNat : ℤ) = -j-1 := Int.toNat_of_nonneg (by omega)
        omega
      · have : ((-j-1).toNat : ℤ) = -j-1 := Int.toNat_of_nonneg (by omega)
        omega
  · rintro (⟨x, hx, hk⟩ | ⟨x, hx, hk⟩)
    · refine ⟨⟨(x:ℤ), by omega⟩, ?_, ?_⟩ <;> omega
    · refine ⟨⟨-(x:ℤ)-1, by omega⟩, ?_, ?_⟩ <;> omega

/-- Reindexing the product over `oddIdx (2m)` into pair products over `k = ±(2i+1)`, `i < m`. -/
private lemma oddIdx_prod_two_mul (m : ℕ) (g : ℤ → ℝ) :
    ∏ k ∈ oddIdx (2*m), g k
      = ∏ i ∈ Finset.range m, (g (2*(i:ℤ)+1) * g (-(2*(i:ℤ)+1))) := by
  rw [oddIdx_two_mul m]
  have hdisj : Disjoint ((Finset.range m).image (fun i : ℕ => (2*(i:ℤ)+1)))
      ((Finset.range m).image (fun i : ℕ => -(2*(i:ℤ)+1))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨x, -, hx⟩ := ha
    obtain ⟨y, -, hy⟩ := hb
    omega
  rw [Finset.prod_union hdisj]
  have hinj1 : Set.InjOn (fun i : ℕ => (2*(i:ℤ)+1)) ↑(Finset.range m) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have hinj2 : Set.InjOn (fun i : ℕ => -(2*(i:ℤ)+1)) ↑(Finset.range m) := by
    intro a _ b _ hab
    simp only at hab
    omega
  rw [Finset.prod_image hinj1, Finset.prod_image hinj2]
  rw [Finset.prod_mul_distrib]


/-- Sum of the first `m` odd numbers: `∑_{i<m}(2i+1) = m²`. -/
private lemma sum_range_two_mul_add_one (m : ℕ) :
    ∑ i ∈ Finset.range m, (2*(i:ℝ)+1) = (m:ℝ)^2 := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Denominator product bound, BW (25) step (i): for `0 < η < 1/2`, `X ≥ 2` even, `X + η ≤ R` and odd
`l` with `|l| ≤ X`: `∏_{k ∈ oddIdx X} (|R² − k·l| + |k|·η) ≤ R^{2X}/(1 − η/2)`.
Route: pair `k` with `−k` (using `R² ≥ X² ≥ |k·l|`, so `|R² − k·l| = R² − k·l`), the pair product
equals `(R²+kη)² − (kl)² ≤ R⁴(1 + 2kη/R²)` (as `η < |l|`), there are `X/2 = m` pairs, and
`∏(1+a_j) ≤ 1/(1−Σa_j)` with `Σa_j = 2η·Σ_{i<m}(2i+1)/R² = ηX²/(2R²) ≤ η/2` since `X ≤ R`. -/
theorem bpOdd_den_prod_le_fix {R η : ℝ} (hη : 0 < η) (hη' : η < 1/2) {X : ℕ} (hX : 2 ≤ X)
    (hXe : Even X) (hXR : (X:ℝ) + η ≤ R) {l : ℤ} (hlo : Odd l) (hl : |l| ≤ (X:ℤ)) :
    ∏ k ∈ oddIdx X, bpD R η l k ≤ R^(2*X) / (1 - η/2) := by
  obtain ⟨m, hm⟩ := hXe
  subst hm
  rw [show m + m = 2*m from by omega, show 2*(2*m) = 4*m from by omega]
  have hcastZ : ((m+m : ℕ) : ℤ) = 2*(m:ℤ) := by push_cast; ring
  have hl2 : |l| ≤ 2*(m:ℤ) := by rw [hcastZ] at hl; exact hl
  have hcastR : ((m+m : ℕ) : ℝ) = 2*(m:ℝ) := by push_cast; ring
  have hXR2 : 2*(m:ℝ) + η ≤ R := by rw [hcastR] at hXR; exact hXR
  have hlR : |(l:ℝ)| ≤ 2*(m:ℝ) := by rw [← Int.cast_abs]; exact_mod_cast hl2
  have hR : 0 < R := by
    have : (0:ℝ) ≤ 2*(m:ℝ) := by positivity
    linarith
  have h2mR : 2*(m:ℝ) ≤ R := by linarith
  have hXsq : (2*(m:ℝ))^2 ≤ R^2 := pow_le_pow_left₀ (by positivity) h2mR 2
  have h4m2 : 4*(m:ℝ)^2 ≤ R^2 := by nlinarith [hXsq]
  have hsum1 : ∑ i ∈ Finset.range m, (2*(i:ℝ)+1) = (m:ℝ)^2 := sum_range_two_mul_add_one m
  have hsum2 : ∑ i ∈ Finset.range m, 2*(2*(i:ℝ)+1)*η/R^2 = 2*η*(m:ℝ)^2/R^2 := by
    rw [show ∑ i ∈ Finset.range m, 2*(2*(i:ℝ)+1)*η/R^2
        = ∑ i ∈ Finset.range m, (2*η/R^2)*(2*(i:ℝ)+1) from by
          apply Finset.sum_congr rfl; intro i _; ring]
    rw [← Finset.mul_sum, hsum1]
    ring
  have hsum_le : ∑ i ∈ Finset.range m, 2*(2*(i:ℝ)+1)*η/R^2 ≤ η/2 := by
    rw [hsum2, div_le_iff₀ (by positivity : (0:ℝ) < R^2)]
    nlinarith [h4m2, hη]
  have hpair : ∀ i ∈ Finset.range m,
      bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1))
        ≤ R^4 * (1 + 2*(2*(i:ℝ)+1)*η/R^2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hki : |(((2*(i:ℤ)+1 : ℤ)) : ℝ)| = 2*(i:ℝ)+1 := by
      have hcast : (((2*(i:ℤ)+1 : ℤ)) : ℝ) = 2*(i:ℝ)+1 := by push_cast; ring
      rw [hcast, abs_of_nonneg (by positivity)]
    have hkl : |(((2*(i:ℤ)+1 : ℤ)) : ℝ)| * |(l:ℝ)| ≤ R^2 := by
      rw [hki]
      have h2 : 2*(i:ℝ)+1 ≤ 2*(m:ℝ) := by
        have hlt : (i:ℝ) + 1 ≤ (m:ℝ) := by
          have h := Nat.succ_le_of_lt hi
          have hc : ((i+1 : ℕ) : ℝ) ≤ ((m:ℕ):ℝ) := by exact_mod_cast h
          simpa using hc
        linarith
      have h3 : (0:ℝ) ≤ |(l:ℝ)| := abs_nonneg _
      calc (2*(i:ℝ)+1) * |(l:ℝ)| ≤ (2*(m:ℝ)) * (2*(m:ℝ)) :=
              mul_le_mul h2 hlR h3 (by positivity)
        _ = (2*(m:ℝ))^2 := by ring
        _ ≤ R^2 := hXsq
    have hlη : η ≤ |(l:ℝ)| := by
      have h1 : (1:ℝ) ≤ |(l:ℝ)| := by
        rw [← Int.cast_abs]
        have : (1:ℤ) ≤ |l| := by
          have h0 : (0:ℤ) < |l| := abs_pos.mpr (by rintro rfl; simp at hlo)
          omega
        exact_mod_cast this
      linarith
    have h := bpD_pair_mul_le (R:=R) (η:=η) (l:=l) (k:=2*(i:ℤ)+1) (le_of_lt hη) hR hkl hlη
    rw [hki] at h
    have heq : R^4 + 2 * R^2 * (2*(i:ℝ)+1) * η = R^4 * (1 + 2*(2*(i:ℝ)+1)*η/R^2) := by
      field_simp
    exact le_trans h (le_of_eq heq)
  have ha_nonneg : ∀ i ∈ Finset.range m, 0 ≤ 2*(2*(i:ℝ)+1)*η/R^2 := by
    intro i _
    have : (0:ℝ) < 2*(i:ℝ)+1 := by positivity
    positivity
  have hprod1 : ∏ i ∈ Finset.range m, (1 + 2*(2*(i:ℝ)+1)*η/R^2)
      ≤ 1/(1 - ∑ i ∈ Finset.range m, 2*(2*(i:ℝ)+1)*η/R^2) :=
    prod_one_add_le_inv_one_sub_sum _ _ ha_nonneg (by linarith [hsum_le, hη'])
  have hbpd_nn : ∀ k : ℤ, 0 ≤ bpD R η l k := by
    intro k
    have h1 : (0:ℝ) ≤ |R^2 - (k:ℝ)*(l:ℝ)| := abs_nonneg _
    have h2 : (0:ℝ) ≤ |(k:ℝ)| * η := mul_nonneg (abs_nonneg _) (le_of_lt hη)
    unfold bpD
    linarith
  have hpair_nn : ∀ i ∈ Finset.range m,
      0 ≤ bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1)) :=
    fun i _ => mul_nonneg (hbpd_nn _) (hbpd_nn _)
  calc ∏ k ∈ oddIdx (2*m), bpD R η l k
      = ∏ i ∈ Finset.range m, (bpD R η l (2*(i:ℤ)+1) * bpD R η l (-(2*(i:ℤ)+1))) :=
        oddIdx_prod_two_mul m (fun k => bpD R η l k)
    _ ≤ ∏ i ∈ Finset.range m, (R^4 * (1 + 2*(2*(i:ℝ)+1)*η/R^2)) :=
          Finset.prod_le_prod₀ hpair_nn hpair
    _ = (R^4)^m * ∏ i ∈ Finset.range m, (1 + 2*(2*(i:ℝ)+1)*η/R^2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ (R^4)^m * (1/(1 - ∑ i ∈ Finset.range m, 2*(2*(i:ℝ)+1)*η/R^2)) :=
          mul_le_mul_of_nonneg_left hprod1 (pow_nonneg (pow_nonneg (le_of_lt hR) 4) m)
    _ ≤ (R^4)^m * (1/(1 - η/2)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (pow_nonneg (le_of_lt hR) 4) m)
          exact one_div_le_one_div_of_le (by linarith [hη']) (by linarith [hsum_le])
    _ = R^(4*m)/(1-η/2) := by rw [← pow_mul, mul_one_div]

end Work.BW
