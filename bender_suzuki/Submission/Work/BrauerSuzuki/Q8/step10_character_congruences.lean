import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.characters
import Submission.Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.star_Irr
import Submission.Work.Induction.isChar_resFun
import Submission.Work.Induction.exists_nat_cfInner_resFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step (10) of Glauberman's `Q₈` case of Brauer–Suzuki: the congruences on `χ(1)`

Let `S` be a Sylow `2`-subgroup of a finite group `G`, `d` Dade's normal form of a generalized
quaternion group on `↥S` with `d.n = 2` (so `↥S ≅ Q₈`), and `x ∈ S` of order `4`.  Let `χ` be an
irreducible complex character of `G`, `ε = ±1`, and suppose that `χ` takes the constant value
`ε` on the six elements of order `4` of `S` (Glauberman (1974), step (9) together with the
conjugacy of all elements of order `4`, step (4b)).

Write `x_i = χ(1)` and `y_i = χ(x²) = χ(τ²)`.  Then (Glauberman, *On groups with a quaternion
Sylow 2-subgroup*, Illinois J. Math. **18** (1974), step (10), p. 64):

* `z_i = x_i - y_i` is divisible by `4`,
* `x_i` is odd,
* if `8 ∣ z_i` then `4 ∣ x_i - ε`.

The proof is the one in the source: let `ψ` be the irreducible character of `Q₈` of degree `2`,
with `ψ(1) = 2`, `ψ(τ²) = -2` and `ψ = 0` off `⟨τ²⟩` (`Quaternion.characters`).  The
multiplicities `m = (χ|_S, ψ)_S` and `k = (χ|_S, 1_S)_S` are natural numbers
(`exists_nat_cfInner_resFun`), and evaluating the two defining sums on the elements
`1, τ²` and the six elements of order `4` gives

`χ(1) - χ(x²) = 4m`   and   `χ(1) + χ(x²) + 6ε = 8k`,

from which all three assertions follow at once.

Everything is assembled here; the three preparatory facts about `Q₈` are the lemmas
`q8_order_structure`, `q8_theta_values` and `q8_central_involution_coe` above.
-/

noncomputable section

open Classical

namespace Work.BrauerSuzuki.Q8

/-! ## The group `Q₈` in Dade's normal form -/

/-- In a generalized quaternion group whose Dade parameter is `n = 2` — that is, in `Q₈` — the
group has order `8`, the element `τ` has order `4`, the central involution `τ ^ 2` has order `2`
and is the only involution, and every element different from `1` and `τ ^ 2` has order `4`. -/
theorem q8_order_structure {P : Type*} [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) :
    Nat.card P = 8 ∧ orderOf d.tau = 4 ∧ orderOf (d.tau ^ 2) = 2 ∧
      (∀ y : P, y ≠ 1 → y ≠ d.tau ^ 2 → orderOf y = 4) ∧
      (∀ y : P, orderOf y = 2 → y = d.tau ^ 2) := by
  obtain ⟨hcard, -, hord, huniq, hout⟩ := Quaternion.genQuaternionData_basic d
  have hexp : 2 ^ (d.n - 1) = 2 := by rw [h2]; norm_num
  have hcard8 : Nat.card P = 8 := by rw [hcard, h2]; norm_num
  have htau4 : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
  have hz2 : orderOf (d.tau ^ 2) = 2 := by simpa [hexp] using hord
  refine ⟨hcard8, htau4, hz2, ?_, fun y hy => by simpa [hexp] using huniq y hy⟩
  intro y hy1 hyz
  by_cases hy : y ∈ Subgroup.zpowers d.tau
  · have hyfin : IsOfFinOrder d.tau := isOfFinOrder_of_finite d.tau
    rw [hyfin.mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hy
    obtain ⟨k, hk, hky⟩ := hy
    rw [Finset.mem_range, htau4] at hk
    subst y
    interval_cases k
    · simp at hy1
    · simpa using htau4
    · simp at hyz
    · have h4 : d.tau ^ 4 = 1 := by rw [← htau4]; exact pow_orderOf_eq_one d.tau
      have h3 : d.tau ^ 3 = d.tau⁻¹ := by
        have hh : d.tau * d.tau ^ 3 = 1 := by rw [← pow_succ']; exact h4
        exact eq_inv_of_mul_eq_one_right hh
      rw [h3, orderOf_inv, htau4]
  · exact (hout y hy).1

/-- In `Q₈` (Dade parameter `n = 2`) there is an irreducible complex character `ψ` of degree `2`
with `ψ (τ ^ 2) = -2` and `ψ y = 0` for every element `y` of order `4`.  This is Dade's `θ`
restricted to the `Q₈` case: `ψ = Ind_{⟨τ⟩}^{P} λ`. -/
theorem q8_theta_values {P : Type*} [Group P] [Fintype P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (h2 : d.n = 2) :
    ∃ ψ : P → ℂ, ψ ∈ Work.CharCore.Irr P ∧ ψ 1 = 2 ∧ ψ (d.tau ^ 2) = -2 ∧
      (∀ y : P, orderOf y = 4 → ψ y = 0) := by
  obtain ⟨lam, th, -, hthIrr, -, -, -, -, -, hth1, hth_notMem, hth_tau, -, -, -, -⟩ :=
    Quaternion.characters d
  refine ⟨th, hthIrr, hth1, ?_, ?_⟩
  · have h := hth_tau 2
    rw [show (d.tau : P) ^ (2 : ℤ) = d.tau ^ 2 by simp] at h
    rw [h, (Quaternion.I_pow_add 2).2.1 (by norm_num) (by norm_num)]
  · intro y hy4
    by_cases hy : y ∈ Subgroup.zpowers d.tau
    · have htau4 : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
      rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four htau4 hy hy4 with h | h
      · rw [h]
        have h1 := hth_tau 1
        rw [show (d.tau : P) ^ (1 : ℤ) = d.tau by simp] at h1
        rw [h1, (Quaternion.I_pow_add 1).2.2 (by norm_num)]
      · rw [h]
        have h1 := hth_tau (-1)
        rw [show (d.tau : P) ^ (-1 : ℤ) = d.tau⁻¹ by simp] at h1
        rw [h1, (Quaternion.I_pow_add (-1)).2.2 (by norm_num)]
    · exact hth_notMem y hy

/-- In `Q₈`, the square of an element `x` of order `4` of a Sylow `2`-subgroup `S` is the central
involution `τ ^ 2` of `S`: both are the unique involution of `↥S`. -/
theorem q8_central_involution_coe {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) :
    ((d.tau ^ 2 : ↥S) : G) = x ^ 2 := by
  obtain ⟨-, -, hz2, -, huniq⟩ := q8_order_structure d h2
  have hxv4 : orderOf (⟨x, hxS⟩ : ↥S) = 4 := by
    rw [← Subgroup.orderOf_coe (⟨x, hxS⟩ : ↥S)]
    exact hx4
  have hsq2 : orderOf ((⟨x, hxS⟩ : ↥S) ^ 2) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← hxv4]
      exact pow_orderOf_eq_one _
    · intro h
      have hdvd : orderOf (⟨x, hxS⟩ : ↥S) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [hxv4] at hdvd
      norm_num at hdvd
  have heq : (⟨x, hxS⟩ : ↥S) ^ 2 = d.tau ^ 2 := huniq _ hsq2
  rw [← heq, Subgroup.coe_pow]

/-! ## The congruences -/

theorem step10_character_congruences {G : Type*} [Group G] [Fintype G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hval : ∀ y : G, y ∈ (S : Subgroup G) → orderOf y = 4 → χ y = (ε : ℂ)) :
    ∃ Y : ℤ, χ (x ^ 2) = (Y : ℂ) ∧
      (4 : ℤ) ∣ ((Work.CharCore.irrDeg χ : ℤ) - Y) ∧ Odd (Work.CharCore.irrDeg χ) ∧
      ((8 : ℤ) ∣ ((Work.CharCore.irrDeg χ : ℤ) - Y) →
        (4 : ℤ) ∣ ((Work.CharCore.irrDeg χ : ℤ) - ε)) := by
  classical
  obtain ⟨hcardP, htau4, hzord, horder4, huniq2⟩ := q8_order_structure d h2
  obtain ⟨ψ, hψIrr, hψ1, hψz, hψ4⟩ := q8_theta_values d h2
  -- the central involution of `↥S`
  set z : ↥S := d.tau ^ 2 with hzdef
  have hzx : (z : G) = x ^ 2 := by
    rw [hzdef]
    exact q8_central_involution_coe S d h2 hxS hx4
  have hz_ne_one : z ≠ 1 := by
    intro h
    rw [h] at hzord
    rw [orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzz : z⁻¹ = z := by
    have h : z ^ 2 = 1 := by simpa [hzord] using pow_orderOf_eq_one z
    rw [pow_two] at h
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hcard8 : Fintype.card ↥S = 8 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardP
  -- `f` is the restriction of `χ` to `↥S`
  let f : ↥S → ℂ := Work.Induction.resFun (S : Subgroup G) χ
  have hfy : ∀ y : ↥S, f y = χ (y : G) := fun y => rfl
  -- the multiplicities `m` of `ψ` and `k` of the principal character in `χ|_S`
  obtain ⟨k, hk⟩ := Work.Induction.exists_nat_cfInner_resFun (G := G) (H := (S : Subgroup G)) hχ
    (θ := fun _ : ↥S => (1 : ℂ)) (Work.CharCore.principalChar_mem_Irr (G := ↥S))
  obtain ⟨m, hm⟩ := Work.Induction.exists_nat_cfInner_resFun (G := G) (H := (S : Subgroup G)) hχ
    (θ := ψ) hψIrr
  have hk' : Work.CharCore.cfInner f (fun _ : ↥S => (1 : ℂ)) = (k : ℂ) := hk
  have hm' : Work.CharCore.cfInner f ψ = (m : ℂ) := hm
  -- the sum against the principal character
  have hsumTriv : (∑ y : ↥S, f y) = (8 : ℂ) * (k : ℂ) := by
    have h := hk'
    rw [Work.CharCore.cfInner_apply] at h
    simp only [mul_one, map_one] at h
    rw [hcard8] at h
    have hmul := congrArg (fun t : ℂ => ((8 : ℕ) : ℂ) * t) h
    rw [← mul_assoc, mul_inv_cancel₀ (by norm_num : ((8 : ℕ) : ℂ) ≠ 0), one_mul] at hmul
    simpa using hmul
  -- the sum against `ψ`
  have hsumPsi : (∑ y : ↥S, f y * starRingEnd ℂ (ψ y)) = (8 : ℂ) * (m : ℂ) := by
    have h := hm'
    rw [Work.CharCore.cfInner_apply] at h
    rw [hcard8] at h
    have hmul := congrArg (fun t : ℂ => ((8 : ℕ) : ℂ) * t) h
    rw [← mul_assoc, mul_inv_cancel₀ (by norm_num : ((8 : ℕ) : ℂ) ≠ 0), one_mul] at hmul
    simpa using hmul
  have hsumPsi' : (∑ y : ↥S, f y * ψ (y⁻¹)) = (8 : ℂ) * (m : ℂ) := by
    rw [← hsumPsi]
    exact Finset.sum_congr rfl (fun y _ => by rw [Work.CharCore.star_Irr ψ hψIrr y])
  -- splitting a sum over `↥S` into the part off `{1, z}` and the two terms `1`, `z`
  have hsplitψ : (∑ y : ↥S, f y * ψ (y⁻¹))
      = (∑ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f y * ψ (y⁻¹))
        + (f 1 * ψ ((1 : ↥S)⁻¹) + f z * ψ (z⁻¹)) := by
    have hs : (∑ x ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f x * ψ (x⁻¹))
        + (∑ x ∈ ({1, z} : Finset ↥S), f x * ψ (x⁻¹)) = ∑ x : ↥S, f x * ψ (x⁻¹) :=
      Finset.sum_sdiff (s₁ := ({1, z} : Finset ↥S))
        (s₂ := (Finset.univ : Finset ↥S)) (Finset.subset_univ _)
    rw [Finset.sum_pair (Ne.symm hz_ne_one)] at hs
    exact hs.symm
  have hsplitTriv : (∑ y : ↥S, f y)
      = (∑ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f y) + (f 1 + f z) := by
    have hs : (∑ x ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f x)
        + (∑ x ∈ ({1, z} : Finset ↥S), f x) = ∑ x : ↥S, f x :=
      Finset.sum_sdiff (s₁ := ({1, z} : Finset ↥S))
        (s₂ := (Finset.univ : Finset ↥S)) (Finset.subset_univ _)
    rw [Finset.sum_pair (Ne.symm hz_ne_one)] at hs
    exact hs.symm
  -- the six elements of order `4`
  have hcard6 : (Finset.univ \ ({1, z} : Finset ↥S)).card = 6 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard8,
      Finset.card_pair (Ne.symm hz_ne_one)]
  have hoff : ∀ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), y ≠ 1 ∧ y ≠ z := by
    intro y hy
    have hy2 : y ∉ ({1, z} : Finset ↥S) := (Finset.mem_sdiff.mp hy).2
    exact ⟨fun h => hy2 (by simp [h]), fun h => hy2 (by simp [h])⟩
  have hrestψ : (∑ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f y * ψ (y⁻¹)) = 0 := by
    refine Finset.sum_eq_zero (fun y hy => ?_)
    obtain ⟨hy1, hyz⟩ := hoff y hy
    have hy4 : orderOf y = 4 := horder4 y hy1 hyz
    rw [hψ4 (y⁻¹) (by rw [orderOf_inv]; exact hy4), mul_zero]
  have hrestTriv : (∑ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f y) = (6 : ℂ) * (ε : ℂ) := by
    have hconst : ∀ y ∈ (Finset.univ \ ({1, z} : Finset ↥S)), f y = (ε : ℂ) := by
      intro y hy
      obtain ⟨hy1, hyz⟩ := hoff y hy
      have hy4 : orderOf y = 4 := horder4 y hy1 hyz
      rw [hfy y]
      exact hval (y : G) y.2 (by rw [Subgroup.orderOf_coe]; exact hy4)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard6]
    simp
  have hpairψ : f 1 * ψ ((1 : ↥S)⁻¹) + f z * ψ (z⁻¹) = 2 * χ 1 - 2 * χ (x ^ 2) := by
    rw [hfy 1, hfy z, Subgroup.coe_one, inv_one, hψ1, hzz, hψz, hzx]
    ring
  have hpairTriv : f 1 + f z = χ 1 + χ (x ^ 2) := by
    rw [hfy 1, hfy z, Subgroup.coe_one, hzx]
  -- the two key relations
  have hA : (8 : ℂ) * (k : ℂ) = χ 1 + χ (x ^ 2) + 6 * (ε : ℂ) := by
    rw [← hsumTriv, hsplitTriv, hrestTriv, hpairTriv]
    ring
  have hB : (8 : ℂ) * (m : ℂ) = 2 * χ 1 - 2 * χ (x ^ 2) := by
    rw [← hsumPsi', hsplitψ, hrestψ, hpairψ]
    ring
  -- `χ 1` is the degree
  have hchi1 : χ 1 = ((Work.CharCore.irrDeg χ : ℤ) : ℂ) := by
    rw [Work.CharCore.irrDeg_spec hχ]
    simp
  -- `χ (x ^ 2)` is the integer `χ 1 - 4 m`
  have hx2 : χ (x ^ 2) = ((Work.CharCore.irrDeg χ : ℤ) : ℂ) - 4 * (m : ℂ) := by
    have h3 : (2 : ℂ) * χ (x ^ 2)
        = 2 * (((Work.CharCore.irrDeg χ : ℤ) : ℂ) - 4 * (m : ℂ)) := by
      rw [hchi1] at hB
      have hB' : (2 : ℂ) * χ (x ^ 2)
          = 2 * ((Work.CharCore.irrDeg χ : ℤ) : ℂ) - 8 * (m : ℂ) := by
        rw [hB]; ring
      rw [hB']; ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3
  have hx2' : χ (x ^ 2) = (((Work.CharCore.irrDeg χ : ℤ) - 4 * (m : ℤ) : ℤ) : ℂ) := by
    rw [hx2]
    push_cast
    ring
  -- the integral relation between the degree, the multiplicities and `ε`
  have hZeq : (8 : ℤ) * (k : ℤ)
      = 2 * (Work.CharCore.irrDeg χ : ℤ) - 4 * (m : ℤ) + 6 * ε := by
    have hcast : (8 : ℂ) * (k : ℂ)
        = 2 * ((Work.CharCore.irrDeg χ : ℤ) : ℂ) - 4 * (m : ℂ) + 6 * (ε : ℂ) := by
      rw [hA, hx2, hchi1]
      ring
    exact_mod_cast hcast
  have hD : (Work.CharCore.irrDeg χ : ℤ) = 4 * (k : ℤ) + 2 * (m : ℤ) - 3 * ε := by
    linarith
  refine ⟨(Work.CharCore.irrDeg χ : ℤ) - 4 * (m : ℤ), hx2', ?_, ?_, ?_⟩
  · exact ⟨(m : ℤ), by ring⟩
  · have hoddZ : Odd (Work.CharCore.irrDeg χ : ℤ) := by
      rw [hD]
      rcases hε with h | h
      · rw [h]; exact ⟨2 * (k : ℤ) + (m : ℤ) - 2, by ring⟩
      · rw [h]; exact ⟨2 * (k : ℤ) + (m : ℤ) + 1, by ring⟩
    exact (Int.odd_coe_nat _).mp hoddZ
  · intro h8
    obtain ⟨t, ht⟩ := h8
    have hmt : (m : ℤ) = 2 * t := by linarith
    exact ⟨(k : ℤ) + t - ε, by rw [hD, hmt]; ring⟩

end Work.BrauerSuzuki.Q8
