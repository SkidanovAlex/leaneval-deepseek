import Mathlib
import Submission.Commons.Combinatorics.Transference.lfc_weight_moment_inj

namespace Commons.Combinatorics.Transference

open _root_.Finset
open scoped BigOperators
open Commons.NumberTheory.Sieve

/-!
# The weighted cube moment with shifts, with the tight linear-forms parameters

This file proves `lfc_weight_moment_shift3`, the sharp version of
`lfc_weight_moment_inj` in which the linear forms condition is applied with exactly as many
forms as there are (`k · 2^{k-1}`) and exactly as many variables as there are (`k+2`), and with
the size parameter `K` itself (rather than `2K²+2`) thanks to the diameter hypothesis
`|c m - c m'| ≤ K`.

The only new ingredients with respect to `lfc_weight_moment_inj` are

* the coefficient bound `IsSmallRat K (gphiC p c i j)` coming from the diameter hypothesis, and
* the sharp cardinality bounds for the index types.
-/

/-- An injective `k ≥ 2`-tuple of integers whose pairwise differences are bounded by `K`
forces `1 ≤ K`. -/
lemma one_le_K_of_diam {k : ℕ} (hk : 2 ≤ k) {K : ℕ} (c : Fin k → ℤ)
    (hdiam : ∀ m m', |c m - c m'| ≤ K) (hcinj : Function.Injective c) : 1 ≤ K := by
  have hne : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hc : c ⟨0, by omega⟩ ≠ c ⟨1, by omega⟩ := fun h => hne (hcinj h)
  have hd := hdiam ⟨0, by omega⟩ ⟨1, by omega⟩
  have hpos : 0 < |c ⟨0, by omega⟩ - c ⟨1, by omega⟩| := abs_pos.mpr (sub_ne_zero.mpr hc)
  have : (1 : ℤ) ≤ (K : ℤ) := by omega
  exact_mod_cast this

/-- Coefficient bound `K` for the `φ`-coefficients, using the diameter hypothesis. -/
lemma isSmallRat_gphiC_K {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (hK : 1 ≤ K)
    (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K) (i j : Fin (k-1)) :
    IsSmallRat K (gphiC p c i j) := by
  unfold gphiC
  split_ifs with hp
  · exact isSmallRat_one hK
  · apply isSmallRat_rat_div_int
    · intro h
      have h' : cg c j = 0 := Int.cast_injective h
      exact hp (by rw [h']; simp)
    · have hd := hdiam ⟨j.val + 1, by have := j.isLt; omega⟩
        ⟨i.val + 1, by have := i.isLt; omega⟩
      rw [Int.abs_eq_natAbs] at hd
      have hnum : (cg c j - cg c i).natAbs ≤ K := by
        unfold cg
        exact_mod_cast hd
      exact hnum
    · exact cg_natAbs_le c hcb j

lemma isSmallRat_phiCoeffG_K {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (hK : 1 ≤ K)
    (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Ix (k-1)) :
    IsSmallRat K (phiCoeffG p c i ω j) := by
  rcases j with j | kk
  · rw [phiCoeffG_inl]; split_ifs
    · exact isSmallRat_gphiC_K hK c hcb hdiam i j
    · exact isSmallRat_zero hK
  · fin_cases kk
    · change IsSmallRat K (phiCoeffG p c i ω (Sum.inr 0))
      rw [phiCoeffG_inr0]; exact isSmallRat_one hK
    · change IsSmallRat K (phiCoeffG p c i ω (Sum.inr 1))
      rw [phiCoeffG_inr1, gC]
      exact isSmallRat_neg (isSmallRat_intCast hK _ (cg_natAbs_le c hcb i))
    · change IsSmallRat K (phiCoeffG p c i ω (Sum.inr 2))
      rw [phiCoeffG_inr2]; exact isSmallRat_zero hK

lemma isSmallRat_phiCoeffG'_K {p : ℕ} [Fact p.Prime] {k : ℕ} {K : ℕ} (hK : 1 ≤ K)
    (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (i : Fin (k-1)) (ω : Fin (k-1) → Bool) (j : Ix (k-1)) :
    IsSmallRat K (phiCoeffG' p c i ω j) := by
  rcases j with j | kk
  · rw [phiCoeffG'_inl]; split_ifs
    · exact isSmallRat_gphiC_K hK c hcb hdiam i j
    · exact isSmallRat_zero hK
  · fin_cases kk
    · change IsSmallRat K (phiCoeffG' p c i ω (Sum.inr 0))
      rw [phiCoeffG'_inr0]; exact isSmallRat_one hK
    · change IsSmallRat K (phiCoeffG' p c i ω (Sum.inr 1))
      rw [phiCoeffG'_inr1]; exact isSmallRat_zero hK
    · change IsSmallRat K (phiCoeffG' p c i ω (Sum.inr 2))
      rw [phiCoeffG'_inr2, gC]
      exact isSmallRat_neg (isSmallRat_intCast hK _ (cg_natAbs_le c hcb i))

/-! ## The applications of the linear forms condition with tight parameters -/

lemma lfc_gvn_S0K {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    {K : ℕ} (hK : 1 ≤ K)
    (hLFC : LinFormsCond p ν (k * 2 ^ (k-1)) (k+2) K ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p, ∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω)) - 1| ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1)) := by
    rw [card_cubeIx]; exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (CubeIx (k-1)) ≤ k * 2 ^ (k-1) := by
    rw [card_cubeIx]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard2 (Lcube (k-1))
    (fun i j => isSmallRat_cubeCoeff' hK i j)
    (fun i => ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩)
    (fun i i' hii => notProp_cube hii)
    (fun _ => 0)
  simpa only [Lcube, cubeForm, Pi.zero_apply, add_zero] using h

lemma lfc_gvn_S1K {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    {K : ℕ} (hK : 1 ≤ K) (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (hc_inj : Function.Injective c) (hcne : ∀ i : Fin (k-1), cg c i ≠ 0)
    (hLFC : LinFormsCond p ν (k * 2 ^ (k-1)) (k+2) K ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p,
        (∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω))
        * ∏ s : PhiIx (k-1), ν (phiFormG p c s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx (k-1) ⊕ PhiIx (k-1)) ≤ k * 2 ^ (k-1) := by
    rw [Fintype.card_sum, card_cubeIx, card_phiIx]
    have h1 : (k - 1) * 2 ^ ((k - 1) - 1) ≤ (k - 1) * 2 ^ (k - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 2 ^ (k - 1) + (k - 1) * 2 ^ (k - 1) = k * 2 ^ (k - 1) := by
      have hm : 1 + (k - 1) = k := by omega
      have hmid : 2 ^ (k - 1) + (k - 1) * 2 ^ (k - 1)
          = (1 + (k - 1)) * 2 ^ (k - 1) := by ring
      rw [hmid, hm]
    exact le_trans (Nat.add_le_add_left h1 _) (le_of_eq h2)
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1) ⊕ PhiIx (k-1)) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := k-1)
    omega
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard
    (Sum.elim (Lcube (k-1)) (LphiG p c))
    (fun i j => by
      rcases i with i | i
      · exact isSmallRat_cubeCoeff' hK i j
      · exact isSmallRat_phiCoeffG_K hK c hcb hdiam i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeffG_inr0_ne p c i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i <;> rcases i' with i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG p c i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 (k-1) i) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 1) (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (cubeCoeff_inr1 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_phiG hc_inj (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, LphiG, Sum.elim_inl, Sum.elim_inr, cubeForm, phiFormG, Pi.zero_apply,
    add_zero] using h

lemma lfc_gvn_S2K {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    {K : ℕ} (hK : 1 ≤ K) (c : Fin k → ℤ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (hc_inj : Function.Injective c) (hcne : ∀ i : Fin (k-1), cg c i ≠ 0)
    (hLFC : LinFormsCond p ν (k * 2 ^ (k-1)) (k+2) K ε) :
    |((Fintype.card (Ix (k-1) → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix (k-1) → ZMod p,
        (∏ ω : CubeIx (k-1), ν (cubeForm (k-1) v ω))
        * (∏ s : PhiIx (k-1), ν (phiFormG p c s.1 s.2.1 v))
        * ∏ s : PhiIx (k-1), ν (phiFormG' p c s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx (k-1) ⊕ (PhiIx (k-1) ⊕ PhiIx (k-1)))
      ≤ k * 2 ^ (k-1) := by
    have hd1 : 1 ≤ k - 1 := by omega
    have hpow : 2 ^ (k - 1) = 2 * 2 ^ ((k - 1) - 1) := pow_two_eq (k - 1) hd1
    have hm : 1 + (k - 1) = k := by omega
    have hkey : 2 ^ (k - 1)
        + ((k - 1) * 2 ^ ((k - 1) - 1) + (k - 1) * 2 ^ ((k - 1) - 1))
        ≤ k * 2 ^ (k - 1) := by
      rw [hpow]
      have he : 2 * 2 ^ ((k - 1) - 1)
          + ((k - 1) * 2 ^ ((k - 1) - 1) + (k - 1) * 2 ^ ((k - 1) - 1))
          = 2 * 2 ^ ((k - 1) - 1) * (1 + (k - 1)) := by ring
      rw [he, hm]
      exact le_of_eq (mul_comm _ _)
    rw [Fintype.card_sum, Fintype.card_sum, card_cubeIx, card_phiIx]
    exact hkey
  have hcard1 : 1 ≤ Fintype.card (CubeIx (k-1) ⊕ (PhiIx (k-1) ⊕ PhiIx (k-1))) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := k-1)
    omega
  have h := lfc_apply_equiv (V := Ix (k-1)) (e := finSumFinEquiv) hLFC (t := (k-1) + 3)
    (by omega) (by omega) hcard1 hcard
    (Sum.elim (Lcube (k-1)) (Sum.elim (LphiG p c) (LphiG' p c)))
    (fun i j => by
      rcases i with i | i | i
      · exact isSmallRat_cubeCoeff' hK i j
      · exact isSmallRat_phiCoeffG_K hK c hcb hdiam i.1 i.2.1 j
      · exact isSmallRat_phiCoeffG'_K hK c hcb hdiam i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeffG_inr0_ne p c i.1 i.2.1⟩
      · exact ⟨Sum.inr 0, phiCoeffG'_inr0_ne p c i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i | i <;> rcases i' with i' | i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG p c i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 (k-1) i) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · exact notProp_of_zero_coord (L := cubeCoeff (k-1) i) (L' := phiCoeffG' p c i'.1 i'.2.1)
          (k := Sum.inr 2) (cubeCoeff_inr2 (k-1) i) (phiCoeffG'_inr2_ne c hcne i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 1) (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (cubeCoeff_inr1 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_phiG hc_inj (fun hc => hii (by rw [hc]))
      · refine notProp_of_zero_coord' (L := phiCoeffG p c i.1 i.2.1)
          (L' := phiCoeffG' p c i'.1 i'.2.1) (k := Sum.inr 1)
          (phiCoeffG_inr1_ne c hcne i.1 i.2.1) (phiCoeffG'_inr1 p c i'.1 i'.2.1) ?_
        exact phiCoeffG'_inr0 p c i'.1 i'.2.1
      · refine notProp_of_zero_coord' (L := phiCoeffG' p c i.1 i.2.1) (L' := cubeCoeff (k-1) i')
          (k := Sum.inr 2) (phiCoeffG'_inr2_ne c hcne i.1 i.2.1) (cubeCoeff_inr2 (k-1) i') ?_
        exact cubeCoeff_inr0 (k-1) i'
      · exact notProp_of_zero_coord (L := phiCoeffG' p c i.1 i.2.1)
          (L' := phiCoeffG p c i'.1 i'.2.1) (k := Sum.inr 1)
          (phiCoeffG'_inr1 p c i.1 i.2.1) (phiCoeffG_inr1_ne c hcne i'.1 i'.2.1)
      · exact notProp_phiG' hc_inj (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, LphiG, LphiG', Sum.elim_inl, Sum.elim_inr, cubeForm, phiFormG, phiFormG',
    Pi.zero_apply, add_zero, mul_assoc] using h

/-! ## The weighted cube moment with tight parameters -/

set_option maxHeartbeats 4000000 in
theorem lfc_weight_moment_shift3 {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) {ν : ZMod p → ℝ}
    (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (c : Fin k → ℤ) (K : ℕ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (hinj : Function.Injective (fun m : Fin k => ((c m : ℤ) : ZMod p)))
    (hcne : ∀ m : Fin k, 1 ≤ m.val → c m ≠ 0)
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (k * 2 ^ (k-1)) (k+2) K ε) :
    (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin (k-1) → Bool,
            ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j))
        * (((((p : ℝ)⁻¹) * (∑ s : ZMod p,
              ∏ i : Fin (k-1),
                ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
                  ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                    - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
                      * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                          * (((c ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹))))
            - 1) ^ 2))
      ≤ 4 * ε * (p : ℝ) ^ (k - 1 + 1) := by
  set P : ℝ := (p : ℝ) with hP
  have hPpos : 0 < P := by
    rw [hP]; exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpne : (p : ℝ) ≠ 0 := by
    have h := (Fact.out : Nat.Prime p).pos
    exact_mod_cast (ne_of_gt h)
  have hPne : P ≠ 0 := by rw [hP]; exact hpne
  have hinjZ : Function.Injective c := by
    intro a b hab
    exact hinj (congrArg (fun z : ℤ => (z : ZMod p)) hab)
  have hcne' : ∀ i : Fin (k-1), cg c i ≠ 0 := by
    intro i
    unfold cg
    exact hcne ⟨i.val + 1, by have := i.isLt; omega⟩ (by
      show (1:ℕ) ≤ i.val + 1
      omega)
  have hK : 1 ≤ K := one_le_K_of_diam (by omega) c hdiam hinjZ
  have hS0 := lfc_gvn_S0K (p := p) (k := k) (by omega) (K := K) hK hLFC
  have hS1 := lfc_gvn_S1K (p := p) (k := k) (by omega) (K := K) hK c hcb hdiam hinjZ hcne' hLFC
  have hS2 := lfc_gvn_S2K (p := p) (k := k) (by omega) (K := K) hK c hcb hdiam hinjZ hcne' hLFC
  rw [sum_fun_sum_equiv] at hS0 hS1 hS2
  simp only [prod_cube_mk] at hS0 hS1 hS2
  simp only [prod_phiG_mk] at hS1 hS2
  simp only [prod_phiG'_mk] at hS2
  have hNval : (Fintype.card (Ix (k-1) → ZMod p) : ℝ) = P ^ ((k-1) + 3) := by
    rw [Fintype.card_fun, ZMod.card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast
    rw [hP]
  rw [hNval] at hS0 hS1 hS2
  have hNpos : 0 < P ^ ((k-1) + 3) := by positivity
  have hNne : P ^ ((k-1) + 3) ≠ 0 := ne_of_gt hNpos
  have hb0 := abs_le.mp hS0
  have hb1 := abs_le.mp hS1
  have hb2 := abs_le.mp hS2
  have key0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
      ≤ (1 + ε) * P ^ ((k-1) + 3) := by
    have h1 : (P ^ ((k-1) + 3))⁻¹
        * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
        ≤ 1 + ε := by linarith [hb0.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 + ε)] at h2
  have key1 : (1 - ε) * P ^ ((k-1) + 3)
      ≤ (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s) := by
    have h1 : 1 - ε ≤ (P ^ ((k-1) + 3))⁻¹
        * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s) := by
      linarith [hb1.1]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 - ε)] at h2
  have key2 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
      ≤ (1 + ε) * P ^ ((k-1) + 3) := by
    have h1 : (P ^ ((k-1) + 3))⁻¹ * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s') ≤ 1 + ε := by
      linarith [hb2.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul,
      mul_comm (P ^ ((k-1) + 3)) (1 + ε)] at h2
  have hA : ∀ h x, P * AavgG p k c ν h x = ∑ s : ZMod p, PhiFG p k c ν h x s := by
    intro h x
    rw [hP, AavgG, ← mul_assoc, mul_inv_cancel₀ hpne, one_mul]
  have h0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
        = P ^ 2 * T0 p (k-1) ν h x := by
      intro h x
      rw [zmod_sum_sum_const, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x)
          = ∑ h, ∑ x, P ^ 2 * T0 p (k-1) ν h x from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h1e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s)
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x * PhiFG p k c ν h x s)
        = P ^ 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) := by
      intro h x
      rw [zmod_sum_sum_smul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s)
          = ∑ h, ∑ x, P ^ 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h2e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
      = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
        = P ^ 2 * (T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) := by
      intro h x
      rw [zmod_sum_sum_mul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
          = ∑ h, ∑ x, P ^ 2 * (T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have hLexp : (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      = (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
        - 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
        + (∑ h, ∑ x, T0 p (k-1) ν h x) := by
    have h2Y : 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
        = ∑ h, ∑ x, 2 * (T0 p (k-1) ν h x * AavgG p k c ν h x) := by
      simp only [Finset.mul_sum]
    rw [h2Y, ← sum_sum_sub, ← sum_sum_add]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hP2L : P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      = (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s * PhiFG p k c ν h x s')
        - 2 * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p (k-1) ν h x * PhiFG p k c ν h x s)
        + (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p (k-1) ν h x) := by
    rw [hLexp]
    have e : P ^ 2 * ((∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
          - 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x)
          + (∑ h, ∑ x, T0 p (k-1) ν h x))
        = P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x) ^ 2)
          - 2 * (P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * AavgG p k c ν h x))
          + P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x) := by ring
    rw [e, ← h2e, ← h1e, ← h0]
  have hNfact : P ^ ((k-1) + 3) = P ^ 2 * (p : ℝ) ^ ((k-1) + 1) := by
    rw [hP, show (k-1) + 3 = 2 + ((k-1) + 1) from by omega, pow_add]
  have hP2pos : 0 < P ^ 2 := by positivity
  have hfinal : P ^ 2 * (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2)
      ≤ P ^ 2 * (4 * ε * (p : ℝ) ^ ((k-1) + 1)) := by
    rw [hP2L]
    have h4 : (1 + ε) * P ^ ((k-1) + 3) - 2 * ((1 - ε) * P ^ ((k-1) + 3))
          + (1 + ε) * P ^ ((k-1) + 3)
        = 4 * ε * (P ^ 2 * (p : ℝ) ^ ((k-1) + 1)) := by
      rw [hNfact]; ring
    linarith [key0, key1, key2, h4]
  have hfin := (mul_le_mul_iff_of_pos_left hP2pos).mp hfinal
  have hgoal : (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin (k-1) → Bool,
            ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j))
        * (((((p : ℝ)⁻¹) * (∑ s : ZMod p,
              ∏ i : Fin (k-1),
                ∏ ω ∈ (Finset.univ.filter (fun ω : Fin (k-1) → Bool => ω i = false)),
                  ν (x + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                    - ((c ⟨1 + i.val, by have := i.isLt; omega⟩ : ℤ) : ZMod p)
                      * (s + ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j
                          * (((c ⟨j.val+1, by have := j.isLt; omega⟩ : ℤ) : ZMod p))⁻¹))))
            - 1) ^ 2))
      = (∑ h, ∑ x, T0 p (k-1) ν h x * (AavgG p k c ν h x - 1) ^ 2) := by
    simp only [T0, AavgG, PhiFG]
  rw [hgoal]
  exact hfin

end Commons.Combinatorics.Transference
