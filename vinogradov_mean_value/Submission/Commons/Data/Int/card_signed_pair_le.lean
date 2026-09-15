import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Submission.Commons.Data.Nat.card_pair_bounds_le

set_option autoImplicit false

noncomputable section

namespace Commons.Data.Int

/-! # Signed pair counting bound

The set of integers `u` with `|u| ≤ L`, `b ∣ a·u` and `a·|u| ≤ L·b` has at most
`2L·(gcd a b)/(max a b) + 3` elements (as reals).

The proof splits `u` by sign; each sign-half is in bijection with the set of
non-negative naturals `n ≤ L` satisfying the same two conditions (in `ℕ`), and
that non-negative set is bounded by `L·(gcd a b)/(max a b) + 1` via
`Commons.Data.Nat.card_pair_bounds_le`.
-/

/-- membership in a symmetric interval is `natAbs ≤ L` -/
private lemma mem_Icc_iff_natAbs_le (L : ℕ) (u : ℤ) :
    u ∈ Finset.Icc (-(L : ℤ)) (L : ℤ) ↔ u.natAbs ≤ L := by
  rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- `b ∣ a·u` (in `ℤ`) iff `b ∣ a·|u|` (in `ℕ`) -/
private lemma int_dvd_mul_natAbs (a b : ℕ) (u : ℤ) :
    (b : ℤ) ∣ (a : ℤ) * u ↔ b ∣ a * u.natAbs := by
  rw [Int.natCast_dvd]
  rw [Int.natAbs_mul]
  rw [Int.natAbs_natCast]

/-- `a·|u| ≤ L·b` (in `ℤ`) iff the same inequality in `ℕ` -/
private lemma int_mul_natAbs_le (a b L : ℕ) (u : ℤ) :
    (a : ℤ) * u.natAbs ≤ (L : ℤ) * (b : ℤ) ↔ a * u.natAbs ≤ L * b := by
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- the signed set in the statement -/
private def S (a b L : ℕ) : Finset ℤ :=
  (Finset.Icc (-(L : ℤ)) (L : ℤ)).filter
    (fun u : ℤ => (b : ℤ) ∣ (a : ℤ) * u ∧ (a : ℤ) * u.natAbs ≤ (L : ℤ) * (b : ℤ))

/-- the non-negative counterpart set (bounded by `Commons.Data.Nat.card_pair_bounds_le`) -/
private def T (a b L : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).filter (fun n : ℕ => b ∣ a * n ∧ a * n ≤ L * b)

/-- membership in the signed set in terms of `natAbs` -/
private lemma mem_S_iff (a b L : ℕ) (u : ℤ) :
    u ∈ S a b L ↔ u.natAbs ≤ L ∧ (b ∣ a * u.natAbs ∧ a * u.natAbs ≤ L * b) := by
  dsimp [S]
  rw [Finset.mem_filter, mem_Icc_iff_natAbs_le]
  rw [int_dvd_mul_natAbs, int_mul_natAbs_le]

/-- the signed set is symmetric -/
private lemma S_neg_mem_iff (a b L : ℕ) (u : ℤ) : u ∈ S a b L ↔ -u ∈ S a b L := by
  rw [mem_S_iff, mem_S_iff, Int.natAbs_neg]

/-- `|S| ≤ 2 |T|`: the map `u ↦ |u|` has fibers of size at most two -/
private lemma card_S_le_two_card_T (a b L : ℕ) : (S a b L).card ≤ 2 * (T a b L).card := by
  classical
  let Sp : Finset ℤ := (S a b L).filter (fun u : ℤ => 0 ≤ u)
  let Sn : Finset ℤ := (S a b L).filter (fun u : ℤ => u ≤ 0)
  have hcover : S a b L ⊆ Sp ∪ Sn := by
    intro u hu
    rw [Finset.mem_union]
    rcases le_total 0 u with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hu, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hu, h⟩)
  have hSp_le_T : Sp.card ≤ (T a b L).card := by
    apply Finset.card_le_card_of_injOn (fun u : ℤ => u.natAbs)
    · intro u hu
      rcases Finset.mem_filter.mp hu with ⟨huS, hu0⟩
      have hu' : u.natAbs ≤ L ∧ (b ∣ a * u.natAbs ∧ a * u.natAbs ≤ L * b) :=
        (mem_S_iff a b L u).mp huS
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hu'.1), hu'.2⟩)
    · intro u hu v hv hnat
      have hu0 : 0 ≤ u := (Finset.mem_filter.mp hu).2
      have hv0 : 0 ≤ v := (Finset.mem_filter.mp hv).2
      have hu_eq : ((u.natAbs : ℤ)) = u := Int.natAbs_of_nonneg hu0
      have hv_eq : ((v.natAbs : ℤ)) = v := Int.natAbs_of_nonneg hv0
      rw [← hu_eq, ← hv_eq]
      exact congrArg (fun n : ℕ => (n : ℤ)) hnat
  have hSn_eq_image : Sn = Sp.image (fun u : ℤ => -u) := by
    ext u
    constructor
    · intro hu
      rw [Finset.mem_filter] at hu
      rcases hu with ⟨huS, hu0⟩
      rw [Finset.mem_image]
      refine ⟨-u, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨(S_neg_mem_iff a b L u).mp huS, neg_nonneg.mpr hu0⟩
      · simp
    · intro hu
      rw [Finset.mem_image] at hu
      rcases hu with ⟨v, hv, rfl⟩
      rw [Finset.mem_filter] at hv
      rcases hv with ⟨hvS, hv0⟩
      rw [Finset.mem_filter]
      exact ⟨(S_neg_mem_iff a b L v).mp hvS, neg_nonpos.mpr hv0⟩
  have hSn_card : Sn.card = Sp.card := by
    rw [hSn_eq_image]
    exact Finset.card_image_of_injective Sp neg_injective
  calc
    (S a b L).card ≤ (Sp ∪ Sn).card := Finset.card_le_card hcover
    _ ≤ Sp.card + Sn.card := Finset.card_union_le Sp Sn
    _ = 2 * Sp.card := by rw [hSn_card]; ring
    _ ≤ 2 * (T a b L).card := Nat.mul_le_mul_left 2 hSp_le_T

theorem card_signed_pair_le (a b L : ℕ) (hmax : 0 < max a b) :
    (((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter
        (fun u : ℤ => (b : ℤ) ∣ (a : ℤ) * u ∧ (a : ℤ) * u.natAbs ≤ (L : ℤ) * (b : ℤ))).card : ℝ)
      ≤ 2 * (L : ℝ) * ((Nat.gcd a b : ℝ) / (max a b : ℝ)) + 3 := by
  change ((S a b L).card : ℝ) ≤ 2 * (L : ℝ) * ((Nat.gcd a b : ℝ) / (max a b : ℝ)) + 3
  have hred : (S a b L).card ≤ 2 * (T a b L).card := card_S_le_two_card_T a b L
  have hT : ((T a b L).card : ℝ) ≤ (L : ℝ) * ((Nat.gcd a b : ℝ) / (max a b : ℝ)) + 1 := by
    simpa [T] using (Commons.Data.Nat.card_pair_bounds_le a b L hmax)
  have h1 : ((S a b L).card : ℝ) ≤ 2 * ((T a b L).card : ℝ) := by
    exact_mod_cast hred
  have h2 : 2 * ((T a b L).card : ℝ) ≤
      2 * ((L : ℝ) * ((Nat.gcd a b : ℝ) / (max a b : ℝ)) + 1) := by
    exact mul_le_mul_of_nonneg_left hT (by norm_num)
  nlinarith

end Commons.Data.Int