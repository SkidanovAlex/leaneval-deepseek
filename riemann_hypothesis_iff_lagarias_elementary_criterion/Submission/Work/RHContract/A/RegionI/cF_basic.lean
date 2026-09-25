import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs

open scoped BigOperators

namespace Work.RHContract.A.RegionI

namespace cFBasic

open Work.RHContract.RegionI

/-- Casting `caS p k` to `ℝ` gives the real geometric partial sum `∑_{i<k} p^{i+1}`. -/
lemma caS_coe_real (p k : ℕ) :
    (caS p k : ℝ) = ∑ i ∈ Finset.range k, (p : ℝ) ^ (i + 1) := by
  simp only [caS, Nat.cast_sum, Nat.cast_pow]

/-- `1 ≤ S_k(p)` whenever `1 ≤ p` and `1 ≤ k`. -/
lemma caS_pos {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) : 1 ≤ caS p k := by
  unfold caS
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hle : (p ^ (0 + 1) : ℕ) ≤ ∑ i ∈ Finset.range k, p ^ (i + 1) :=
    Finset.single_le_sum (s := Finset.range k) (f := fun i => p ^ (i + 1))
      (fun i hi => Nat.zero_le _) hmem
  have hp1 : 1 ≤ p ^ (0 + 1) := by simpa using hp
  omega

/-- `S_k(p)` is strictly increasing in `p` (for `k ≥ 1`). -/
lemma caS_lt {p q k : ℕ} (hk : 1 ≤ k) (hlt : p < q) : caS p k < caS q k := by
  unfold caS
  refine Finset.sum_lt_sum ?_ ?_
  · intro i hi
    exact pow_le_pow_left₀ (Nat.zero_le p) (le_of_lt hlt) (i + 1)
  · exact ⟨0, Finset.mem_range.mpr (by omega), by simpa using hlt⟩

/-- `p^{k+1} − p = (p−1)·S_k(p)` over the reals. -/
lemma pow_succ_sub_self_eq_mul_caS {p k : ℕ} :
    (p : ℝ) ^ (k + 1) - (p : ℝ) = ((p : ℝ) - 1) * (caS p k : ℝ) := by
  have hmul : (∑ i ∈ Finset.range k, (p : ℝ) ^ (i + 1)) =
      (p : ℝ) * ∑ i ∈ Finset.range k, (p : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [pow_succ']
  have hg : (p : ℝ) ^ k - 1 = ((p : ℝ) - 1) * ∑ i ∈ Finset.range k, (p : ℝ) ^ i := by
    have h := geom_sum_mul (x := (p : ℝ)) k
    calc
      (p : ℝ) ^ k - 1 = (∑ i ∈ Finset.range k, (p : ℝ) ^ i) * ((p : ℝ) - 1) := h.symm
      _ = ((p : ℝ) - 1) * ∑ i ∈ Finset.range k, (p : ℝ) ^ i := by ring
  calc
    (p : ℝ) ^ (k + 1) - (p : ℝ) = (p : ℝ) * ((p : ℝ) ^ k - 1) := by
      rw [pow_succ']; ring
    _ = ((p : ℝ) - 1) * ((p : ℝ) * ∑ i ∈ Finset.range k, (p : ℝ) ^ i) := by
      rw [hg]; ring
    _ = ((p : ℝ) - 1) * (∑ i ∈ Finset.range k, (p : ℝ) ^ (i + 1)) := by
      rw [← hmul]
    _ = ((p : ℝ) - 1) * (caS p k : ℝ) := by
      rw [caS_coe_real]

/-- The CA level ratio equals `1 + 1/S_k(p)`. -/
lemma ratio_eq_one_add_inv_caS {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1)) - 1) / (((p : ℝ) ^ (k + 1)) - (p : ℝ)) =
      1 + 1 / (caS p k : ℝ) := by
  have hfac := pow_succ_sub_self_eq_mul_caS (p := p) (k := k)
  have hnum : (p : ℝ) ^ (k + 1) - 1 = ((p : ℝ) - 1) * ((caS p k : ℝ) + 1) := by
    calc
      (p : ℝ) ^ (k + 1) - 1 = ((p : ℝ) ^ (k + 1) - (p : ℝ)) + ((p : ℝ) - 1) := by ring
      _ = ((p : ℝ) - 1) * (caS p k : ℝ) + ((p : ℝ) - 1) := by rw [hfac]
      _ = ((p : ℝ) - 1) * ((caS p k : ℝ) + 1) := by ring
  have hpmin : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hS : 1 ≤ caS p k := caS_pos (by omega : 1 ≤ p) hk
  have hSpos : (0 : ℝ) < (caS p k : ℝ) := by exact_mod_cast hS
  have hSne : (caS p k : ℝ) ≠ 0 := ne_of_gt hSpos
  rw [hnum, hfac]
  field_simp [hpmin, hSne]

/-- `F(·,k)` is strictly decreasing in the prime argument `p`. -/
lemma cF_anti_p {p q k : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 1 ≤ k) (hlt : p < q) :
    cF q k < cF p k := by
  let Ap : ℝ := (((p : ℝ) ^ (k + 1)) - 1) / (((p : ℝ) ^ (k + 1)) - (p : ℝ))
  let Aq : ℝ := (((q : ℝ) ^ (k + 1)) - 1) / (((q : ℝ) ^ (k + 1)) - (q : ℝ))
  have hSp : 1 ≤ caS p k := caS_pos (by omega : 1 ≤ p) hk
  have hSq : 1 ≤ caS q k := caS_pos (by omega : 1 ≤ q) hk
  have hSppos : (0 : ℝ) < (caS p k : ℝ) := by exact_mod_cast hSp
  have hSqpos : (0 : ℝ) < (caS q k : ℝ) := by exact_mod_cast hSq
  have hS : (caS p k : ℝ) < (caS q k : ℝ) := by
    exact_mod_cast (caS_lt (p := p) (q := q) (k := k) hk hlt)
  have hA : Aq < Ap := by
    dsimp [Ap, Aq]
    rw [ratio_eq_one_add_inv_caS hp hk, ratio_eq_one_add_inv_caS hq hk]
    have hinv : 1 / (caS q k : ℝ) < 1 / (caS p k : ℝ) :=
      one_div_lt_one_div_of_lt hSppos hS
    linarith
  have hAq1 : 1 < Aq := by
    dsimp [Aq]
    rw [ratio_eq_one_add_inv_caS hq hk]
    have h : (0 : ℝ) < 1 / (caS q k : ℝ) := one_div_pos.mpr hSqpos
    linarith
  have hAp1 : 1 < Ap := by
    dsimp [Ap]
    rw [ratio_eq_one_add_inv_caS hp hk]
    have h : (0 : ℝ) < 1 / (caS p k : ℝ) := one_div_pos.mpr hSppos
    linarith
  have hlogA : Real.log Aq < Real.log Ap := Real.log_lt_log (lt_trans zero_lt_one hAq1) hA
  have hlogAqpos : 0 < Real.log Aq := Real.log_pos hAq1
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hloglt : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast (by omega : p < q))
  unfold cF
  rw [div_lt_div_iff₀ hlogq hlogp]
  have hm1 : Real.log Aq * Real.log (p : ℝ) < Real.log Aq * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_left hloglt hlogAqpos
  have hm2 : Real.log Aq * Real.log (q : ℝ) < Real.log Ap * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_right hlogA hlogq
  exact lt_trans hm1 hm2

end cFBasic

theorem cF_basic :
    (∀ p k : ℕ, 1 ≤ p → 1 ≤ k → 1 ≤ Work.RHContract.RegionI.caS p k) ∧
    (∀ p q k : ℕ, 1 ≤ k → p < q → Work.RHContract.RegionI.caS p k < Work.RHContract.RegionI.caS q k) ∧
    (∀ p k : ℕ, 2 ≤ p → 1 ≤ k →
      Work.RHContract.RegionI.cF p k =
        Real.log (1 + 1 / (Work.RHContract.RegionI.caS p k : ℝ)) / Real.log (p : ℝ)) ∧
    (∀ p q k : ℕ, 2 ≤ p → 2 ≤ q → 1 ≤ k → p < q →
      Work.RHContract.RegionI.cF q k < Work.RHContract.RegionI.cF p k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p k hp hk
    exact cFBasic.caS_pos hp hk
  · intro p q k hk hlt
    exact cFBasic.caS_lt hk hlt
  · intro p k hp hk
    unfold Work.RHContract.RegionI.cF
    rw [cFBasic.ratio_eq_one_add_inv_caS hp hk]
  · intro p q k hp hq hk hlt
    exact cFBasic.cF_anti_p hp hq hk hlt

end Work.RHContract.A.RegionI
