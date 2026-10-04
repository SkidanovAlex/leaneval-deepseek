import Mathlib
import Submission.Work.Diff.STE.flat.Sobolev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dyadic annuli of the frequency lattice partition it

The dyadic annuli `annulus m = {k | 2 ^ (2m) ≤ ⟨k⟩² < 2 ^ (2m + 2)}` of the frequency lattice
`ℤ^ι` (see `Submission.Work.Diff.STE.flat.Sobolev`) split `ℤ^ι` into the disjoint shells
`4^m ≤ ⟨k⟩² < 4^(m+1)`, `m ≥ 0`.  Since `⟨k⟩² ≥ 1 = 4^0`, every frequency `k` lies in exactly
one such annulus, and this file records the consequences:

* `annulusIdx k` : the dyadic index of `k`, i.e. the unique `m` with `k ∈ annulus m`
  (`mem_annulus_annulusIdx`, `eq_annulusIdx_of_mem`);
* `blockFun_apply_annulusIdx`, `blockFun_apply_of_ne_annulusIdx` : the block of a family at
  frequency `k` equals the family at `k` for `m = annulusIdx k` and vanishes otherwise.

The main result `tsum_annulus` then says that the sum over the blocks is the sum over the lattice:
`∑_m ∑_k blockFun m g k = ∑_k g k` for every summable (Banach-space valued) family `g`.
-/

namespace Work.Diff.STE.flat.Sobolev

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(2 : ℝ) ^ (2 * m) = 4 ^ m`: the dyadic annuli are the shells `[4^m, 4^(m+1))` of `⟨k⟩²`. -/
private lemma two_pow_two_mul (m : ℕ) : (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m := by
  rw [pow_mul]
  norm_num

/-- Membership in the `m`-th dyadic annulus, in terms of powers of `4`. -/
lemma mem_annulus_iff (k : ι → ℤ) (m : ℕ) :
    k ∈ annulus m ↔
      (4 : ℝ) ^ m ≤ Work.Diff.STE.wt k ∧ Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1) := by
  simp only [annulus, Set.mem_setOf_eq]
  rw [two_pow_two_mul m, two_pow_two_mul (m + 1)]

/-- Every frequency lies strictly below some power of `4`. -/
lemma exists_wt_lt_four_pow (k : ι → ℤ) :
    ∃ m : ℕ, Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1) := by
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).eventually_gt_atTop
      (Work.Diff.STE.wt k)).exists
  exact ⟨n, lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩

/-- The dyadic index of a frequency `k`: the unique `m` with `4^m ≤ ⟨k⟩² < 4^(m+1)`,
equivalently the unique `m` with `k ∈ annulus m`. -/
noncomputable def annulusIdx (k : ι → ℤ) : ℕ :=
  Nat.find (p := fun m => Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1)) (exists_wt_lt_four_pow k)

lemma wt_lt_four_pow_annulusIdx_succ (k : ι → ℤ) :
    Work.Diff.STE.wt k < (4 : ℝ) ^ (annulusIdx k + 1) :=
  Nat.find_spec (p := fun m => Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1))
    (exists_wt_lt_four_pow k)

lemma annulusIdx_le_of_wt_lt {k : ι → ℤ} {m : ℕ}
    (h : Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1)) : annulusIdx k ≤ m :=
  Nat.find_min' (p := fun m => Work.Diff.STE.wt k < (4 : ℝ) ^ (m + 1))
    (exists_wt_lt_four_pow k) h

lemma four_pow_annulusIdx_le (k : ι → ℤ) :
    (4 : ℝ) ^ (annulusIdx k) ≤ Work.Diff.STE.wt k := by
  rcases Nat.eq_zero_or_pos (annulusIdx k) with h0 | hpos
  · rw [h0]
    simpa using Work.Diff.STE.wt_one_le k
  · have hlt : annulusIdx k - 1 < annulusIdx k := by omega
    have hnot : ¬ (Work.Diff.STE.wt k < (4 : ℝ) ^ ((annulusIdx k - 1) + 1)) :=
      Nat.find_min (exists_wt_lt_four_pow k) hlt
    rw [Nat.sub_add_cancel hpos] at hnot
    exact not_lt.mp hnot

/-- Every frequency lies in its own dyadic annulus. -/
lemma mem_annulus_annulusIdx (k : ι → ℤ) : k ∈ annulus (annulusIdx k) :=
  (mem_annulus_iff k (annulusIdx k)).mpr
    ⟨four_pow_annulusIdx_le k, wt_lt_four_pow_annulusIdx_succ k⟩

/-- The dyadic index is unique: the annuli are pairwise disjoint. -/
lemma eq_annulusIdx_of_mem {k : ι → ℤ} {m : ℕ} (hm : k ∈ annulus m) : m = annulusIdx k := by
  obtain ⟨h1, h2⟩ := (mem_annulus_iff k m).mp hm
  have hle : m ≤ annulusIdx k := by
    have : m < annulusIdx k + 1 :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).mp
        (lt_of_le_of_lt h1 (wt_lt_four_pow_annulusIdx_succ k))
    omega
  have hge : annulusIdx k ≤ m := by
    have : annulusIdx k < m + 1 :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).mp
        (lt_of_le_of_lt (four_pow_annulusIdx_le k) h2)
    omega
  omega

lemma blockFun_apply_annulusIdx {E : Type*} [Zero E] (g : (ι → ℤ) → E) (k : ι → ℤ) :
    blockFun (annulusIdx k) g k = g k := by
  classical
  simp only [blockFun]
  exact if_pos (mem_annulus_annulusIdx k)

lemma blockFun_apply_of_not_mem {E : Type*} [Zero E] (g : (ι → ℤ) → E) {m : ℕ} {k : ι → ℤ}
    (hk : k ∉ annulus m) : blockFun m g k = 0 := by
  classical
  simp only [blockFun]
  exact if_neg hk

lemma blockFun_apply_of_ne_annulusIdx {E : Type*} [Zero E] (g : (ι → ℤ) → E) {m : ℕ}
    {k : ι → ℤ} (hm : m ≠ annulusIdx k) : blockFun m g k = 0 :=
  blockFun_apply_of_not_mem g fun hk => hm (eq_annulusIdx_of_mem hk)

theorem tsum_annulus {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    (g : (ι → ℤ) → E) (hg : Summable g) :
    (∑' m : ℕ, ∑' k : ι → ℤ, Work.Diff.STE.flat.blockFun m g k) = ∑' k : ι → ℤ, g k := by
  classical
  have he : Function.Injective (fun k : ι → ℤ => (annulusIdx k, k)) := fun k l hkl =>
    congrArg Prod.snd hkl
  have hzero : ∀ p ∉ Set.range (fun k : ι → ℤ => (annulusIdx k, k)),
      Work.Diff.STE.flat.blockFun p.1 g p.2 = 0 := by
    rintro ⟨m, k⟩ hp
    exact blockFun_apply_of_ne_annulusIdx (m := m) (k := k) g fun h => hp ⟨k, by simp [h]⟩
  have hcomp : Summable (fun k : ι → ℤ => Work.Diff.STE.flat.blockFun (annulusIdx k) g k) :=
    hg.congr fun k => (blockFun_apply_annulusIdx g k).symm
  have hsum : Summable (fun p : ℕ × (ι → ℤ) => Work.Diff.STE.flat.blockFun p.1 g p.2) :=
    (Function.Injective.summable_iff
      (f := fun p : ℕ × (ι → ℤ) => Work.Diff.STE.flat.blockFun p.1 g p.2)
      (g := fun k : ι → ℤ => (annulusIdx k, k)) he hzero).mp hcomp
  calc (∑' m : ℕ, ∑' k : ι → ℤ, Work.Diff.STE.flat.blockFun m g k)
      = ∑' k : ι → ℤ, ∑' m : ℕ, Work.Diff.STE.flat.blockFun m g k :=
        (Summable.tsum_comm (f := fun (m : ℕ) (k : ι → ℤ) =>
          Work.Diff.STE.flat.blockFun m g k) hsum).symm
    _ = ∑' k : ι → ℤ, g k := tsum_congr fun k => by
        rw [tsum_eq_single (annulusIdx k) fun m hm => blockFun_apply_of_ne_annulusIdx g hm]
        exact blockFun_apply_annulusIdx g k

end Work.Diff.STE.flat.Sobolev
