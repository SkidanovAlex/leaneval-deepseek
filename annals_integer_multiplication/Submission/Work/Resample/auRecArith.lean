import Mathlib
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auKClose
import Submission.Work.Resample.auKTdiv
import Submission.Work.Resample.auSmallSizes

/-!
# Arithmetic of the resampling table (`Work.Resample.auRecArith`)

Every integer value occurring in the table word `Work.Resample.auPrep` fits the uniform size bound
`auSZ p = 10p + 400`, and the two quantities `K_k = auK s t k`, `K_{k+1}` that the record word
computes with `Int.tdiv` are the ones defined by `auK`:

* `auC p α s t k = t·K_k − t·m − s·k` with `|t·K_k − s·k| ≤ t` (`auKClose`) and `m = auM p α ≤ 2p`,
  so `|auC| ≤ t·(m+1) ≤ 2^{2p}` and `isz (auC) ≤ 2p + 3 ≤ auSZ p`;
* `auM p α ≤ 2p`, `auL p α = 2·auM + 1 ≤ 4p + 1`;
* `isz (auPi p) ≤ auSZ p` (`auKit.isz_auPi_le`), the cast bounds for `k, s, t, p, α`
  (`auSmallSizes`) and for every index `i < auL p α`;
* `Int.tdiv (2ks + t) (2t) = K_k` and `Int.tdiv (2ks + t + 2s) (2t) = K_{k+1}` (`auKTdiv`).
-/

namespace Work.Resample

open HvdH

/-- The offset `auC p α s t k = t·K_k − t·m − s·k` has modulus at most `2^{2p}`: the rounding
error of `K_k` contributes at most `t`, and `t·m ≤ 2^p·2p`. -/
theorem auCNatAbs_le (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    (auC p α s t k).natAbs ≤ 2 ^ (2 * p) := by
  have ht1 : 1 ≤ t := by omega
  have hA : |(t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)| ≤ (t : ℤ) := auKClose s t k ht1
  have hAn : ((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)).natAbs ≤ t := by
    have h : (((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)).natAbs : ℤ) ≤ (t : ℤ) := by
      rw [Int.natCast_natAbs]; exact hA
    exact_mod_cast h
  have hCe : auC p α s t k
      = ((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)) - (t : ℤ) * (auM p α : ℤ) := by
    simp only [auC]; ring
  have hmul : ((t : ℤ) * (auM p α : ℤ)).natAbs = t * auM p α := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  have hsteps : (auC p α s t k).natAbs ≤ t + t * auM p α := by
    rw [hCe]
    calc (((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)) - (t : ℤ) * (auM p α : ℤ)).natAbs
        ≤ ((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)).natAbs
          + ((t : ℤ) * (auM p α : ℤ)).natAbs := Int.natAbs_sub_le _ _
      _ = ((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)).natAbs + t * auM p α := by rw [hmul]
      _ ≤ t + t * auM p α := Nat.add_le_add_right hAn _
  have hM : auM p α ≤ 2 * p := (auMLe p α hα hαp).1
  have htle : t ≤ 2 ^ p := le_of_lt htp
  have hmle : auM p α + 1 ≤ 2 ^ p := by
    have h4 := four_mul_add_one_lt_two_pow p hp
    omega
  calc (auC p α s t k).natAbs ≤ t + t * auM p α := hsteps
    _ = t * (auM p α + 1) := by ring
    _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul htle hmle
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

/-- The offset `auC` fits the uniform size bound of the table word. -/
theorem auCSizeLe (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    HvdH.isz (auC p α s t k) ≤ auSZ p := by
  have h := auCNatAbs_le p α s t k hs hst htp hα hp hαp hk
  have h1 : (auC p α s t k).natAbs < 2 ^ (2 * p + 1) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right one_lt_two (by omega))
  have h2 : ((auC p α s t k).natAbs).size ≤ 2 * p + 1 := Nat.size_le.mpr h1
  simp only [HvdH.isz, auSZ]
  omega

theorem auRecArith (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    (HvdH.isz (Work.Resample.auPi p) ≤ Work.Resample.auSZ p ∧
      Work.Resample.auM p α ≤ 2 * p ∧ Work.Resample.auL p α ≤ 4 * p + 1 ∧
      HvdH.isz ((Work.Resample.auL p α : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((Work.Resample.auK s t k : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (Work.Resample.auC p α s t k) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (((k : ℕ) : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (((s : ℕ) : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (((t : ℕ) : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (((p : ℕ) : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz (((α : ℕ) : ℤ)) ≤ Work.Resample.auSZ p ∧
      (∀ i, i < Work.Resample.auL p α → HvdH.isz (((i : ℕ) : ℤ)) ≤ Work.Resample.auSZ p)) ∧
    Int.tdiv ((2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ)) ((2 : ℤ) * (t : ℤ))
        = ((Work.Resample.auK s t k : ℕ) : ℤ) ∧
    Int.tdiv (((2 : ℤ) * (k : ℤ) * (s : ℤ) + (t : ℤ)) + 2 * (s : ℤ)) ((2 : ℤ) * (t : ℤ))
        = ((Work.Resample.auK s t (k + 1) : ℕ) : ℤ) := by
  have ht : 0 < t := by omega
  have hs1 : 1 ≤ s := by omega
  have hk1 : k + 1 ≤ t := by omega
  obtain ⟨hM, hL⟩ := auMLe p α hα hαp
  obtain ⟨hOffSz, hCopSz, hMSz, hLSz0, hKleS, hKmono, hK0, hKstep, hKdiff, hCop⟩ :=
    auSizes p α s t hs hst hα hp hαp htp
  have hLSz : HvdH.isz ((auL p α : ℕ) : ℤ) ≤ auSZ p := by
    simp only [auSZ] at hLSz0 ⊢
    omega
  have hK_lt : auK s t k < 2 ^ p := (auKArith p s t k hs hst htp hk).1
  have hK1_lt : auK s t (k + 1) < 2 ^ p :=
    lt_of_le_of_lt (auK_le_s hs1 ht hk1) (lt_trans hst htp)
  have hSmall := auSmallSizes p α s t k hs hst htp hα hp hαp hk
  refine ⟨⟨isz_auPi_le p, hM, hL, hLSz, isz_le_pow2 (le_of_lt hK_lt),
      isz_le_pow2 (le_of_lt hK1_lt), auCSizeLe p α s t k hs hst htp hα hp hαp hk,
      hSmall.1, hSmall.2.1, hSmall.2.2.1, hSmall.2.2.2.1, hSmall.2.2.2.2.1,
      hSmall.2.2.2.2.2⟩, (auKTdiv s t k ht).1, (auKTdiv s t k ht).2⟩

end Work.Resample
