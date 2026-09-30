import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.struct
import Submission.Work.BMF.recursion.card_pair_fibre_sum
import Submission.Work.BMF.recursion.prime_avoid
import Submission.Work.BMF.recursion.exists_perm_pair
import Submission.Work.BMF.recursion.powerSums_perm
import Submission.Work.BMF.recursion.I1_le_I2
import Submission.Work.BMF.recursion.I2_bound
import Submission.Work.BMF.recursion.Tdbl_le_rpow
import Submission.Work.BMF.recursion.J_le_two_S
import Submission.Work.BMF.recursion.S1_le_I1
import Submission.Work.BMF.recursion.S2_le_k4_Tdbl

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BMF

open scoped BigOperators
open LeanEval.NumberTheory.VinogradovMeanValue
open Work.BMF.recursion

/-- **The bootstrap of case (a)**: `J ≤ C·J^{1-1/S}` forces `J ≤ C^S`, for `C = 4k⁴`. -/
private lemma bootstrap (k S : ℕ) (hS : 2 ≤ S) {J : ℝ} (hJ0 : 0 ≤ J)
    (h : J ≤ 4 * (k : ℝ) ^ 4 * J ^ (1 - 1 / (S : ℝ))) : J ≤ (4 * (k : ℝ) ^ 4) ^ S := by
  rcases eq_or_lt_of_le hJ0 with hJ | hJ
  · rw [← hJ]; exact pow_nonneg (by positivity) S
  · have hSpos : (0 : ℝ) < (S : ℝ) := by
      exact_mod_cast (by omega : 0 < S)
    have h1S : (1 : ℝ) / (S : ℝ) ≤ 1 := by
      rw [div_le_one hSpos]
      exact_mod_cast (by omega : 1 ≤ S)
    have hpow : 0 < J ^ (1 - 1 / (S : ℝ)) := Real.rpow_pos_of_pos hJ _
    have hkey : J ^ (1 / (S : ℝ)) * J ^ (1 - 1 / (S : ℝ)) = J := by
      rw [← Real.rpow_add hJ]
      have : 1 / (S : ℝ) + (1 - 1 / (S : ℝ)) = 1 := by ring
      rw [this, Real.rpow_one]
    have hdiv : J ^ (1 / (S : ℝ)) ≤ 4 * (k : ℝ) ^ 4 := by
      have hle : J / J ^ (1 - 1 / (S : ℝ)) ≤ 4 * (k : ℝ) ^ 4 := by
        rw [div_le_iff₀ hpow]; exact h
      have h2 : J / J ^ (1 - 1 / (S : ℝ)) = J ^ (1 / (S : ℝ)) := by
        rw [div_eq_iff (ne_of_gt hpow)]
        exact hkey.symm
      rwa [h2] at hle
    calc J = (J ^ (1 / (S : ℝ))) ^ S := by
          rw [← Real.rpow_natCast (J ^ (1 / (S : ℝ))) S, ← Real.rpow_mul hJ0]
          congr 1
          rw [one_div, inv_mul_cancel₀ (by positivity : (S : ℝ) ≠ 0), Real.rpow_one]
      _ ≤ (4 * (k : ℝ) ^ 4) ^ S := pow_le_pow_left₀ (Real.rpow_nonneg hJ0 _) hdiv S

/-- **The classical Vinogradov–Linnik recursion** (Wooley, *On Vinogradov's mean value theorem, II*, Michigan Math. J. **40** (1993), 175–180). Let `k ≥ 2`, `k ≤ S`, `Q ≥ 1`, and let `M ≥ k` with `M^k > Q`. Let `P` be a set of at least `⌈k³/2⌉` primes, all of them `> M` and `≤ Y`. Then `J_{S,k}(Q) ≤ (4k⁴)^S + 4·k!·|P|²·Y^{2(S−k)+k(k−1)/2}·Q^k·J_{S−k,k}(1 + Q/M)`, where `J` is the Vinogradov counting function `LeanEval.NumberTheory.VinogradovMeanValue.J`. Route: Wooley's case `(a)`/`(b)` split (analyse the `k` "head" coordinates for being pairwise distinct / not), `∫|f|^{2S} = J` (`Submission.Vinogradov.vmvt_orthogonality_norm`), Hölder twice, the prime-avoidance trick (`|P| ≥ k²(k−1)/2`), and Linnik's lemma `Work.BMF.linnik_bound` (import `Submission.Work.BMF.linnik_bound`, file `Submission/Work/BMF/linnik_bound.lean`). -/
theorem recursion_step (k S Q M Y : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (hQ : 1 ≤ Q)
    (hM : k ≤ M) (hMQ : (Q:ℝ) < (M:ℝ)^k)
    (P : Finset ℕ) (hPp : ∀ p ∈ P, Nat.Prime p) (hPlb : ∀ p ∈ P, M < p) (hPub : ∀ p ∈ P, p ≤ Y)
    (hPc : ⌈(k:ℝ)^3/2⌉₊ ≤ P.card) :
    LeanEval.NumberTheory.VinogradovMeanValue.J S k Q ≤
      (4*(k:ℝ)^4)^S + 4*((k.factorial : ℕ):ℝ)*(P.card:ℝ)^2*(Y:ℝ)^(2*(S-k)+k*(k-1)/2)*(Q:ℝ)^k
      * LeanEval.NumberTheory.VinogradovMeanValue.J (S-k) k (1 + Q / M) := by
  classical
  have hS2 : 2 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hM1 : 1 ≤ M := by omega
  have hQn : Q < M ^ k := by exact_mod_cast hMQ
  -- the prime-set size hypothesis in the form needed by `prime_avoid`
  have hPc' : k * (k - 1) * (k - 1) < 2 * P.card := by
    have hceil : (k : ℝ) ^ 3 / 2 ≤ ((⌈(k : ℝ) ^ 3 / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hcard : ((⌈(k : ℝ) ^ 3 / 2⌉₊ : ℕ) : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hPc
    have h1 : (k : ℝ) ^ 3 ≤ 2 * (P.card : ℝ) := by linarith
    have h2 : (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 1) < (k : ℝ) ^ 3 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith [sq_nonneg ((k : ℝ) - 1), hk1]
    have hcast : ((k * (k - 1) * (k - 1) : ℕ) : ℝ)
        = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      ring
    have h3 : ((k * (k - 1) * (k - 1) : ℕ) : ℝ) < 2 * (P.card : ℝ) := by
      rw [hcast]; linarith
    exact_mod_cast h3
  set S1 : ℝ := (S1pair S k Q hkS : ℝ) with hS1def
  set S2 : ℝ := (S2pair S k Q hkS : ℝ) with hS2def
  have hJ2 : J S k Q ≤ 2 * (S1 + S2) := J_le_two_S S k Q hk hkS
  have hJ0 : 0 ≤ J S k Q := by rw [J_eq_solSet]; positivity
  -- the target's second term
  have hRHS2 : (0 : ℝ) ≤ 4 * ((k.factorial : ℕ) : ℝ) * (P.card : ℝ) ^ 2 *
      (Y : ℝ) ^ (2 * (S - k) + k * (k - 1) / 2) * (Q : ℝ) ^ k * J (S - k) k (1 + Q / M) := by
    have h1 : (0 : ℝ) ≤ ((k.factorial : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (P.card : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (Y : ℝ) ^ (2 * (S - k) + k * (k - 1) / 2) := by positivity
    have h4 : (0 : ℝ) ≤ (Q : ℝ) ^ k := by positivity
    have h5 : (0 : ℝ) ≤ J (S - k) k (1 + Q / M) := by rw [J_eq_solSet]; positivity
    positivity
  rcases le_total S1 S2 with hcase | hcase
  · -- Case (a): `S1 ≤ S2`, so `J ≤ 4 S2` and the collision bound applies
    have hJ4 : J S k Q ≤ 4 * S2 := by linarith
    have hS2b : S2 ≤ (k : ℝ) ^ 4 * (Tdbl S k Q hk hkS : ℝ) := S2_le_k4_Tdbl S k Q hk hkS
    have hTb : (Tdbl S k Q hk hkS : ℝ) ≤ (J S k Q) ^ (1 - 1 / (S : ℝ)) :=
      Tdbl_le_rpow S k Q hk hkS hQ
    have hchain : J S k Q ≤ 4 * (k : ℝ) ^ 4 * (J S k Q) ^ (1 - 1 / (S : ℝ)) := by
      calc J S k Q ≤ 4 * S2 := hJ4
        _ ≤ 4 * ((k : ℝ) ^ 4 * (Tdbl S k Q hk hkS : ℝ)) :=
              mul_le_mul_of_nonneg_left hS2b (by norm_num)
        _ = 4 * (k : ℝ) ^ 4 * (Tdbl S k Q hk hkS : ℝ) := by ring
        _ ≤ 4 * (k : ℝ) ^ 4 * (J S k Q) ^ (1 - 1 / (S : ℝ)) :=
              mul_le_mul_of_nonneg_left hTb (by positivity)
    exact le_trans (bootstrap k S hS2 hJ0 hchain) (by
      have hZ : (0:ℝ) ≤ (4 * (k:ℝ) ^ 4) ^ S := pow_nonneg (by positivity) S
      linarith [hRHS2, hZ])
  · -- Case (b): `S2 ≤ S1`, so `J ≤ 4 S1` and the Linnik bound applies
    have hJ4 : J S k Q ≤ 4 * S1 := by linarith
    have hI1b : ∀ p ∈ P, (I1 S k Q p hkS : ℝ) ≤
        (Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) * (Q : ℝ) ^ k *
          ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M) := by
      intro p hp
      have hpprime : p.Prime := hPp p hp
      have hp1 : 1 ≤ p := hpprime.one_le
      have hkp : k < p := lt_of_le_of_lt hM (hPlb p hp)
      have hMp : M ≤ p := le_of_lt (hPlb p hp)
      have hQp : Q < p ^ k := lt_of_lt_of_le hQn (Nat.pow_le_pow_left hMp k)
      have hpY : (p : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hPub p hp
      have hsup : ∀ y ∈ Finset.range p, (I2 S k Q p y hkS : ℝ) ≤
          (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
            J (S - k) k (1 + Q / M) := by
        intro y hy
        have hy' : y < p := Finset.mem_range.mp hy
        exact I2_bound S k Q M p y hk hkS hpprime hkp hQp hM1 hMp hy'
      have hsupR : (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) ≤
          (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
            J (S - k) k (1 + Q / M) := by
        have hne : (Finset.range p).Nonempty :=
          ⟨0, Finset.mem_range.mpr hpprime.pos⟩
        obtain ⟨y, hy, hysup⟩ :=
          Finset.exists_mem_eq_sup _ hne (fun y => I2 S k Q p y hkS)
        rw [hysup]
        exact hsup y hy
      have h1 := I1_le_I2 S k Q p hkS hp1
      have hp2 : (p : ℝ) ^ (2 * (S - k)) ≤ (Y : ℝ) ^ (2 * (S - k)) :=
        pow_le_pow_left₀ (by positivity) hpY _
      have hp3 : (p : ℝ) ^ (k * (k - 1) / 2) ≤ (Y : ℝ) ^ (k * (k - 1) / 2) :=
        pow_le_pow_left₀ (by positivity) hpY _
      have hA0 : (0 : ℝ) ≤ ((k.factorial : ℕ) : ℝ) := by positivity
      have hB0 : (0 : ℝ) ≤ (Q : ℝ) ^ k := by positivity
      have hC0 : (0 : ℝ) ≤ (p : ℝ) ^ (k * (k - 1) / 2) := by positivity
      have hD0 : (0 : ℝ) ≤ J (S - k) k (1 + Q / M) := by rw [J_eq_solSet]; positivity
      have hp0 : (0 : ℝ) ≤ (p : ℝ) ^ (2 * (S - k)) := by positivity
      calc (I1 S k Q p hkS : ℝ)
          ≤ (p : ℝ) ^ (2 * (S - k)) *
              (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := h1
        _ ≤ (p : ℝ) ^ (2 * (S - k)) * ((Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) *
              (p : ℝ) ^ (k * (k - 1) / 2) * J (S - k) k (1 + Q / M)) :=
            mul_le_mul_of_nonneg_left hsupR hp0
        _ ≤ (Y : ℝ) ^ (2 * (S - k)) * ((Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) *
              (Y : ℝ) ^ (k * (k - 1) / 2) * J (S - k) k (1 + Q / M)) := by
            have hAB : (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) *
                J (S - k) k (1 + Q / M) ≤
                (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * (Y : ℝ) ^ (k * (k - 1) / 2) *
                J (S - k) k (1 + Q / M) := by
              refine mul_le_mul_of_nonneg_right ?_ hD0
              exact mul_le_mul_of_nonneg_left hp3 (by positivity)
            refine mul_le_mul hp2 hAB ?_ ?_
            · exact mul_nonneg (mul_nonneg (mul_nonneg hB0 hA0) (by positivity)) hD0
            · positivity
        _ = (Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) * (Q : ℝ) ^ k *
              ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M) := by ring
    set T : ℝ := ∑ p ∈ P, (I1 S k Q p hkS : ℝ) with hTdef
    set cst : ℝ := (Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) * (Q : ℝ) ^ k *
        ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M) with hcstdef
    have hSum : T ≤ (P.card : ℝ) * cst := by
      rw [hTdef, hcstdef]
      calc ∑ p ∈ P, (I1 S k Q p hkS : ℝ) ≤ ∑ _p ∈ P,
            ((Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) * (Q : ℝ) ^ k *
              ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M)) :=
            Finset.sum_le_sum hI1b
        _ = (P.card : ℝ) * ((Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) *
              (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hS1b : S1 ≤ (P.card : ℝ) * T := by
      rw [hTdef]
      exact S1_le_I1 S k Q M hk hkS hQn P hPp hPlb hPc'
    have hcst0 : 0 ≤ cst := by
      rw [hcstdef]
      have h4 : (0 : ℝ) ≤ J (S - k) k (1 + Q / M) := by rw [J_eq_solSet]; positivity
      positivity
    have hcard0 : (0 : ℝ) ≤ (P.card : ℝ) := by positivity
    have hPT : (P.card : ℝ) * T ≤ (P.card : ℝ) * ((P.card : ℝ) * cst) :=
      mul_le_mul_of_nonneg_left hSum hcard0
    have hS1c : S1 ≤ (P.card : ℝ) ^ 2 * cst := by
      calc S1 ≤ (P.card : ℝ) * T := hS1b
        _ ≤ (P.card : ℝ) * ((P.card : ℝ) * cst) := hPT
        _ = (P.card : ℝ) ^ 2 * cst := by ring
    have hB : J S k Q ≤ 4 * ((k.factorial : ℕ) : ℝ) * (P.card : ℝ) ^ 2 *
        (Y : ℝ) ^ (2 * (S - k) + k * (k - 1) / 2) * (Q : ℝ) ^ k *
          J (S - k) k (1 + Q / M) := by
      have hJ4' : J S k Q ≤ 4 * S1 := hJ4
      have hstep1 : J S k Q ≤ 4 * ((P.card : ℝ) ^ 2 * cst) := by linarith
      have hcst_eq : cst = (Y : ℝ) ^ (2 * (S - k)) * (Y : ℝ) ^ (k * (k - 1) / 2) *
          (Q : ℝ) ^ k * ((k.factorial : ℕ) : ℝ) * J (S - k) k (1 + Q / M) := hcstdef
      rw [hcst_eq] at hstep1
      rw [pow_add]
      have hkv : 0 ≤ ((k.factorial : ℕ) : ℝ) := by positivity
      nlinarith [hstep1, hkv, hcard0, (by positivity : (0:ℝ) ≤ (Y:ℝ) ^ (2 * (S - k))),
        (by positivity : (0:ℝ) ≤ (Y:ℝ) ^ (k * (k - 1) / 2)),
        (by positivity : (0:ℝ) ≤ (Q:ℝ) ^ k),
        (by rw [J_eq_solSet]; positivity : (0:ℝ) ≤ J (S - k) k (1 + Q / M))]
    exact le_trans hB (by
      have hZ : (0:ℝ) ≤ (4 * (k:ℝ) ^ 4) ^ S := pow_nonneg (by positivity) S
      linarith [hRHS2, hZ])

end Work.BMF
