import Mathlib
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj
import Submission.Commons.Combinatorics.Ramsey.kvec_injective
import Submission.Commons.Combinatorics.Ramsey.exists_subspace_dense_slices
import Submission.Commons.Combinatorics.Ramsey.dkt_dichotomy

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

/-- Lifting a subspace of `[k]^M` to `[k+1]^M` commutes with `kvec`: for a word `z`,
`liftSub S (kvec z) = kvec (S z)`. -/
lemma liftSub_kvec (M m k : ℕ) (S : Subspace (Fin m) (Fin k) (Fin M)) (z : Fin m → Fin k) :
    liftSub M m k S (kvec z) = kvec (S z) := by
  funext i
  rcases h : S.idxFun i with a | e
  · simp [Subspace.apply_def, liftSub, kvec, h]
  · simp [Subspace.apply_def, liftSub, kvec, h]

theorem dkt_c5 (k : ℕ) (hk : 1 ≤ k)
    (hdhj : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ T : Finset (Fin n → Fin k), δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ l : _root_.Combinatorics.Line (Fin k) (Fin n), ∀ x : Fin k, l x ∈ T)
    (hl4 : ∀ (K m : ℕ), 2 ≤ K → 1 ≤ m → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Fin K),
        ε * (K : ℝ) ^ n < (A.card : ℝ) →
        ∃ l : ℕ, ∃ h : l < n, ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin K) (Fin l),
          ∀ x : Fin m → Fin K,
            ((A.card : ℝ) / (K : ℝ) ^ n - ε) * ((K : ℝ) ^ (n - l)) ≤
              (((Finset.univ : Finset (Fin (n - l) → Fin K)).filter
                 (fun y => Commons.Combinatorics.Ramsey.cat (le_of_lt h) (V x) y ∈ A)).card : ℝ))
    (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Fin (k+1)),
      δ * (((k+1 : ℕ) : ℝ)) ^ n ≤ (A.card : ℝ) →
      ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
        ∀ x : Fin m → Fin k, V (Commons.Combinatorics.Ramsey.kvec x) ∈ A := by
  classical
  obtain ⟨nD, hnD⟩ := mdhj_of_dhj k hk hdhj m hm (δ/2) (by linarith)
  set M : ℕ := max nD 1 with hMdef
  have hMD : nD ≤ M := le_max_left _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  obtain ⟨nL, hnL⟩ := hl4 (k+1) M (by omega) hM1 (δ/2) (by linarith) (by linarith)
  refine ⟨max nL 1, ?_⟩
  intro n hn A hA
  have hnLle : nL ≤ n := le_trans (le_max_left _ _) hn
  have hkp : (0:ℝ) < ((k+1:ℕ):ℝ) := by positivity
  have hXpos : (0:ℝ) < (((k+1:ℕ):ℝ))^n := pow_pos hkp n
  have hlt : (δ/2) * (((k+1:ℕ):ℝ))^n < (A.card : ℝ) := by
    have h2 : (δ/2) * (((k+1:ℕ):ℝ))^n < δ * (((k+1:ℕ):ℝ))^n := by
      nlinarith [hδ, hXpos]
    linarith
  obtain ⟨l, h, W, hW⟩ := hnL n hnLle A hlt
  have hYpos : (0:ℝ) < (((k+1:ℕ):ℝ))^(n-l) := pow_pos hkp _
  have hAden : δ ≤ (A.card:ℝ) / (((k+1:ℕ):ℝ))^n := (le_div_iff₀ hXpos).mpr hA
  -- slice lower bound
  have hslice : ∀ a : Fin M → Fin k,
      (δ/2) * (((k+1:ℕ):ℝ))^(n-l) ≤
        ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ) := by
    intro a
    have hw := hW (kvec a)
    have hstep : (δ/2) ≤ (A.card:ℝ) / (((k+1:ℕ):ℝ))^n - δ/2 := by linarith
    have key : (δ/2) * (((k+1:ℕ):ℝ))^(n-l) ≤
        ((A.card:ℝ) / (((k+1:ℕ):ℝ))^n - δ/2) * (((k+1:ℕ):ℝ))^(n-l) :=
      mul_le_mul_of_nonneg_right hstep (le_of_lt hYpos)
    linarith [key, hw]
  -- double counting (Fubini)
  have hfub : (∑ a : Fin M → Fin k,
        ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
          cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ))
      = ∑ y : Fin (n-l) → Fin (k+1),
        ((Finset.univ.filter (fun a : Fin M → Fin k =>
          cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ) := by
    simp only [cast_card_filter_univ]
    exact Finset.sum_comm
  have hcardk : ((Fintype.card (Fin M → Fin k) : ℕ) : ℝ) = (k:ℝ)^M := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    push_cast
    ring
  have hcardk1 : ((Fintype.card (Fin (n-l) → Fin (k+1)) : ℕ) : ℝ) = ((k+1:ℕ):ℝ)^(n-l) := by
    rw [Fintype.card_pi_const, Fintype.card_fin]
    push_cast
    ring
  have hsum_ge : (k:ℝ)^M * ((δ/2) * (((k+1:ℕ):ℝ))^(n-l))
      ≤ ∑ y : Fin (n-l) → Fin (k+1),
        ((Finset.univ.filter (fun a : Fin M → Fin k =>
          cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ) := by
    rw [← hfub]
    have h1 : (∑ a : Fin M → Fin k, (δ/2) * (((k+1:ℕ):ℝ))^(n-l))
        ≤ ∑ a : Fin M → Fin k,
          ((Finset.univ.filter (fun y : Fin (n-l) → Fin (k+1) =>
            cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ) :=
      Finset.sum_le_sum (fun a _ => hslice a)
    have hconst : (∑ a : Fin M → Fin k, (δ/2) * (((k+1:ℕ):ℝ))^(n-l))
        = ((Fintype.card (Fin M → Fin k) : ℕ) : ℝ) * ((δ/2) * (((k+1:ℕ):ℝ))^(n-l)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hconst, hcardk] at h1
    exact h1
  -- pigeonhole
  have hex : ∃ y0 : Fin (n-l) → Fin (k+1),
      (δ/2) * (k:ℝ)^M ≤
        ((Finset.univ.filter (fun a : Fin M → Fin k =>
          cat (le_of_lt h) (W (kvec a)) y0 ∈ A)).card : ℝ) := by
    by_contra hno
    simp only [not_exists, not_le] at hno
    have hnonempty : (Finset.univ : Finset (Fin (n-l) → Fin (k+1))).Nonempty :=
      ⟨fun _ => ⟨0, Nat.succ_pos k⟩, Finset.mem_univ _⟩
    have hsum_lt : (∑ y : Fin (n-l) → Fin (k+1),
          ((Finset.univ.filter (fun a : Fin M → Fin k =>
            cat (le_of_lt h) (W (kvec a)) y ∈ A)).card : ℝ))
        < ∑ _y : Fin (n-l) → Fin (k+1), ((δ/2) * (k:ℝ)^M) :=
      Finset.sum_lt_sum_of_nonempty hnonempty (fun y _ => hno y)
    have hsum_const2 : (∑ _y : Fin (n-l) → Fin (k+1), ((δ/2) * (k:ℝ)^M))
        = ((k+1:ℕ):ℝ)^(n-l) * ((δ/2) * (k:ℝ)^M) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardk1]
    rw [hsum_const2] at hsum_lt
    have heq : (k:ℝ)^M * ((δ/2) * (((k+1:ℕ):ℝ))^(n-l))
        = ((k+1:ℕ):ℝ)^(n-l) * ((δ/2) * (k:ℝ)^M) := by ring
    linarith [hsum_ge, hsum_lt, heq]
  obtain ⟨y0, hy0⟩ := hex
  obtain ⟨Vt, hVt⟩ := hnD M hMD
    (Finset.univ.filter (fun a : Fin M → Fin k =>
      cat (le_of_lt h) (W (kvec a)) y0 ∈ A)) hy0
  refine ⟨extendSub m k l n (compSub W (liftSub M m k Vt)) (le_of_lt h) y0, ?_⟩
  intro x
  have hU : (compSub W (liftSub M m k Vt)) (kvec x) = W (kvec (Vt x)) := by
    rw [compSub_apply, liftSub_kvec]
  have hV : (extendSub m k l n (compSub W (liftSub M m k Vt)) (le_of_lt h) y0) (kvec x)
      = cat (le_of_lt h) (W (kvec (Vt x))) y0 := by
    rw [extendSub_apply, hU]
  rw [hV]
  exact (Finset.mem_filter.mp (hVt x)).2

end

end Commons.Combinatorics.Ramsey
