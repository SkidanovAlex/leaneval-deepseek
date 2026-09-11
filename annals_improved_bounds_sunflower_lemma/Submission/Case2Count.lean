import Mathlib
import Submission.FixedUDefs

/-!
# Case-2 V-count (Markov bound via spreadness)

Context: `S` k-uniform over ground `X`, `U ⊆ X`, `V` random `v`-subset of
`X\U`.  Fix a member `A0 ∈ S`, set `s := |χ(A0,U)|`, and fix a `t`-subset
`C0 ⊆ χ(A0,U)`.  Write `R := χ(A0,U)`, `φ := φ(s,t) =
r^k·(ρv/n)^s·(vr/n)^{-t}` with `n := |X|`.

We bound the number of `V ∈ 𝒱` (`:= cardSubsets (X\U) v`) for which
  `φ < |τ(C0, V ∪ R, s)|`,
where `τ(C0, B0, s) := { A' ∈ S : C0 ⊆ χ(A',U) ⊆ B0 ∧ |χ(A',U)| = s }`.

The file contains the self-contained helper lemmas first, and then the
theorem `case2_Vcount` (Markov bound via spreadness).
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-! ## binomial-ratio helpers (reals) -/

lemma case2cv_choose_succ_mul (n k : ℕ) :
    (n + 1).choose (k + 1) * (k + 1) = n.choose k * (n + 1) := by
  simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k).symm

lemma case2cv_choose_step_le_ratio {N v i : ℕ} (hi : i < v) (hv : v ≤ N) :
    (N - i - 1).choose (v - i - 1) * ((N : ℝ) / (v : ℝ)) ≤ (N - i).choose (v - i) := by
  let n : ℕ := N - i - 1
  let k : ℕ := v - i - 1
  have hn0 : N - i - 1 = n := by dsimp [n]
  have hk0 : v - i - 1 = k := by dsimp [k]
  have hn : N - i = n + 1 := by dsimp [n]; omega
  have hk : v - i = k + 1 := by dsimp [k]; omega
  rw [hn0, hk0, hn, hk]
  have hidR : ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      (n.choose k : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (case2cv_choose_succ_mul n k)
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hnonneg : 0 ≤ (n.choose k : ℝ) := by positivity
  have hEq : ((n + 1).choose (k + 1) : ℝ) =
      (n.choose k : ℝ) * ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    field_simp [ne_of_gt hkpos]
    linarith
  have hnum : (N : ℝ) * ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (v : ℝ) := by
    have hk1n : (k + 1 : ℕ) = v - i := by dsimp [k]; omega
    have hn1n : (n + 1 : ℕ) = N - i := by dsimp [n]; omega
    have hiN : i ≤ N := by omega
    have hiV : i ≤ v := by omega
    rw [hk1n, hn1n, Nat.cast_sub hiN, Nat.cast_sub hiV]
    have hvR : (v : ℝ) ≤ (N : ℝ) := by exact_mod_cast hv
    have hiR : 0 ≤ (i : ℝ) := by positivity
    have hmon : (v : ℝ) * (i : ℝ) ≤ (N : ℝ) * (i : ℝ) := mul_le_mul_of_nonneg_right hvR hiR
    nlinarith
  have hvR0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
  have hratio : (N : ℝ) / (v : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hvR0 hkpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  calc
    (n.choose k : ℝ) * ((N : ℝ) / (v : ℝ)) ≤ ((n + 1).choose (k + 1) : ℝ) := by
      calc
        (n.choose k : ℝ) * ((N : ℝ) / (v : ℝ)) ≤ (n.choose k : ℝ) * (((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio hnonneg
        _ = (n.choose k : ℝ) * ((n + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by ring
        _ = ((n + 1).choose (k + 1) : ℝ) := hEq.symm

lemma case2cv_choose_sdiff_ratio {N v d : ℕ} (hd : d ≤ v) (hv0 : 0 < v) (hv : v ≤ N) :
    (N.choose v : ℝ) ≥ (N - d).choose (v - d) * (((N : ℝ) / (v : ℝ)) ^ d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd' : d ≤ v := by omega
      have hstep := case2cv_choose_step_le_ratio (N := N) (v := v) (i := d) (by omega) hv
      have hpow0 : 0 ≤ ((N : ℝ) / (v : ℝ)) ^ d := by
        exact pow_nonneg (div_nonneg (by positivity : 0 ≤ (N : ℝ)) (le_of_lt (by exact_mod_cast hv0 : (0:ℝ) < (v:ℝ)))) d
      calc
        (N - (d + 1)).choose (v - (d + 1)) * (((N : ℝ) / (v : ℝ)) ^ (d + 1))
            = (N - d - 1).choose (v - d - 1) * (((N : ℝ) / (v : ℝ)) ^ d) * ((N : ℝ) / (v : ℝ)) := by
              have h1 : N - (d + 1) = N - d - 1 := by omega
              have h2 : v - (d + 1) = v - d - 1 := by omega
              rw [h1, h2, pow_succ]
              ring
        _ ≤ (N - d).choose (v - d) * (((N : ℝ) / (v : ℝ)) ^ d) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul_of_nonneg_right hstep hpow0)
        _ ≤ (N.choose v : ℝ) := by
              exact ih hd'

lemma case2cv_choose_sdiff_ratio_down {N v d : ℕ} (hd : d ≤ v) (hv0 : 0 < v) (hv : v ≤ N) :
    ((N - d).choose (v - d) : ℝ) ≤ (N.choose v : ℝ) * (((v : ℝ) / (N : ℝ)) ^ d) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv0
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hmain := case2cv_choose_sdiff_ratio (N := N) (v := v) (d := d) hd hv0 hv
  have hpow : ((N : ℝ) / (v : ℝ)) ^ d * ((v : ℝ) / (N : ℝ)) ^ d = 1 := by
    rw [← mul_pow]
    field_simp [ne_of_gt hvR, ne_of_gt hNpos]
    ring
  calc
    ((N - d).choose (v - d) : ℝ)
        = ((N - d).choose (v - d) : ℝ) * (((N : ℝ) / (v : ℝ)) ^ d * ((v : ℝ) / (N : ℝ)) ^ d) := by rw [hpow, mul_one]
    _ = (((N - d).choose (v - d) : ℝ) * (((N : ℝ) / (v : ℝ)) ^ d)) * ((v : ℝ) / (N : ℝ)) ^ d := by ring
    _ ≤ (N.choose v : ℝ) * ((v : ℝ) / (N : ℝ)) ^ d := by
        exact mul_le_mul_of_nonneg_right hmain (by positivity)

/-- number of v-subsets of X containing a fixed subset D (real bound) -/
lemma case2cv_count_subset_le {X D : Finset α} {v : ℕ}
    (hD : D ⊆ X) (hv : 0 < v) (hvX : v ≤ X.card) :
    (((cardSubsets X v).filter (fun V => D ⊆ V)).card : ℝ) ≤
      (X.card.choose v : ℝ) * (((v : ℝ) / (X.card : ℝ)) ^ D.card) := by
  classical
  by_cases hvd : v < D.card
  · have hzero : ((cardSubsets X v).filter (fun V => D ⊆ V)).card = 0 := by
      rw [Finset.card_filter]
      apply Finset.sum_eq_zero
      intro V hV
      have hVm : V ∈ cardSubsets X v := hV
      have hvc : V.card = v := (Finset.mem_powersetCard.mp hVm).2
      by_cases hDV : D ⊆ V
      · exfalso
        have hle : D.card ≤ V.card := Finset.card_le_card hDV
        omega
      · simp [hDV]
    rw [hzero]
    have hpos : 0 ≤ (X.card.choose v : ℝ) := by positivity
    have hpos1 : 0 ≤ (v : ℝ) := by positivity
    have hpos2 : 0 ≤ (X.card : ℝ) := by positivity
    simpa using (mul_nonneg hpos (pow_nonneg (div_nonneg hpos1 hpos2) D.card))
  · have hd : D.card ≤ v := by omega
    let T : Finset (Finset α) := cardSubsets X v
    let F : Finset (Finset α) := T.filter (fun V => D ⊆ V)
    let G : Finset (Finset α) := cardSubsets (X \ D) (v - D.card)
    have hmap : ∀ V ∈ F, V \ D ∈ G := by
      intro V hV
      have hVm : V ∈ cardSubsets X v := (Finset.mem_filter.mp hV).1
      have hDV : D ⊆ V := (Finset.mem_filter.mp hV).2
      have hVX : V ⊆ X := (Finset.mem_powersetCard.mp hVm).1
      have hVc : V.card = v := (Finset.mem_powersetCard.mp hVm).2
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro x hx
        have hx1 : x ∈ V := (Finset.mem_sdiff.mp hx).1
        have hx2 : x ∉ D := (Finset.mem_sdiff.mp hx).2
        exact Finset.mem_sdiff.mpr ⟨hVX hx1, hx2⟩
      · rw [card_sdiff_of_subset' hDV, hVc]
    have hinj : Set.InjOn (fun V : Finset α => V \ D) (↑F : Set (Finset α)) := by
      intro V hV W hW hEq
      have hEq' : V \ D = W \ D := by simpa using hEq
      apply Finset.ext
      intro x
      have hDV : D ⊆ V := (Finset.mem_filter.mp hV).2
      have hDW : D ⊆ W := (Finset.mem_filter.mp hW).2
      constructor
      · intro hx
        by_cases hxD : x ∈ D
        · exact hDW hxD
        · have hxV' : x ∈ V \ D := Finset.mem_sdiff.mpr ⟨hx, hxD⟩
          have hxW' : x ∈ W \ D := by rw [← hEq']; exact hxV'
          exact (Finset.mem_sdiff.mp hxW').1
      · intro hx
        by_cases hxD : x ∈ D
        · exact hDV hxD
        · have hxW' : x ∈ W \ D := Finset.mem_sdiff.mpr ⟨hx, hxD⟩
          have hxV' : x ∈ V \ D := by rw [hEq']; exact hxW'
          exact (Finset.mem_sdiff.mp hxV').1
    have hcard : F.card ≤ G.card := by
      exact Finset.card_le_card_of_injOn (fun V : Finset α => V \ D) hmap hinj
    have hmain := case2cv_choose_sdiff_ratio_down (N := X.card) (v := v) (d := D.card) hd hv hvX
    calc
      (F.card : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hcard
      _ = (((X \ D).card.choose (v - D.card) : ℕ) : ℝ) := by
          rw [card_cardSubsets]
      _ = ((X.card - D.card).choose (v - D.card) : ℝ) := by rw [card_sdiff_of_subset' hD]
      _ ≤ (X.card.choose v : ℝ) * (((v : ℝ) / (X.card : ℝ)) ^ D.card) := hmain

/-! ## powerset sum `Σ_E x^|E| = (1+x)^n` -/

lemma case2cv_sum_powerset_pow (X : Finset α) (x : ℝ) :
    (∑ E ∈ X.powerset, x ^ E.card) = (1 + x) ^ X.card := by
  classical
  have hsplit := Finset.sum_powerset X (fun E : Finset α => x ^ E.card)
  have h1 : (∑ j ∈ Finset.range (X.card + 1), ∑ E ∈ X.powersetCard j, x ^ E.card)
      = (∑ j ∈ Finset.range (X.card + 1), (X.card.choose j : ℝ) * x ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hinner : (∑ E ∈ X.powersetCard j, x ^ E.card) = (X.card.choose j : ℝ) * x ^ j := by
      calc
        (∑ E ∈ X.powersetCard j, x ^ E.card) = (∑ E ∈ X.powersetCard j, x ^ j) := by
          apply Finset.sum_congr rfl
          intro E hE
          have hc : E.card = j := (Finset.mem_powersetCard.mp hE).2
          rw [hc]
        _ = (X.card.choose j : ℝ) * x ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
    exact hinner
  have h2 : (1 + x) ^ X.card = (∑ j ∈ Finset.range (X.card + 1), (X.card.choose j : ℝ) * x ^ j) := by
    have h3 : (1 + x) ^ X.card = (x + 1) ^ X.card := by rw [add_comm]
    rw [h3, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    have : 1 ^ (X.card - j) = (1 : ℝ) := by rw [one_pow]
    simp [this, mul_comm, mul_left_comm, mul_assoc]
  calc
    (∑ E ∈ X.powerset, x ^ E.card) = (∑ j ∈ Finset.range (X.card + 1), ∑ E ∈ X.powersetCard j, x ^ E.card) := hsplit
    _ = (∑ j ∈ Finset.range (X.card + 1), (X.card.choose j : ℝ) * x ^ j) := h1
    _ = (1 + x) ^ X.card := h2.symm

/-! ## real power identities around `φ = r^k (ρ v/n)^s (v r/n)^{-t}` -/

lemma case2cv_sub1 (v n : ℝ) (s t : ℕ) (hts : t ≤ s) (hv : v ≠ 0) (hn : n ≠ 0) :
    (v / n) ^ t * ((v / n) ^ s)⁻¹ = (n / v) ^ (s - t) := by
  have hpow1 : (v / n) ^ s = (v / n) ^ t * (v / n) ^ (s - t) := by
    calc
      (v / n) ^ s = (v / n) ^ (t + (s - t)) := by congr 1; omega
      _ = (v / n) ^ t * (v / n) ^ (s - t) := by rw [pow_add]
  rw [hpow1, mul_inv]
  have hne : (v / n) ^ t ≠ 0 := pow_ne_zero t (by
    apply div_ne_zero hv hn)
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rw [← inv_pow]
  congr 1
  field_simp [hv, hn]

lemma case2cv_rho_div (rho v n : ℝ) (s t : ℕ) (hts : t ≤ s)
    (hrho : rho ≠ 0) (hv : v ≠ 0) (hn : n ≠ 0) :
    (v / n) ^ t / (rho ^ s * (v / n) ^ s) = (rho ^ s)⁻¹ * (n / v) ^ (s - t) := by
  have hsub := case2cv_sub1 (v := v) (n := n) (s := s) (t := t) hts hv hn
  calc
    (v / n) ^ t / (rho ^ s * (v / n) ^ s)
        = (v / n) ^ t * ((rho ^ s * (v / n) ^ s)⁻¹) := by rw [div_eq_mul_inv]
    _ = (v / n) ^ t * ((rho ^ s)⁻¹ * ((v / n) ^ s)⁻¹) := by rw [mul_inv]
    _ = (rho ^ s)⁻¹ * ((v / n) ^ t * ((v / n) ^ s)⁻¹) := by ring
    _ = (rho ^ s)⁻¹ * (n / v) ^ (s - t) := by rw [hsub]

lemma case2cv_cancel_r (r rho v n N : ℝ) (k s t : ℕ)
    (hr : r ≠ 0) (hrho : rho ≠ 0) (hv : v ≠ 0) (hn : n ≠ 0) (hN : N ≠ 0)
    (htk : t ≤ k) :
    (v * r / n) ^ t * r ^ (k - t) * (v / N) ^ (s - t) /
      (r ^ k * (rho * v / n) ^ s)
    = (v / n) ^ t * (v / N) ^ (s - t) / (rho ^ s * (v / n) ^ s) := by
  have hvr : v * r / n = v / n * r := by ring
  have hrv : rho * v / n = rho * (v / n) := by ring
  have hrr : r ^ t * r ^ (k - t) = r ^ k := by
    rw [mul_comm, ← pow_add]
    rw [Nat.sub_add_cancel htk]
  rw [hvr, hrv, mul_pow, mul_pow]
  rw [← hrr]
  field_simp [hr, hrho, hv, hn]

/-- `φ^{-1}·r^{k-t}·(v/N)^{s-t} = ρ^{-s}·(n/N)^{s-t}` for `φ = r^k(ρv/n)^s/(vr/n)^t` -/
lemma case2cv_phi_mul (r rho v n N : ℝ) (k s t : ℕ)
    (hr : 0 < r) (hrho : 0 < rho) (hv : 0 < v) (hn : 0 < n) (hN : 0 < N)
    (hts : t ≤ s) (htk : t ≤ k) :
    ((r ^ k * ((rho * v / n) ^ s) / ((v * r / n) ^ t))⁻¹) *
      r ^ (k - t) * (v / N) ^ (s - t)
    = (rho ^ s)⁻¹ * (n / N) ^ (s - t) := by
  have hφ1 : ((r ^ k * ((rho * v / n) ^ s) / ((v * r / n) ^ t))⁻¹) =
      (v * r / n) ^ t / (r ^ k * (rho * v / n) ^ s) := by
    field_simp
  have hcr := case2cv_cancel_r (r := r) (rho := rho) (v := v) (n := n) (N := N) (k := k) (s := s) (t := t)
    (ne_of_gt hr) (ne_of_gt hrho) (ne_of_gt hv) (ne_of_gt hn) (ne_of_gt hN) htk
  have hrd := case2cv_rho_div (rho := rho) (v := v) (n := n) (s := s) (t := t) hts
    (ne_of_gt hrho) (ne_of_gt hv) (ne_of_gt hn)
  calc
    ((r ^ k * ((rho * v / n) ^ s) / ((v * r / n) ^ t))⁻¹) *
      r ^ (k - t) * (v / N) ^ (s - t)
        = (v * r / n) ^ t * r ^ (k - t) * (v / N) ^ (s - t) /
            (r ^ k * (rho * v / n) ^ s) := by
            rw [hφ1]
            ring
    _ = (v / n) ^ t * (v / N) ^ (s - t) / (rho ^ s * (v / n) ^ s) := hcr
    _ = (v / N) ^ (s - t) * ((v / n) ^ t / (rho ^ s * (v / n) ^ s)) := by ring
    _ = (v / N) ^ (s - t) * ((rho ^ s)⁻¹ * (n / v) ^ (s - t)) := by rw [hrd]
    _ = (rho ^ s)⁻¹ * ((v / N) ^ (s - t) * (n / v) ^ (s - t)) := by ring
    _ = (rho ^ s)⁻¹ * (n / N) ^ (s - t) := by
        have hC : (v / N) * (n / v) = n / N := by field_simp
        rw [← mul_pow]
        rw [hC]

/-! ## factorization of spreadness terms by `(N/(v r))^j` -/

lemma case2cv_pow_factor (r v N x : ℝ) (k' s' : ℕ)
    (hr : 0 < r) (hv : 0 < v) (hN : 0 < N) (hx : r * (v / N) * x = 1) :
    ∀ m, m ≤ s' → m ≤ k' →
      r ^ (k' - m) * (v / N) ^ (s' - m) = r ^ k' * (v / N) ^ s' * x ^ m := by
  intro m
  induction m with
  | zero =>
      intro hs' hk'
      simp
  | succ m ih =>
      intro hs' hk'
      have hs'm : m ≤ s' := by omega
      have hk'm : m ≤ k' := by omega
      have hmain' : r * v * x = N := by
        calc
          r * v * x = (r * (v / N) * x) * N := by field_simp [hN]
          _ = 1 * N := by rw [hx]
          _ = N := by ring
      have hstep : r ^ (k' - m) * (v / N) ^ (s' - m) * x
          = r ^ (k' - (m + 1)) * (v / N) ^ (s' - (m + 1)) := by
        have he1 : k' - m = (k' - (m + 1)) + 1 := by omega
        have he2 : s' - m = (s' - (m + 1)) + 1 := by omega
        rw [he1, he2, pow_add, pow_add]
        field_simp [hv, hN]
        exact hmain'
      calc
        r ^ (k' - (m + 1)) * (v / N) ^ (s' - (m + 1))
            = r ^ (k' - m) * (v / N) ^ (s' - m) * x := hstep.symm
        _ = (r ^ k' * (v / N) ^ s' * x ^ m) * x := by
            rw [ih hs'm hk'm]
        _ = r ^ k' * (v / N) ^ s' * x ^ (m + 1) := by
            rw [pow_succ]
            ring

/-- `r^{k-b}(v/N)^{s-b} = r^{k-t}(v/N)^{s-t}·(N/(v r))^{b-t}` for `t ≤ b ≤ s ≤ k` -/
lemma case2cv_term_b {r v N : ℝ} {k s t b : ℕ}
    (htb : t ≤ b) (hbs : b ≤ s) (hsk : s ≤ k)
    (hr : 0 < r) (hv : 0 < v) (hN : 0 < N) :
    r ^ (k - b) * (v / N) ^ (s - b)
      = r ^ (k - t) * (v / N) ^ (s - t) * (N / (v * r)) ^ (b - t) := by
  have hx : r * (v / N) * (N / (v * r)) = 1 := by
    field_simp [ne_of_gt hr, ne_of_gt hv, ne_of_gt hN]
  have hbt : b - t ≤ s - t := by omega
  have hbk : b - t ≤ k - t := by omega
  have hpf := case2cv_pow_factor (r := r) (v := v) (N := N) (x := N / (v * r))
    (k' := k - t) (s' := s - t) hr hv hN hx (b - t) hbt hbk
  have he1 : (k - t) - (b - t) = k - b := by omega
  have he2 : (s - t) - (b - t) = s - b := by omega
  rw [he1, he2] at hpf
  exact hpf

/-! ## generic Finset counting helpers -/

lemma case2cv_sdiff_subset_iff {χ R V : Finset α} : χ ⊆ V ∪ R ↔ χ \ R ⊆ V := by
  constructor
  · intro h x hx
    have hxχ : x ∈ χ := (Finset.mem_sdiff.mp hx).1
    have hxR : x ∉ R := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (h hxχ) with hxV | hxR2
    · exact hxV
    · exact False.elim (hxR hxR2)
  · intro h x hx
    by_cases hxR : x ∈ R
    · exact Finset.mem_union_right V hxR
    · exact Finset.mem_union_left R (h (Finset.mem_sdiff.mpr ⟨hx, hxR⟩))

lemma case2cv_card_eq_indicator {β : Type*} (s : Finset β) (p : β → Prop) [DecidablePred p] :
    ((s.filter p).card : ℝ) = ∑ i ∈ s, if p i then (1 : ℝ) else 0 := by
  rw [Finset.card_filter]
  simp [Nat.cast_sum]

/-- sum over `B ⊆ R, C0 ⊆ B` of `x^(|B|-|C0|)` equals sum over subsets `E ⊆ R\C0` of `x^|E|` -/
lemma case2cv_BB_powerset_sum (R C0 : Finset α) (x : ℝ) (hC0R : C0 ⊆ R) :
    (∑ B ∈ ((R.powerset).filter (fun B : Finset α => C0 ⊆ B)), x ^ (B.card - C0.card))
      = ∑ E ∈ (R \ C0).powerset, x ^ E.card := by
  classical
  refine Finset.sum_bij (fun B hB => B \ C0) ?hin ?hinj ?hsurj ?h
  · intro B hB
    rw [Finset.mem_powerset]
    intro x0 hx0
    have hBR : B ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have hxB : x0 ∈ B := (Finset.mem_sdiff.mp hx0).1
    have hxR : x0 ∈ R := hBR hxB
    have hxC : x0 ∉ C0 := (Finset.mem_sdiff.mp hx0).2
    exact Finset.mem_sdiff.mpr ⟨hxR, hxC⟩
  · intro B1 hB1 B2 hB2 hEq
    have hC0B1 : C0 ⊆ B1 := (Finset.mem_filter.mp hB1).2
    have hC0B2 : C0 ⊆ B2 := (Finset.mem_filter.mp hB2).2
    apply Finset.ext
    intro x0
    constructor
    · intro hx
      by_cases hxC : x0 ∈ C0
      · exact hC0B2 hxC
      · have h1 : x0 ∈ B1 \ C0 := Finset.mem_sdiff.mpr ⟨hx, hxC⟩
        have h2 : x0 ∈ B2 \ C0 := by
          have hEq' : B1 \ C0 = B2 \ C0 := by simpa using hEq
          rwa [← hEq']
        exact (Finset.mem_sdiff.mp h2).1
    · intro hx
      by_cases hxC : x0 ∈ C0
      · exact hC0B1 hxC
      · have h1 : x0 ∈ B2 \ C0 := Finset.mem_sdiff.mpr ⟨hx, hxC⟩
        have h2 : x0 ∈ B1 \ C0 := by
          have hEq' : B1 \ C0 = B2 \ C0 := by simpa using hEq
          rwa [hEq']
        exact (Finset.mem_sdiff.mp h2).1
  · intro E hE
    have hEsub : E ⊆ R \ C0 := Finset.mem_powerset.mp hE
    have hC0B : C0 ⊆ E ∪ C0 := by simp
    have hsub : E ∪ C0 ⊆ R := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxE | hxC
      · exact (Finset.mem_sdiff.mp (hEsub hxE)).1
      · exact hC0R hxC
    have hmemBB : E ∪ C0 ∈ (R.powerset).filter (fun B : Finset α => C0 ⊆ B) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hsub, hC0B⟩
    refine ⟨E ∪ C0, hmemBB, ?_⟩
    ext x
    constructor
    · intro hx
      have hxE : x ∈ E ∪ C0 := (Finset.mem_sdiff.mp hx).1
      have hxC : x ∉ C0 := (Finset.mem_sdiff.mp hx).2
      rcases Finset.mem_union.mp hxE with hxE2 | hxC2
      · exact hxE2
      · exact False.elim (hxC hxC2)
    · intro hx
      have hxC : x ∉ C0 := by
        intro hxC
        have hxsub : x ∈ R \ C0 := hEsub hx
        exact (Finset.mem_sdiff.mp hxsub).2 hxC
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left C0 hx, hxC⟩
  · intro B hB
    have hC0B : C0 ⊆ B := (Finset.mem_filter.mp hB).2
    have hcard : (B \ C0).card = B.card - C0.card := by
      rw [Finset.card_sdiff (s := C0) (t := B)]
      have hC0B' : C0 ∩ B = C0 := by
        apply Finset.ext
        intro x
        constructor
        · intro hx; exact (Finset.mem_inter.mp hx).1
        · intro hx; exact Finset.mem_inter.mpr ⟨hx, hC0B hx⟩
      rw [hC0B']
    rw [hcard]


/-- the core V-sum bound for case 2 (Markov needs only this plus division by φ) -/
lemma case2cv_sumtau_le {X : Finset α} {S : Finset (Finset α)} {U A0 C0 : Finset α}
    {v k s t : ℕ} {r : ℝ}
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (huni : ∀ A ∈ S, A.card = k)
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X) (hM : A0 ∈ S)
    (hs : (chi S U A0).card = s) (hC : C0 ⊆ chi S U A0) (htC : C0.card = t)
    (ht1 : 1 ≤ t) (hv : 0 < v) (hn : 0 < X.card) (hr1 : 1 ≤ r)
    (hvn : v ≤ (X \ U).card) :
    (∑ V ∈ cardSubsets (X \ U) v, ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ))
      ≤ (cardSubsets (X \ U) v).card *
          (r ^ (k - t)) * (((v : ℝ) / ((X \ U).card : ℝ)) ^ (s - t)) *
          (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r)) ^ (s - t) := by
  classical
  let R : Finset α := chi S U A0
  let VV : Finset (Finset α) := cardSubsets (X \ U) v
  let AA : Finset (Finset α) := S.filter (fun A' : Finset α => C0 ⊆ chi S U A' ∧ (chi S U A').card = s)
  let BB : Finset (Finset α) := (R.powerset).filter (fun B : Finset α => C0 ⊆ B)
  let q : ℝ := (v : ℝ) / ((X \ U).card : ℝ)
  let x : ℝ := ((X \ U).card : ℝ) / ((v : ℝ) * r)
  have hsR : R.card = s := by simpa [R] using hs
  have hts : t ≤ s := by
    have hle : C0.card ≤ (chi S U A0).card := Finset.card_le_card hC
    omega
  have hsk : s ≤ k := by
    have hc := chi_card_le_k'' (S:=S) (U:=U) (A:=A0) hM huni
    omega
  have htks : t ≤ k := le_trans hts hsk
  have hCne : C0.Nonempty := by
    have hcardpos : 0 < C0.card := by omega
    exact Finset.card_pos.mp hcardpos
  have hRsubX : R ⊆ X := by
    intro z hz
    have hzA0 : z ∈ A0 := chi_subset (S:=S) (U:=U) (A:=A0) hM hz
    exact hS A0 hM hzA0
  have hC0X : C0 ⊆ X := subset_trans hC hRsubX
  have hNpos : 0 < (X \ U).card := by omega
  have hNR : (0 : ℝ) < ((X \ U).card : ℝ) := by exact_mod_cast hNpos
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hrR : 0 < r := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (by positivity) (mul_nonneg (le_of_lt hvR) (le_of_lt hrR))
  have hR0 : (0 : ℝ) < (rho : ℝ) := by unfold rho; positivity
  -- for every V the tau-finset is AA-filtered by the V-extra condition
  have htau_eq : ∀ V ∈ VV, tau S U C0 (V ∪ R) s =
      (AA.filter (fun A' : Finset α => chi S U A' ⊆ V ∪ R)) := by
    intro V hV
    apply Finset.ext
    intro A'
    by_cases hA : A' ∈ S
    · simp [tau, AA, hA]
      tauto
    · simp [tau, AA, hA]
  -- double count
  have hDC :
      (∑ V ∈ VV, ((tau S U C0 (V ∪ R) s).card : ℝ))
        = ∑ A' ∈ AA, (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)) := by
    calc
      (∑ V ∈ VV, ((tau S U C0 (V ∪ R) s).card : ℝ))
          = ∑ V ∈ VV, (((AA.filter (fun A' : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro V hV
            rw [htau_eq V hV]
      _ = ∑ V ∈ VV, ∑ A' ∈ AA, (if chi S U A' ⊆ V ∪ R then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro V hV
            rw [case2cv_card_eq_indicator (s := AA) (p := fun A' : Finset α => chi S U A' ⊆ V ∪ R)]
      _ = ∑ A' ∈ AA, ∑ V ∈ VV, (if chi S U A' ⊆ V ∪ R then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ A' ∈ AA, (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)) := by
            apply Finset.sum_congr rfl
            intro A' hA'
            rw [← case2cv_card_eq_indicator (s := VV) (p := fun V : Finset α => chi S U A' ⊆ V ∪ R)]
  -- per A' counting bound
  have hcountA : ∀ A' ∈ AA,
      (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ) ≤
        (((X \ U).card.choose v : ℕ) : ℝ) * q ^ ((chi S U A' \ R).card)) := by
    intro A' hA'
    have hA'S : A' ∈ S := (Finset.mem_filter.mp hA').1
    have hχsub : chi S U A' ⊆ X \ U :=
      chi_subset_sdiff (S:=S) (X:=X) (U:=U) (A:=A') hA'S hU (hS A' hA'S)
    have hD : chi S U A' \ R ⊆ X \ U := by
      intro z hz
      exact hχsub (Finset.mem_sdiff.mp hz).1
    have hbnd := case2cv_count_subset_le (X := X \ U) (D := chi S U A' \ R) (v := v) hD hv hvn
    have hset' : VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R) =
        VV.filter (fun V : Finset α => chi S U A' \ R ⊆ V) := by
      apply Finset.filter_congr
      intro V hV
      exact case2cv_sdiff_subset_iff
    rw [hset']
    simpa [VV, q] using hbnd
  have hchoose : (((X \ U).card.choose v : ℕ) : ℝ) = (VV.card : ℝ) := by
    have hc : VV.card = (X \ U).card.choose v := by
      simpa [VV] using (card_cardSubsets (X := X \ U) (w := v))
    rw [hc]
  have hsumA : (∑ A' ∈ AA, (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)))
      ≤ (VV.card : ℝ) * (∑ A' ∈ AA, q ^ (chi S U A' \ R).card) := by
    calc
      (∑ A' ∈ AA, (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)))
          ≤ (∑ A' ∈ AA, (((X \ U).card.choose v : ℕ) : ℝ) * q ^ (chi S U A' \ R).card) := by
            exact Finset.sum_le_sum (fun A' hA' => hcountA A' hA')
      _ = (((X \ U).card.choose v : ℕ) : ℝ) * (∑ A' ∈ AA, q ^ (chi S U A' \ R).card) := by
            rw [← Finset.mul_sum]
      _ = (VV.card : ℝ) * (∑ A' ∈ AA, q ^ (chi S U A' \ R).card) := by rw [hchoose]
  -- exponent change per A': |χ\R| = s - |χ∩R|
  have hG0 : (∑ A' ∈ AA, q ^ (chi S U A' \ R).card)
      = ∑ A' ∈ AA, q ^ (s - (chi S U A' ∩ R).card) := by
    apply Finset.sum_congr rfl
    intro A' hA'
    have hA'S : A' ∈ S := (Finset.mem_filter.mp hA').1
    have hχs : (chi S U A').card = s := (Finset.mem_filter.mp hA').2.2
    have hmain := Finset.card_sdiff (s := R) (t := chi S U A')
    have hRχ : R ∩ chi S U A' = chi S U A' ∩ R := by rw [inter_comm]
    have hcard : (chi S U A' \ R).card = s - (chi S U A' ∩ R).card := by
      rw [hmain, hχs, hRχ]
    rw [hcard]
  -- every g(A') is in BB
  have hgmem : ∀ A' ∈ AA, chi S U A' ∩ R ∈ BB := by
    intro A' hA'
    have hC0χ : C0 ⊆ chi S U A' := (Finset.mem_filter.mp hA').2.1
    have hsub : chi S U A' ∩ R ⊆ R := Finset.inter_subset_right
    have hC0 : C0 ⊆ chi S U A' ∩ R := by
      intro z hz
      exact Finset.mem_inter.mpr ⟨hC0χ hz, hC hz⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_powerset]
      exact Finset.inter_subset_right
    · exact hC0
  -- fiber decomposition
  have hfiber_sum :
      (∑ A' ∈ AA, q ^ (s - (chi S U A' ∩ R).card))
        = ∑ B ∈ BB, q ^ (s - B.card) *
            ((AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card : ℝ) := by
    calc
      (∑ A' ∈ AA, q ^ (s - (chi S U A' ∩ R).card))
          = ∑ A' ∈ AA, ∑ B ∈ BB,
              (if chi S U A' ∩ R = B then q ^ (s - B.card) else 0) := by
            apply Finset.sum_congr rfl
            intro A' hA'
            rw [Finset.sum_eq_single (chi S U A' ∩ R)]
            · simp
            · intro B hB hBA
              by_cases h : chi S U A' ∩ R = B
              · exfalso; exact hBA h.symm
              · simp [h]
            · intro hnot
              exfalso
              exact hnot (hgmem A' hA')
      _ = ∑ B ∈ BB, q ^ (s - B.card) *
            (∑ A' ∈ AA, (if chi S U A' ∩ R = B then (1 : ℝ) else 0)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro B hB
            calc
              (∑ A' ∈ AA, (if chi S U A' ∩ R = B then q ^ (s - B.card) else 0))
                  = ∑ A' ∈ AA, q ^ (s - B.card) *
                      (if chi S U A' ∩ R = B then (1 : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro A' hA'
                    by_cases h : chi S U A' ∩ R = B <;> simp [h]
              _ = q ^ (s - B.card) * (∑ A' ∈ AA, (if chi S U A' ∩ R = B then (1 : ℝ) else 0)) := by
                    rw [Finset.mul_sum]
      _ = ∑ B ∈ BB, q ^ (s - B.card) *
            ((AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro B hB
            rw [← case2cv_card_eq_indicator (s := AA) (p := fun A' : Finset α => chi S U A' ∩ R = B)]
  -- spreadness bound on the fibers
  have hfiber_le : ∀ B ∈ BB,
      ((AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card : ℝ) ≤ r ^ (k - B.card) := by
    intro B hB
    have hBmem : B ∈ R.powerset := (Finset.mem_filter.mp hB).1
    have hBsubR : B ⊆ R := Finset.mem_powerset.mp hBmem
    have hC0B : C0 ⊆ B := (Finset.mem_filter.mp hB).2
    have hBne : B.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : 0 < C0.card := by omega
      have hle : C0.card ≤ B.card := Finset.card_le_card hC0B
      omega
    have hBsubX : B ⊆ X := subset_trans hBsubR hRsubX
    have hsub : AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)
        ⊆ S.filter (fun A : Finset α => B ⊆ A) := by
      intro A' hA'
      have hA'1 : A' ∈ AA := (Finset.mem_filter.mp hA').1
      have hA'S : A' ∈ S := (Finset.mem_filter.mp hA'1).1
      have hg : chi S U A' ∩ R = B := (Finset.mem_filter.mp hA').2
      have hBsubχ : B ⊆ chi S U A' := by
        rw [← hg]
        exact Finset.inter_subset_left
      exact Finset.mem_filter.mpr ⟨hA'S, subset_trans hBsubχ (chi_subset (S:=S) (U:=U) (A:=A') hA'S)⟩
    have hle : (AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card ≤
        (S.filter (fun A : Finset α => B ⊆ A)).card := Finset.card_le_card hsub
    have hsp := hspread B hBsubX hBne
    exact le_trans (by exact_mod_cast hle) hsp
  have hG1 :
      (∑ B ∈ BB, q ^ (s - B.card) * ((AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card : ℝ))
        ≤ ∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card) := by
    apply Finset.sum_le_sum
    intro B hB
    exact mul_le_mul_of_nonneg_left (hfiber_le B hB) (pow_nonneg hq0 (s - B.card))
  have hG : (∑ A' ∈ AA, q ^ (chi S U A' \ R).card)
      ≤ ∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card) := by
    calc
      (∑ A' ∈ AA, q ^ (chi S U A' \ R).card) = ∑ A' ∈ AA, q ^ (s - (chi S U A' ∩ R).card) := hG0
      _ = ∑ B ∈ BB, q ^ (s - B.card) * ((AA.filter (fun A' : Finset α => chi S U A' ∩ R = B)).card : ℝ) := hfiber_sum
      _ ≤ ∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card) := hG1
  -- sum over B via factorization
  have hfac : ∀ B ∈ BB,
      q ^ (s - B.card) * r ^ (k - B.card)
        = r ^ (k - t) * q ^ (s - t) * x ^ (B.card - t) := by
    intro B hB
    have hBmem : B ∈ R.powerset := (Finset.mem_filter.mp hB).1
    have hBsubR : B ⊆ R := Finset.mem_powerset.mp hBmem
    have hC0B : C0 ⊆ B := (Finset.mem_filter.mp hB).2
    have htb : t ≤ B.card := by
      have hle : C0.card ≤ B.card := Finset.card_le_card hC0B
      omega
    have hbs : B.card ≤ s := by
      have hle : B.card ≤ R.card := Finset.card_le_card hBsubR
      omega
    have hterm := case2cv_term_b (r := r) (v := (v : ℝ)) (N := ((X \ U).card : ℝ))
      (k := k) (s := s) (t := t) (b := B.card) htb hbs hsk hrR hvR hNR
    -- hterm : r^{k-b} * ((v:ℝ)/N)^{s-b} = r^{k-t} * q^{s-t} * x^{b-t}
    have hterm' : q ^ (s - B.card) * r ^ (k - B.card)
        = r ^ (k - t) * q ^ (s - t) * x ^ (B.card - t) := by
      have hmul : q ^ (s - B.card) * r ^ (k - B.card) = r ^ (k - B.card) * q ^ (s - B.card) := by ring
      rw [hmul]
      simpa [q, x] using hterm
    exact hterm'
  have hpowx : (∑ B ∈ BB, x ^ (B.card - t)) = (1 + x) ^ (s - t) := by
    have htc' : C0.card = t := htC
    have hbij := case2cv_BB_powerset_sum (R := R) (C0 := C0) x hC
    -- hbij : Σ_B x^{B.card - C0.card} = Σ_E x^{E.card}
    have hBij' : (∑ B ∈ BB, x ^ (B.card - C0.card)) = (∑ E ∈ (R \ C0).powerset, x ^ E.card) := by
      simpa [BB] using hbij
    have hBij2 : (∑ B ∈ BB, x ^ (B.card - t)) = ∑ E ∈ (R \ C0).powerset, x ^ E.card := by
      calc
        (∑ B ∈ BB, x ^ (B.card - t)) = ∑ B ∈ BB, x ^ (B.card - C0.card) := by
          apply Finset.sum_congr rfl
          intro B hB
          congr 1
          omega
        _ = ∑ E ∈ (R \ C0).powerset, x ^ E.card := hBij'
    have hpowset := case2cv_sum_powerset_pow (X := R \ C0) x
    have hcardRC0 : (R \ C0).card = s - t := by
      have hmain := Finset.card_sdiff (s := C0) (t := R)
      have hC0R : C0 ∩ R = C0 := by
        apply Finset.ext
        intro z
        constructor
        · intro hz; exact (Finset.mem_inter.mp hz).1
        · intro hz; exact Finset.mem_inter.mpr ⟨hz, hC hz⟩
      rw [hmain, hC0R, hsR, htC]
    calc
      (∑ B ∈ BB, x ^ (B.card - t)) = ∑ E ∈ (R \ C0).powerset, x ^ E.card := hBij2
      _ = (1 + x) ^ (R \ C0).card := hpowset
      _ = (1 + x) ^ (s - t) := by rw [hcardRC0]
  have hS : (∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card))
      ≤ r ^ (k - t) * q ^ (s - t) * (1 + x) ^ (s - t) := by
    calc
      (∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card))
          = (∑ B ∈ BB, r ^ (k - t) * q ^ (s - t) * x ^ (B.card - t)) := by
            apply Finset.sum_congr rfl
            intro B hB
            exact hfac B hB
      _ = r ^ (k - t) * q ^ (s - t) * (∑ B ∈ BB, x ^ (B.card - t)) := by
            rw [Finset.mul_sum]
      _ ≤ r ^ (k - t) * q ^ (s - t) * (1 + x) ^ (s - t) := by
            exact mul_le_mul_of_nonneg_left (le_of_eq hpowx)
              (mul_nonneg (pow_nonneg (le_of_lt hrR) (k - t)) (pow_nonneg hq0 (s - t)))
  -- assemble
  calc
    (∑ V ∈ cardSubsets (X \ U) v, ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ))
        = (∑ V ∈ VV, ((tau S U C0 (V ∪ R) s).card : ℝ)) := by
          simp [VV, R]
    _ = ∑ A' ∈ AA, (((VV.filter (fun V : Finset α => chi S U A' ⊆ V ∪ R)).card : ℝ)) := hDC
    _ ≤ (VV.card : ℝ) * (∑ A' ∈ AA, q ^ (chi S U A' \ R).card) := hsumA
    _ ≤ (VV.card : ℝ) * (∑ B ∈ BB, q ^ (s - B.card) * r ^ (k - B.card)) := by
          exact mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ (VV.card : ℝ))
    _ ≤ (VV.card : ℝ) * (r ^ (k - t) * q ^ (s - t) * (1 + x) ^ (s - t)) := by
          exact mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ (VV.card : ℝ))
    _ = (cardSubsets (X \ U) v).card * (r ^ (k - t)) * q ^ (s - t) * (1 + x) ^ (s - t) := by
          simp only [VV, q, x]
          ring
/-! ## main theorem -/

/-- number of V with φ(s,t) < |τ(C0, V∪χ(A0,U), s)| is small (case 2) -/
theorem case2_Vcount {X : Finset α} {S : Finset (Finset α)} {U A0 C0 : Finset α}
    {v k s t : ℕ} {r : ℝ}
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (huni : ∀ A ∈ S, A.card = k)
    (hU : U ⊆ X) (hS : ∀ A ∈ S, A ⊆ X) (hM : A0 ∈ S)
    (hs : (chi S U A0).card = s) (hC : C0 ⊆ chi S U A0) (htC : C0.card = t)
    (ht1 : 1 ≤ t) (hv : 0 < v) (hn : 0 < X.card) (hr1 : 1 ≤ r)
    (hvn : v ≤ (X \ U).card) :
    ((((cardSubsets (X \ U) v).filter
        (fun V => phiVal r k X v s t < ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ))).card : ℝ)
      ≤ (cardSubsets (X \ U) v).card * (((rho : ℝ) ^ s)⁻¹) *
          (((X.card : ℝ) / ((X \ U).card : ℝ)) *
            (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r))) ^ (s - t)) := by
  classical
  let Cnt : Finset (Finset α) := (cardSubsets (X \ U) v).filter
        (fun V => phiVal r k X v s t < ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ))
  let q : ℝ := (v : ℝ) / ((X \ U).card : ℝ)
  let x : ℝ := ((X \ U).card : ℝ) / ((v : ℝ) * r)
  change (Cnt.card : ℝ) ≤ (cardSubsets (X \ U) v).card * (((rho : ℝ) ^ s)⁻¹) *
          (((X.card : ℝ) / ((X \ U).card : ℝ)) *
            (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r))) ^ (s - t)
  have hts : t ≤ s := by
    have hle : C0.card ≤ (chi S U A0).card := Finset.card_le_card hC
    omega
  have hsk : s ≤ k := by
    have hc := chi_card_le_k'' (S:=S) (U:=U) (A:=A0) hM huni
    omega
  have htks : t ≤ k := le_trans hts hsk
  have hNpos : 0 < (X \ U).card := by omega
  have hnR : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hn
  have hNR : (0 : ℝ) < ((X \ U).card : ℝ) := by exact_mod_cast hNpos
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hrR : 0 < r := by linarith
  have hrhoR : 0 < (rho : ℝ) := by unfold rho; positivity
  have hnumpos : 0 < r ^ k * ((rho * (v : ℝ) / (X.card : ℝ)) ^ s) := by
    have h1 : 0 < (rho * (v : ℝ) / (X.card : ℝ)) ^ s := by
      apply pow_pos
      exact div_pos (mul_pos hrhoR hvR) hnR
    exact mul_pos (pow_pos hrR k) h1
  have hdenpos : 0 < ((v : ℝ) * r / (X.card : ℝ)) ^ t := by
    apply pow_pos
    exact div_pos (mul_pos hvR hrR) hnR
  have hphi_pos : 0 < phiVal r k X v s t := by
    dsimp [phiVal, phi]
    exact div_pos hnumpos hdenpos
  have hsum := case2cv_sumtau_le (X := X) (S := S) (U := U) (A0 := A0) (C0 := C0)
    (v := v) (k := k) (s := s) (t := t) (r := r) hspread huni hU hS hM hs hC htC ht1 hv hn hr1 hvn
  have hMk : (Cnt.card : ℝ) ≤ (phiVal r k X v s t)⁻¹ *
      (∑ V ∈ cardSubsets (X \ U) v, ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ)) := by
    have hterm : ∀ V ∈ Cnt, (1 : ℝ) ≤
        ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) * (phiVal r k X v s t)⁻¹ := by
      intro V hV
      have hph : phiVal r k X v s t < ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) :=
        (Finset.mem_filter.mp hV).2
      have hle : phiVal r k X v s t ≤ ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) := le_of_lt hph
      have hprod : phiVal r k X v s t * (phiVal r k X v s t)⁻¹ ≤
          ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) * (phiVal r k X v s t)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr hphi_pos))
      have hphne : phiVal r k X v s t ≠ 0 := ne_of_gt hphi_pos
      simpa [mul_inv_cancel₀ hphne] using hprod
    calc
      (Cnt.card : ℝ) = ∑ V ∈ Cnt, (1 : ℝ) := by simp
      _ ≤ ∑ V ∈ Cnt, ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) * (phiVal r k X v s t)⁻¹ := by
            exact Finset.sum_le_sum hterm
      _ ≤ ∑ V ∈ cardSubsets (X \ U) v,
            ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) * (phiVal r k X v s t)⁻¹ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun V : Finset α =>
              phiVal r k X v s t < ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ)) (cardSubsets (X \ U) v))
              (by
                intro V hV hVnot
                have hnon : 0 ≤ ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ) := by positivity
                positivity)
      _ = (phiVal r k X v s t)⁻¹ * (∑ V ∈ cardSubsets (X \ U) v,
            ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ)) := by
            rw [← Finset.sum_mul]
            ring
  have hphm := case2cv_phi_mul (r := r) (rho := rho) (v := (v : ℝ)) (n := (X.card : ℝ))
    (N := ((X \ U).card : ℝ)) (k := k) (s := s) (t := t) hrR hrhoR hvR hnR hNR hts htks
  have hphm' : (phiVal r k X v s t)⁻¹ * r ^ (k - t) * q ^ (s - t)
      = ((rho : ℝ) ^ s)⁻¹ * (((X.card : ℝ) / ((X \ U).card : ℝ)) ^ (s - t)) := by
    simpa [q, phiVal, phi] using hphm
  calc
    (Cnt.card : ℝ)
        ≤ (phiVal r k X v s t)⁻¹ *
            (∑ V ∈ cardSubsets (X \ U) v, ((tau S U C0 (V ∪ chi S U A0) s).card : ℝ)) := hMk
    _ ≤ (phiVal r k X v s t)⁻¹ * ((cardSubsets (X \ U) v).card * (r ^ (k - t)) *
            q ^ (s - t) * (1 + x) ^ (s - t)) := by
          have hle := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hphi_pos))
          simpa [q, x] using hle
    _ = (cardSubsets (X \ U) v).card * ((phiVal r k X v s t)⁻¹ * r ^ (k - t) * q ^ (s - t)) *
          (1 + x) ^ (s - t) := by ring
    _ = (cardSubsets (X \ U) v).card * (((rho : ℝ) ^ s)⁻¹ * (((X.card : ℝ) / ((X \ U).card : ℝ)) ^ (s - t))) *
          (1 + x) ^ (s - t) := by
          rw [hphm']
    _ = (cardSubsets (X \ U) v).card * ((rho : ℝ) ^ s)⁻¹ *
          (((X.card : ℝ) / ((X \ U).card : ℝ)) ^ (s - t) * (1 + x) ^ (s - t)) := by ring
    _ = (cardSubsets (X \ U) v).card * ((rho : ℝ) ^ s)⁻¹ *
          ((((X.card : ℝ) / ((X \ U).card : ℝ)) * (1 + x)) ^ (s - t)) := by
          rw [← mul_pow]
    _ = (cardSubsets (X \ U) v).card * (((rho : ℝ) ^ s)⁻¹) *
          (((X.card : ℝ) / ((X \ U).card : ℝ)) *
            (1 + ((X \ U).card : ℝ) / ((v : ℝ) * r))) ^ (s - t) := by
          dsimp [x]

end Submission.Sun
