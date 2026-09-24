import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCut
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSWBlock

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The `B`-term bilinear form in the small-conductor (Siegel–Walfisz) range

For a primitive non-principal Dirichlet character `ψ` of modulus `r ≤ (log x)^C` we bound the
bilinear form `bilinForm U V y a b r ψ` with

* `a = aCut M Y j t₁` the indicator of the primes in the dyadic block `[Q_j, 2 Q_j)`,
  `Q_j = blockStart M j = M · 2^j`, further cut by `t₁ ∣ q`;
* `b = bCut Y t₂` the indicator of the products `q₂ q₃` of primes `≥ Y`, cut by `t₂ ∣ m`;
* `U = 2 Q_j`, `V = ⌊(x+2)/Q_j⌋ + 1`, `y = x + 2`,

by

`‖bilinForm‖ ≤ 4 Q_j / (log x)^A · bPairCount Y V`.

The mechanism is the Siegel–Walfisz prime character sum `BLodSWBlock`: splitting the bilinear
form as `Σ_n b_n ψ(n) · A_n` with `A_n = Σ_{m ≤ U, mn ≤ y} a_m ψ(m)`, each inner sum `A_n` is a
prime character sum over the dyadic block `[Q_j, 2 Q_j)` (cut at `min (2 Q_j) (y / n)`), hence
`≪ Q_j / (log x)^{A+1}` by `BLodSWBlock`, plus at most two boundary primes past `x`; the factor
`(log x)^A ≤ Q_j` absorbs those.  The `b`-side is then controlled termwise by
`Σ_n ‖bCut Y t₂ n‖ ≤ bPairCount Y V`.

## Main auxiliary steps

* `bInner`: the inner sum `A_n`;
* `bilinForm_eq_sum_bInner`: `bilinForm = Σ_n b_n ψ(n) A_n`;
* `norm_bilinForm_le`: `‖bilinForm‖ ≤ C · Σ_n ‖b_n‖` whenever `‖A_n‖ ≤ C` for all `n ∈ [1,V]`;
* `sum_norm_bCut_le`: `Σ_{n ≤ V} ‖bCut Y t₂ n‖ ≤ bPairCount Y V`;
* `bInner_aCut_le`: the inner bound `‖A_n‖ ≤ 4 Q_j / (log x)^A`, uniformly in `n ≥ 1`.
-/

/-- The inner sum `A_n = Σ_{m ≤ U, m n ≤ y} a_m ψ(m)` of the bilinear form. -/
noncomputable def bInner (U y : ℕ) (a : ℕ → ℂ) (r : ℕ) (ψ : DirichletCharacter ℂ r) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 U, (if m * n ≤ y then (1:ℂ) else 0) * a m * ψ ((m : ℕ) : ZMod r)

/-- The bilinear form is the `ψ`-twisted `b`-sum of the inner sums `bInner`. -/
theorem bilinForm_eq_sum_bInner (U V y : ℕ) (a b : ℕ → ℂ) (r : ℕ)
    (ψ : DirichletCharacter ℂ r) :
    bilinForm U V y a b r ψ
      = ∑ n ∈ Finset.Icc 1 V, b n * ψ ((n:ℕ) : ZMod r) * bInner U y a r ψ n := by
  rw [bilinForm_eq]
  simp only [bInner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.cast_mul, map_mul]
  ring

/-- Factoring the bilinear form: if the inner sums `bInner U y a r ψ n` are all bounded by `C`
on `n ∈ [1,V]`, then `‖bilinForm‖ ≤ C · Σ_{n ≤ V} ‖b_n‖`. -/
theorem norm_bilinForm_le (U V y : ℕ) (a b : ℕ → ℂ) (r : ℕ) (ψ : DirichletCharacter ℂ r)
    (C : ℝ) (hC : ∀ n ∈ Finset.Icc 1 V, ‖bInner U y a r ψ n‖ ≤ C) :
    ‖bilinForm U V y a b r ψ‖ ≤ C * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ := by
  rw [bilinForm_eq_sum_bInner]
  calc ‖∑ n ∈ Finset.Icc 1 V, b n * ψ ((n:ℕ) : ZMod r) * bInner U y a r ψ n‖
      ≤ ∑ n ∈ Finset.Icc 1 V, ‖b n * ψ ((n:ℕ) : ZMod r) * bInner U y a r ψ n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ‖b n‖ * C := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have h1 : ‖b n * ψ ((n:ℕ) : ZMod r)‖ ≤ ‖b n‖ * 1 := by
          calc ‖b n * ψ ((n:ℕ) : ZMod r)‖ ≤ ‖b n‖ * ‖ψ ((n:ℕ) : ZMod r)‖ := norm_mul_le _ _
            _ ≤ ‖b n‖ * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _)
        calc ‖b n * ψ ((n:ℕ) : ZMod r) * bInner U y a r ψ n‖
            ≤ ‖b n * ψ ((n:ℕ) : ZMod r)‖ * ‖bInner U y a r ψ n‖ := norm_mul_le _ _
          _ ≤ (‖b n‖ * 1) * C := mul_le_mul h1 (hC n hn) (norm_nonneg _) (by positivity)
          _ = ‖b n‖ * C := by ring
    _ = C * ∑ n ∈ Finset.Icc 1 V, ‖b n‖ := by rw [← Finset.sum_mul]; ring

/-- `‖bCoeff Y v‖` is the indicator of `bCoeff Y v ≠ 0`. -/
theorem norm_bCoeff_eq (Y v : ℕ) : ‖bCoeff Y v‖ = if bCoeff Y v ≠ 0 then (1:ℝ) else 0 := by
  by_cases h : ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = v
  · rw [show bCoeff Y v = 1 from by unfold bCoeff; rw [if_pos h]]; simp
  · rw [show bCoeff Y v = 0 from by unfold bCoeff; rw [if_neg h]]; simp

/-- The `b`-side of the bilinear form is dominated by the count of twin-prime pairs: for the
`t₂`-cut coefficients, `Σ_{n ≤ V} ‖bCut Y t₂ n‖ ≤ bPairCount Y V`. -/
theorem sum_norm_bCut_le (Y t₂ V : ℕ) :
    ∑ n ∈ Finset.Icc 1 V, ‖bCut Y t₂ n‖ ≤ (bPairCount Y V : ℝ) := by
  have h2 : ((Finset.Icc 1 V).filter (fun n => bCoeff Y n ≠ 0)).card
      = ∑ n ∈ Finset.Icc 1 V, (if bCoeff Y n ≠ 0 then (1:ℝ) else 0) := by
    rw [Finset.card_filter]; push_cast; rfl
  calc ∑ n ∈ Finset.Icc 1 V, ‖bCut Y t₂ n‖
      ≤ ∑ n ∈ Finset.Icc 1 V, (if bCoeff Y n ≠ 0 then (1:ℝ) else 0) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        refine le_trans (norm_bCut_le_bCoeff Y t₂ n) ?_
        rw [norm_bCoeff_eq]
    _ = ((Finset.Icc 1 V).filter (fun n => bCoeff Y n ≠ 0)).card := h2.symm
    _ ≤ (bPairCount Y V : ℝ) := by
        exact_mod_cast card_filter_bCoeff_ne_zero_le_bPairCount Y V

/-- **The inner sum bound.**  For `n ≥ 1`, the prime character sum over the dyadic block
`[Q_j, 2 Q_j)` cut at `min (2 Q_j) (⌊(x+2)/n⌋)` — i.e. the `n`-th inner sum of the bilinear
form with the `aCut` coefficients, with `t₁ = 1` — is at most `4 Q_j / (log x)^A`, given the
Siegel–Walfisz input at exponent `A+1`, the bound `(log x)^A ≤ Q_j`, and `log x ≥ 2`.

If `t₁ ≠ 1`, the cut `t₁ ∣ q` leaves at most the single term `q = t₁`. -/
theorem bInner_aCut_le (A : ℝ) (x M Y j t₁ n : ℕ) (r : ℕ) (ψ : DirichletCharacter ℂ r)
    (hn : 1 ≤ n) (hlog : 2 ≤ Real.log (x:ℝ))
    (hlogle : (Real.log (x:ℝ))^A ≤ (blockStart M j : ℝ))
    (hSW : ∀ T : ℕ, T ≤ x → ‖∑ q ∈ Finset.Icc 1 (2 * blockStart M j),
        (if q ≤ T then (1:ℂ) else 0) * aCoeff M Y j q * ψ ((q:ℕ) : ZMod r)‖
        ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^(A+1)) :
    ‖bInner (2 * blockStart M j) (x+2) (aCut M Y j t₁) r ψ n‖
      ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A := by
  set Q : ℕ := blockStart M j with hQ
  have hn0 : 0 < n := hn
  have hLpos : (0:ℝ) < (Real.log (x:ℝ))^A := Real.rpow_pos_of_pos (by linarith) A
  have hQL : (Real.log (x:ℝ))^A ≤ (Q:ℝ) := hlogle
  have hLpow : (Real.log (x:ℝ))^(A+1) = (Real.log (x:ℝ))^A * Real.log (x:ℝ) :=
    Real.rpow_add_one (by linarith : Real.log (x:ℝ) ≠ 0) A
  -- the budget: one Siegel-Walfisz block bound at exponent `A+1`, plus the two boundary primes
  have hfinal : 4 * (Q:ℝ) / (Real.log (x:ℝ))^(A+1) + 2 ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
    have hkey : 4 * (Q:ℝ) / (Real.log (x:ℝ))^(A+1) ≤ 2 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
      rw [hLpow]
      have h1 : (Real.log (x:ℝ))^A * 2 ≤ (Real.log (x:ℝ))^A * Real.log (x:ℝ) :=
        mul_le_mul_of_nonneg_left hlog hLpos.le
      calc 4 * (Q:ℝ) / ((Real.log (x:ℝ))^A * Real.log (x:ℝ))
          ≤ 4 * (Q:ℝ) / ((Real.log (x:ℝ))^A * 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h1
        _ = 2 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
            have hne : ((Real.log (x:ℝ))^A) ≠ 0 := ne_of_gt hLpos
            field_simp
            ring
    have h2 : (2:ℝ) ≤ 2 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
      rw [le_div_iff₀ hLpos]; linarith
    calc 4 * (Q:ℝ) / (Real.log (x:ℝ))^(A+1) + 2
        ≤ 2 * (Q:ℝ) / (Real.log (x:ℝ))^A + 2 * (Q:ℝ) / (Real.log (x:ℝ))^A :=
          add_le_add hkey h2
      _ = 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := by ring
  by_cases ht1 : t₁ = 1
  · -- `t₁ = 1`: the inner sum is the Siegel–Walfisz block sum, cut at `min (2 Q) (y/n)`
    subst ht1
    have ha : ∀ m, aCut M Y j 1 m = aCoeff M Y j m := by
      intro m; unfold aCut; rw [if_pos (one_dvd m), mul_one]
    have hbin : bInner (2*Q) (x+2) (aCut M Y j 1) r ψ n
        = bInner (2*Q) (x+2) (aCoeff M Y j) r ψ n := by
      simp only [bInner]
      exact Finset.sum_congr rfl (fun m _ => by rw [ha m])
    set T : ℕ := min (2*Q) ((x+2)/n) with hT
    set T1 : ℕ := min T x with hT1
    have hT1le : T1 ≤ x := by rw [hT1]; exact min_le_right _ _
    have hT1T : T1 ≤ T := by rw [hT1]; exact min_le_left _ _
    -- split the sum at `min T x`: the part up to `x` is Siegel–Walfisz, the rest has ≤ 2 terms
    have hinner : bInner (2*Q) (x+2) (aCoeff M Y j) r ψ n
        = (∑ m ∈ Finset.Icc 1 (2*Q),
              (if m ≤ T1 then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r))
          + (∑ m ∈ Finset.Icc 1 (2*Q),
              (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)) := by
      simp only [bInner]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm2 : m ≤ 2*Q := (Finset.mem_Icc.mp hm).2
      have hdiv : (m ≤ (x+2)/n) ↔ (m*n ≤ x+2) := Nat.le_div_iff_mul_le hn0
      have hiff : (m * n ≤ x + 2) ↔ (m ≤ T) := by
        rw [hT]
        constructor
        · intro h; exact le_min hm2 (hdiv.mpr h)
        · intro h; exact hdiv.mp (le_trans h (min_le_right _ _))
      have hpt : (if m ≤ T then (1:ℂ) else 0)
          = (if m ≤ T1 then (1:ℂ) else 0) + (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) := by
        by_cases h1 : m ≤ T1
        · have h2 : m ≤ T := le_trans h1 hT1T
          have h3 : ¬ (T1 < m) := not_lt.mpr h1
          rw [if_pos h2, if_pos h1, if_neg (fun hh => h3 hh.1)]; ring
        · have hlt : T1 < m := not_le.mp h1
          by_cases h2 : m ≤ T
          · rw [if_pos h2, if_neg h1, if_pos (by tauto : T1 < m ∧ m ≤ T)]; ring
          · rw [if_neg h2, if_neg h1, if_neg (fun hh => h2 hh.2)]; ring
      rw [if_congr hiff rfl rfl, hpt]
      ring
    have hS1 : ‖∑ m ∈ Finset.Icc 1 (2*Q),
          (if m ≤ T1 then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖
        ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^(A+1) := hSW T1 hT1le
    have hS2 : ‖∑ m ∈ Finset.Icc 1 (2*Q),
          (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖ ≤ 2 := by
      have hcard : ((Finset.Icc 1 (2*Q)).filter
          (fun m => (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0)).card ≤ 2 := by
        have hsub : ((Finset.Icc 1 (2*Q)).filter
            (fun m => (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0)) ⊆ ({x+1, x+2} : Finset ℕ) := by
          intro m hm
          simp only [Finset.mem_filter] at hm
          obtain ⟨hmI, hrest⟩ := hm
          obtain ⟨⟨hlt, hmT⟩, -⟩ := hrest
          obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hmI
          have hmn : m * n ≤ x + 2 :=
            (Nat.le_div_iff_mul_le hn0).mp (le_trans hmT (min_le_right _ _))
          have hmx : m ≤ x + 2 := le_trans (Nat.le_mul_of_pos_right m hn0) hmn
          have hxlt : x < m := by
            by_cases hxT : x < T
            · rw [hT1, min_eq_right hxT.le] at hlt; exact hlt
            · rw [not_lt] at hxT
              rw [hT1, min_eq_left hxT] at hlt
              omega
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        refine le_trans (Finset.card_le_card hsub) ?_
        simp
      have hsum_eq : (∑ m ∈ Finset.Icc 1 (2*Q),
            (if (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0 then (1:ℝ) else 0))
          = (((Finset.Icc 1 (2*Q)).filter
              (fun m => (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0)).card : ℝ) := by
        rw [Finset.card_filter]; push_cast; rfl
      calc ‖∑ m ∈ Finset.Icc 1 (2*Q),
            (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖
          ≤ ∑ m ∈ Finset.Icc 1 (2*Q),
              ‖(if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ m ∈ Finset.Icc 1 (2*Q),
              (if (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0 then (1:ℝ) else 0) := by
              refine Finset.sum_le_sum (fun m _ => ?_)
              by_cases hP : T1 < m ∧ m ≤ T
              · by_cases ha' : aCoeff M Y j m = 0
                · rw [if_pos hP, if_neg (fun hh => hh.2 ha'), ha']; simp
                · rw [if_pos hP,
                    if_pos (by tauto : (T1 < m ∧ m ≤ T) ∧ aCoeff M Y j m ≠ 0), one_mul]
                  calc ‖aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖
                      ≤ ‖aCoeff M Y j m‖ * ‖ψ ((m:ℕ):ZMod r)‖ := norm_mul_le _ _
                    _ ≤ 1 * 1 := mul_le_mul (norm_aCoeff_le_one M Y j m)
                        (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _) (by norm_num)
                    _ = 1 := by norm_num
              · rw [if_neg hP, if_neg (fun hh => hP hh.1)]; simp
        _ = _ := hsum_eq
        _ ≤ 2 := by exact_mod_cast hcard
    rw [hbin, hinner]
    calc ‖(∑ m ∈ Finset.Icc 1 (2*Q),
              (if m ≤ T1 then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r))
          + (∑ m ∈ Finset.Icc 1 (2*Q),
              (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r))‖
        ≤ ‖∑ m ∈ Finset.Icc 1 (2*Q),
              (if m ≤ T1 then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖
          + ‖∑ m ∈ Finset.Icc 1 (2*Q),
              (if T1 < m ∧ m ≤ T then (1:ℂ) else 0) * aCoeff M Y j m * ψ ((m:ℕ):ZMod r)‖ :=
            norm_add_le _ _
      _ ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^(A+1) + 2 := add_le_add hS1 hS2
      _ ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := hfinal
  · -- `t₁ ≠ 1`: the divisibility cut leaves at most one prime, namely `t₁` itself
    have hcard : ((Finset.Icc 1 (2*Q)).filter (fun m => m.Prime ∧ t₁ ∣ m)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
      obtain ⟨-, hpa, hda⟩ := ha
      obtain ⟨-, hpb, hdb⟩ := hb
      have ha1 : a = t₁ := by
        rcases hpa.eq_one_or_self_of_dvd t₁ hda with h | h
        · exact absurd h ht1
        · exact h.symm
      have hb1 : b = t₁ := by
        rcases hpb.eq_one_or_self_of_dvd t₁ hdb with h | h
        · exact absurd h ht1
        · exact h.symm
      rw [ha1, hb1]
    have hsum_eq : (∑ m ∈ Finset.Icc 1 (2*Q), (if m.Prime ∧ t₁ ∣ m then (1:ℝ) else 0))
        = (((Finset.Icc 1 (2*Q)).filter (fun m => m.Prime ∧ t₁ ∣ m)).card : ℝ) := by
      rw [Finset.card_filter]; push_cast; rfl
    calc ‖bInner (2*Q) (x+2) (aCut M Y j t₁) r ψ n‖
        ≤ ∑ m ∈ Finset.Icc 1 (2*Q),
            ‖(if m*n ≤ x+2 then (1:ℂ) else 0) * aCut M Y j t₁ m * ψ ((m:ℕ):ZMod r)‖ := by
          rw [show bInner (2*Q) (x+2) (aCut M Y j t₁) r ψ n
            = ∑ m ∈ Finset.Icc 1 (2*Q),
                (if m*n ≤ x+2 then (1:ℂ) else 0) * aCut M Y j t₁ m
                  * ψ ((m:ℕ):ZMod r) from rfl]
          exact norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 (2*Q), (if m.Prime ∧ t₁ ∣ m then (1:ℝ) else 0) := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            by_cases hP : m*n ≤ x+2
            · by_cases hprime : m.Prime
              · by_cases hd : t₁ ∣ m
                · rw [if_pos hP, if_pos (by tauto : m.Prime ∧ t₁ ∣ m), one_mul]
                  calc ‖aCut M Y j t₁ m * ψ ((m:ℕ):ZMod r)‖
                      ≤ ‖aCut M Y j t₁ m‖ * ‖ψ ((m:ℕ):ZMod r)‖ := norm_mul_le _ _
                    _ ≤ 1 * 1 := mul_le_mul (norm_aCut_le_one M Y j t₁ m)
                        (DirichletCharacter.norm_le_one ψ _) (norm_nonneg _) (by norm_num)
                    _ = 1 := by norm_num
                · have hz : aCut M Y j t₁ m = 0 := by unfold aCut; rw [if_neg hd, mul_zero]
                  rw [if_pos hP, if_neg (fun hh => hd hh.2), hz]; simp
              · have hz : aCut M Y j t₁ m = 0 := by
                  unfold aCut
                  rw [show aCoeff M Y j m = 0 from by
                    unfold aCoeff; rw [if_neg (fun h => hprime h.1)]]
                  rw [zero_mul]
                rw [if_pos hP, if_neg (fun hh => hprime hh.1), hz]; simp
            · rw [if_neg hP]; split_ifs <;> norm_num
      _ = (((Finset.Icc 1 (2*Q)).filter (fun m => m.Prime ∧ t₁ ∣ m)).card : ℝ) := hsum_eq
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ 4 * (Q:ℝ) / (Real.log (x:ℝ))^A := by
          rw [le_div_iff₀ hLpos]
          nlinarith [hQL]

/-- **The `B`-term bilinear form in the small-conductor range.**  For every primitive
non-principal character `ψ` of modulus `r ≤ (log x)^C` and every sift limit `M ≥ x^{1/14}`, the
bilinear form of the `B`-term defect over the dyadic block `j` is bounded by
`4 · blockStart M j / (log x)^A` times the number of pairs of primes `≥ Y` with product below
the hyperbola limit. -/
theorem BLodCutSmallR (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {r : ℕ}, 2 ≤ r → r ≤ ⌊(Real.log (x:ℝ))^C⌋₊ →
      ∀ (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ (M Y j t₁ t₂ : ℕ), (x:ℝ)^((1:ℝ)/14) ≤ M →
        ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
            (aCut M Y j t₁) (bCut Y t₂) r ψ‖
          ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A
              * (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := by
  -- Siegel–Walfisz input, at exponent `A + 1` so that it dominates the target exponent `A`
  have hSWall : ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {r : ℕ}, 2 ≤ r → r ≤ ⌊(Real.log (x:ℝ))^C⌋₊ →
      ∀ (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ (M Y j T : ℕ), (x:ℝ)^((1:ℝ)/14) ≤ M → T ≤ x →
        ‖∑ q ∈ Finset.Icc 1 (2 * blockStart M j),
            (if q ≤ T then (1:ℂ) else 0) * aCoeff M Y j q * ψ ((q:ℕ) : ZMod r)‖
          ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^(A+1) :=
    BLodSWBlock (A+1) C (by linarith) hC
  have hlog2 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ Real.log (x:ℝ) :=
    eventually_const_le_nat_log 2
  have hlogle : ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x:ℝ))^A ≤ (x:ℝ)^((1:ℝ)/14) := by
    have h := eventually_nat_log_pow_mul_le_rpow A (1/14) hA (by norm_num) 1
    simpa using h
  filter_upwards [hSWall, hlog2, hlogle] with x hSW hlog hl
  intro r hr2 hrC ψ hprim hne M Y j t₁ t₂ hM
  -- `(log x)^A ≤ x^{1/14} ≤ M ≤ blockStart M j`
  have hcast : (M : ℝ) ≤ (blockStart M j : ℝ) := by
    have hle : M ≤ blockStart M j := by
      rw [blockStart]; exact Nat.le_mul_of_pos_right M (Nat.two_pow_pos j)
    exact_mod_cast hle
  have hLA : (Real.log (x:ℝ))^A ≤ (blockStart M j : ℝ) := le_trans (le_trans hl hM) hcast
  have hinner : ∀ n ∈ Finset.Icc 1 ((x + 2) / blockStart M j + 1),
      ‖bInner (2 * blockStart M j) (x + 2) (aCut M Y j t₁) r ψ n‖
        ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A := by
    intro n hn
    exact bInner_aCut_le A x M Y j t₁ n r ψ (Finset.mem_Icc.mp hn).1 hlog hLA
      (fun T hT => hSW hr2 hrC ψ hprim hne M Y j T hM hT)
  calc ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
          (aCut M Y j t₁) (bCut Y t₂) r ψ‖
      ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A
          * ∑ n ∈ Finset.Icc 1 ((x + 2) / blockStart M j + 1), ‖bCut Y t₂ n‖ :=
        norm_bilinForm_le _ _ _ _ _ _ _ (4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A) hinner
    _ ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A
          * (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_norm_bCut_le Y t₂ _) (by positivity)

end Work.NumberTheory.Chen.BTermCount
