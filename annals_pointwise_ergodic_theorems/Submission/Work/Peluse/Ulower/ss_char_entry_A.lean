import Mathlib
import Submission.Work.Peluse.Ulower.helpers
import Submission.Work.Peluse.Ulower.boxSumPow_neg
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one
import Submission.Work.Peluse.Ulower.char_dilate_le
import Submission.Work.Peluse.Ulower.ss_decimate
import Submission.Work.Peluse.Ulower.dSup_div_add_one_le
import Submission.Work.Peluse.Ulower.symIcc_ratio_lower
import Submission.Work.Peluse.Ulower.const_compare

/-!
# `Work.Peluse.Ulower.ss_char_entry_A` — the `U²`-inverse entry under the one-sided scale bound

`Work.Peluse.Ulower.ss_char_entry` assumes the two-sided scale relation `Scaled Ns N P.natDegree`
(`N^d/2 ≤ Ns ≤ 2 N^d`).  The unbalanced chapter `Work.Peluse.Ulower.ss_u2_level_A` only has the
one-sided bound `N^d ≤ A·Ns` (with `A` fixed before the constants), so the entry must be redone with
the `A`-dependent constant `ssAmaxA P A = 3 + coeffSum P · A` in place of `ssAmax P`.

The body below is the body of `ss_char_entry` with the single substitution
`dSup_div_add_one_le … hSc ↦ dSup_div_add_one_le_A … hsc` and `ssAmax P ↦ ssAmaxA P A`
everywhere; the cardinality ratio `ss_aux_symIcc_ratio` is replaced by its `A`-version
`symIcc_ratio_lower_A` (its arithmetic core `ss_aux_symIcc_ratio_arith` is `private`, so it is
duplicated here as `symIcc_ratio_arith_A`).
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse


/-! ## The `A`-version of the support-box bookkeeping -/

/-- `A`-version of `ssAmax P`: the constant `3 + (∑|a_i|)·A` with which the support-box bound
`L'' ≤ ssAmaxA P A · Ns` holds under the *one-sided* scale hypothesis `N^d ≤ A·Ns`. -/
def ssAmaxA (P : Polynomial ℤ) (A : ℕ) : ℕ := 3 + coeffSum P * A

lemma three_le_ssAmaxA (P : Polynomial ℤ) (A : ℕ) : 3 ≤ ssAmaxA P A := by
  rw [ssAmaxA]; omega

lemma ssAmaxA_pos (P : Polynomial ℤ) (A : ℕ) : 0 < ssAmaxA P A :=
  lt_of_lt_of_le (by norm_num) (three_le_ssAmaxA P A)

/-- For `N ≥ 1` every term `|a_i| N^i` of `polySup P N` (with `i ≤ deg P`) is at most
`|a_i| N ^ deg P`, so `polySup P N ≤ coeffSum P · N ^ deg P`. -/
private lemma polySup_le_coeffSum_mul_pow (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    Work.Peluse.polySup P N ≤ coeffSum P * N ^ P.natDegree := by
  rw [Work.Peluse.polySup, coeffSum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hi')

/-- **The support-box bookkeeping under the one-sided scale hypothesis `N^d ≤ A·Ns`.**
`dSup P Ns N = Ns + polySup P N ≤ Ns + coeffSum P · N^d ≤ Ns + coeffSum P · A · Ns`, and dividing
by `|c|` (`≥ 1`) can only decrease the left-hand side; adding `1` costs at most `(Ns+1) ≤ 3Ns`. -/
theorem dSup_div_add_one_le_A {P : Polynomial ℤ} {c : ℤ}
    (hc1 : 1 ≤ c.natAbs) {Ns N A : ℕ} (hNs : 1 ≤ Ns) (hN : 1 ≤ N)
    (hsc : (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ)) :
    (Work.Peluse.dSup P Ns N) / c.natAbs + 1 ≤ ssAmaxA P A * Ns := by
  have hpow : N ^ P.natDegree ≤ A * Ns := by
    have h1 : ((N ^ P.natDegree : ℕ) : ℝ) ≤ ((A * Ns : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_mul]; exact hsc
    exact_mod_cast h1
  have hpoly : Work.Peluse.polySup P N ≤ coeffSum P * (A * Ns) :=
    le_trans (polySup_le_coeffSum_mul_pow P hN) (Nat.mul_le_mul_left _ hpow)
  have hdsup : Work.Peluse.dSup P Ns N ≤ Ns + coeffSum P * (A * Ns) := by
    rw [Work.Peluse.dSup]
    exact Nat.add_le_add_left hpoly Ns
  have hkey : Ns + 1 ≤ 3 * Ns := by omega
  calc (Work.Peluse.dSup P Ns N) / c.natAbs + 1
      ≤ Work.Peluse.dSup P Ns N + 1 := Nat.add_le_add_right (Nat.div_le_self _ _) 1
    _ ≤ Ns + coeffSum P * (A * Ns) + 1 := Nat.add_le_add_right hdsup 1
    _ = (Ns + 1) + coeffSum P * A * Ns := by ring
    _ ≤ 3 * Ns + coeffSum P * A * Ns := Nat.add_le_add_right hkey _
    _ = (3 + coeffSum P * A) * Ns := by ring
    _ = ssAmaxA P A * Ns := by rw [ssAmaxA]

/-! ## The `A`-version of the cardinality ratio -/

/-- The scalar arithmetic behind `symIcc_ratio_lower_A`: for `A ≥ 3`, `k ≥ 1`, `Ns ≥ 1`,
`Ns ≤ L` and `M ≤ A · Ns` one has `2 / (3 A k) ≤ (2 L + 1) / (k (2 M + 1))`. -/
private lemma symIcc_ratio_arith_A {A k L M Ns : ℕ} (hA : 3 ≤ A) (hk : 1 ≤ k)
    (hNs : 1 ≤ Ns) (hLge : Ns ≤ L) (hMle : M ≤ A * Ns) :
    2 / (3 * (A : ℝ) * (k : ℝ)) ≤ (2 * (L : ℝ) + 1) / ((k : ℝ) * (2 * (M : ℝ) + 1)) := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hA3 : (3 : ℝ) ≤ A := by exact_mod_cast hA
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hML : (M : ℝ) ≤ (A : ℝ) * (Ns : ℝ) := by exact_mod_cast hMle
  have hNs1 : (1 : ℝ) ≤ Ns := by exact_mod_cast hNs
  have hLN : (Ns : ℝ) ≤ L := by exact_mod_cast hLge
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : 2 * (2 * (M : ℝ) + 1) ≤ 3 * (A : ℝ) * (2 * (L : ℝ) + 1) := by nlinarith
  nlinarith [hkey, hk1]

/-- The symmetric interval `symIcc L = [-L,L]` has `2L+1` elements. -/
private lemma symIcc_card_real (L : ℕ) :
    ((Work.Peluse.symIcc L).card : ℝ) = 2 * (L : ℝ) + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - -((L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]
  push_cast
  ring

/-- **The size ratio of the two support boxes, `A`-version.** -/
theorem symIcc_ratio_lower_A {P : Polynomial ℤ} {c : ℤ} (hc : c ≠ 0) {Ns N D A : ℕ}
    (hc1 : 1 ≤ c.natAbs) (hNs : 1 ≤ Ns) (hD : 1 ≤ D)
    (hL'' : max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D ≤ ssAmaxA P A * Ns) :
    2 / (3 * (ssAmaxA P A : ℝ) * (c.natAbs : ℝ)) ≤
      ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
        ((c.natAbs : ℝ) *
          ((Work.Peluse.symIcc (max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D)).card : ℝ)) := by
  rw [symIcc_card_real, symIcc_card_real]
  refine symIcc_ratio_arith_A (three_le_ssAmaxA P A) hc1 hNs ?_ hL''
  rw [Work.Peluse.dSup]
  exact Nat.le_add_right _ _

theorem ss_char_entry_A {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) :
    ∀ A : ℕ, 1 ≤ A → ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        1 ≤ N → 1 ≤ Ns → 1 ≤ D → N ≤ Ns →
        (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ) →
        (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) →
        ∃ ξ : ℝ, C₀ * δ ^ K₀ * ((D : ℝ) / (Ns : ℝ)) ^ K₀ * (Ns : ℝ) ≤
          ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ := by
  intro A hA
  obtain ⟨C₀', hC₀', K₀', hK₀'1, hchar⟩ := char_of_boxNormPow_two h1
  have hPne : P ≠ 0 := by intro hzero; rw [hzero] at hd; simp at hd
  have hclead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hclead1 : 1 ≤ P.leadingCoeff.natAbs := Int.natAbs_pos.mpr hclead
  have hAmaxpos : 0 < (ssAmaxA P A : ℝ) := by exact_mod_cast ssAmaxA_pos P A
  have hcnpos : (0 : ℝ) < ((P.leadingCoeff).natAbs : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hclead1)
  refine ⟨C₀' * (2 / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ))) ^ K₀' /
      (ssAmaxA P A : ℝ) ^ (K₀' - 1), ?_, K₀', hK₀'1, ?_⟩
  · have hb1 : 0 < (2 : ℝ) / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) := by positivity
    exact div_pos (mul_pos hC₀' (pow_pos hb1 K₀')) (pow_pos hAmaxpos (K₀' - 1))
  · intro Ns N D f₀ f₁ δ hN hNs hD1 hNNs hsc hDNs hsupp0 hsupp1 hb0 hb1 hδ0 hδ1 hbox
    have hsuppF : Work.Peluse.SupportIn (Work.Peluse.dualFn N P f₀ f₁) (Work.Peluse.dSup P Ns N) :=
      Work.Peluse.Tools.dualFn_supportIn (by omega) P f₀ f₁ hsupp0 hsupp1 hNNs
    have hbndF : ∀ x : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ x‖ ≤ 1 :=
      Work.Peluse.Ulower.dualFn_norm_le_one hN P f₀ f₁ hb0 hb1
    have hbox' : δ ≤ Work.Peluse.boxNormPow 2
        (fun _ : Fin 2 => Work.Peluse.arithIcc P.leadingCoeff D)
        (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) := hbox
    obtain ⟨r, hr, hηdec⟩ := ss_decimate hclead hD1 hsuppF hbndF hδ0 hbox'
    set L'' : ℕ := max ((Work.Peluse.dSup P Ns N) / P.leadingCoeff.natAbs + 1) D with hL''def
    have hL''1 : 1 ≤ L'' := le_trans hD1 (le_max_right _ _)
    have hL''D : D ≤ L'' := le_max_right _ _
    have hgsupp : Work.Peluse.SupportIn
        (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))) L'' := by
      rw [hL''def]
      exact ss_support_dilate hclead (D := D) (L := Work.Peluse.dSup P Ns N)
        (fun z => Work.Peluse.dualFn N P f₀ f₁ z) hsuppF r hr
    have hgbnd : ∀ z : ℤ, ‖Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))‖ ≤ 1 :=
      fun z => hbndF _
    set η : ℝ := ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
        ((P.leadingCoeff.natAbs : ℝ) * ((Work.Peluse.symIcc L'').card : ℝ)) * δ with hηdef
    have hηdec' : η ≤ Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
        (Work.Peluse.symIcc L'')
          (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))) := by
      rw [hηdef, hL''def]
      exact hηdec
    have hηpos : 0 < η := by
      have hs : (0:ℝ) < ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) := by
        have : 0 < (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card := by rw [card_symIcc]; positivity
        exact_mod_cast this
      have hs2 : (0:ℝ) < ((Work.Peluse.symIcc L'').card : ℝ) := by
        have : 0 < (Work.Peluse.symIcc L'').card := by rw [card_symIcc]; positivity
        exact_mod_cast this
      rw [hηdef]
      positivity
    have hηle1 : η ≤ 1 := by
      refine le_trans hηdec' ?_
      refine Work.Peluse.BoxNorm.boxNormPow_le_one hgbnd ?_
      intro x hx
      exact hgsupp x (Nat.lt_of_not_le (by rwa [symIcc_mem_iff] at hx))
    obtain ⟨β, hβ⟩ := hchar L'' D
      (fun z : ℤ => Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ)))
      η hL''1 hD1 (by exact_mod_cast hL''D) hgsupp hgbnd hηpos hηle1 hηdec'
    have hsumF : Summable (fun x : ℤ => ‖Work.Peluse.dualFn N P f₀ f₁ x‖) := by
      apply summable_of_ne_finset_zero (s := Work.Peluse.symIcc (Work.Peluse.dSup P Ns N))
      intro x hx
      rw [norm_eq_zero]
      exact hsuppF x (Nat.lt_of_not_le (by rwa [symIcc_mem_iff] at hx))
    obtain ⟨ξ, hξ⟩ := char_dilate_le (F := Work.Peluse.dualFn N P f₀ f₁) hclead hsumF r hr β
    have hβ' : C₀' * η ^ K₀' * ((D:ℝ)/(L'':ℝ)) ^ K₀' * (L'':ℝ) ≤
        ‖∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
          * Work.Peluse.ee (β * (z:ℝ))‖ := by
      have hcongr : (∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Complex.exp (2 * Real.pi * Complex.I * (β:ℂ) * (z:ℂ)))
          = ∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Work.Peluse.ee (β * (z:ℝ)) := by
        refine tsum_congr (fun z => ?_)
        rw [Work.Peluse.exp_mul_eq_ee]
      rw [← hcongr]
      exact hβ
    have hL''Amax_nat : L'' ≤ ssAmaxA P A * Ns := by
      rw [hL''def]
      refine max_le ?_ ?_
      · exact dSup_div_add_one_le_A (P := P) (c := P.leadingCoeff) hclead1 hNs hN hsc
      · calc D ≤ Ns := Nat.cast_le.mp hDNs
          _ ≤ ssAmaxA P A * Ns := Nat.le_mul_of_pos_left Ns (ssAmaxA_pos P A)
    have hL''Amax : (L'':ℝ) ≤ (ssAmaxA P A : ℝ) * (Ns:ℝ) := by
      rw [← Nat.cast_mul]; exact_mod_cast hL''Amax_nat
    have hL''pos : (0:ℝ) < (L'':ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL''1)
    have hNspos : (0:ℝ) < (Ns:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs)
    have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
    have hratio : 2 / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) ≤
        ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
          (((P.leadingCoeff).natAbs : ℝ) * ((Work.Peluse.symIcc L'').card : ℝ)) := by
      have htmp : max ((Work.Peluse.dSup P Ns N) / P.leadingCoeff.natAbs + 1) D ≤ ssAmaxA P A * Ns := by
        rw [← hL''def]; exact hL''Amax_nat
      have h := symIcc_ratio_lower_A (P := P) (c := P.leadingCoeff) hclead hclead1 hNs hD1 htmp
      rw [hL''def]
      exact h
    have hηlb : 2 / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ)) * δ ≤ η := by
      rw [hηdef]
      exact mul_le_mul_of_nonneg_right hratio hδ0.le
    refine ⟨ξ, ?_⟩
    calc C₀' * (2 / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ))) ^ K₀' /
            (ssAmaxA P A : ℝ) ^ (K₀' - 1) * δ ^ K₀' * ((D:ℝ)/(Ns:ℝ)) ^ K₀' * (Ns:ℝ)
        ≤ C₀' * η ^ K₀' * ((D:ℝ)/(L'':ℝ)) ^ K₀' * (L'':ℝ) :=
          const_compare (K := K₀') (C := C₀') (δ := δ) (η := η)
            (cmin := 2 / (3 * (ssAmaxA P A : ℝ) * ((P.leadingCoeff).natAbs : ℝ)))
            (Amax := (ssAmaxA P A : ℝ)) (Ns := (Ns:ℝ)) (D := (D:ℝ)) (L'' := (L'':ℝ))
            hK₀'1 hC₀' (by positivity) hAmaxpos hδ0 hDpos hηlb hNspos hL''pos hL''Amax
      _ ≤ ‖∑' z : ℤ, Work.Peluse.dualFn N P f₀ f₁ (P.leadingCoeff * z + (r : ℤ))
            * Work.Peluse.ee (β * (z:ℝ))‖ := hβ'
      _ ≤ ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * Work.Peluse.ee (ξ * (x:ℝ))‖ := hξ
      _ = ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ := by
            congr 1
            exact tsum_congr (fun x => by rw [ss_ee_eq_exp])

end

end Work.Peluse.Ulower
