import Mathlib
import Submission.Work.HP.Defs

/-!
# The dyadic sum bound for a `D`-count

Given a finite family `D : ι → ℝ` with `1 ≤ D p ≤ Λ` and the counting hypothesis

`#{p | D p ≤ Δ} ≤ C · Δ^s   (Δ ≥ 1)`

together with `0 ≤ s ≤ m`, we bound the dyadic sum

`∑ p, (D p)^(-m) ≤ C · 2^s · (⌈logb 2 Λ⌉₊ + 1)`.

The proof groups the points `p` into the dyadic shells `[2^j, 2^(j+1))`, where `j = ⌊logb 2 (D p)⌋₊`,
so that the `j`-th shell is contained in `{p | D p ≤ 2^(j+1)}` and thus has at most `C · 2^((j+1)s)`
elements, while each term in it is at most `2^(-j m)`.  The shell contribution is therefore
`≤ C · 2^s` (using `j (s - m) ≤ 0`), and there are `⌈logb 2 Λ⌉₊ + 1` shells.
-/

set_option linter.unusedVariables false

namespace Work.HP.MDEstimates

open Finset
open scoped BigOperators

/-- Dyadic bracketing of a real number `D ≥ 1`: with `k = ⌊logb 2 D⌋₊` one has
`2^k ≤ D < 2^(k+1)`, and if also `D ≤ Λ` then `k ≤ ⌈logb 2 Λ⌉₊`. -/
theorem dyadic_index_props (D Λ : ℝ) (hD : 1 ≤ D) (hDΛ : D ≤ Λ) :
    (2:ℝ)^(⌊Real.logb 2 D⌋₊ : ℝ) ≤ D ∧
    D < (2:ℝ)^((⌊Real.logb 2 D⌋₊ : ℝ) + 1) ∧
    ⌊Real.logb 2 D⌋₊ ≤ ⌈Real.logb 2 Λ⌉₊ := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD
  have hlog0 : 0 ≤ Real.logb 2 D := Real.logb_nonneg (by norm_num) hD
  have hlogeq : (2:ℝ) ^ Real.logb 2 D = D := Real.rpow_logb (by norm_num) (by norm_num) hD0
  refine ⟨?_, ?_, ?_⟩
  · calc (2:ℝ)^(⌊Real.logb 2 D⌋₊ : ℝ) ≤ (2:ℝ)^(Real.logb 2 D) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
      _ = D := hlogeq
  · calc D = (2:ℝ)^(Real.logb 2 D) := hlogeq.symm
      _ < (2:ℝ)^((⌊Real.logb 2 D⌋₊ : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Nat.lt_floor_add_one _)
  · have hlogΛ : Real.logb 2 D ≤ Real.logb 2 Λ :=
      Real.logb_le_logb_of_le (by norm_num) hD0 hDΛ
    have hlogΛ0 : 0 ≤ Real.logb 2 Λ := Real.logb_nonneg (by norm_num) (le_trans hD hDΛ)
    have h1 : ⌊Real.logb 2 D⌋₊ ≤ ⌊Real.logb 2 Λ⌋₊ := Nat.floor_mono hlogΛ
    have h2 : ⌊Real.logb 2 Λ⌋₊ ≤ ⌈Real.logb 2 Λ⌉₊ := by
      have hle : ((⌊Real.logb 2 Λ⌋₊ : ℝ)) ≤ ((⌈Real.logb 2 Λ⌉₊ : ℝ)) :=
        le_trans (Nat.floor_le hlogΛ0) (Nat.le_ceil _)
      exact_mod_cast hle
    exact le_trans h1 h2

/-- The shell estimate: for `0 ≤ s ≤ m` and `j : ℕ`,
`(2^(j+1))^s · 2^(-(j m)) ≤ 2^s`. -/
theorem dyadic_rpow_term (j : ℕ) {s m : ℝ} (hs : 0 ≤ s) (hsm : s ≤ m) :
    ((2:ℝ)^((j:ℝ)+1))^s * (2:ℝ)^(-(j:ℝ)*m) ≤ (2:ℝ)^s := by
  have hexp : ((j:ℝ)+1)*s + (-(j:ℝ)*m) ≤ s := by
    have hjm : (j:ℝ) * (s - m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg j) (by linarith)
    nlinarith [hjm]
  calc ((2:ℝ)^((j:ℝ)+1))^s * (2:ℝ)^(-(j:ℝ)*m)
      = (2:ℝ)^(((j:ℝ)+1)*s) * (2:ℝ)^(-(j:ℝ)*m) := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((j:ℝ)+1) s]
    _ = (2:ℝ)^(((j:ℝ)+1)*s + (-(j:ℝ)*m)) := (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2:ℝ)^s := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- The `j`-th dyadic shell `{p | ⌊logb 2 (D p)⌋₊ = j}` has at most `C · (2^(j+1))^s` elements,
as an immediate consequence of the counting hypothesis `hN` at `Δ = 2^(j+1)` (the shell is
contained in `{p | D p ≤ 2^(j+1)}`). -/
theorem dyadic_fiber_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (C s : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s) (hD1 : ∀ p, 1 ≤ D p)
    (hN : ∀ Δ : ℝ, 1 ≤ Δ → (({p | D p ≤ Δ} : Set ι).ncard : ℝ) ≤ C * Δ ^ s)
    (j : ℕ) :
    ((Finset.univ.filter (fun p => ⌊Real.logb 2 (D p)⌋₊ = j)).card : ℝ)
      ≤ C * ((2:ℝ)^((j:ℝ)+1))^s := by
  classical
  have hΔ1 : 1 ≤ (2:ℝ)^((j:ℝ)+1) := by
    rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hsub : Finset.univ.filter (fun p => ⌊Real.logb 2 (D p)⌋₊ = j) ⊆
      Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hD0 : (0:ℝ) < D p := lt_of_lt_of_le one_pos (hD1 p)
    have hlt : D p < (2:ℝ)^((⌊Real.logb 2 (D p)⌋₊ : ℝ) + 1) := by
      calc D p = (2:ℝ)^Real.logb 2 (D p) :=
            (Real.rpow_logb (by norm_num) (by norm_num) hD0).symm
        _ < (2:ℝ)^((⌊Real.logb 2 (D p)⌋₊ : ℝ) + 1) :=
              Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Nat.lt_floor_add_one _)
    rw [hp] at hlt
    exact le_of_lt hlt
  have h1 : (Finset.univ.filter (fun p => ⌊Real.logb 2 (D p)⌋₊ = j)).card
      ≤ (Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1))).card :=
    Finset.card_le_card hsub
  have hset : (↑(Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1))) : Set ι)
      = {p | D p ≤ (2:ℝ)^((j:ℝ)+1)} := by
    ext p
    simp
  have h2 : ((Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1))).card : ℝ)
      = (({p | D p ≤ (2:ℝ)^((j:ℝ)+1)} : Set ι).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset (Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1))), hset]
  have h3 := hN ((2:ℝ)^((j:ℝ)+1)) hΔ1
  have h4 : ((Finset.univ.filter (fun p => ⌊Real.logb 2 (D p)⌋₊ = j)).card : ℝ)
      ≤ ((Finset.univ.filter (fun p => D p ≤ (2:ℝ)^((j:ℝ)+1))).card : ℝ) := by
    exact_mod_cast h1
  linarith [h4, h2, h3]

/-- **The dyadic sum bound.** -/
theorem dyadic_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → ℝ) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hD1 : ∀ p, 1 ≤ D p) (hDΛ : ∀ p, D p ≤ Λ) (C s m : ℝ) (hC : 0 ≤ C) (hs : 0 ≤ s) (hsm : s ≤ m)
    (hN : ∀ Δ : ℝ, 1 ≤ Δ → (({p | D p ≤ Δ} : Set ι).ncard : ℝ) ≤ C * Δ ^ s) :
    (∑ p, (D p) ^ (-m)) ≤ C * 2 ^ s * ((⌈Real.logb 2 Λ⌉₊ : ℝ) + 1) := by
  classical
  set K : ℕ := ⌈Real.logb 2 Λ⌉₊ with hK
  have hm0 : 0 ≤ m := le_trans hs hsm
  -- pointwise bound of each term by the power of two attached to its shell
  have hterm : ∀ p, (D p) ^ (-m) ≤ (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m) := by
    intro p
    have hD0 : (0:ℝ) < D p := lt_of_lt_of_le one_pos (hD1 p)
    have hlog0 : 0 ≤ Real.logb 2 (D p) := Real.logb_nonneg (by norm_num) (hD1 p)
    have hlow : (2:ℝ)^(⌊Real.logb 2 (D p)⌋₊ : ℝ) ≤ D p :=
      calc (2:ℝ)^(⌊Real.logb 2 (D p)⌋₊ : ℝ) ≤ (2:ℝ)^(Real.logb 2 (D p)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
        _ = D p := Real.rpow_logb (by norm_num) (by norm_num) hD0
    have hpos2 : (0:ℝ) < (2:ℝ)^(⌊Real.logb 2 (D p)⌋₊ : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc (D p) ^ (-m) ≤ ((2:ℝ)^(⌊Real.logb 2 (D p)⌋₊ : ℝ)) ^ (-m) :=
          Real.rpow_le_rpow_of_nonpos hpos2 hlow (by linarith)
      _ = (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m) := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (⌊Real.logb 2 (D p)⌋₊ : ℝ) (-m)]
          congr 1
          ring
  have step1 : (∑ p, (D p) ^ (-m))
      ≤ ∑ p, (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m) :=
    Finset.sum_le_sum (fun p _ => hterm p)
  -- the shells partition the index set
  have hmap : ∀ p ∈ (Finset.univ : Finset ι), ⌊Real.logb 2 (D p)⌋₊ ∈ Finset.range (K + 1) := by
    intro p _
    rw [Finset.mem_range]
    have h := (dyadic_index_props (D p) Λ (hD1 p) (hDΛ p)).2.2
    rw [hK]
    exact Nat.lt_succ_of_le h
  have fiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun p => (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m))
  have hinner : ∀ j ∈ Finset.range (K + 1),
      (∑ i ∈ Finset.univ.filter (fun i => ⌊Real.logb 2 (D i)⌋₊ = j),
        (2:ℝ)^(-(⌊Real.logb 2 (D i)⌋₊ : ℝ) * m)) ≤ C * 2^s := by
    intro j _
    have hconstant : (∑ i ∈ Finset.univ.filter (fun i => ⌊Real.logb 2 (D i)⌋₊ = j),
        (2:ℝ)^(-(⌊Real.logb 2 (D i)⌋₊ : ℝ) * m))
        = ((Finset.univ.filter (fun i => ⌊Real.logb 2 (D i)⌋₊ = j)).card : ℝ)
          * (2:ℝ)^(-(j:ℝ)*m) := by
      have hc : ∀ i ∈ Finset.univ.filter (fun i => ⌊Real.logb 2 (D i)⌋₊ = j),
          (2:ℝ)^(-(⌊Real.logb 2 (D i)⌋₊ : ℝ) * m) = (2:ℝ)^(-(j:ℝ)*m) := by
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    have hcard := dyadic_fiber_card_le D C s hC hs hD1 hN j
    have hrpow := dyadic_rpow_term j hs hsm
    rw [hconstant]
    calc ((Finset.univ.filter (fun i => ⌊Real.logb 2 (D i)⌋₊ = j)).card : ℝ)
            * (2:ℝ)^(-(j:ℝ)*m)
        ≤ (C * ((2:ℝ)^((j:ℝ)+1))^s) * (2:ℝ)^(-(j:ℝ)*m) :=
          mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by norm_num) _)
      _ = C * (((2:ℝ)^((j:ℝ)+1))^s * (2:ℝ)^(-(j:ℝ)*m)) := by ring
      _ ≤ C * (2:ℝ)^s := mul_le_mul_of_nonneg_left hrpow hC
  have step2 : (∑ p, (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m))
      ≤ ∑ j ∈ Finset.range (K + 1), C * 2^s := by
    rw [← fiber]
    exact Finset.sum_le_sum hinner
  have step3 : (∑ j ∈ Finset.range (K + 1), C * 2^s) = ((K:ℝ) + 1) * (C * 2^s) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  calc (∑ p, (D p) ^ (-m))
      ≤ ∑ p, (2:ℝ)^(-(⌊Real.logb 2 (D p)⌋₊ : ℝ) * m) := step1
    _ ≤ ∑ j ∈ Finset.range (K + 1), C * 2^s := step2
    _ = ((K:ℝ) + 1) * (C * 2^s) := step3
    _ = C * 2 ^ s * ((⌈Real.logb 2 Λ⌉₊ : ℝ) + 1) := by
        rw [hK]
        ring

end Work.HP.MDEstimates
