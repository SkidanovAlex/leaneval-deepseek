import Mathlib
import Submission.Work.BMF.recursion.LinnikDefs
import Submission.Work.BMF.recursion.LinnikStepDefs
import Submission.Work.BMF.recursion.linnik_reduce
import Submission.Work.BMF.recursion.linnik_lvl_one
import Submission.Work.BMF.N4chain.linnik_lin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# A self-contained Linnik bound for the recursion step

This module proves the shifted well-conditioned count used by `Work.BMF.recursion.I2_bound`
(`linnik_count`), together with the p-adic lifting step it needs (`linnik_step_aux`) and the
first-order binomial congruence on which the step rests (`add_pow_modEq_of_sq_dvd`).

The lifting step `linnik_step_aux` is *the same statement* as the still-`sorry`ed
`Work.BMF.recursion.linnik_step` in `recursion/linnik_step.lean`; it is proved here from the
in-workspace linear-counting lemma `Work.BMF.N4chain.linnik_lin` (Vandermonde/counting lemma
for the affine system `p ∣ C j + j·Σᵢ aᵢ^{j-1} wᵢ`, `ℓ+1 ≤ j ≤ k`), so that
`linnik_shift`-style bounds are available sorry-free to the rest of the recursion development.
-/

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

/-! ## First-order binomial congruence -/

/-- The binomial expansion of `(x+y)^j`, up to its first two terms; the remainder is a multiple
of `y^2`. -/
theorem add_pow_first_terms (x y : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    (x + y) ^ j = x ^ j + (j : ℤ) * x ^ (j - 1) * y
      + y ^ 2 * ∑ m ∈ Finset.range (j - 1), x ^ m * y ^ (j - 2 - m) * (j.choose m : ℤ) := by
  rcases Nat.lt_or_ge j 2 with hj1 | hj2
  · interval_cases j
    simp
  · have hbin := add_pow x y j
    have hsplit : (∑ m ∈ Finset.range (j + 1), x ^ m * y ^ (j - m) * (j.choose m : ℤ))
        = (∑ m ∈ Finset.range (j - 1), x ^ m * y ^ (j - m) * (j.choose m : ℤ))
          + (x ^ (j - 1) * y ^ (j - (j - 1)) * (j.choose (j - 1) : ℤ))
          + (x ^ j * y ^ (j - j) * (j.choose j : ℤ)) := by
      have h1 : j - 1 + 1 = j := Nat.sub_add_cancel hj
      have h2 : j + 1 = ((j - 1) + 1) + 1 := by omega
      conv_lhs => rw [h2]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, h1]
    have hsub : j - (j - 1) = 1 := by omega
    have hzero : j - j = 0 := Nat.sub_self j
    have hchoose : (j.choose (j - 1) : ℤ) = (j : ℤ) := by
      have hc : ((j - 1) + 1).choose (j - 1) = (j - 1) + 1 := Nat.choose_succ_self_right (j - 1)
      rw [Nat.sub_add_cancel hj] at hc
      exact_mod_cast hc
    have hchoose2 : (j.choose j : ℤ) = 1 := by simp
    rw [hbin, hsplit, hsub, hzero, pow_one, pow_zero, mul_one, hchoose, hchoose2, mul_one]
    rw [Finset.mul_sum]
    have hsum_eq : (∑ m ∈ Finset.range (j - 1), x ^ m * y ^ (j - m) * (j.choose m : ℤ))
        = ∑ m ∈ Finset.range (j - 1), y ^ 2 * (x ^ m * y ^ (j - 2 - m) * (j.choose m : ℤ)) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm' : m ≤ j - 2 := by have := Finset.mem_range.mp hm; omega
      have hexp : j - m = 2 + (j - 2 - m) := by omega
      rw [hexp, pow_add]
      ring
    rw [hsum_eq]
    ring

/-- **Divisibility form**: `y^2` divides `(x+y)^j - x^j - j x^{j-1} y`. -/
theorem sq_dvd_pow_sub_add (x y : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    y ^ 2 ∣ (x + y) ^ j - x ^ j - (j : ℤ) * x ^ (j - 1) * y := by
  refine ⟨∑ m ∈ Finset.range (j - 1), x ^ m * y ^ (j - 2 - m) * (j.choose m : ℤ), ?_⟩
  rw [add_pow_first_terms x y j hj]
  ring

/-- **First-order binomial congruence**: if `n ∣ y^2` then `(x+y)^j ≡ x^j + j x^{j-1} y`
modulo `n`. -/
theorem add_pow_modEq_of_sq_dvd (x y : ℤ) (j : ℕ) (hj : 1 ≤ j) (n : ℤ) (h : n ∣ y ^ 2) :
    (x + y) ^ j ≡ x ^ j + (j : ℤ) * x ^ (j - 1) * y [ZMOD n] := by
  obtain ⟨c, hc⟩ := sq_dvd_pow_sub_add x y j hj
  obtain ⟨e, he⟩ := h
  rw [Int.modEq_iff_dvd]
  refine ⟨-(e * c), ?_⟩
  rw [he] at hc
  linear_combination -hc

/-- `p^(ℓ+1)` divides the square of `p^ℓ * d`. -/
theorem prime_pow_sq_dvd (p ℓ : ℕ) (hℓ : 1 ≤ ℓ) (d : ℤ) :
    (p : ℤ) ^ (ℓ + 1) ∣ ((p : ℤ) ^ ℓ * d) ^ 2 := by
  have h : ℓ + 1 ≤ 2 * ℓ := by omega
  have h1 : (p : ℤ) ^ (ℓ + 1) ∣ (p : ℤ) ^ (2 * ℓ) := pow_dvd_pow (p : ℤ) h
  have h2 : (p : ℤ) ^ (2 * ℓ) ∣ ((p : ℤ) ^ ℓ * d) ^ 2 := by
    refine ⟨d ^ 2, ?_⟩
    rw [show 2 * ℓ = ℓ + ℓ by ring, pow_add]
    ring
  exact dvd_trans h1 h2

/-! ## The reduction lands in the lower level -/

lemma dvd_linnikRed_sub (p ℓ k : ℕ) (b : Fin k → Fin (p ^ (ℓ + 1))) (i : Fin k) :
    (p : ℤ) ^ ℓ ∣ ((linnikRed p ℓ k b i).val : ℤ) - ((b i).val : ℤ) := by
  have h := Nat.mod_add_div (b i).val (p ^ ℓ)
  have hcast : ((((b i).val % p ^ ℓ + p ^ ℓ * ((b i).val / p ^ ℓ) : ℕ)) : ℤ) = ((b i).val : ℤ) := by
    rw [h]
  have hsplit : ((b i).val : ℤ)
      = (((b i).val % p ^ ℓ : ℕ) : ℤ) + (p : ℤ) ^ ℓ * (((b i).val / p ^ ℓ : ℕ) : ℤ) := by
    rw [← hcast]
    push_cast
    ring
  rw [linnikRed_apply, hsplit]
  exact ⟨-(((b i).val / p ^ ℓ : ℕ) : ℤ), by ring⟩

/-- Reducing a level-`(ℓ+1)` tuple modulo `p^ℓ` gives a level-`ℓ` tuple. -/
theorem linnikRed_mem_Lvl (p k ℓ : ℕ) (hp : p.Prime) (hℓ : 1 ≤ ℓ) (H : ℕ → ℕ)
    {b : Fin k → Fin (p ^ (ℓ + 1))} (hb : b ∈ Lvl p k (ℓ + 1) H) :
    linnikRed p ℓ k b ∈ Lvl p k ℓ H := by
  classical
  obtain ⟨-, hbdist, hbdiv⟩ := Finset.mem_filter.mp hb
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i j hij hcontra
    apply hbdist i j hij
    have h1 : (((linnikRed p ℓ k b i).val : ℕ) : ZMod p) = (((b i).val : ℕ) : ZMod p) := by
      rw [linnikRed_apply, ZMod.natCast_eq_natCast_iff]
      exact Nat.ModEq.of_dvd (by simpa using pow_dvd_pow p hℓ)
        (Nat.mod_modEq (b i).val (p ^ ℓ))
    have h2 : (((linnikRed p ℓ k b j).val : ℕ) : ZMod p) = (((b j).val : ℕ) : ZMod p) := by
      rw [linnikRed_apply, ZMod.natCast_eq_natCast_iff]
      exact Nat.ModEq.of_dvd (by simpa using pow_dvd_pow p hℓ)
        (Nat.mod_modEq (b j).val (p ^ ℓ))
    rw [h1, h2] at hcontra
    exact hcontra
  · intro j hj1 hj2
    by_cases hjle : j ≤ ℓ
    · have hmin1 : min j (ℓ + 1) = j := by omega
      have hmin2 : min j ℓ = j := by omega
      have hd : (p : ℤ) ^ j ∣ (∑ i, ((b i).val : ℤ) ^ j) - (H j : ℤ) := by
        have := hbdiv j hj1 hj2
        rwa [hmin1] at this
      have hsum : (p : ℤ) ^ j ∣
          (∑ i, (((linnikRed p ℓ k b i).val : ℤ)) ^ j) - (∑ i, ((b i).val : ℤ) ^ j) :=
        pow_sum_congr ((p : ℤ) ^ j) k j (fun i => (b i).val)
          (fun i => (linnikRed p ℓ k b i).val)
          (fun i => dvd_trans (pow_dvd_pow (p : ℤ) hjle) (dvd_linnikRed_sub p ℓ k b i))
      rw [hmin2]
      have hfinal := dvd_add hsum hd
      convert hfinal using 1
      ring
    · have hmin1 : min j (ℓ + 1) = ℓ + 1 := by omega
      have hmin2 : min j ℓ = ℓ := by omega
      have hd : (p : ℤ) ^ (ℓ + 1) ∣ (∑ i, ((b i).val : ℤ) ^ j) - (H j : ℤ) := by
        have := hbdiv j hj1 hj2
        rwa [hmin1] at this
      have hd' : (p : ℤ) ^ ℓ ∣ (∑ i, ((b i).val : ℤ) ^ j) - (H j : ℤ) :=
        dvd_trans (pow_dvd_pow (p : ℤ) (by omega : ℓ ≤ ℓ + 1)) hd
      have hsum : (p : ℤ) ^ ℓ ∣
          (∑ i, (((linnikRed p ℓ k b i).val : ℤ)) ^ j) - (∑ i, ((b i).val : ℤ) ^ j) :=
        pow_sum_congr ((p : ℤ) ^ ℓ) k j (fun i => (b i).val)
          (fun i => (linnikRed p ℓ k b i).val) (fun i => dvd_linnikRed_sub p ℓ k b i)
      rw [hmin2]
      have hfinal := dvd_add hsum hd'
      convert hfinal using 1
      ring

/-! ## The fibre bound and the lifting step -/

/-- The quotient digit of a level-`(ℓ+1)` tuple, viewed in `Fin p`. -/
def liftDigit (p ℓ : ℕ) {k : ℕ} (b : Fin k → Fin (p ^ (ℓ + 1))) : Fin k → Fin p :=
  fun i => ⟨(b i).val / p ^ ℓ, by
    apply Nat.div_lt_of_lt_mul
    calc (b i).val < p ^ (ℓ + 1) := (b i).isLt
      _ = p ^ ℓ * p := pow_succ p ℓ⟩

theorem liftDigit_apply (p ℓ : ℕ) {k : ℕ} (b : Fin k → Fin (p ^ (ℓ + 1))) (i : Fin k) :
    (liftDigit p ℓ b i).val = (b i).val / p ^ ℓ := rfl

/-- **The fibre bound of the lifting step.**  Each fibre of the reduction map has at most `p^ℓ`
elements. -/
theorem linnik_fibre_card (p k ℓ : ℕ) (hp : p.Prime) (hk : k < p) (hℓ : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (H : ℕ → ℕ) (b0 : Fin k → Fin (p ^ ℓ)) (hb0 : b0 ∈ Lvl p k ℓ H) :
    ((Lvl p k (ℓ + 1) H).filter (fun b => linnikRed p ℓ k b = b0)).card ≤ p ^ ℓ := by
  classical
  have hppos : 0 < p := hp.pos
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set a : Fin k → Fin p := fun i => ⟨(b0 i).val % p, Nat.mod_lt _ hppos⟩ with ha
  have hainj : Function.Injective a := by
    intro i j hij
    by_contra hne
    refine (Finset.mem_filter.mp hb0).2.1 i j hne ?_
    have h1 : (b0 i).val % p = (b0 j).val % p := by
      have := congrArg Fin.val hij
      simpa only [ha] using this
    rw [ZMod.natCast_eq_natCast_iff']
    exact h1
  set C : ℕ → ℤ := fun j => ((∑ i, ((b0 i).val : ℤ) ^ j) - (H j : ℤ)) / (p : ℤ) ^ ℓ with hC
  have hlin := _root_.Work.BMF.N4chain.linnik_lin p k ℓ hp hk hℓ hℓk a hainj C
  refine le_trans (Finset.card_le_card_of_injOn (fun b => liftDigit p ℓ b) ?_ ?_) hlin
  · intro b hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨hbLvl, hbred⟩ := hb
    have hbdiv := (Finset.mem_filter.mp hbLvl).2.2
    have hb0div := (Finset.mem_filter.mp hb0).2.2
    intro j hj1 hj2
    have hmin1 : min j (ℓ + 1) = ℓ + 1 := by omega
    have hmin2 : min j ℓ = ℓ := by omega
    have hY : (p : ℤ) ^ ℓ ∣ (∑ i, ((b0 i).val : ℤ) ^ j) - (H j : ℤ) := by
      have h := hb0div j (by omega) hj2
      rwa [hmin2] at h
    have hlift : (p : ℤ) ^ (ℓ + 1) ∣ (∑ i, ((b i).val : ℤ) ^ j) - (H j : ℤ) := by
      have h := hbdiv j (by omega) hj2
      rwa [hmin1] at h
    -- the digit expansion of a lift
    have hdigit : ∀ i, ((b i).val : ℤ)
        = ((b0 i).val : ℤ) + (p : ℤ) ^ ℓ * ((liftDigit p ℓ b i).val : ℤ) := by
      intro i
      have h1 : (b i).val % p ^ ℓ = (b0 i).val := by
        have := congrArg Fin.val (congrFun hbred i)
        simpa only [linnikRed_apply] using this
      have hmod := Nat.mod_add_div (b i).val (p ^ ℓ)
      have hcast : ((((b i).val % p ^ ℓ + p ^ ℓ * ((b i).val / p ^ ℓ) : ℕ)) : ℤ) = ((b i).val : ℤ) := by
        rw [hmod]
      have hsplit : ((b i).val : ℤ)
          = (((b i).val % p ^ ℓ : ℕ) : ℤ) + (p : ℤ) ^ ℓ * (((b i).val / p ^ ℓ : ℕ) : ℤ) := by
        rw [← hcast]
        push_cast
        ring
      rw [hsplit, h1, liftDigit_apply]
    -- first-order expansion, term by term
    have hper : ∀ i, ((b i).val : ℤ) ^ j ≡ ((b0 i).val : ℤ) ^ j
        + (j : ℤ) * ((b0 i).val : ℤ) ^ (j - 1)
          * ((p : ℤ) ^ ℓ * ((liftDigit p ℓ b i).val : ℤ)) [ZMOD (p : ℤ) ^ (ℓ + 1)] := by
      intro i
      conv_lhs => rw [hdigit i]
      exact add_pow_modEq_of_sq_dvd _ _ j (by omega : 1 ≤ j) _ (prime_pow_sq_dvd p ℓ hℓ _)
    have hsum := Int.ModEq.sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hper i)
    have hsum' : (∑ i, ((b i).val : ℤ) ^ j) ≡ (∑ i, ((b0 i).val : ℤ) ^ j)
        + (j : ℤ) * (p : ℤ) ^ ℓ
          * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ))
        [ZMOD (p : ℤ) ^ (ℓ + 1)] := by
      have h2 : (∑ i, (j : ℤ) * ((b0 i).val : ℤ) ^ (j - 1)
            * ((p : ℤ) ^ ℓ * ((liftDigit p ℓ b i).val : ℤ)))
          = (j : ℤ) * (p : ℤ) ^ ℓ
            * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [Finset.sum_add_distrib, h2] at hsum
      exact hsum
    have hA : (p : ℤ) ^ (ℓ + 1) ∣ (∑ i, ((b0 i).val : ℤ) ^ j)
        + (j : ℤ) * (p : ℤ) ^ ℓ
          * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ))
        - (∑ i, ((b i).val : ℤ) ^ j) := Int.modEq_iff_dvd.mp hsum'
    have hkey : (p : ℤ) ^ (ℓ + 1) ∣ (∑ i, ((b0 i).val : ℤ) ^ j)
        + (j : ℤ) * (p : ℤ) ^ ℓ
          * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ))
        - (H j : ℤ) := by
      have := dvd_add hA hlift
      convert this using 1
      ring
    -- divide by `p^ℓ`
    have hCval : C j * (p : ℤ) ^ ℓ = (∑ i, ((b0 i).val : ℤ) ^ j) - (H j : ℤ) := by
      rw [hC]
      exact Int.ediv_mul_cancel hY
    obtain ⟨m, hm⟩ := hkey
    have hW : (p : ℤ) ∣ C j + (j : ℤ)
        * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)) := by
      refine ⟨m, ?_⟩
      have h3 : (p : ℤ) ^ ℓ * (C j + (j : ℤ)
            * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)))
          = (p : ℤ) ^ ℓ * ((p : ℤ) * m) := by
        have h4 : (p : ℤ) ^ ℓ * (C j + (j : ℤ)
              * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)))
            = C j * (p : ℤ) ^ ℓ + (j : ℤ) * (p : ℤ) ^ ℓ
              * (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)) := by
          ring
        rw [h4, hCval]
        have h5 : (p : ℤ) ^ (ℓ + 1) * m = (p : ℤ) ^ ℓ * ((p : ℤ) * m) := by
          rw [pow_succ]
          ring
        rw [← h5, ← hm]
        ring
      exact mul_left_cancel₀ (pow_ne_zero ℓ hpz) h3
    -- replace the base residues by their residues mod `p`
    have hreplace : (p : ℤ) ∣ (∑ i, ((b0 i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ))
        - (∑ i, ((a i).val : ℤ) ^ (j - 1) * ((liftDigit p ℓ b i).val : ℤ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum (fun i _ => ?_)
      have h1 : (p : ℤ) ∣ ((b0 i).val : ℤ) - ((a i).val : ℤ) := by
        rw [ha]
        simpa using dvd_sub_mod p (b0 i).val
      have h2 : (p : ℤ) ∣ ((b0 i).val : ℤ) ^ (j - 1) - ((a i).val : ℤ) ^ (j - 1) :=
        dvd_trans h1 (sub_dvd_pow_sub_pow _ _ (j - 1))
      have h3 := dvd_mul_of_dvd_left h2 (((liftDigit p ℓ b i).val : ℤ))
      convert h3 using 1
      ring
    have hsub2 := dvd_sub hW (dvd_mul_of_dvd_right hreplace (j : ℤ))
    convert hsub2 using 1
    ring
  · intro b hb c hc hbc
    simp only [Finset.mem_coe, Finset.mem_filter] at hb hc
    funext i
    apply Fin.ext
    have h1 : (b i).val % p ^ ℓ = (b0 i).val := by
      have := congrArg Fin.val (congrFun hb.2 i)
      simpa only [linnikRed_apply] using this
    have h2 : (c i).val % p ^ ℓ = (b0 i).val := by
      have := congrArg Fin.val (congrFun hc.2 i)
      simpa only [linnikRed_apply] using this
    have h3 : (b i).val / p ^ ℓ = (c i).val / p ^ ℓ := by
      have := congrArg Fin.val (congrFun hbc i)
      simpa only [liftDigit_apply] using this
    have hb1 := Nat.mod_add_div (b i).val (p ^ ℓ)
    have hc1 := Nat.mod_add_div (c i).val (p ^ ℓ)
    calc (b i).val = (b i).val % p ^ ℓ + p ^ ℓ * ((b i).val / p ^ ℓ) := hb1.symm
      _ = (b0 i).val + p ^ ℓ * ((b i).val / p ^ ℓ) := by rw [h1]
      _ = (b0 i).val + p ^ ℓ * ((c i).val / p ^ ℓ) := by rw [h3]
      _ = (c i).val % p ^ ℓ + p ^ ℓ * ((c i).val / p ^ ℓ) := by rw [h2]
      _ = (c i).val := hc1

/-- **The p-adic lifting step** (Linnik). -/
theorem linnik_step_aux (p k ℓ : ℕ) (hp : p.Prime) (hk : k < p) (hℓ : 1 ≤ ℓ) (hℓk : ℓ + 1 ≤ k)
    (H : ℕ → ℕ) :
    (Lvl p k (ℓ + 1) H).card ≤ p ^ ℓ * (Lvl p k ℓ H).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to
    (fun b hb => linnikRed_mem_Lvl p k ℓ hp hℓ H hb) (p ^ ℓ)
    (fun b0 hb0 => linnik_fibre_card p k ℓ hp hk hℓ hℓk H b0 hb0)

/-- **Linnik's bound** (shifted well-conditioned count), proved here from the level induction
using the in-workspace `linnik_reduce`, `linnik_lvl_one` and the lifting step `linnik_step_aux`. -/
theorem linnik_count (p k X y : ℕ) (hp : p.Prime) (hk : k < p) (hX : X < p ^ k) (H : ℕ → ℕ) :
    ((Finset.univ : Finset (Tup k X)).filter (fun a =>
      (∀ i j : Fin k, i ≠ j → ¬ (p : ℤ) ∣ (((a i).1 : ℤ) - ((a j).1 : ℤ))) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ k →
        ((p : ℤ) ^ j) ∣ ((∑ i, (((a i).1 : ℤ) - (y : ℤ)) ^ j) - (H j : ℤ))))).card
    ≤ k.factorial * p ^ (k * (k - 1) / 2) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_univ]
    simp
  · refine le_trans (linnik_reduce p k X y hp hX H) ?_
    have hmain : ∀ m, m ≤ k → 1 ≤ m →
        (Lvl p k m H).card ≤ k.factorial * p ^ (∑ i ∈ Finset.range m, i) := by
      intro m
      induction m with
      | zero => intro _ h; omega
      | succ m ih =>
        intro hmk hm1
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          have h1 := linnik_lvl_one p k hp hk H
          simpa using h1
        · have hstep := linnik_step_aux p k m hp hk hmpos (by omega) H
          have hprev := ih (by omega) hmpos
          calc (Lvl p k (m + 1) H).card
              ≤ p ^ m * (Lvl p k m H).card := hstep
            _ ≤ p ^ m * (k.factorial * p ^ (∑ i ∈ Finset.range m, i)) :=
                Nat.mul_le_mul_left _ hprev
            _ = k.factorial * p ^ (∑ i ∈ Finset.range (m + 1), i) := by
                rw [Finset.sum_range_succ, pow_add]
                ring
    have hk_end := hmain k le_rfl hkpos
    rw [Finset.sum_range_id k] at hk_end
    exact hk_end


end

end Work.BMF.recursion
