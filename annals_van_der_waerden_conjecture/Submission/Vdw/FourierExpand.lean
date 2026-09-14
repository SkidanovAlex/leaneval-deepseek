import Mathlib
import Submission.Vdw.Counting
import Submission.Commons.NumberTheory.ZMod.norm_sum_box_stdAddChar_le

open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Fourier expansion of an indicator function on `(ZMod p)^m` (paper §4)

The second half of the Fourier-equidistribution method of the paper's §4: the
indicator of a finite set `T` of residue vectors, evaluated at the residues of
the elements of `s ⊆ ι`, expands as

    `1_T (w y) = p^{-m} Σ_{a ∈ (Z/p)^m} (Σ_{x ∈ T} χ (a·x)) · χ (-(a·w y))`

with `χ = ZMod.stdAddChar`.  This is the orthogonality
`Σ_{a} χ (a·(x-y)) = p^m [x = y]` (`sum_stdAddChar_coord`, proved coordinatewise
from `AddChar.sum_mulShift` and the primitivity of `stdAddChar`) combined with
the multiplicativity of the character over sums
(`Commons.NumberTheory.ZMod.AddChar.map_sum_eq_prod`).

The companion module `Submission/Vdw/BoxFourier.lean` bounds each of the two
factors over a box of integer coefficient vectors, so that

    # {z ∈ box : residue (z) ∈ T} ≤ |T|·|box|/p^m + (error term)

with the error term controlled by the Fourier coefficients of `T` — the shape
of the paper's Corollary `index2forms`/`fbound2`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

lemma sum_stdAddChar_coord (p : ℕ) [Fact p.Prime] (m : ℕ) (x : Fin m → ZMod p) :
    ∑ a : Fin m → ZMod p, ZMod.stdAddChar (∑ i, a i * x i)
      = if x = 0 then (p : ℂ) ^ m else 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hfac : ∑ a : Fin m → ZMod p, ZMod.stdAddChar (∑ i, a i * x i)
      = ∏ i : Fin m, ∑ b : ZMod p, ZMod.stdAddChar (b * x i) := by
    rw [Finset.prod_univ_sum (t := fun _ : Fin m => (Finset.univ : Finset (ZMod p)))]
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact (Commons.NumberTheory.ZMod.AddChar.map_sum_eq_prod ZMod.stdAddChar Finset.univ
      (fun i => a i * x i))
  rw [hfac]
  have h1 : ∀ i : Fin m, ∑ b : ZMod p, ZMod.stdAddChar (b * x i)
      = if x i = 0 then (p : ℂ) else 0 := by
    intro i
    rw [AddChar.sum_mulShift (x i) (ZMod.isPrimitive_stdAddChar p), ZMod.card p]
    push_cast
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  by_cases hx : x = 0
  · subst hx
    simp [Finset.prod_const]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hx (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), if_neg hx]

lemma norm_stdAddChar_eq_one {p : ℕ} [NeZero p] (x : ZMod p) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma stdAddChar_neg_eq_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    ZMod.stdAddChar (-x) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (norm_stdAddChar_eq_one x)

lemma indicator_eq_inv_mul_sum (p : ℕ) [Fact p.Prime] (m : ℕ)
    (x y : Fin m → ZMod p) :
    (if x = y then (1 : ℂ) else 0)
      = ((p : ℂ) ^ m)⁻¹ * ∑ a : Fin m → ZMod p, ZMod.stdAddChar (∑ i, a i * (x i - y i)) := by
  have hp : ((p : ℂ) ^ m) ≠ 0 := by
    have h : (p : ℂ) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    exact pow_ne_zero _ h
  have hcoord : ∑ a : Fin m → ZMod p, ZMod.stdAddChar (∑ i, a i * (x i - y i))
      = if x - y = 0 then (p : ℂ) ^ m else 0 := by
    simpa only [Pi.sub_apply] using sum_stdAddChar_coord p m (x - y)
  rw [hcoord]
  by_cases h : x = y
  · have hz : x - y = 0 := by rw [h, sub_self]
    rw [if_pos h, hz, if_pos rfl]
    exact (inv_mul_cancel₀ hp).symm
  · have h2 : x - y ≠ 0 := fun hz => h (sub_eq_zero.mp hz)
    rw [if_neg h, if_neg h2, mul_zero]

lemma stdAddChar_sub_eq_mul (p : ℕ) [Fact p.Prime] (m : ℕ)
    (a x y : Fin m → ZMod p) :
    ZMod.stdAddChar (∑ i, a i * (x i - y i))
      = ZMod.stdAddChar (∑ i, a i * x i) * ZMod.stdAddChar (-(∑ i, a i * y i)) := by
  have harg : (∑ i, a i * (x i - y i)) = (∑ i, a i * x i) - (∑ i, a i * y i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [harg, AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.map_neg_eq_inv]

/-- **Fourier expansion of the indicator of a finite set of residues**:
summing the indicator of `T` over the residues of the elements of `s ⊆ ι`
equals `p^{-m}` times the sum over frequencies of the product of the
`T`-Fourier sum and the character sum over `s`. -/
lemma sum_indicator_comp_eq_fourier (p : ℕ) [Fact p.Prime] (m : ℕ)
    (T : Finset (Fin m → ZMod p)) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → (Fin m → ZMod p)) :
    ∑ y ∈ s, (if w y ∈ T then (1 : ℂ) else 0)
      = ((p : ℂ) ^ m)⁻¹ * ∑ a : Fin m → ZMod p,
          (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
            (∑ y ∈ s, ZMod.stdAddChar (-(∑ i, a i * w y i))) := by
  classical
  have hk : ∀ y : ι, (if w y ∈ T then (1 : ℂ) else 0)
      = ∑ x ∈ T, (if x = w y then (1 : ℂ) else 0) := by
    intro y
    rw [Finset.sum_ite_eq' T (w y) (fun _ => (1 : ℂ))]
  calc ∑ y ∈ s, (if w y ∈ T then (1 : ℂ) else 0)
      = ∑ y ∈ s, ∑ x ∈ T, (if x = w y then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl (fun y _ => hk y)
    _ = ∑ x ∈ T, ∑ y ∈ s, (if x = w y then (1 : ℂ) else 0) := Finset.sum_comm
    _ = ∑ x ∈ T, ∑ y ∈ s,
          ((p : ℂ) ^ m)⁻¹ * ∑ a : Fin m → ZMod p,
            ZMod.stdAddChar (∑ i, a i * (x i - w y i)) :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
          (fun y _ => indicator_eq_inv_mul_sum p m x (w y)))
    _ = ((p : ℂ) ^ m)⁻¹ * ∑ x ∈ T, ∑ y ∈ s, ∑ a : Fin m → ZMod p,
          ZMod.stdAddChar (∑ i, a i * (x i - w y i)) := by
        simp_rw [Finset.mul_sum]
    _ = ((p : ℂ) ^ m)⁻¹ * ∑ a : Fin m → ZMod p, ∑ x ∈ T, ∑ y ∈ s,
          ZMod.stdAddChar (∑ i, a i * (x i - w y i)) := by
        congr 1
        have h1 : (∑ x ∈ T, ∑ y ∈ s, ∑ a : Fin m → ZMod p,
              ZMod.stdAddChar (∑ i, a i * (x i - w y i)))
            = ∑ x ∈ T, ∑ a : Fin m → ZMod p, ∑ y ∈ s,
              ZMod.stdAddChar (∑ i, a i * (x i - w y i)) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
        rw [h1, Finset.sum_comm]
    _ = ((p : ℂ) ^ m)⁻¹ * ∑ a : Fin m → ZMod p,
          (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
            (∑ y ∈ s, ZMod.stdAddChar (-(∑ i, a i * w y i))) := by
        congr 1
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl
          (fun y _ => stdAddChar_sub_eq_mul p m a x (w y)))

/-! ## The box-counting inequality

With the Fourier expansion in hand, the count of the box elements whose
residue lies in `T` is bounded by the main term `|T|·|box|/p^m` plus an error
term in which each nonzero frequency `a` contributes the product of the two
Fourier factors: the `T`-Fourier sum (bounded by `B`) and the box character
sum (bounded by `W a`).  This is the shape of the paper's Corollary
`index2forms`/`fbound2`; the companion module `Submission/Vdw/BoxFourier.lean`
supplies the box bound `W a = ∏ i, min (2H+1) (p/(2·minrep (a i)))`.
-/

theorem ncard_box_residue_le_of_fourier (p : ℕ) [Fact p.Prime] (m H : ℕ)
    (T : Finset (Fin m → ZMod p)) (B : ℝ) (hB0 : 0 ≤ B) (W : (Fin m → ZMod p) → ℝ)
    (hB : ∀ a : Fin m → ZMod p, a ≠ 0 →
      ‖∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)‖ ≤ B)
    (hW : ∀ a, a ≠ 0 →
      ‖∑ y : BddVec m H, ZMod.stdAddChar (-(∑ i, a i * ((y i : ℤ) : ZMod p)))‖ ≤ W a) :
    (Nat.card {z : BddVec m H // (fun i => ((z i : ℤ) : ZMod p)) ∈ T} : ℝ)
      ≤ (T.card : ℝ) * ((2 * H + 1 : ℕ) : ℝ) ^ m / (p : ℝ) ^ m
        + B / (p : ℝ) ^ m *
            ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, W a := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  set w : BddVec m H → (Fin m → ZMod p) := fun z i => ((z i : ℤ) : ZMod p) with hw
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  -- Step 1: the cardinality is the sum of the indicators (as a complex number)
  have hcard : ((Nat.card {z : BddVec m H // w z ∈ T} : ℕ) : ℂ)
      = ∑ z ∈ (Finset.univ : Finset (BddVec m H)), (if w z ∈ T then (1 : ℂ) else 0) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl (fun z _ => by split_ifs <;> simp)
  -- Step 2: the Fourier expansion
  have hexp := sum_indicator_comp_eq_fourier p m T (Finset.univ : Finset (BddVec m H)) w
  -- Step 3: the zero-frequency term
  have hC0 : (∑ x ∈ T, ZMod.stdAddChar (∑ i, (0 : Fin m → ZMod p) i * x i))
      = (T.card : ℂ) := by
    simp
  have hD0 : (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
        ZMod.stdAddChar (-(∑ i, (0 : Fin m → ZMod p) i * w y i)))
      = (((2 * H + 1) ^ m : ℕ) : ℂ) := by
    have h1 : ∀ y : BddVec m H,
        ZMod.stdAddChar (-(∑ i, (0 : Fin m → ZMod p) i * w y i)) = 1 := by
      intro y
      simp
    rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, bddVec_card]
    simp
  -- Step 4: the non-zero frequencies bound
  have hDbound : ∀ a : Fin m → ZMod p, a ≠ 0 →
      ‖∑ y ∈ (Finset.univ : Finset (BddVec m H)),
        ZMod.stdAddChar (-(∑ i, a i * w y i))‖ ≤ W a := by
    intro a ha
    have hcongr : (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
        ZMod.stdAddChar (-(∑ i, a i * w y i)))
        = ∑ y ∈ (Finset.univ : Finset (BddVec m H)),
          ZMod.stdAddChar (-(∑ i, a i * ((y i : ℤ) : ZMod p))) :=
      Finset.sum_congr rfl (fun y _ => rfl)
    rw [hcongr]
    exact hW a ha
  have hbound : ‖∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
        (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
          (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
            ZMod.stdAddChar (-(∑ i, a i * w y i)))‖
      ≤ B * ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, W a := by
    calc ‖∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
          (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
            (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
              ZMod.stdAddChar (-(∑ i, a i * w y i)))‖
        ≤ ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
            ‖(∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
              (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
                ZMod.stdAddChar (-(∑ i, a i * w y i)))‖ := norm_sum_le _ _
      _ = ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
            ‖∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)‖ *
              ‖∑ y ∈ (Finset.univ : Finset (BddVec m H)),
                ZMod.stdAddChar (-(∑ i, a i * w y i))‖ := by
          exact Finset.sum_congr rfl (fun a _ => norm_mul _ _)
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, B * W a := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          obtain ⟨ha0, -⟩ := Finset.mem_erase.mp ha
          exact mul_le_mul (hB a ha0) (hDbound a ha0) (norm_nonneg _) hB0
      _ = B * ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, W a := by
          rw [Finset.mul_sum]
  -- Step 5: assemble
  have hsplit : (∑ a : Fin m → ZMod p, (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
        (∑ y ∈ (Finset.univ : Finset (BddVec m H)), ZMod.stdAddChar (-(∑ i, a i * w y i))))
      = (T.card : ℂ) * (((2 * H + 1) ^ m : ℕ) : ℂ) +
        ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0,
          (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
            (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
              ZMod.stdAddChar (-(∑ i, a i * w y i))) := by
    conv_lhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin m → ZMod p))]
    rw [hC0, hD0, add_comm]
  have hnorm : ‖((Nat.card {z : BddVec m H // w z ∈ T} : ℕ) : ℂ)‖
      ≤ ((p : ℝ) ^ m)⁻¹ *
        ((T.card : ℝ) * (((2 * H + 1 : ℕ) : ℝ) ^ m)
          + B * ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, W a) := by
    rw [hcard, hexp]
    have hc : ‖((p : ℂ) ^ m)⁻¹‖ = ((p : ℝ) ^ m)⁻¹ := by
      rw [norm_inv, norm_pow]
      have : ‖((p : ℂ))‖ = (p : ℝ) := Complex.norm_natCast p
      rw [this]
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hb0 : (0 : ℝ) ≤ (T.card : ℝ) * (((2 * H + 1 : ℕ) : ℝ) ^ m) := by positivity
    have hsum : ‖∑ a : Fin m → ZMod p, (∑ x ∈ T, ZMod.stdAddChar (∑ i, a i * x i)) *
          (∑ y ∈ (Finset.univ : Finset (BddVec m H)),
            ZMod.stdAddChar (-(∑ i, a i * w y i)))‖
        ≤ (T.card : ℝ) * (((2 * H + 1 : ℕ) : ℝ) ^ m)
          + B * ∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)).erase 0, W a := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) (add_le_add (le_of_eq ?_) hbound)
      rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast, Nat.cast_pow]
    exact hsum
  rw [Complex.norm_natCast] at hnorm
  refine le_trans hnorm ?_
  rw [mul_add, inv_mul_eq_div, inv_mul_eq_div]
  exact le_of_eq (by ring)

end

end Submission.Vdw
