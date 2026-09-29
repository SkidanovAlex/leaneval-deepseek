import Mathlib
import Submission.Work.C17.exp2_defs

/-!
# Inverses of two-term local expansions at `x = 0`

`Exp2 f e l m` says that `f = x^e·(l + m·x + O(x²))` at `x = 0` (see
`Submission.Work.C17.exp2_defs`).  This file proves that the condition is closed under
inversion: if `l ≠ 0` then

`f⁻¹ = x^{-e}·(l⁻¹ - (m/l²)·x + O(x²))`,

i.e. `Exp2 f⁻¹ (-e) l⁻¹ (-(m/l²))`.

The proof is a single computation with the order of vanishing `ordAtT 0`.  Writing
`H = f·x^{-e}` and `H = L + M·x + O(x²)` (`L = l`, `M = m` in `ℚ(x)`), the identity

`L²·H·(H⁻¹ - L⁻¹ + (M/L²)·x) = -L·(H - L - M·x) + M·(H - L)·x`

exhibits `L²·H·(H⁻¹ - L⁻¹ + (M/L²)·x)` as a sum of two functions of order `≥ 2`, while
`L²·H` has order `0` because `H` is a unit of the local ring at `0`.
-/

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-- If `G - c` vanishes to order at least one at `0` and `c ≠ 0`, then `G` is a unit of the
local ring at `0` (`ordAtT 0 G = 0`).  This is the local-ring analogue of the fact that a
continuous function with a nonzero limit at `0` does not vanish there. -/
theorem unit0_of_sub_rat_ordAtT_ge_one {G : RatFunc ℚ} {c : ℚ} (hc : c ≠ 0)
    (h : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (G - algebraMap ℚ (RatFunc ℚ) c)) :
    Unit0 G := by
  have hregu : Reg (G - algebraMap ℚ (RatFunc ℚ) c) := reg_of_ordAtT_ge h (by norm_num)
  have hreg : Reg G := by
    have h1 := reg_add (reg_rat c) hregu
    rwa [show algebraMap ℚ (RatFunc ℚ) c + (G - algebraMap ℚ (RatFunc ℚ) c) = G by ring] at h1
  rw [Unit0]
  refine le_antisymm ?_ hreg
  have hB : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (-(G - algebraMap ℚ (RatFunc ℚ) c)) := by
    rw [ordAtT_neg]; exact h
  have hmin : min (ordAtT (0 : ℚ) G) (ordAtT (0 : ℚ) (-(G - algebraMap ℚ (RatFunc ℚ) c)))
      ≤ (0 : WithTop ℤ) := by
    have hh := ordAtT_add_ge (0 : ℚ) G (-(G - algebraMap ℚ (RatFunc ℚ) c))
    rw [show G + -(G - algebraMap ℚ (RatFunc ℚ) c) = algebraMap ℚ (RatFunc ℚ) c by ring,
      ordAtT_rat hc] at hh
    exact hh
  by_contra hcon
  have hcon' : (0 : WithTop ℤ) < ordAtT (0 : ℚ) G := not_le.mp hcon
  have h5 : (0 : WithTop ℤ) < ordAtT (0 : ℚ) (-(G - algebraMap ℚ (RatFunc ℚ) c)) :=
    lt_of_lt_of_le zero_lt_one hB
  exact absurd (lt_of_lt_of_le (lt_min hcon' h5) hmin) (lt_irrefl 0)

/-- Inversion of a two-term expansion: if `H = L + M·x + O(x²)` with `L ≠ 0`, then
`H⁻¹ = L⁻¹ - (M/L²)·x + O(x²)`. -/
theorem inv_ordAtT_ge_two {H : RatFunc ℚ} {L M : ℚ} (hL : L ≠ 0)
    (h : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ)) :
    ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (H⁻¹ - algebraMap ℚ (RatFunc ℚ) L⁻¹ - algebraMap ℚ (RatFunc ℚ) (-(M / L ^ 2)) * xQ) := by
  have hLne : (algebraMap ℚ (RatFunc ℚ) L) ≠ 0 := fun hh =>
    hL ((algebraMap ℚ (RatFunc ℚ)).injective (by rw [hh, map_zero]))
  -- `H - L = M·x + O(x²)` has order at least one
  have hu : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (H - algebraMap ℚ (RatFunc ℚ) L) := by
    have h1 : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
        (H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ) :=
      le_trans (by norm_num) h
    have h2 : ((1 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (algebraMap ℚ (RatFunc ℚ) M * xQ) := by
      rcases eq_or_ne M 0 with rfl | hM
      · rw [map_zero, zero_mul, ordAtT_zero]; exact le_top
      · have hMne : algebraMap ℚ (RatFunc ℚ) M ≠ 0 := fun hh =>
          hM ((algebraMap ℚ (RatFunc ℚ)).injective (by rw [hh, map_zero]))
        rw [ordAtT_mul (0 : ℚ) hMne xQ_ne_zero, ordAtT_rat hM, ordAtT_xQ]
        norm_num
    have h3 := ordAtT_add_ge'
      (a := H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ)
      (b := algebraMap ℚ (RatFunc ℚ) M * xQ) (j := 1) h1 h2
    rwa [show H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ
      + algebraMap ℚ (RatFunc ℚ) M * xQ = H - algebraMap ℚ (RatFunc ℚ) L by ring] at h3
  -- hence `H` is a unit at `0`
  have hunit : Unit0 H := unit0_of_sub_rat_ordAtT_ge_one hL hu
  have hHne : H ≠ 0 := unit0_ne_zero hunit
  have hunit' : ordAtT (0 : ℚ) H = 0 := hunit
  have hcast : algebraMap ℚ (RatFunc ℚ) (-(M / L ^ 2))
      = -(algebraMap ℚ (RatFunc ℚ) M / (algebraMap ℚ (RatFunc ℚ) L) ^ 2) := by
    rw [map_neg, map_div₀, map_pow]
  set W : RatFunc ℚ := H⁻¹ - algebraMap ℚ (RatFunc ℚ) L⁻¹
    - algebraMap ℚ (RatFunc ℚ) (-(M / L ^ 2)) * xQ with hW
  have hW' : W = H⁻¹ - (algebraMap ℚ (RatFunc ℚ) L)⁻¹
      + ((algebraMap ℚ (RatFunc ℚ) M) / (algebraMap ℚ (RatFunc ℚ) L) ^ 2) * xQ := by
    rw [hW, hcast, map_inv₀]
    ring
  -- the key identity, clearing the denominators `L`, `L²` and `H`
  have hkey : (algebraMap ℚ (RatFunc ℚ) L) ^ 2 * H * W
      = -((algebraMap ℚ (RatFunc ℚ) L)
            * (H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ))
        + (algebraMap ℚ (RatFunc ℚ) M) * ((H - algebraMap ℚ (RatFunc ℚ) L) * xQ) := by
    rw [hW']
    field_simp
    ring
  -- the right-hand side above has order at least two: both summands do
  have hRHS : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      (-((algebraMap ℚ (RatFunc ℚ) L)
            * (H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ))
        + (algebraMap ℚ (RatFunc ℚ) M) * ((H - algebraMap ℚ (RatFunc ℚ) L) * xQ)) := by
    refine ordAtT_add_ge' ?_ ?_
    · have h1 : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
          ((algebraMap ℚ (RatFunc ℚ) L)
            * (H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ)) :=
        ordAtT_mul_ge (a := algebraMap ℚ (RatFunc ℚ) L)
          (b := H - algebraMap ℚ (RatFunc ℚ) L - algebraMap ℚ (RatFunc ℚ) M * xQ)
          (j := 0) (k := 2) (reg_rat L) h
      rw [ordAtT_neg]
      exact h1
    · have h1 : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
          ((H - algebraMap ℚ (RatFunc ℚ) L) * xQ) := by
        have h2 := ordAtT_mul_ge (a := H - algebraMap ℚ (RatFunc ℚ) L) (b := xQ) (j := 1) (k := 1)
          hu (le_of_eq ordAtT_xQ.symm)
        simpa using h2
      have h3 := ordAtT_mul_ge (a := algebraMap ℚ (RatFunc ℚ) M)
        (b := (H - algebraMap ℚ (RatFunc ℚ) L) * xQ) (j := 0) (k := 2) (reg_rat M) h1
      simpa using h3
  have hLH : ordAtT (0 : ℚ) ((algebraMap ℚ (RatFunc ℚ) L) ^ 2 * H) = 0 := by
    rw [ordAtT_mul (0 : ℚ) (pow_ne_zero 2 hLne) hHne, ordAtT_pow (0 : ℚ) hLne 2,
      ordAtT_rat hL, hunit']
    simp
  have hLHS : ((2 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ)
      ((algebraMap ℚ (RatFunc ℚ) L) ^ 2 * H * W) := by
    rw [hkey]; exact hRHS
  -- `L²·H` is a unit, so the order of `W` is the order of `L²·H·W`
  rcases eq_or_ne W 0 with h0 | h0
  · rw [h0, ordAtT_zero]; exact le_top
  · have hmul := ordAtT_mul (0 : ℚ) (mul_ne_zero (pow_ne_zero 2 hLne) hHne) h0
    have hstep : ordAtT (0 : ℚ) ((algebraMap ℚ (RatFunc ℚ) L) ^ 2 * H * W)
        = ordAtT (0 : ℚ) W := by
      rw [hmul, hLH]; simp
    rw [← hstep]
    exact hLHS

theorem exp2_inv {f : RatFunc ℚ} {e : ℤ} {l m : ℚ} (hf : Exp2 f e l m) (hl : l ≠ 0) :
    Exp2 f⁻¹ (-e) l⁻¹ (-(m / l ^ 2)) := by
  unfold Exp2 at hf ⊢
  rw [neg_neg]
  have hHinv : f⁻¹ * xQ ^ e = (f * xQ ^ (-e))⁻¹ := by
    rw [mul_inv_rev, ← zpow_neg, neg_neg, mul_comm]
  rw [hHinv]
  exact inv_ordAtT_ge_two hl hf

end

end Work.C17
