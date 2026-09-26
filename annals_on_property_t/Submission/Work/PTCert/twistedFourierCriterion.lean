import Mathlib
import Submission.Work.PTCert.Math
import Submission.Work.PTCert.TFDefs
import Submission.Work.PTCert.Fourier.WSfunAct
import Submission.Work.PTCert.Fourier.WSfunPairing

/-!
# The twisted Fourier criterion

`Work.PTCert.twistedFourierCriterion` proves `Submission.PTCert.TwistedFourierCriterion`.

The proof has three ingredients.

* `chiS` is a genuine sign character of `A = (Fin m → ZMod 2)`: it is multiplicative
  (`chiS_add`) and its values are `±1`; summing it over all subsets `S` gives `2^m · [a = 0]`
  (`chiS_sum`).

* The Fourier-twisted bilinear form `WSfun S x y = Σ_a χ_S(a) · sgn a y · M x (act a y)`
  satisfies, by the `M`-invariance `sgn a x · sgn a y · M (act a x) (act a y) = M x y`,
  the equivariance `WSfun S (act a x) (act b y) = χ_S(a + b) · sgn a x · sgn b y · WSfun S x y`
  (`Fourier.WSfunAct`), which folds the double sum over `ι` onto the orbit representatives
  (`Fourier.WSfunPairing`).

* `chiS_sum` (applied the other way) inverts the twist: `Σ_S WSfun S x y = 2^m · M x y`, so
  `M` is `2^{-m}` times a sum, over the sign characters, of the quadratic forms of the
  representative matrices `W_S`, which are positive semidefinite by hypothesis.
-/

open OnPropertyT Submission.RouteB
open scoped BigOperators Matrix

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- `(if x + y = 0 then 1 else -1) = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1)`
for `x y : ZMod 2`: the function `x ↦ if x = 0 then 1 else -1` is a character of `ℤ/2`. -/
lemma zmod2_eps_add (x y : ZMod 2) :
    (if x + y = 0 then (1 : ℝ) else -1)
      = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rcases (by revert x; decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with hx | hx <;>
  rcases (by revert y; decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) y with hy | hy <;>
  subst hx <;> subst hy <;> norm_num [h2] <;> decide

/-- `chiS S` is multiplicative in the group variable. -/
lemma chiS_add {m : ℕ} (S : Finset (Fin m)) (a b : Fin m → ZMod 2) :
    chiS S (a + b) = chiS S a * chiS S b := by
  simp only [chiS]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.add_apply]
  exact zmod2_eps_add (a i) (b i)

/-- `chiS S a` is a square root of unity. -/
lemma chiS_sq {m : ℕ} (S : Finset (Fin m)) (a : Fin m → ZMod 2) :
    chiS S a * chiS S a = 1 := by
  simp only [chiS]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  by_cases h : a i = 0 <;> simp [h]

/-- `chiS S a = ±1`. -/
lemma chiS_pm {m : ℕ} (S : Finset (Fin m)) (a : Fin m → ZMod 2) :
    chiS S a = 1 ∨ chiS S a = -1 :=
  mul_self_eq_one_iff.mp (chiS_sq S a)

/-- `chiS S 0 = 1`. -/
lemma chiS_zero {m : ℕ} (S : Finset (Fin m)) : chiS S (0 : Fin m → ZMod 2) = 1 := by
  simp [chiS]

/-- **Character orthogonality.** Summing the sign character over all `S` gives
`2^m` at the origin and `0` elsewhere. -/
lemma chiS_sum {m : ℕ} (a : Fin m → ZMod 2) :
    ∑ S : Finset (Fin m), chiS S a = if a = 0 then (2 : ℝ) ^ m else 0 := by
  have hprod : ∑ S : Finset (Fin m), chiS S a
      = ∏ i : Fin m, (if a i = 0 then (2:ℝ) else 0) := by
    have h := Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => (if a i = 0 then (1:ℝ) else -1))
    rw [Finset.powerset_univ] at h
    have h1 : (∏ i : Fin m, (if a i = 0 then (2:ℝ) else 0))
        = ∏ i : Fin m, (1 + (if a i = 0 then (1:ℝ) else -1)) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : a i = 0 <;> simp only [hi, if_true, if_false] <;> norm_num
    rw [h1, h]
    apply Finset.sum_congr rfl
    intro S _
    rw [chiS]
  rw [hprod]
  by_cases h : a = 0
  · subst h
    simp only [Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    rw [funext_iff] at h
    simp only [Pi.zero_apply] at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (f := fun j => if a j = 0 then (2:ℝ) else 0)
      (Finset.mem_univ i) (by simp [hi])

/-- **Fourier inversion for `M`.** Summing the twisted form `WSfun` over all sign characters
recovers `2^m · M`. -/
lemma WSfun_sum {m : ℕ} {ι : Type}
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ)
    (M : Matrix ι ι ℝ)
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1)
    (x y : ι) :
    ∑ S : Finset (Fin m), WSfun act sgn M S x y = (2:ℝ)^m * M x y := by
  have hsgn0 : sgn 0 y = 1 := by
    have h := hsgn 0 0 y
    rw [zero_add, hact0 y] at h
    rcases hsgnval 0 y with h1 | h1
    · exact h1
    · rw [h1] at h; norm_num at h
  simp only [WSfun]
  rw [Finset.sum_comm]
  have hinner : ∀ a : Fin m → ZMod 2,
      (∑ S : Finset (Fin m), chiS S a * sgn a y * M x (act a y))
        = (if a = 0 then (2:ℝ)^m else 0) * (sgn a y * M x (act a y)) := by
    intro a
    rw [← Finset.sum_mul, ← Finset.sum_mul, chiS_sum, mul_assoc]
  simp only [hinner]
  rw [Finset.sum_eq_single 0]
  · rw [if_pos rfl, hsgn0, hact0, one_mul]
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ 0) h

theorem twistedFourierCriterion : TwistedFourierCriterion := by
  intro m ι _instF _instD act sgn hact hact0 hsgn hsgnval M hMsym hMinv rep nu
    hactnu hreprep _hrepact hWS
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hMsym
  · intro v
    have hchi : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2),
        chiS S (a + b) = chiS S a * chiS S b := fun S a b => chiS_add S a b
    have hstar : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2) (x y : ι),
        WSfun act sgn M S (act a x) (act b y)
          = chiS S (a + b) * sgn a x * sgn b y * WSfun act sgn M S x y :=
      fun S a b x y =>
        Fourier.WSfunAct act sgn M hact hact0 hsgn hsgnval hMinv S hchi a b x y
    -- `2^m • M` is the sum of the twisted forms
    have hMf : ∀ x y : ι,
        ∑ S : Finset (Fin m), WSfun act sgn M S x y = (2:ℝ)^m * M x y :=
      fun x y => WSfun_sum act sgn M hact0 hsgn hsgnval x y
    -- the total quadratic form is `2^m` times the sum of the per-character ones
    have hmain : (∑ S : Finset (Fin m), ∑ x : ι, ∑ y : ι,
          v x * WSfun act sgn M S x y * v y)
        = (2:ℝ)^m * ∑ x : ι, ∑ y : ι, v x * M x y * v y := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [← Finset.sum_mul, ← Finset.mul_sum, hMf x y]
      ring
    -- each per-character quadratic form is nonnegative, by the PSD hypothesis
    have hpos : 0 ≤ ∑ S : Finset (Fin m), ∑ x : ι, ∑ y : ι,
          v x * WSfun act sgn M S x y * v y := by
      apply Finset.sum_nonneg
      intro S _
      have hpair := Fourier.WSfunPairing act sgn M rep nu hactnu hreprep S hchi (hstar S) v
      rw [show (∑ x : ι, ∑ y : ι, v x * WSfun act sgn M S x y * v y)
            = ∑ x : ι, ∑ y : ι, v x * v y * WSfun act sgn M S x y from by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))]
      rw [hpair]
      have hpsd := (hWS S).dotProduct_mulVec_nonneg
        (fun xb : {x : ι // rep x = x} => cSfun v sgn nu rep S xb.1)
      have hconv : star (fun xb : {x : ι // rep x = x} => cSfun v sgn nu rep S xb.1)
            ⬝ᵥ ((Matrix.of fun xb yb : {x : ι // rep x = x} =>
                WSfun act sgn M S xb.1 yb.1) *ᵥ
              (fun xb : {x : ι // rep x = x} => cSfun v sgn nu rep S xb.1))
          = ∑ xb : {x : ι // rep x = x}, ∑ yb : {x : ι // rep x = x},
              cSfun v sgn nu rep S xb.1 * cSfun v sgn nu rep S yb.1
                * WSfun act sgn M S xb.1 yb.1 := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
        refine Finset.sum_congr rfl (fun xb _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun yb _ => by ring)
      rw [← hconv]
      exact hpsd
    have hexp : star v ⬝ᵥ (M *ᵥ v) = ∑ x : ι, ∑ y : ι, v x * M x y * v y := by
      simp only [dotProduct, Matrix.mulVec, star_trivial]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => by ring)
    rw [hexp]
    have hcpos : 0 < (2:ℝ)^m := by positivity
    have hstep : (∑ x : ι, ∑ y : ι, v x * M x y * v y)
        = ((2:ℝ)^m)⁻¹ * (∑ S : Finset (Fin m), ∑ x : ι, ∑ y : ι,
            v x * WSfun act sgn M S x y * v y) := by
      rw [show (∑ x : ι, ∑ y : ι, v x * M x y * v y)
            = ((2:ℝ)^m)⁻¹ * ((2:ℝ)^m * ∑ x : ι, ∑ y : ι, v x * M x y * v y) from by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]]
      rw [hmain]
    rw [hstep]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hcpos)) hpos

end Work.PTCert
