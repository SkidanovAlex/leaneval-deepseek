/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Route V: the invariant derivation on `N(E)` and its kernel (definitions)

This file contains the vocabulary of the proof of `Work.MotV.derivZeroConst`:

> for an elliptic curve `E` over a field `N` of characteristic `0`, the kernel of a derivation
> `D : N(E) → N(E)` with `D x = 2y + a₁x + a₃` and `D y = 3x² + 2a₂x + a₄ - a₁y`
> (the derivation dual to the invariant differential) consists of the constants.

## The mathematical content

Write `e = a₁x + a₃` and `c = x³ + a₂x² + a₄x + a₆`, so that `y` satisfies the quadratic relation
`y² + e·y = c` over `N(x)`.  Put

* `w = invDP E = 2y + e`  (the `y`-derivative of the Weierstrass equation),
* `B = bPoly E = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)`, so that `w² = B(x)`.

In characteristic `≠ 2` the function field `N(E)` is `N(x)(w)`, an extension of `N(x)` of degree
`2`: `N(E) = N(x) + N(x)·w`.  The given derivation `D` is an `N`-derivation, and on `N(x)` one has
`D(f(x)) = w·f'(x)` for the formal derivative `f'`; then `D(w) = B'(x)/2` (`B'` the derivative of
`B`).

If `f = A + B·w` with `A, B ∈ N(x)` satisfies `D f = 0`, then

    0 = D f = w·(A' + B·B'(x)/2) + B(x)·B'

and since `w ∉ N(x)` while the second term lies in `N(x)`, both terms vanish separately: `B' = 0`,
so `B ∈ N`, and then `A + B·B/2` has vanishing derivative, so is a constant.  This gives
`f = c + B·(w - B(x)/2)`, and testing `D f = 0` once more (using `w ≠ 1` and `B'(x) ≠ 0`) forces
`B = 0`, so `f ∈ N`.

This file collects the two definitions `invDP` and `bPoly`, the subfield `baseField` (the image of
`N(x)` in `N(E)`), and elementary rewriting lemmas about them.

## Main definitions

* `Work.MotV.invDP E`: the element `2y + a₁x + a₃ = 2·genY E + eK E`;
* `Work.MotV.bPoly E`: the polynomial `(a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)` over `N`, with
  `w² = bPoly E` evaluated at `x`;
* `Work.MotV.baseField E`: the image of `N(x) → N(E)`, `x ↦ genX E`, as a `Subfield` of `N(E)`.

## Tags

elliptic curve, invariant derivation, constants, function field
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.NeTwoDecomp
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.FuncExt
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-- The element `w = 2y + a₁x + a₃ = 2·genY E + eK E` of the function field: the derivative of `y`
with respect to the invariant parameter, whose square is `bPoly E` evaluated at `x`. -/
def invDP (E : WeierstrassCurve N) : MotC2.Func E := 2 * MotC2.genY E + MotC2.eK E

/-- `B(X) = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)`, the polynomial with `B(x) = w²`. -/
def bPoly (E : WeierstrassCurve N) : Polynomial N :=
  MotC2.linCoef E ^ 2 + 4 * MotC2.cubCoef E

/-- The subfield `N(x) ⊆ N(E)`, the image of the structure map `N(X) → N(E)`, `X ↦ genX E`
(equivalently: the range of `MotC2.xPsi E`). -/
def baseField (E : WeierstrassCurve N) : Subfield (MotC2.Func E) :=
  (MotC2.xPsi E).toRingHom.fieldRange

@[simp]
lemma mem_baseField_iff (E : WeierstrassCurve N) (z : MotC2.Func E) :
    z ∈ baseField E ↔ ∃ w : RatFunc N, MotC2.xPsi E w = z :=
  Iff.rfl

lemma xPhi_linCoef (E : WeierstrassCurve N) : MotC2.xPhi E (MotC2.linCoef E) = MotC2.eK E := by
  simp only [MotC2.linCoef, MotC2.eK, MotC2.xPhi]
  simp

lemma xPhi_cubCoef (E : WeierstrassCurve N) : MotC2.xPhi E (MotC2.cubCoef E) = MotC2.cK E := by
  simp only [MotC2.cubCoef, MotC2.cK, MotC2.xPhi]
  simp

lemma xPhi_mem_baseField (E : WeierstrassCurve N) (p : Polynomial N) :
    MotC2.xPhi E p ∈ baseField E :=
  ⟨algebraMap (Polynomial N) (RatFunc N) p, MotC2.xPsi_apply_algebraMap E p⟩

lemma eK_mem_baseField (E : WeierstrassCurve N) : MotC2.eK E ∈ baseField E := by
  rw [← xPhi_linCoef E]
  exact xPhi_mem_baseField E _

lemma cK_mem_baseField (E : WeierstrassCurve N) : MotC2.cK E ∈ baseField E := by
  rw [← xPhi_cubCoef E]
  exact xPhi_mem_baseField E _

lemma genX_mem_baseField (E : WeierstrassCurve N) : MotC2.genX E ∈ baseField E := by
  have h := xPhi_mem_baseField E Polynomial.X
  rwa [MotC2.xPhi_X] at h

lemma algebraMap_mem_baseField (E : WeierstrassCurve N) (c : N) :
    algebraMap N (MotC2.Func E) c ∈ baseField E :=
  MotC2.algebraMap_mem_range_xPsi E c

/-- The polynomial `bPoly E` evaluated at `x` is `w² = (2y + a₁x + a₃)²`. -/
lemma xPhi_bPoly (E : WeierstrassCurve N) :
    MotC2.xPhi E (bPoly E) = (invDP E) ^ 2 := by
  have h := MotC2.y_sq E
  have hP : (invDP E) ^ 2 = MotC2.eK E ^ 2 + 4 * MotC2.cK E := by
    rw [invDP]
    linear_combination (norm := first | refl_ring1 | ring1) 4 * h
  rw [hP, bPoly]
  exact MotC2.xPhi_D E

/-! ## elementary rewriting lemmas for `xPhi` / `xPsi` -/

lemma xPhi_C_aux (E : WeierstrassCurve N) (c : N) :
    MotC2.xPhi E (Polynomial.C c) = algebraMap N (MotC2.Func E) c := by
  rw [MotC2.xPhi_apply, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply N (Polynomial N) (MotC2.Func E)]

lemma xPhi_eq_zero_iff_aux (E : WeierstrassCurve N) (p : Polynomial N) :
    MotC2.xPhi E p = 0 ↔ p = 0 :=
  ⟨fun h => MotC2.xPhi_injective E (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

lemma xPhi_ne_zero_aux (E : WeierstrassCurve N) {p : Polynomial N} (hp : p ≠ 0) :
    MotC2.xPhi E p ≠ 0 := fun h => hp ((xPhi_eq_zero_iff_aux E p).mp h)

lemma xPsi_div_aux (E : WeierstrassCurve N) (p q : Polynomial N) :
    MotC2.xPsi E
        (algebraMap (Polynomial N) (RatFunc N) p / algebraMap (Polynomial N) (RatFunc N) q)
      = MotC2.xPhi E p / MotC2.xPhi E q := by
  rw [MotC2.xPsi, RatFunc.liftAlgHom_apply_div]
  simp only [Algebra.ofId_apply, MotC2.xPhi_apply]

lemma two_eq_algebraMap_aux (E : WeierstrassCurve N) :
    (2 : MotC2.Func E) = algebraMap N (MotC2.Func E) 2 :=
  (map_natCast (algebraMap N (MotC2.Func E)) 2).symm

lemma two_mem_baseField_aux (E : WeierstrassCurve N) : (2 : MotC2.Func E) ∈ baseField E := by
  have h := Subfield.add_mem (baseField E) (Subfield.one_mem (baseField E))
    (Subfield.one_mem (baseField E))
  simpa using h

lemma two_ne_zero_aux (E : WeierstrassCurve N) [CharZero N] : (2 : MotC2.Func E) ≠ 0 := by
  rw [two_eq_algebraMap_aux E]
  exact fun h0 => (by norm_num : (2 : N) ≠ 0)
    (FaithfulSMul.algebraMap_injective N (MotC2.Func E) (by rw [h0, map_zero]))

lemma half_eq_aux (E : WeierstrassCurve N) :
    (1 / 2 : MotC2.Func E) = algebraMap N (MotC2.Func E) (1 / 2 : N) := by
  rw [map_div₀, map_one, ← two_eq_algebraMap_aux E]

lemma invDP_mul_self_aux (E : WeierstrassCurve N) :
    invDP E * invDP E = MotC2.xPhi E (bPoly E) := by
  rw [← pow_two, xPhi_bPoly E]

/-! ## the derivation on `N(x)` -/

lemma derivXPoly_aux (E : WeierstrassCurve N)
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = invDP E) (p : Polynomial N) :
    D (MotC2.xPhi E p) = MotC2.xPhi E (derivative p) * invDP E := by
  simpa only [MotC2.xPhi, smul_eq_mul, hDx] using Derivation.map_aeval D p (MotC2.genX E)

lemma derivXRat_aux (E : WeierstrassCurve N)
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = invDP E) (p q : Polynomial N) (hq : q ≠ 0) :
    D (MotC2.xPhi E p / MotC2.xPhi E q)
      = MotC2.xPhi E (derivative p * q - p * derivative q) / (MotC2.xPhi E q) ^ 2 *
          invDP E := by
  have hq0 : MotC2.xPhi E q ≠ 0 := xPhi_ne_zero_aux E hq
  rw [Derivation.leibniz_div, derivXPoly_aux E D hDx p, derivXPoly_aux E D hDx q]
  simp only [smul_eq_mul, map_mul, map_sub, inv_pow]
  field_simp
  try ring

/-- `D` of the element `w = 2y + a₁x + a₃`: derived from `D (w^2) = 2 w D w` and
`w^2 = bPoly E` evaluated at `x`. -/
lemma deriv_invDP_aux (E : WeierstrassCurve N) [CharZero N]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = invDP E) (hw0 : invDP E ≠ 0) :
    D (invDP E) = (1 / 2) * MotC2.xPhi E (derivative (bPoly E)) := by
  have h1 := derivXPoly_aux E D hDx (bPoly E)
  have h2 := xPhi_bPoly E
  have h3 : MotC2.xPhi E (derivative (bPoly E)) * invDP E = (2 * D (invDP E)) * invDP E := by
    rw [← h1, h2, pow_two, Derivation.leibniz]
    first | refl_ring1 | ring
  have h4 : MotC2.xPhi E (derivative (bPoly E)) = 2 * D (invDP E) :=
    mul_right_cancel₀ hw0 h3
  have h2f : (2 : MotC2.Func E) ≠ 0 := two_ne_zero_aux E
  rw [h4, div_eq_mul_inv, one_mul, ← mul_assoc, inv_mul_cancel₀ h2f, one_mul]

/-! ## consequences of `y ∉ N(x)` -/

lemma invDP_notMem_baseField_aux (E : WeierstrassCurve N) [CharZero N]
    (hgy : MotC2.genY E ∉ baseField E) : invDP E ∉ baseField E := by
  intro h
  refine hgy ?_
  have h2 : MotC2.genY E = (invDP E - MotC2.eK E) / 2 := by
    rw [invDP, eq_div_iff (two_ne_zero_aux E)]
    first | refl_ring1 | ring
  rw [h2]
  exact Subfield.div_mem (baseField E)
    (Subfield.sub_mem (baseField E) h (eK_mem_baseField E)) (two_mem_baseField_aux E)

lemma one_sub_invDP_ne_zero_aux (E : WeierstrassCurve N) [CharZero N]
    (hgy : MotC2.genY E ∉ baseField E) : 1 - invDP E ≠ 0 := by
  intro h
  refine hgy ?_
  have hw1 : invDP E = 1 := (sub_eq_zero.mp h).symm
  have h2 : 2 * MotC2.genY E + MotC2.eK E = 1 := by
    rw [← invDP, hw1]
  have h3 : MotC2.genY E = (1 - MotC2.eK E) / 2 := by
    rw [eq_div_iff (two_ne_zero_aux E), mul_comm, eq_sub_iff_add_eq]
    exact h2
  rw [h3]
  exact Subfield.div_mem (baseField E)
    (Subfield.sub_mem (baseField E) (Subfield.one_mem (baseField E)) (eK_mem_baseField E))
    (two_mem_baseField_aux E)

/-- The sum decomposition `N(E) = N(x) + N(x)·w` is direct: `w = invDP E` is not in
`N(x) = baseField E`. -/
lemma indep_aux (E : WeierstrassCurve N) [CharZero N]
    (hw : invDP E ∉ baseField E) {X Y : MotC2.Func E}
    (hX : X ∈ baseField E) (hY : Y ∈ baseField E)
    (h : X * invDP E + Y = 0) : X = 0 ∧ Y = 0 := by
  have hX0 : X = 0 := by
    by_contra hX0
    have h1 : invDP E = -Y / X := by
      rw [eq_div_iff hX0]
      rw [eq_neg_iff_add_eq_zero, mul_comm]
      exact h
    exact hw (h1 ▸ Subfield.div_mem (baseField E) (Subfield.neg_mem (baseField E) hY) hX)
  refine ⟨hX0, ?_⟩
  rw [hX0, zero_mul, zero_add] at h
  exact h

/-! ## the main argument -/

theorem derivZeroConst_aux {N : Type*} [Field N] [CharZero N] (E : WeierstrassCurve N)
    [E.IsElliptic]
    (D : Derivation N (MotC2.Func E) (MotC2.Func E))
    (hDx : D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₃)
    (hDy : D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ -
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E)
    (hNF : ∀ f : MotC2.Func E, ∃ a b : RatFunc N,
      f = MotC2.xPsi E a + MotC2.xPsi E b * invDP E)
    (hPDZ : ∀ p q : Polynomial N, q ≠ 0 →
      derivative p * q - p * derivative q = 0 →
      ∃ c : N, MotC2.xPhi E p / MotC2.xPhi E q = algebraMap N (MotC2.Func E) c)
    (hBP : derivative (bPoly E) ≠ 0)
    (hBN : (bPoly E).natDegree = 3)
    (hGY : MotC2.genY E ∉ baseField E) :
    ∀ f : MotC2.Func E, D f = 0 → ∃ c : N, algebraMap N (MotC2.Func E) c = f := by
  have hDx' : D (MotC2.genX E) = invDP E := by
    simp only [hDx, invDP, MotC2.eK]
    first | refl_ring1 | ring
  have hw_not : invDP E ∉ baseField E := invDP_notMem_baseField_aux E hGY
  have hw0 : invDP E ≠ 0 := fun h => hw_not (h ▸ Subfield.zero_mem (baseField E))
  have hb0 : bPoly E ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hBN
    exact absurd hBN (by norm_num)
  intro f hf
  -- normal form
  obtain ⟨a, b, hab⟩ := hNF f
  -- representatives in `N(X)`
  obtain ⟨p, q, hqmem, haq⟩ := IsFractionRing.div_surjective (Polynomial N) a
  obtain ⟨r, s, hsmem, hbs⟩ := IsFractionRing.div_surjective (Polynomial N) b
  have hq : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hqmem
  have hs : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hsmem
  have hq0 : MotC2.xPhi E q ≠ 0 := xPhi_ne_zero_aux E hq
  have hs0 : MotC2.xPhi E s ≠ 0 := xPhi_ne_zero_aux E hs
  have hs20 : (MotC2.xPhi E s) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have hf' : f = MotC2.xPhi E p / MotC2.xPhi E q +
      (MotC2.xPhi E r / MotC2.xPhi E s) * invDP E := by
    rw [hab, ← haq, ← hbs, xPsi_div_aux E p q, xPsi_div_aux E r s]
  -- the two "derivatives"
  set A' : MotC2.Func E :=
    MotC2.xPhi E (derivative p * q - p * derivative q) / (MotC2.xPhi E q) ^ 2 with hA'
  set B' : MotC2.Func E :=
    MotC2.xPhi E (derivative r * s - r * derivative s) / (MotC2.xPhi E s) ^ 2 with hB'
  have hu : D (MotC2.xPhi E p / MotC2.xPhi E q) = A' * invDP E := by
    rw [derivXRat_aux E D hDx' p q hq, ← hA']
  have hv : D (MotC2.xPhi E r / MotC2.xPhi E s) = B' * invDP E := by
    rw [derivXRat_aux E D hDx' r s hs, ← hB']
  have hw : D (invDP E) = (1 / 2) * MotC2.xPhi E (derivative (bPoly E)) :=
    deriv_invDP_aux E D hDx' hw0
  have hD0 : D (MotC2.xPhi E p / MotC2.xPhi E q +
      (MotC2.xPhi E r / MotC2.xPhi E s) * invDP E) = 0 := hf' ▸ hf
  have hexp : D (MotC2.xPhi E p / MotC2.xPhi E q +
        (MotC2.xPhi E r / MotC2.xPhi E s) * invDP E)
      = A' * invDP E + (MotC2.xPhi E (bPoly E) * B' +
          (1 / 2) * (MotC2.xPhi E r / MotC2.xPhi E s) *
            MotC2.xPhi E (derivative (bPoly E))) := by
    have e1 : D (MotC2.xPhi E p / MotC2.xPhi E q +
        (MotC2.xPhi E r / MotC2.xPhi E s) * invDP E)
        = A' * invDP E + ((MotC2.xPhi E r / MotC2.xPhi E s) *
              ((1 / 2) * MotC2.xPhi E (derivative (bPoly E))) +
            invDP E * (B' * invDP E)) := by
      rw [map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hu, hv, hw]
      try ring
    rw [e1]
    have e2 : invDP E * (B' * invDP E) = MotC2.xPhi E (bPoly E) * B' := by
      calc invDP E * (B' * invDP E) = B' * (invDP E * invDP E) := by ring
        _ = B' * MotC2.xPhi E (bPoly E) := by rw [invDP_mul_self_aux E]
        _ = MotC2.xPhi E (bPoly E) * B' := by ring
    rw [e2]
    ring_nf
  have hmain : A' * invDP E + (MotC2.xPhi E (bPoly E) * B' +
        (1 / 2) * (MotC2.xPhi E r / MotC2.xPhi E s) *
          MotC2.xPhi E (derivative (bPoly E))) = 0 := by
    rw [← hexp]
    exact hD0
  -- membership in `N(x)`
  have hA'mem : A' ∈ baseField E := by
    rw [hA']
    exact Subfield.div_mem (baseField E) (xPhi_mem_baseField E _)
      (Subfield.pow_mem (baseField E) (xPhi_mem_baseField E q) 2)
  have hB'mem : B' ∈ baseField E := by
    rw [hB']
    exact Subfield.div_mem (baseField E) (xPhi_mem_baseField E _)
      (Subfield.pow_mem (baseField E) (xPhi_mem_baseField E s) 2)
  have hYmem : MotC2.xPhi E (bPoly E) * B' +
      (1 / 2) * (MotC2.xPhi E r / MotC2.xPhi E s) *
        MotC2.xPhi E (derivative (bPoly E)) ∈ baseField E := by
    refine Subfield.add_mem (baseField E)
      (Subfield.mul_mem (baseField E) (xPhi_mem_baseField E _) hB'mem) ?_
    refine Subfield.mul_mem (baseField E) (Subfield.mul_mem (baseField E) ?_ ?_)
      (xPhi_mem_baseField E _)
    · rw [half_eq_aux E]
      exact algebraMap_mem_baseField E ((1 : N) / 2)
    · exact Subfield.div_mem (baseField E) (xPhi_mem_baseField E r) (xPhi_mem_baseField E s)
  obtain ⟨hA'0, hODE⟩ := indep_aux E hw_not hA'mem hYmem hmain
  -- `A' = 0` forces `A` to be constant
  have hp'q : derivative p * q - p * derivative q = 0 := by
    have h : MotC2.xPhi E (derivative p * q - p * derivative q) = 0 := by
      have hh := hA'0
      rw [hA'] at hh
      exact (div_eq_zero_iff.mp hh).resolve_right (pow_ne_zero 2 hq0)
    exact (xPhi_eq_zero_iff_aux E _).mp h
  obtain ⟨cA, hcA⟩ := hPDZ p q hq hp'q
  have hfA : f = algebraMap N (MotC2.Func E) cA +
      (MotC2.xPhi E r / MotC2.xPhi E s) * invDP E := by
    rw [hf', hcA]
  -- the ODE for `B`
  have hODE2 : 2 * MotC2.xPhi E (bPoly E) * B' +
      (MotC2.xPhi E r / MotC2.xPhi E s) * MotC2.xPhi E (derivative (bPoly E)) = 0 := by
    have hm : (2 : MotC2.Func E) * (MotC2.xPhi E (bPoly E) * B' +
        (1 / 2) * (MotC2.xPhi E r / MotC2.xPhi E s) * MotC2.xPhi E (derivative (bPoly E)))
        = 2 * MotC2.xPhi E (bPoly E) * B' +
          (MotC2.xPhi E r / MotC2.xPhi E s) * MotC2.xPhi E (derivative (bPoly E)) := by
      have h2 : (2 : MotC2.Func E) ≠ 0 := two_ne_zero_aux E
      field_simp
    rw [← hm, hODE, mul_zero]
  have hΩ : 2 * bPoly E * (derivative r * s - r * derivative s) +
      derivative (bPoly E) * r * s = 0 := by
    have hid : MotC2.xPhi E (2 * bPoly E * (derivative r * s - r * derivative s) +
        derivative (bPoly E) * r * s)
        = (2 * MotC2.xPhi E (bPoly E) * B' +
            (MotC2.xPhi E r / MotC2.xPhi E s) *
              MotC2.xPhi E (derivative (bPoly E))) * (MotC2.xPhi E s) ^ 2 := by
      rw [hB']
      simp only [map_add, map_mul, map_pow, map_ofNat]
      field_simp
      try ring
    have h : MotC2.xPhi E (2 * bPoly E * (derivative r * s - r * derivative s) +
        derivative (bPoly E) * r * s) = 0 := by
      rw [hid, hODE2, zero_mul]
    exact (xPhi_eq_zero_iff_aux E _).mp h
  -- `B ^ 2 * bPoly E` has zero derivative, hence is constant
  have hN2 : derivative (r ^ 2 * bPoly E) * s ^ 2 - (r ^ 2 * bPoly E) * derivative (s ^ 2) = 0 := by
    have hrel : derivative (r ^ 2 * bPoly E) * s ^ 2 - (r ^ 2 * bPoly E) * derivative (s ^ 2)
        = r * s * (2 * bPoly E * (derivative r * s - r * derivative s) +
            derivative (bPoly E) * r * s) := by
      simp only [pow_two, derivative_mul, derivative_natCast, nsmul_eq_mul]
      first | refl_ring1 | ring
    rw [hrel, hΩ, mul_zero]
  obtain ⟨k, hk⟩ := hPDZ (r ^ 2 * bPoly E) (s ^ 2) (pow_ne_zero 2 hs) hN2
  -- hence `r ^ 2 * bPoly E = C k * s ^ 2`
  have hpoly : r ^ 2 * bPoly E = Polynomial.C k * s ^ 2 := by
    apply MotC2.xPhi_injective E
    have hs2 : MotC2.xPhi E (s ^ 2) = (MotC2.xPhi E s) ^ 2 := by rw [map_pow]
    have h1 : MotC2.xPhi E (r ^ 2 * bPoly E) =
        algebraMap N (MotC2.Func E) k * (MotC2.xPhi E s) ^ 2 := by
      rw [← hs2]
      exact (div_eq_iff (by rwa [hs2])).mp hk
    rw [h1, map_mul (MotC2.xPhi E) (Polynomial.C k) (s ^ 2), map_pow (MotC2.xPhi E) s 2,
      xPhi_C_aux E k]
  by_cases hB0 : MotC2.xPhi E r / MotC2.xPhi E s = 0
  · refine ⟨cA, ?_⟩
    rw [hfA, hB0, zero_mul, add_zero]
  · exfalso
    have hr : r ≠ 0 := by
      intro hr0
      exact hB0 (by rw [hr0, map_zero, zero_div])
    have hk0 : k ≠ 0 := by
      intro hk0
      have hz : r ^ 2 * bPoly E = 0 := by
        rw [hpoly, hk0, map_zero, zero_mul]
      rcases mul_eq_zero.mp hz with h | h
      · exact hr (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
      · exact hb0 h
    have hdeg := congrArg Polynomial.natDegree hpoly
    rw [Polynomial.natDegree_mul (pow_ne_zero 2 hr) hb0, Polynomial.natDegree_pow,
      Polynomial.natDegree_C_mul hk0, Polynomial.natDegree_pow, hBN] at hdeg
    omega

/-! ## the polynomial `bPoly E` is a cubic (hence its derivative is nonzero) -/

/-- `bPoly E = (a₁X+a₃)² + 4(X³+a₂X²+a₄X+a₆)` is a polynomial of degree `3`. -/
lemma bPoly_natDegree (E : WeierstrassCurve N) [CharZero N] : (bPoly E).natDegree = 3 := by
  rw [bPoly, MotC2.linCoef, MotC2.cubCoef]
  compute_degree!

/-- The derivative of `bPoly E` is nonzero (in characteristic `0`). -/
lemma bPoly_derivative_ne_zero (E : WeierstrassCurve N) [CharZero N] :
    derivative (bPoly E) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero, bPoly_natDegree E]
  norm_num

/-- **The normal form**: every element of `N(E)` is `A + B·w` with `A, B ∈ N(x)` and
`w = invDP E = 2y + a₁x + a₃` (characteristic `≠ 2`).

Obtained from `Work.MotC2.NeTwoDecomp` (which gives `f = (b₁ + b₂y)/(s₁ + s₂y)` with
`bᵢ, sᵢ ∈ N[x]` together with the norm identity `f·(s₁² - s₁s₂e - s₂²c) = A + B·y`): dividing by the
norm, which lies in `N(x)`, expresses `f` as `A' + B'·y` with `A', B' ∈ N(x)`, and then
`y = (w - e)/2`. -/
lemma invDP_normalForm (E : WeierstrassCurve N) (h2 : (2 : N) ≠ 0) (f : MotC2.Func E) :
    ∃ a b : RatFunc N, f = MotC2.xPsi E a + MotC2.xPsi E b * invDP E := by
  obtain ⟨b₁, b₂, s₁, s₂, hb₁, hb₂, hs₁, hs₂, hss, hfd, hNne, hnorm⟩ :=
    MotC2.NeTwoDecomp N E f
  have hb₁' : b₁ ∈ baseField E := MotC2.Ax_subset_range_xPsi E hb₁
  have hb₂' : b₂ ∈ baseField E := MotC2.Ax_subset_range_xPsi E hb₂
  have hs₁' : s₁ ∈ baseField E := MotC2.Ax_subset_range_xPsi E hs₁
  have hs₂' : s₂ ∈ baseField E := MotC2.Ax_subset_range_xPsi E hs₂
  have heK : MotC2.eK E ∈ baseField E := eK_mem_baseField E
  have hcK : MotC2.cK E ∈ baseField E := cK_mem_baseField E
  have h2mem : (2 : MotC2.Func E) ∈ baseField E := two_mem_baseField_aux E
  have hU : s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E ∈ baseField E := by
    refine Subfield.sub_mem (baseField E) (Subfield.sub_mem (baseField E) ?_ ?_) ?_
    · exact Subfield.pow_mem (baseField E) hs₁' 2
    · exact Subfield.mul_mem (baseField E) (Subfield.mul_mem (baseField E) hs₁' hs₂') heK
    · exact Subfield.mul_mem (baseField E) (Subfield.pow_mem (baseField E) hs₂' 2) hcK
  have hA : b₁ * s₁ - b₁ * s₂ * MotC2.eK E - b₂ * s₂ * MotC2.cK E ∈ baseField E := by
    refine Subfield.sub_mem (baseField E) (Subfield.sub_mem (baseField E) ?_ ?_) ?_
    · exact Subfield.mul_mem (baseField E) hb₁' hs₁'
    · exact Subfield.mul_mem (baseField E) (Subfield.mul_mem (baseField E) hb₁' hs₂') heK
    · exact Subfield.mul_mem (baseField E) (Subfield.mul_mem (baseField E) hb₂' hs₂') hcK
  have hB : b₂ * s₁ - b₁ * s₂ ∈ baseField E :=
    Subfield.sub_mem (baseField E) (Subfield.mul_mem (baseField E) hb₂' hs₁')
      (Subfield.mul_mem (baseField E) hb₁' hs₂')
  have hU0 : s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E ≠ 0 := hNne
  have hf : f = (b₁ * s₁ - b₁ * s₂ * MotC2.eK E - b₂ * s₂ * MotC2.cK E) /
        (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) +
      ((b₂ * s₁ - b₁ * s₂) /
        (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E)) * MotC2.genY E := by
    have h1 := congrArg
      (fun z : MotC2.Func E => z / (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E))
      hnorm
    rw [mul_div_cancel_right₀ _ hU0] at h1
    rw [h1]
    field_simp
    try ring
  have h2f : (2 : MotC2.Func E) ≠ 0 := by
    rw [two_eq_algebraMap_aux E]
    exact fun h0 => h2 (FaithfulSMul.algebraMap_injective N (MotC2.Func E)
      (by rw [h0, map_zero]))
  have hy : MotC2.genY E = (invDP E - MotC2.eK E) / 2 := by
    rw [invDP, eq_div_iff h2f, mul_comm, eq_sub_iff_add_eq]
  have hf2 : f = ((b₁ * s₁ - b₁ * s₂ * MotC2.eK E - b₂ * s₂ * MotC2.cK E) /
          (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) -
        (b₂ * s₁ - b₁ * s₂) /
          (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) * MotC2.eK E / 2) +
      ((b₂ * s₁ - b₁ * s₂) /
        (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) / 2) * invDP E := by
    rw [hf, hy]
    field_simp
    try ring
  have hX : (b₁ * s₁ - b₁ * s₂ * MotC2.eK E - b₂ * s₂ * MotC2.cK E) /
          (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) -
        (b₂ * s₁ - b₁ * s₂) /
          (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) * MotC2.eK E / 2 ∈
      baseField E := by
    refine Subfield.sub_mem (baseField E) (Subfield.div_mem (baseField E) hA hU) ?_
    exact Subfield.div_mem (baseField E)
      (Subfield.mul_mem (baseField E) (Subfield.div_mem (baseField E) hB hU) heK) h2mem
  have hY : (b₂ * s₁ - b₁ * s₂) /
        (s₁ ^ 2 - s₁ * s₂ * MotC2.eK E - s₂ ^ 2 * MotC2.cK E) / 2 ∈ baseField E :=
    Subfield.div_mem (baseField E) (Subfield.div_mem (baseField E) hB hU) h2mem
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  refine ⟨a, b, ?_⟩
  rw [hf2, ← ha, ← hb]
  rfl

end

end Work.MotV
