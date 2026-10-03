/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `∗`-regularity of the natural extension of a Sylvester rank function

This file proves `isStarRegularRank_naturalExtension`, the formalisation of [JZLA20,
Proposition 3.6]: if `U` is a positive definite `∗`-regular ring, `τ` a `∗`-automorphism of `U`
(encoded by a `∗`-compatible `MulSemiringAction (Multiplicative ℤ) U`, hypothesis `hstar`) and
`rk` a `τ`-compatible Sylvester matrix rank function on `U`, then the natural extension `rkE` of
`rk` to `U[t^{±1};τ]` is a `∗`-regular rank function.

The mathematical content of `IsStarRegularRank rkE` is the existence of a *positive definite*
`∗`-regular ring `V` together with an **epic** ring homomorphism `φ : U[t^{±1};τ] →+* V` and a
faithful Sylvester rank function `rkV` on `V` which pulls back to `rkE`.

The envelope is the ultraproduct ring of [JZLA20, §3.2],

`P^U_{ω,τ} = (∏_{n ≥ 1} M_n(U)) / ker rk_ω`,

where `rk_ω = lim_ω (rk ∘ flatten)/(n+1)` is the ultralimit of the flattened ranks (mirroring the
construction of the natural extension itself), and the rank function on the quotient is faithful
by construction.  The natural map

`Φ : U[t^{±1};τ] →+* P^U_{ω,τ}`

is defined by its universal property: the constants map to the family of Toeplitz matrices of the
constant and `t` to the family of Toeplitz matrices of `t` (which is a unit modulo `ker rk_ω`
because its rank is `1`), the twist relation `t a = τ(a) t` holding because
`toeplitz n (t) · toeplitz n (a) = toeplitz n (τ a) · toeplitz n (t)`.

`V` is then the `∗`-regular closure of the image of `Φ` in `P^U_{ω,τ}`; by
`isEpic_of_starRegularClosure` the corresponding map is epic, since the `∗`-regular closure of a
`∗`-subring generates itself, and `Φ` is a `∗`-homomorphism because `toeplitz n (p∗) = (toeplitz n p)∗`
and `t∗ = t⁻¹` modulo the kernel.

The rank of the pullback along `Φ` is the natural extension of `rk`: on the constants this is the
computation `trunc i (A t^0) = i · A`, and on `I + A t` the computation
`trunc i (I + A t) = i · n`, together with the uniqueness of the natural extension.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.skewToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.envelopeToeplitz
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_exists
import Submission.Work.ORHughesFree.JZLA20
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_unique
import Submission.Work.ORHughesFree.NaturalExtension.natExt_exists_universe
import Submission.Work.ORHughesFree.NaturalExtension.isEpic_of_starRegularClosure
import Submission.Work.ORHughesFree.NaturalExtension.starSkewLaurent
import Submission.Work.ORHughesFree.NaturalExtension.starRegularQuotient
import Submission.Work.ORHughesFree.NaturalExtension.star_mem_of_mem_ideal
import Submission.Work.ORHughesFree.NaturalExtension.blimRankW
import Submission.Work.ORHughesFree.NaturalExtension.productStarRegular
import Submission.Work.ORHughesFree.NaturalExtension.toeplitzT_rank
import Submission.Work.ORHughesFree.NaturalExtension.blimRank_toeplitzT
import Submission.Work.ORHughesFree.NaturalExtension.starRegularClosure_codRestrict_top
import Submission.Work.ORHughesFree.NaturalExtension.starRegular_subring_positiveDefinite
import Submission.Work.ORHughesFree.Epic.exists_faithful_quotient
import Submission.Work.ORHughesFree.DivisionRank.rank_eq_full_iff_isUnit
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_isStarRegular
import Submission.Work.ORHughesFree.StarRegular.mem_starRegularClosure_iff
import Submission.Work.ORHughesFree.StarRegular.exists_isRelativeInverse
import Submission.Work.ORHughesFree.StarRegular.isRelativeInverse_unique

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-! ## The relative inverse of the star -/

/-- The star of a relative inverse is the relative inverse of the star. -/
theorem isRelativeInverse_star {U : Type*} [Ring U] [StarRing U] {x y : U}
    (h : IsRelativeInverse x y) : IsRelativeInverse (star x) (star y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : star (x * y * x) = star x := by rw [h.left]
    simpa [star_mul, mul_assoc] using h1
  · have h1 : star (y * x * y) = star y := by rw [h.right]
    simpa [star_mul, mul_assoc] using h1
  · show star (star x * star y) = star x * star y
    rw [star_mul, star_star, star_star]
    rw [show star x * star y = y * x by rw [← star_mul, h.star_right]]
  · show star (star y * star x) = star y * star x
    rw [star_mul, star_star, star_star]
    rw [show star y * star x = x * y by rw [← star_mul, h.star_left]]

/-! ## The Moore--Penrose products are idempotents generating the ideal of `x` -/

/-- `x * x^{[-1]}` is an idempotent. -/
theorem relativeInverse_mul_idem {U : Type*} [Ring U] [StarRing U] {x w : U}
    (h : IsRelativeInverse x w) : (x * w) * (x * w) = x * w := by
  calc (x * w) * (x * w) = x * (w * x * w) := by simp only [mul_assoc]
    _ = x * w := by rw [h.right]

/-- `x^{[-1]} * x` is an idempotent. -/
theorem relativeInverse_idem_mul {U : Type*} [Ring U] [StarRing U] {x w : U}
    (h : IsRelativeInverse x w) : (w * x) * (w * x) = w * x := by
  calc (w * x) * (w * x) = w * (x * w * x) := by simp only [mul_assoc]
    _ = w * x := by rw [h.left]

/-- `x * x^{[-1]}` generates the same principal right ideal as `x`. -/
theorem relativeInverse_mul_range {U : Type*} [Ring U] [StarRing U] {x w : U}
    (h : IsRelativeInverse x w) (t : U) :
    (∃ r : U, (x * w) * r = t) ↔ (∃ r : U, x * r = t) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨w * r, by rw [mul_assoc]⟩
  · rintro ⟨r, rfl⟩
    refine ⟨x * r, ?_⟩
    rw [← mul_assoc (x * w) x r, h.left]

/-- `x^{[-1]} * x` generates the same principal left ideal as `x`. -/
theorem relativeInverse_range_mul {U : Type*} [Ring U] [StarRing U] {x w : U}
    (h : IsRelativeInverse x w) (t : U) :
    (∃ r : U, r * (w * x) = t) ↔ (∃ r : U, r * x = t) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r * w, by rw [mul_assoc]⟩
  · rintro ⟨r, rfl⟩
    refine ⟨r * x, ?_⟩
    rw [mul_assoc, ← mul_assoc x w x, h.left]

/-- Projections (self-adjoint idempotents) which generate the same principal right ideal are
equal.  (The corresponding statement for arbitrary idempotents is false.) -/
theorem eq_of_projection_rightIdeal_eq {Q : Type*} [Ring Q] [StarRing Q] {e f : Q}
    (he : star e = e) (he' : e * e = e) (hf : star f = f) (hf' : f * f = f)
    (h : ∀ t : Q, (∃ r : Q, e * r = t) ↔ (∃ r : Q, f * r = t)) : e = f := by
  have hfe : e = f * e := by
    obtain ⟨r, hr⟩ := (h e).mp ⟨1, mul_one e⟩
    calc e = f * r := hr.symm
      _ = (f * f) * r := by rw [hf']
      _ = f * (f * r) := mul_assoc f f r
      _ = f * e := by rw [← hr]
  have hef : f = e * f := by
    obtain ⟨r, hr⟩ := (h f).mpr ⟨1, mul_one f⟩
    calc f = e * r := hr.symm
      _ = (e * e) * r := by rw [he']
      _ = e * (e * r) := mul_assoc e e r
      _ = e * f := by rw [← hr]
  calc e = star e := he.symm
    _ = star (f * e) := congrArg star hfe
    _ = star e * star f := star_mul f e
    _ = e * f := by rw [he, hf]
    _ = f := hef.symm

/-- Projections which generate the same principal left ideal are equal. -/
theorem eq_of_projection_leftIdeal_eq {Q : Type*} [Ring Q] [StarRing Q] {e f : Q}
    (he : star e = e) (he' : e * e = e) (hf : star f = f) (hf' : f * f = f)
    (h : ∀ t : Q, (∃ r : Q, r * e = t) ↔ (∃ r : Q, r * f = t)) : e = f := by
  have hef : e = e * f := by
    obtain ⟨r, hr⟩ := (h e).mp ⟨1, one_mul e⟩
    have h1 : e * f = e := by
      calc e * f = ((r * f) * f) := by rw [hr]
        _ = r * (f * f) := mul_assoc r f f
        _ = r * f := by rw [hf']
        _ = e := hr
    exact h1.symm
  have hfe : f = f * e := by
    obtain ⟨r, hr⟩ := (h f).mpr ⟨1, one_mul f⟩
    have h1 : f * e = f := by
      calc f * e = ((r * e) * e) := by rw [hr]
        _ = r * (e * e) := mul_assoc r e e
        _ = r * e := by rw [he']
        _ = f := hr
    exact h1.symm
  calc e = star e := he.symm
    _ = star (e * f) := congrArg star hef
    _ = star f * star e := star_mul e f
    _ = f * e := by rw [he, hf]
    _ = f := hfe.symm

/-! ## Ring homomorphisms agreeing on `x` agree on `x^{[-1]}` (the `∗`-case) -/

/-- If `g` and `h` are `∗`-homomorphisms into a `∗`-ring which agree on `x`, then they agree on
every relative inverse of `x`.  This is immediate from the uniqueness of the relative inverse in
a `∗`-ring. -/
theorem map_relativeInverse_eq_of_starHom {V Q : Type*} [Ring V] [StarRing V] [Ring Q] [StarRing Q]
    (g h : V →+* Q) (hg : ∀ v : V, g (star v) = star (g v)) (hh : ∀ v : V, h (star v) = star (h v))
    {x w : V} (hw : IsRelativeInverse x w) (hx : g x = h x) : g w = h w := by
  have h1 : IsRelativeInverse (g x) (g w) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [← map_mul] using congrArg g hw.left
    · simpa only [← map_mul] using congrArg g hw.right
    · calc star (g x * g w) = star (g (x * w)) := by rw [map_mul]
        _ = g (star (x * w)) := (hg (x * w)).symm
        _ = g (x * w) := by rw [hw.star_left]
        _ = g x * g w := map_mul g x w
    · calc star (g w * g x) = star (g (w * x)) := by rw [map_mul]
        _ = g (star (w * x)) := (hg (w * x)).symm
        _ = g (w * x) := by rw [hw.star_right]
        _ = g w * g x := map_mul g w x
  have h2 : IsRelativeInverse (h x) (h w) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [← map_mul] using congrArg h hw.left
    · simpa only [← map_mul] using congrArg h hw.right
    · calc star (h x * h w) = star (h (x * w)) := by rw [map_mul]
        _ = h (star (x * w)) := (hh (x * w)).symm
        _ = h (x * w) := by rw [hw.star_left]
        _ = h x * h w := map_mul h x w
    · calc star (h w * h x) = star (h (w * x)) := by rw [map_mul]
        _ = h (star (w * x)) := (hh (w * x)).symm
        _ = h (w * x) := by rw [hw.star_right]
        _ = h w * h x := map_mul h w x
  rw [hx] at h1
  exact StarRegular.isRelativeInverse_unique h1 h2

/-- The `1 × 1` matrices are a copy of the ring. -/
noncomputable def oneByOneRingEquiv (R : Type) [Ring R] : Matrix (Fin 1) (Fin 1) R ≃+* R where
  toFun M := M 0 0
  invFun r := oneByOne r
  left_inv M := by ext i j; fin_cases i; fin_cases j; rfl
  right_inv r := rfl
  map_add' M N := rfl
  map_mul' M N := by simp [Matrix.mul_apply]

/-- `a` is a unit as soon as the `1 × 1` matrix `a` is. -/
theorem isUnit_of_isUnit_oneByOne {R : Type} [Ring R] {a : R} (h : IsUnit (oneByOne a)) :
    IsUnit a := by
  have h1 : IsUnit ((oneByOneRingEquiv R) (oneByOne a)) :=
    IsUnit.map (oneByOneRingEquiv R).toMonoidHom h
  exact h1

/-- The Toeplitz family is additive. -/
theorem toeplitzFamily_add' {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (p q : SkewL U) : toeplitzFamily (p + q) = toeplitzFamily p + toeplitzFamily q := by
  funext n; exact toeplitz_add' (n+1) p q

set_option synthInstance.maxHeartbeats 200000 in
/-- **The `∗`-regular envelope of the natural extension.**

This is the construction of [JZLA20, §3.2]: the ring `P^U_{ω,τ} = (∏_n M_n(U))/ker rk_ω`, the
map `U[t^{±1};τ] → P^U_{ω,τ}` and the `∗`-regular closure of its image. -/
theorem isStarRegularRank_naturalExtension {U : Type} [Ring U] [StarRing U] [IsStarRegular U] [MulSemiringAction (Multiplicative ℤ) U] (hpos : IsPositiveDefiniteStarRegular U) (rk : SylvesterRank U) (hstar : ∀ (n : Multiplicative ℤ) (x : U), star (n • x) = n • star x) (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U), rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A) (rkE : SylvesterRank (SkewMonoidAlgebra U (Multiplicative ℤ))) (h : IsNaturalExtension rk rkE) : IsStarRegularRank rkE := by
  classical
  haveI hSA : StarAction U := ⟨hstar⟩
  have hst := starSkewLaurent (U := U)
  letI hStarL : StarRing (SkewL U) :=
    { star := starSkewL, star_involutive := fun p => hst.2.1 p,
      star_mul := fun p q => hst.1 p q, star_add := fun p q => hst.2.2.1 p q }
  obtain ⟨hW_star, hW_pd⟩ := productStarRegular (U := U) hpos
  haveI : IsStarRegular (W U) := hW_star
  haveI : IsPositiveDefiniteStarRegular (W U) := hW_pd
  obtain ⟨ω, hω⟩ := exists_ultrafilter_le_atTop
  obtain ⟨rk_W, hrk_W⟩ := blimRankW (U := U) ω rk
  obtain ⟨I, hI2, rk_P, hI_mem, hfaithP, hrkP⟩ := Epic.exists_faithful_quotient rk_W
  haveI : I.IsTwoSided := hI2
  have hI_star : ∀ x ∈ I, star x ∈ I := fun x hx => star_mem_of_mem_ideal I hx
  letI : StarRing (W U ⧸ I) := starRingQuotient I hI_star
  obtain ⟨hP_star, hP_pd⟩ := starRegularQuotient (R := W U) hW_pd I hI_star
  haveI : IsStarRegular (W U ⧸ I) := hP_star
  haveI : IsPositiveDefiniteStarRegular (W U ⧸ I) := hP_pd
  let mk : W U →+* (W U ⧸ I) := Ideal.Quotient.mk I
  set X : W U := toeplitzFamily (skewLaurentT : SkewL U) with hXdef
  have hrkX : rk_W.rk 1 1 (oneByOne X) = 1 := by
    rw [hrk_W 1 1 (oneByOne X)]
    exact (blimRank_toeplitzT (U := U) rk ω hω).1
  have hrkX0 : rk_W.rk 1 1 (oneByOne (1 - X * star X)) = 0 := by
    rw [hrk_W 1 1 (oneByOne (1 - X * star X))]
    exact (blimRank_toeplitzT (U := U) rk ω hω).2
  have hrkX_P : rk_P.rk 1 1 (oneByOne (mk X)) = 1 := by
    have h1 := hrkP 1 1 (oneByOne X)
    rw [show (oneByOne X).map (Ideal.Quotient.mk I) = oneByOne (mk X) from rfl] at h1
    rw [h1, hrkX]
  have hunit1 : IsUnit (oneByOne (mk X)) := by
    refine (DivisionRank.rank_eq_full_iff_isUnit rk_P hfaithP 1 (oneByOne (mk X))).mpr ?_
    simpa using hrkX_P
  have hunit : IsUnit (mk X) := isUnit_of_isUnit_oneByOne hunit1
  let u : (W U ⧸ I)ˣ := hunit.unit
  have hu : (u : W U ⧸ I) = mk X := hunit.unit_spec
  have hmk0 : mk (1 - X * star X) = 0 := by
    have hmem : (1 - X * star X) ∈ I := (hI_mem (1 - X * star X)).mpr hrkX0
    simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hux : mk X * mk (star X) = 1 := by
    rw [← map_mul]
    have h1 : X * star X = 1 - (1 - X * star X) := by abel
    rw [h1, map_sub, hmk0, map_one, sub_zero]
  have hstaru : star ((u : W U ⧸ I)) = ↑(u⁻¹) := by
    have h1 : star (mk X) = mk (star X) := starQuot_mk I hI_star X
    rw [hu, h1]
    have h2 : ↑(u⁻¹) * (mk X) = 1 := by
      have h4 : (↑(u⁻¹) * (↑u : W U ⧸ I)) = 1 := Units.inv_mul u
      simpa [hu] using h4
    calc mk (star X) = 1 * mk (star X) := (one_mul _).symm
      _ = (↑(u⁻¹) * mk X) * mk (star X) := by rw [h2]
      _ = ↑(u⁻¹) * (mk X * mk (star X)) := mul_assoc _ _ _
      _ = ↑(u⁻¹) * 1 := by rw [hux]
      _ = ↑(u⁻¹) := mul_one _
  -- the ring homomorphisms whose universal property defines `Φ`
  let f : U →+* (W U ⧸ I) := mk.comp toeplitzConstHom
  let g : Multiplicative ℤ →* (W U ⧸ I) :=
    { toFun := fun y => ↑(u ^ (Multiplicative.toAdd y))
      map_one' := by
        rw [show Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 from rfl, zpow_zero,
          Units.val_one]
      map_mul' := by
        intro a b
        rw [show Multiplicative.toAdd (a * b) =
            Multiplicative.toAdd a + Multiplicative.toAdd b from rfl, _root_.zpow_add,
          Units.val_mul] }
  have hconststar : ∀ c : U, star (toeplitzConstHom c) = toeplitzConstHom (star c) := by
    intro c
    funext n
    show star (toeplitz (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c)) =
      toeplitz (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (star c))
    rw [← hst.2.2.2.2.2 (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c)]
    congr 1
    show starSkewL (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c) =
      SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (star c)
    have hs := hst.2.2.2.2.1 0 c
    simpa using hs
  have hfstar : ∀ c : U, star (f c) = f (star c) := by
    intro c
    show star (mk (toeplitzConstHom c)) = mk (toeplitzConstHom (star c))
    rw [← hconststar c]
    show starQuot I (mk (toeplitzConstHom c)) = mk (star (toeplitzConstHom c))
    exact starQuot_mk I hI_star (toeplitzConstHom c)
  have hstar_zpow : ∀ k : ℤ, star ((↑(u ^ k)) : W U ⧸ I) = ↑(u ^ (-k)) := by
    have hpos : ∀ m : ℕ, star ((↑(u ^ (m : ℤ))) : W U ⧸ I) = ↑(u ^ (-(m : ℤ))) := by
      intro m
      have h1 : star ((↑u : W U ⧸ I) ^ m) = ↑((u⁻¹) ^ m) := by
        rw [star_pow, hstaru, Units.val_pow_eq_pow_val]
      rw [show ((↑(u ^ (m : ℤ))) : W U ⧸ I) = (↑u : W U ⧸ I) ^ m from by
        rw [zpow_natCast]; exact Units.val_pow_eq_pow_val u m, h1]
      rw [show (u ^ (-(m : ℤ)) : (W U ⧸ I)ˣ) = (u⁻¹) ^ m from by
        rw [_root_.zpow_neg, zpow_natCast, inv_pow]]
    intro k
    by_cases hk : 0 ≤ k
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
      exact hpos m
    · have hk' : k < 0 := not_le.mp hk
      have h1 : star ((↑(u ^ (-k))) : W U ⧸ I) = ↑(u ^ k) := by
        have h2 : ((((-k).toNat : ℕ) : ℤ)) = -k := by omega
        have h3 := hpos ((-k).toNat)
        rw [h2, neg_neg] at h3
        exact h3
      calc star ((↑(u ^ k)) : W U ⧸ I)
          = star (star ((↑(u ^ (-k))) : W U ⧸ I)) := by rw [← h1]
        _ = ((↑(u ^ (-k))) : W U ⧸ I) := star_star _
  have hgstar : ∀ y : Multiplicative ℤ, star (g y) = g y⁻¹ := by
    have hg' : ∀ k : ℤ, star (g (Multiplicative.ofAdd k)) = g (Multiplicative.ofAdd (-k)) := by
      intro k
      show star ((↑(u ^ k)) : W U ⧸ I) = ↑(u ^ (-k))
      exact hstar_zpow k
    intro y
    have h1 : y⁻¹ = Multiplicative.ofAdd (- Multiplicative.toAdd y) := by
      apply inv_eq_of_mul_eq_one_right
      show Multiplicative.toAdd y + - Multiplicative.toAdd y = 0
      simp
    rw [h1]
    exact hg' (Multiplicative.toAdd y)
  have hcomm_pos : ∀ (j : ℕ) (x : U),
      f (Multiplicative.ofAdd (j : ℤ) • x) * g (Multiplicative.ofAdd (j : ℤ)) =
        g (Multiplicative.ofAdd (j : ℤ)) * f x := by
    intro j x
    have hXj : g (Multiplicative.ofAdd (j : ℤ)) = mk (X ^ j) := by
      show ↑(u ^ (Multiplicative.toAdd (Multiplicative.ofAdd (j : ℤ)))) = mk (X ^ j)
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (j : ℤ)) = (j : ℤ) from rfl,
        zpow_natCast,
        show ((↑(u ^ j)) : W U ⧸ I) = (↑u : W U ⧸ I) ^ j from Units.val_pow_eq_pow_val u j,
        map_pow, ← hu]
    rw [hXj]
    show mk (toeplitzConstHom (Multiplicative.ofAdd (j : ℤ) • x)) * mk (X ^ j) =
      mk (X ^ j) * mk (toeplitzConstHom x)
    rw [← map_mul, ← map_mul]
    congr 1
    show toeplitzConstHom (Multiplicative.ofAdd (j : ℤ) • x) * X ^ j =
      X ^ j * toeplitzConstHom x
    funext n
    rw [Pi.mul_apply, Pi.mul_apply]
    show toeplitz (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)
          ((Multiplicative.ofAdd (j : ℤ)) • x)) * (X ^ j) n =
      (X ^ j) n * toeplitz (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x)
    rw [show (X ^ j) n = toeplitz (n+1) ((skewLaurentT : SkewL U) ^ j) from
      congrFun (toeplitzFam_skewLaurentT_pow j) n]
    exact (toeplitzTPowConstMul (n+1) j x).symm
  have hcomm_int : ∀ (k : ℤ) (x : U),
      f (Multiplicative.ofAdd k • x) * g (Multiplicative.ofAdd k) =
        g (Multiplicative.ofAdd k) * f x := by
    intro k x
    by_cases hk : 0 ≤ k
    · obtain ⟨j, hjcast⟩ : ∃ j : ℕ, (j : ℤ) = k := ⟨k.toNat, by omega⟩
      rw [← hjcast]
      exact hcomm_pos j x
    · have hk' : k < 0 := not_le.mp hk
      obtain ⟨j, hjcast⟩ : ∃ j : ℕ, (j : ℤ) = -k := ⟨(-k).toNat, by omega⟩
      have hpos := hcomm_pos j ((Multiplicative.ofAdd k) • x)
      have h1 : (Multiplicative.ofAdd (j : ℤ)) • (Multiplicative.ofAdd k • x) = x := by
        rw [← mul_smul, show Multiplicative.ofAdd (j : ℤ) * Multiplicative.ofAdd k =
          Multiplicative.ofAdd ((j : ℤ) + k) from rfl, show (j : ℤ) + k = 0 by omega]
        exact one_smul _ _
      rw [h1] at hpos
      have hA : g (Multiplicative.ofAdd k) * g (Multiplicative.ofAdd (j : ℤ)) = 1 := by
        rw [← map_mul, show Multiplicative.ofAdd k * Multiplicative.ofAdd (j : ℤ) =
          Multiplicative.ofAdd (k + (j : ℤ)) from rfl, show k + (j : ℤ) = 0 by omega]
        exact map_one g
      have hB : g (Multiplicative.ofAdd (j : ℤ)) * g (Multiplicative.ofAdd k) = 1 := by
        rw [← map_mul, show Multiplicative.ofAdd (j : ℤ) * Multiplicative.ofAdd k =
          Multiplicative.ofAdd ((j : ℤ) + k) from rfl, show (j : ℤ) + k = 0 by omega]
        exact map_one g
      calc f ((Multiplicative.ofAdd k) • x) * g (Multiplicative.ofAdd k)
          = (g (Multiplicative.ofAdd k) * g (Multiplicative.ofAdd (j : ℤ))) *
              f ((Multiplicative.ofAdd k) • x) * g (Multiplicative.ofAdd k) := by
            rw [hA, one_mul]
        _ = g (Multiplicative.ofAdd k) *
              (g (Multiplicative.ofAdd (j : ℤ)) * f ((Multiplicative.ofAdd k) • x)) *
                g (Multiplicative.ofAdd k) := by noncomm_ring
        _ = g (Multiplicative.ofAdd k) *
              (f x * g (Multiplicative.ofAdd (j : ℤ))) * g (Multiplicative.ofAdd k) := by
            rw [← hpos]
        _ = g (Multiplicative.ofAdd k) * f x *
              (g (Multiplicative.ofAdd (j : ℤ)) * g (Multiplicative.ofAdd k)) := by
            noncomm_ring
        _ = g (Multiplicative.ofAdd k) * f x := by rw [hB, mul_one]
  have hcomm : ∀ {x : U} {y : Multiplicative ℤ}, f (y • x) * g y = g y * f x := by
    intro x y
    exact hcomm_int (Multiplicative.toAdd y) x
  let Φ : SkewL U →+* (W U ⧸ I) := SkewMonoidAlgebra.liftNCRingHom f g (fun {x y} => hcomm)
  have hΦsingle : ∀ (a : Multiplicative ℤ) (b : U),
      Φ (SkewMonoidAlgebra.single a b) = f b * g a := by
    intro a b
    show SkewMonoidAlgebra.liftNC (f : U →+ (W U ⧸ I)) g
      (SkewMonoidAlgebra.single a b) = f b * g a
    exact SkewMonoidAlgebra.liftNC_single (f : U →+ (W U ⧸ I)) g a b
  let ψ : SkewL U →+* (W U ⧸ I) :=
    { toFun := fun p => star (Φ (star p))
      map_one' := by simp
      map_zero' := by simp
      map_add' := by intro p q; rw [star_add, map_add, star_add]
      map_mul' := by intro p q; rw [star_mul, map_mul, star_mul] }
  have hψΦ : ψ = Φ := by
    have h1 : ψ.toAddMonoidHom =
        SkewMonoidAlgebra.liftNC (f : U →+ (W U ⧸ I)) g := by
      refine SkewMonoidAlgebra.eq_liftNC (f : U →+ (W U ⧸ I)) g ψ.toAddMonoidHom ?_
      intro a b
      show star (Φ (star (SkewMonoidAlgebra.single a b))) = f b * g a
      have hs : star (SkewMonoidAlgebra.single a b) =
          SkewMonoidAlgebra.single a⁻¹ (a⁻¹ • star b) := by
        have h2 := hst.2.2.2.2.1 (Multiplicative.toAdd a) b
        change starSkewL
            (SkewMonoidAlgebra.single (Multiplicative.ofAdd (Multiplicative.toAdd a)) b) =
          SkewMonoidAlgebra.single
            (Multiplicative.ofAdd (Multiplicative.toAdd a))⁻¹
            ((Multiplicative.ofAdd (Multiplicative.toAdd a))⁻¹ • star b) at h2
        exact h2
      rw [hs, hΦsingle a⁻¹ (a⁻¹ • star b), star_mul, hgstar a⁻¹, hfstar (a⁻¹ • star b)]
      rw [show star (a⁻¹ • star b) = a⁻¹ • b from by
        rw [StarAction.map_smul, star_star]]
      rw [show g (a⁻¹)⁻¹ = g a from by rw [inv_inv]]
      rw [← hcomm (x := a⁻¹ • b) (y := a)]
      congr 1
      rw [← mul_smul, mul_inv_cancel, one_smul]
    apply RingHom.ext
    intro p
    have h2 : ψ.toAddMonoidHom p = (SkewMonoidAlgebra.liftNC (f : U →+ (W U ⧸ I)) g) p :=
      DFunLike.congr_fun h1 p
    show ψ p = Φ p
    exact h2
  have hΦstar : ∀ p : SkewL U, Φ (star p) = star (Φ p) := by
    intro p
    have h1 : star (Φ p) = Φ (star p) := by
      have h2 : star (Φ (star (star p))) = Φ (star p) := congrArg (fun f => f (star p)) hψΦ
      simpa using h2
    exact h1.symm
  have hΦconst : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      (skewLaurentConst n m A).map Φ = A.map f := by
    intro n m A
    ext i j
    show Φ (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (A i j)) = f (A i j)
    rw [hΦsingle, map_one, mul_one]
  have hnatural_const : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      (SylvesterRank.pullback Φ rk_P).rk n m (skewLaurentConst n m A) = rk.rk n m A := by
    intro n m A
    show rk_P.rk n m ((skewLaurentConst n m A).map Φ) = rk.rk n m A
    rw [hΦconst n m A]
    have hmap : A.map f = (A.map toeplitzConstHom).map (Ideal.Quotient.mk I) := by
      ext i j; rfl
    rw [hmap, hrkP n m (A.map toeplitzConstHom), hrk_W n m (A.map toeplitzConstHom), blimRank]
    have hflat : ∀ k : ℕ, flatW n m (A.map toeplitzConstHom) k =
        trunc (k+1) (skewLaurentConst n m A) := by
      intro k
      have h1 : A.map toeplitzConstHom = toeplitzMatrix (skewLaurentConst n m A) := by
        ext i j; rfl
      rw [h1]
      exact flatW_toeplitzMatrix (skewLaurentConst n m A) k
    have hev : ∀ᶠ k in Filter.atTop,
        rk.rk (n * (k+1)) (m * (k+1)) (flatW n m (A.map toeplitzConstHom) k) /
            ((k+1 : ℕ) : ℝ) = rk.rk n m A := by
      filter_upwards with k
      rw [hflat k, rk_trunc_skewLaurentConst_univ rk hτ A (k+1)]
      have hk : (((k+1 : ℕ)) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [blim_congr ω hω hev, blim_const ω (rk.rk n m A)]
  have htoep_one : toeplitzFamily (1 : SkewL U) = 1 := funext fun k => toeplitz_one' (k+1)
  have htoep_zero : toeplitzFamily (0 : SkewL U) = 0 := funext fun k => toeplitz_zero' (k+1)
  have htoep_single_one : ∀ a : U,
      mk (toeplitzFamily (SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) a)) =
        f a * g (Multiplicative.ofAdd 1) := by
    intro a
    have ht : (skewLaurentT : SkewL U) =
        SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : U) := rfl
    have hm : SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) a =
        SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a *
          (skewLaurentT : SkewL U) := by
      rw [ht, SkewMonoidAlgebra.single_mul_single]
      simp
    have hmul : toeplitzFamily (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a *
          (skewLaurentT : SkewL U)) =
        toeplitzFamily (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) *
          toeplitzFamily (skewLaurentT : SkewL U) :=
      (toeplitzFamily_mul_of_nonneg (p := SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a)
        (q := (skewLaurentT : SkewL U))
        (fun k hk => coeffElt_monomial_nonneg (j := 0) a hk)
        (fun k hk => coeffElt_monomial_nonneg (j := 1) (1 : U) hk)).symm
    rw [hm, hmul, map_mul]
    have h1 : mk (toeplitzFamily (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a)) = f a := rfl
    have h2 : mk (toeplitzFamily (skewLaurentT : SkewL U)) = g (Multiplicative.ofAdd (1 : ℤ)) := by
      rw [show g (Multiplicative.ofAdd (1 : ℤ)) =
          ↑(u ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)))) from rfl,
        show Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ)) = (1 : ℤ) from rfl,
        zpow_one, ← hu]
    rw [h1, h2]
  have hΦonePlus : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) U),
      (onePlusAt n A).map Φ = (toeplitzMatrix (onePlusAt n A)).map (Ideal.Quotient.mk I) := by
    intro n A
    ext i j
    have h1 : (onePlusAt n A) i j =
        ((1 : Matrix (Fin n) (Fin n) (SkewL U)) i j) +
          SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) (A i j) := by
      simp only [onePlusAt, Matrix.add_apply, Matrix.map_apply]
    rw [Matrix.map_apply, h1, map_add, hΦsingle]
    rw [Matrix.map_apply, show (toeplitzMatrix (onePlusAt n A)) i j =
        toeplitzFamily ((onePlusAt n A) i j) from rfl, h1, toeplitzFamily_add', map_add,
      htoep_single_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp [htoep_one]
    · rw [Matrix.one_apply_ne hij]
      simp [htoep_zero]
  have hnatural_onePlus : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) U),
      (SylvesterRank.pullback Φ rk_P).rk n n (onePlusAt n A) = n := by
    intro n A
    show rk_P.rk n n ((onePlusAt n A).map Φ) = (n : ℝ)
    rw [hΦonePlus n A, hrkP n n (toeplitzMatrix (onePlusAt n A)),
      hrk_W n n (toeplitzMatrix (onePlusAt n A)), blimRank]
    have hev : ∀ᶠ k in Filter.atTop,
        rk.rk (n * (k+1)) (n * (k+1)) (flatW n n (toeplitzMatrix (onePlusAt n A)) k) /
            ((k+1 : ℕ) : ℝ) = (n : ℝ) := by
      filter_upwards with k
      rw [flatW_toeplitzMatrix, rk_trunc_onePlusAt_univ rk A (k+1)]
      have hk : (((k+1 : ℕ)) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [blim_congr ω hω hev, blim_const ω (n : ℝ)]
  have hnatural : IsNaturalExtension rk (SylvesterRank.pullback Φ rk_P) :=
    ⟨hnatural_const, hnatural_onePlus⟩
  let V : StarSubring (W U ⧸ I) := starRegularClosure (starSubringClosure (Set.range Φ))
  haveI : IsStarRegular ↥V := StarRegular.starRegularClosure_isStarRegular _
  have hVpd : IsPositiveDefiniteStarRegular ↥V :=
    starRegular_subring_positiveDefinite (Subring.subtype V.toSubring)
      (fun a b h => Subtype.ext h) (fun v => rfl) hP_pd
  have hΦstar' : ∀ p : SkewL U, closureCorestrict Φ (star p) = star (closureCorestrict Φ p) := by
    intro p
    apply Subtype.ext
    exact hΦstar p
  have hepic : IsEpic (closureCorestrict Φ) :=
    isEpic_of_starRegularClosure (closureCorestrict Φ) hΦstar' (by
      intro v
      have h := starRegularClosure_codRestrict_top (S := SkewL U) (P := W U ⧸ I) Φ hΦstar
      have h2 : v ∈ (starRegularClosure
          (starSubringClosure (Set.range (closureCorestrict Φ)))).toSubring := by
        rw [h]
        exact Subring.mem_top v
      exact h2)
  let rkV : SylvesterRank ↥V := SylvesterRank.pullback (Subring.subtype V.toSubring) rk_P
  have hfaithV : rkV.IsFaithful := by
    intro a ha
    have h1 : rk_P.rk 1 1 (oneByOne ((Subring.subtype V.toSubring) a)) = 0 := by
      have h2 := ha
      change rk_P.rk 1 1 ((oneByOne a).map (Subring.subtype V.toSubring)) = 0 at h2
      rwa [show (oneByOne a).map (Subring.subtype V.toSubring) =
        oneByOne ((Subring.subtype V.toSubring) a) from rfl] at h2
    have h3 : (Subring.subtype V.toSubring) a = 0 := hfaithP _ h1
    exact Subtype.ext h3
  have hrkE : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)),
      rkE.rk n m A = rkV.rk n m (A.map (closureCorestrict Φ)) := by
    intro n m A
    rw [naturalExtension_unique rk hτ h hnatural n m A]
    show rk_P.rk n m (A.map Φ) =
      rk_P.rk n m ((A.map (closureCorestrict Φ)).map (Subring.subtype V.toSubring))
    congr 1
  exact ⟨↥V, inferInstance, inferInstance, inferInstance, hVpd, closureCorestrict Φ, rkV,
    hepic, hfaithV, hrkE⟩

end Work.ORHughesFree.NaturalExtension
