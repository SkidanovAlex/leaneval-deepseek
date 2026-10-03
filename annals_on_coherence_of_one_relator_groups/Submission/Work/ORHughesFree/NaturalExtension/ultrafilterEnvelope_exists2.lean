import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.UltrafilterEnvelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.isStarRegularRank_naturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.isFaithful_of_isNaturalExtension

set_option synthInstance.maxHeartbeats 200000

/-!
# The ultrafilter envelope `P^U_{ω,τ}` of a `τ`-compatible rank function, exposed

[JZLA20, Proposition 3.6] constructs, for a positive definite `∗`-regular ring `U`, a
`τ`-compatible faithful Sylvester rank function `rk` on `U` and a natural extension `rkE` of `rk`
to `U[t^{±1};τ] = U[t^{±1};τ]`, an *epic `∗`-regular envelope* of `rkE`.  Its proof
(`Submission.Work.ORHughesFree.NaturalExtension.isStarRegularRank_naturalExtension`) only records
the ring, the structure map and the rank function existentially, through the predicate
`IsStarRegularRank`.

This file exposes that construction as the structure
`Work.ORHughesFree.NaturalExtension.UltrafilterEnvelope` of
`Submission.Work.ORHughesFree.NaturalExtension.UltrafilterEnvelopeDefs`, which [JZLA20,
Theorem 6.1] needs by name.  The ring is the ultraproduct

  `P = P^U_{ω,τ} = (∏_{n ≥ 1} M_n(U)) / ker rk_ω`,

the structure map `f_ω : U[t^{±1};τ] →+* P` is the map `Φ` sending the constants to the families of
Toeplitz matrices of the constants and `t` to the family of Toeplitz matrices of `t`, and the rank
function is `rk_ω`, the faithful quotient rank.  The proof below reproduces the construction of
`isStarRegularRank_naturalExtension` (stopping at the point where the data is available) and adds
the one property that the existential statement did not record, namely that `Φ` is injective.

Injectivity is the content of [JZLA20, (4)]: if `p ≠ 0` then, writing `p = a_i t^i + …` with first
non-zero coefficient `a_i`, the rank of `p` is at least `rk (a_i) > 0`, because the natural
extension of a faithful rank function is faithful (`isFaithful_of_isNaturalExtension`).  Hence
`rkE (p) ≠ 0` and, since `rkE` is the pullback of `rk_ω` along `Φ`, `Φ p ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

theorem ultrafilterEnvelope_exists2 {U : Type} [Ring U] [StarRing U] [IsStarRegular U]
    [MulSemiringAction (Multiplicative ℤ) U] (hpos : IsPositiveDefiniteStarRegular U)
    (rk : SylvesterRank U) (hrk : rk.IsFaithful)
    (hstar : ∀ (n : Multiplicative ℤ) (x : U), star (n • x) = n • star x)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    (rkE : SylvesterRank (SkewMonoidAlgebra U (Multiplicative ℤ)))
    (h : IsNaturalExtension rk rkE) :
    Nonempty (Work.ORHughesFree.NaturalExtension.UltrafilterEnvelope (U := U) hpos rk hstar hτ rkE) := by
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
  -- The natural extension of a faithful rank function is faithful; this is
  -- `isFaithful_of_isNaturalExtension`.
  have hfaithE : rkE.IsFaithful := isFaithful_of_isNaturalExtension rk hrk h
  -- Consequently `Φ` is injective: if `Φ p = 0` then `rkE (p) = 0`, so `p = 0`.
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    have hz : Φ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have h1 : rk_P.rk 1 1 ((oneByOne (p - q)).map Φ) = 0 := by
      rw [show (oneByOne (p - q)).map Φ = oneByOne (Φ (p - q)) from rfl, hz]
      exact rk_P.rk_zero 1 1
    have h2 : rkE.rk 1 1 (oneByOne (p - q)) = 0 := by
      rw [naturalExtension_unique rk hτ h hnatural 1 1 (oneByOne (p - q))]
      exact h1
    have h3 : p - q = 0 := hfaithE (p - q) h2
    exact sub_eq_zero.mp h3
  -- pulling `rk_ω` back along `Φ` gives the natural extension `rkE`
  have hrank : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)),
      rkE.rk n m A = rk_P.rk n m (A.map Φ) := by
    intro n m A
    rw [naturalExtension_unique rk hτ h hnatural n m A]
    rfl
  exact ⟨
    { P := W U ⧸ I
      ringP := inferInstance
      starP := inferInstance
      isStarRegularP := hP_star
      positiveDefiniteP := hP_pd
      rkP := rk_P
      faithfulP := hfaithP
      fω := Φ
      fω_star := fun p => hΦstar p
      fω_injective := hΦinj
      rank_compat := hrank }⟩

end Work.ORHughesFree.NaturalExtension
