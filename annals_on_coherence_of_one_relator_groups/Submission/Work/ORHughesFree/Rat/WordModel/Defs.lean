import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.Restrict

set_option autoImplicit false

namespace Work.ORHughesFree
namespace Rat
namespace WordModel

open MonoidAlgebra

/-!
# The DHS word model of `Rat(U)`

[JZLA20, §4.2] (after Dicks–Herbera–Sánchez) exhibits `Rat(U)` as `ℕ[U ♮ X] ∖ {0}`, where
`X` is the `U`-biset of "`⋄`-letters" and `U ♮ X` the monoid of words.  The `⋄`-letters are in
bijection with `Rat(U)` itself, so the whole construction is recursive; here it is realised as a
mutually inductive type of symbols and letters, and the monoid of words is the quotient of the
free monoid on the symbols by the relation "same value in `Rat(U)`".

The purpose of this file is to provide a *faithful* model `ℕ[U ♮ X]` of `Rat(U)` (as a semiring
together with its rational `U`-semiring structure), which detects the image of `Rat(V) ⊆ Rat(U)`
in the form of a support condition: this is what proves the additive purity of `Rat(V) ⊆ Rat(U)`.
-/

mutual
/-- The symbols of a word: a group element, or a `⋄`-letter. -/
inductive PSym (U : Type) where
  | grp : U → PSym U
  | lt : PLetter U → PSym U
/-- A `⋄`-letter, named by a formal finite sum of words. -/
inductive PLetter (U : Type) where
  | mk : List (List (PSym U) × ℕ) → PLetter U
end

/-- A word: a finite sequence of symbols. -/
abbrev PWord (U : Type) := List (PSym U)

mutual
noncomputable def symVal {U : Type} [Group U] : PSym U → RatU U
  | .grp u => RatU.ofGroup u
  | .lt x => letterVal x
noncomputable def letterVal {U : Type} [Group U] : PLetter U → RatU U
  | .mk l => RatU.ratOp (sumVal l)
noncomputable def sumVal {U : Type} [Group U] : List (PWord U × ℕ) → RatU U
  | [] => 0
  | p :: t => p.2 • wordVal p.1 + sumVal t
noncomputable def wordVal {U : Type} [Group U] : PWord U → RatU U
  | [] => 1
  | s :: t => symVal s * wordVal t
end

variable {U : Type} [Group U]

/-- The value of a list of symbols. -/
theorem wordVal_eq_prod (w : PWord U) : wordVal w = (w.map symVal).prod := by
  induction w with
  | nil => simp [wordVal]
  | cons s t ih => simp only [List.map_cons, List.prod_cons, wordVal, ih]

/-- The value of a list of (word, coefficient) pairs. -/
theorem sumVal_eq_sum (l : List (PWord U × ℕ)) :
    sumVal l = (l.map (fun p => p.2 • wordVal p.1)).sum := by
  induction l with
  | nil => simp [sumVal]
  | cons p t ih => simp only [List.map_cons, List.sum_cons, sumVal, ih]

theorem wordVal_append (a b : PWord U) : wordVal (a ++ b) = wordVal a * wordVal b := by
  rw [wordVal_eq_prod, wordVal_eq_prod, wordVal_eq_prod, List.map_append, List.prod_append]

/-- The relation on words: having the same value in `Rat(U)`. -/
def Mrel (U : Type) [Group U] (a b : PWord U) : Prop := wordVal a = wordVal b

theorem Mrel_refl (a : PWord U) : Mrel U a a := rfl

theorem Mrel_symm {a b : PWord U} (h : Mrel U a b) : Mrel U b a := h.symm

theorem Mrel_trans {a b c : PWord U} (h1 : Mrel U a b) (h2 : Mrel U b c) : Mrel U a c :=
  h1.trans h2

instance wordSetoid (U : Type) [Group U] : Setoid (PWord U) where
  r := Mrel U
  iseqv := ⟨Mrel_refl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The monoid of words `U ♮ X`. -/
abbrev Mword (U : Type) [Group U] : Type := Quotient (wordSetoid U)

namespace Mword

instance instMonoid (U : Type) [Group U] : Monoid (Mword U) where
  mul a b := Quotient.lift₂ (fun x y => Quotient.mk _ (x ++ y))
    (fun a₁ b₁ a₂ b₂ h1 h2 => Quotient.sound (by
      show Mrel U (a₁ ++ b₁) (a₂ ++ b₂)
      rw [Mrel, wordVal_append, wordVal_append, h1, h2])) a b
  one := Quotient.mk _ []
  one_mul a := by
    induction a using Quotient.inductionOn with
    | h x => exact Quotient.sound (by show Mrel U ([] ++ x) x; rfl)
  mul_one a := by
    induction a using Quotient.inductionOn with
    | h x => exact Quotient.sound (by show Mrel U (x ++ []) x; simp [Mrel, wordVal])
  mul_assoc a b c := by
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        induction c using Quotient.inductionOn with
        | h z => exact Quotient.sound (by show Mrel U ((x ++ y) ++ z) (x ++ (y ++ z)); simp [Mrel])

end Mword

/-- The value of a word in `Rat(U)`. -/
noncomputable def Mval {U : Type} [Group U] : Mword U → RatU U :=
  Quotient.lift wordVal (fun a b h => h)

@[simp] theorem Mval_mk (a : PWord U) : Mval (Quotient.mk _ a) = wordVal a := rfl

@[simp] theorem Mval_mul (a b : Mword U) : Mval (a * b) = Mval a * Mval b := by
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y => exact wordVal_append x y

@[simp] theorem Mval_one : Mval (1 : Mword U) = 1 := rfl

theorem Mval_out (w : Mword U) : Mval w = wordVal (Quotient.out w) := by
  induction w using Quotient.inductionOn with
  | h a =>
    show wordVal a = wordVal (Quotient.out (Quotient.mk _ a))
    exact (Quotient.mk_out' (s₁ := wordSetoid U) a).symm

noncomputable def Uword (u : U) : PWord U := [PSym.grp u]

noncomputable def Mu (u : U) : Mword U := Quotient.mk _ (Uword u)

@[simp] theorem Mval_Mu (u : U) : Mval (Mu u) = RatU.ofGroup u := by
  rw [Mu, Mval_mk]
  simp [Uword, wordVal, symVal]

theorem Mu_mul (u v : U) : (Mu u : Mword U) * Mu v = Mu (u * v) := by
  refine Quotient.sound ?_
  show Mrel U ([PSym.grp u] ++ [PSym.grp v]) [PSym.grp (u * v)]
  simp only [Mrel, wordVal, symVal, List.nil_append, List.cons_append, List.prod_cons,
    List.prod_nil, mul_one, RatU.ofGroup_mul]

@[simp] theorem Mu_one : (Mu 1 : Mword U) = 1 := by
  refine Quotient.sound ?_
  show Mrel U [PSym.grp 1] []
  simp only [Mrel, wordVal, symVal, List.prod_cons, List.prod_nil, mul_one, RatU.ofGroup_one]

/-- The monoid algebra `ℕ[M]`. -/
abbrev S (U : Type) [Group U] := MonoidAlgebra ℕ (Mword U)

noncomputable def toList (z : S U) : List (PWord U × ℕ) :=
  (z.coeff.support.val.toList).map (fun w => (Quotient.out w, z.coeff w))

noncomputable def letterOf (z : S U) : Mword U :=
  Quotient.mk _ [PSym.lt (PLetter.mk (toList z))]

@[simp] theorem letterOf_val (z : S U) : Mval (letterOf z) = RatU.ratOp (sumVal (toList z)) := by
  rw [letterOf, Mval_mk]
  simp [wordVal, symVal, letterVal]

/-- **The letter of `z` is the `⋄` of `z`**: the formal sum of the words supporting `z` has value
`σ z`, where `σ` is the value map `ℕ[M] → Rat(U)`. -/
theorem sumVal_toList (z : S U) : sumVal (toList z) = z.coeff.sum (fun w c => c • Mval w) := by
  have hmap : List.map (fun p : PWord U × ℕ => p.2 • wordVal p.1)
        (List.map (fun w => (Quotient.out w, z.coeff w)) (z.coeff.support.val.toList))
      = List.map (fun w => z.coeff w • Mval w) (z.coeff.support.val.toList) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro w _
    simp [Mval_out]
  rw [sumVal_eq_sum, toList, hmap, Multiset.sum_map_toList, ← Finset.sum_eq_multiset_sum,
    ← Finsupp.sum_of_support_subset z.coeff (subset_refl _) (fun w c => c • Mval w)
      (fun i hi => by simp)]

/-- The monoid homomorphism `M →* Rat(U)` underlying `σ`. -/
noncomputable def MmonoidHom : Mword U →* RatU U where
  toFun := Mval
  map_one' := Mval_one
  map_mul' := Mval_mul

/-- The value map `σ : ℕ[M] → Rat(U)`. -/
noncomputable def sigma : S U →+* RatU U :=
  ((MonoidAlgebra.lift ℕ (RatU U) (Mword U)) MmonoidHom).toRingHom

@[simp] theorem sigma_apply (z : S U) :
    sigma z = z.coeff.sum (fun w c => c • Mval w) :=
  MonoidAlgebra.lift_apply _ _

@[simp] theorem sigma_single (w : Mword U) (c : ℕ) :
    sigma (MonoidAlgebra.single w c) = c • Mval w :=
  MonoidAlgebra.lift_single _ w c

theorem sigma_letterOf (z : S U) : sigma (MonoidAlgebra.single (letterOf z) 1) = Mval (letterOf z) := by
  simp

theorem Mval_injective : Function.Injective (Mval : Mword U → RatU U) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | h x =>
    induction b using Quotient.inductionOn with
    | h y => exact Quotient.sound h

/-- `single (a*b) 1` is the product of the two monomials. -/
theorem single_mul_single_one (a b : Mword U) :
    MonoidAlgebra.single (a * b) (1 : ℕ) =
      MonoidAlgebra.single a 1 * MonoidAlgebra.single b 1 := by
  rw [MonoidAlgebra.single_mul_single, mul_one]

/-- **The key `⋄`-identity**: the letter of the conjugates of `z` is the conjugate of the letter
of `z` in the word monoid. -/
theorem letterOf_smul (u : U) (z : S U) (v : U) :
    letterOf (MonoidAlgebra.single (Mu u) 1 * (z * MonoidAlgebra.single (Mu v) 1))
      = Mu v⁻¹ * letterOf z * Mu u⁻¹ := by
  apply Mval_injective
  rw [letterOf_val, sumVal_toList]
  rw [Mval_mul, Mval_mul, Mval_Mu, Mval_Mu, letterOf_val, sumVal_toList]
  have hZ : sigma (MonoidAlgebra.single (Mu u) 1 * (z * MonoidAlgebra.single (Mu v) 1))
      = RatU.smul u (RatU.smulRight (sigma z) v) := by
    rw [map_mul, map_mul, sigma_single, sigma_single, Mval_Mu, Mval_Mu]
    rw [one_smul, one_smul, RatU.smul_eq_ofGroup_mul, RatU.smulRight_eq_mul_ofGroup]
  have hax : RatU.ratOp (RatU.smul u (RatU.smulRight (sigma z) v))
      = RatU.smulRight (RatU.smul v⁻¹ (RatU.ratOp (sigma z))) u⁻¹ :=
    (RatU.rational (U := U)).rat_smul u v (sigma z)
  rw [← sigma_apply, hZ, hax, RatU.smulRight_eq_mul_ofGroup, RatU.smul_eq_ofGroup_mul,
    sigma_apply]

/-- The rational operation of `ℕ[M]`: the monomial on the letter of `z`, and `0` when the value
`sigma z` is `0` (the axiom `RationalUSemiring.ratOp_zero`; cf. `rNURatOp`). -/
noncomputable def rSRatOp (U : Type) [Group U] (z : S U) : S U := by
  classical
  exact if sigma z = 0 then 0 else MonoidAlgebra.single (letterOf z) 1

theorem rSRatOp_of_ne {U : Type} [Group U] {z : S U} (h : sigma z ≠ 0) :
    rSRatOp U z = MonoidAlgebra.single (letterOf z) 1 := by
  rw [rSRatOp, if_neg h]

theorem rSRatOp_of_eq_zero {U : Type} [Group U] {z : S U} (h : sigma z = 0) :
    rSRatOp U z = 0 := by
  rw [rSRatOp, if_pos h]

theorem rSRatOp_zero (U : Type) [Group U] : rSRatOp U (0 : S U) = 0 :=
  rSRatOp_of_eq_zero (map_zero sigma)

/-- The rational `U`-semiring structure on `ℕ[M]`. -/
noncomputable def rS : RationalUSemiring U (S U) where
  ratOp := rSRatOp U
  smul u z := MonoidAlgebra.single (Mu u) 1 * z
  smulRight z u := z * MonoidAlgebra.single (Mu u) 1
  smul_eq_mul u z := by rw [mul_one]
  smulRight_eq_mul z u := by rw [one_mul]
  smul_mul u v := by
    rw [mul_one, mul_one, mul_one, MonoidAlgebra.single_mul_single, Mu_mul, mul_one]
  smul_one_one := by rw [Mu_one, mul_one, MonoidAlgebra.one_def]
  smulRight_one_one := by rw [Mu_one, one_mul, MonoidAlgebra.one_def]
  smulRight_one u := by rw [one_mul, mul_one]
  ratOp_zero := rSRatOp_zero U
  rat_smul u v z := by
    have hsig : sigma (MonoidAlgebra.single (Mu u) 1 * (z * MonoidAlgebra.single (Mu v) 1))
        = RatU.ofGroup u * (sigma z * RatU.ofGroup v) := by
      rw [map_mul, map_mul, sigma_single, sigma_single, Mval_Mu, Mval_Mu, one_smul, one_smul]
    by_cases hz : sigma z = 0
    · have hz' : sigma (MonoidAlgebra.single (Mu u) 1
          * (z * MonoidAlgebra.single (Mu v) 1)) = 0 := by rw [hsig, hz, zero_mul, mul_zero]
      rw [rSRatOp_of_eq_zero hz', rSRatOp_of_eq_zero hz]
      simp
    · have hz' : sigma (MonoidAlgebra.single (Mu u) 1
          * (z * MonoidAlgebra.single (Mu v) 1)) ≠ 0 := by
        rw [hsig]
        exact fun h => hz ((RatU.ofGroup_mul_eq_zero_iff u v (sigma z)).mp h)
      rw [rSRatOp_of_ne hz', rSRatOp_of_ne hz]
      simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
      congr 1
      exact letterOf_smul u z v

/-- The universal morphism `Rat(U) → ℕ[M]`. -/
noncomputable def rho : RatU U →+* S U := RatU.lift (S U) rS

/-- `ρ` commutes with `⋄`, for those `x` whose image has non-zero value.  The condition
`σ (ρ x) ≠ 0` cannot be dropped: when `x = 0` the left-hand side is `0` (as `⋄ 0 = 0`) while
`single (letterOf (ρ x)) 1` is a non-zero monomial of `ℕ[U ♮ X]`. -/
@[simp] theorem rho_ratOp {x : RatU U} (hx : sigma (rho x) ≠ 0) :
    rho (RatU.ratOp x) = MonoidAlgebra.single (letterOf (rho x)) 1 := by
  rw [show rho (RatU.ratOp x) = rS.ratOp (rho x) from (RatU.lift_isHom (S U) rS).map_rat x]
  change rSRatOp U (rho x) = MonoidAlgebra.single (letterOf (rho x)) 1
  rw [rSRatOp_of_ne hx]

end WordModel
end Rat
end Work.ORHughesFree
