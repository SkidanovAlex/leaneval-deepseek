import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.Eval
import Submission.Work.ORHughesFree.Rat.FreeProduct.evalList_relNE
import Submission.Work.ORHughesFree.Rat.FreeProduct.evalList_mulFirst
import Submission.Work.ORHughesFree.Rat.FreeProduct.evalList_mulLast
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.WordModel.sigma_rho

/-!
# The rational `U`-semiring `ℕ[U ♮ X]` and the normal form of a word

`Rat(U)` is the initial rational `U`-semiring (`Rat/RTerm.lean`); the word model
`ℕ[Mword]` of `Rat/WordModel/Defs.lean` is one of its models, and `U ♮ X`
(`Rat/FreeProduct/NU.lean`) is the underlying monoid of `Mword`.

This file assembles the dictionary between the two: the evaluation homomorphism
`evalHom : U ♮ X →* Rat(U)`, the induced ring homomorphism `sigma2 : ℕ[U ♮ X] →+* Rat(U)`,
the rational `U`-semiring structure `rNU` on `ℕ[U ♮ X]` whose `⋄` is `z ↦ single (Xgen (sigma2 z)) 1`,
the universal morphism `Psi : Rat(U) →+* ℕ[U ♮ X]`, and the *normal form* `nrm : Mword → U ♮ X`
characterised by `Psi (Mval m) = single (nrm m) 1`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat
namespace FreeProduct

open Work.ORHughesFree
open MonoidAlgebra

variable {U : Type} [Group U]

/-! ### The evaluation of `U ♮ X` in `Rat(U)` -/

/-- The evaluation of the `X`-part: the product of the `⋄`-values of a word. -/
noncomputable def evalX : XPart U → RatU U :=
  Quotient.lift (fun L : NEL (U := U) => evalList L.1)
    (fun _ _ h => evalList_relNE h)

@[simp] theorem evalX_mk (L : NEL (U := U)) : evalX (Quotient.mk _ L) = evalList L.1 := rfl

/-- The evaluation of the monoid `U ♮ X` in `Rat(U)`: `Ugen u ↦ ofGroup u`, `Xgen a ↦ a⋄`. -/
noncomputable def evalNU (x : NU U) : RatU U :=
  match x with
  | Sum.inl u => RatU.ofGroup u
  | Sum.inr P => evalX P

@[simp] theorem evalNU_Ugen (u : U) : evalNU (NU.Ugen u) = RatU.ofGroup u := rfl

@[simp] theorem evalNU_mk (L : NEL (U := U)) :
    evalNU (Sum.inr (Quotient.mk _ L)) = evalList L.1 := rfl

@[simp] theorem evalNU_Xgen (a : RatU U) : evalNU (NU.Xgen a) = RatU.ratOp a := by
  show evalX (Quotient.mk _ (⟨[a], by simp⟩ : NEL (U := U))) = RatU.ratOp a
  rw [evalX_mk]
  exact evalList_singleton a

theorem evalNU_mul_Ugen (x : NU U) (u : U) :
    evalNU (x * NU.Ugen u) = evalNU x * RatU.ofGroup u := by
  rcases x with v | P
  · show RatU.ofGroup (v * u) = RatU.ofGroup v * RatU.ofGroup u
    rw [RatU.ofGroup_mul]
  · refine Quotient.inductionOn P (fun L => ?_)
    rw [show (Sum.inr (Quotient.mk _ L) : NU U) * Sum.inl u
        = Sum.inr (Quotient.mk _ (⟨mulLast L.1 u, mulLast_ne_nil u L.2⟩ : NEL (U := U)))
        from NU.mk_mul_inl L u]
    simp only [evalNU_mk, evalList_mulLast u L.2, evalNU_Ugen]

theorem evalNU_Ugen_mul (u : U) (x : NU U) :
    evalNU (NU.Ugen u * x) = RatU.ofGroup u * evalNU x := by
  rcases x with v | P
  · show RatU.ofGroup (u * v) = RatU.ofGroup u * RatU.ofGroup v
    rw [RatU.ofGroup_mul]
  · refine Quotient.inductionOn P (fun L => ?_)
    rw [show (Sum.inl u : NU U) * Sum.inr (Quotient.mk _ L)
        = Sum.inr (Quotient.mk _ (⟨mulFirst u L.1, mulFirst_ne_nil u L.2⟩ : NEL (U := U)))
        from NU.inl_mul_mk u L]
    simp only [evalNU_mk, evalList_mulFirst u L.2, evalNU_Ugen]

theorem evalNU_mul (x y : NU U) : evalNU (x * y) = evalNU x * evalNU y := by
  rcases x with u | P
  · exact evalNU_Ugen_mul u y
  · refine Quotient.inductionOn P (fun L => ?_)
    rcases y with v | Q
    · exact evalNU_mul_Ugen _ v
    · refine Quotient.inductionOn Q (fun M => ?_)
      rw [show (Sum.inr (Quotient.mk _ L) : NU U) * Sum.inr (Quotient.mk _ M)
          = Sum.inr (Quotient.mk _ (⟨L.1 ++ M.1, by simp [L.2]⟩ : NEL (U := U)))
          from NU.mk_mul_mk L M]
      simp only [evalNU_mk, evalList_append]

/-- The evaluation homomorphism `U ♮ X →* Rat(U)`. -/
noncomputable def evalHom : NU U →* RatU U where
  toFun := evalNU
  map_one' := by
    rw [show (1 : NU U) = Sum.inl 1 from rfl]
    exact RatU.ofGroup_one
  map_mul' := evalNU_mul

@[simp] theorem evalHom_apply (x : NU U) : evalHom x = evalNU x := rfl

/-! ### The rational `U`-semiring `ℕ[U ♮ X]` -/

/-- The monoid algebra `ℕ[U ♮ X]`. -/
abbrev S2 (U : Type) [Group U] := MonoidAlgebra ℕ (NU U)

/-- The evaluation `ℕ[U ♮ X] →+* Rat(U)`. -/
noncomputable def sigma2 : S2 U →+* RatU U :=
  ((MonoidAlgebra.lift ℕ (RatU U) (NU U)) evalHom).toRingHom

theorem sigma2_single (p : NU U) (c : ℕ) :
    sigma2 (MonoidAlgebra.single p c) = c • evalNU p := by
  rw [show sigma2 (MonoidAlgebra.single p c)
      = (MonoidAlgebra.lift ℕ (RatU U) (NU U)) evalHom (MonoidAlgebra.single p c) from rfl,
    MonoidAlgebra.lift_single, evalHom_apply]

@[simp] theorem sigma2_single_one (p : NU U) :
    sigma2 (MonoidAlgebra.single p 1) = evalNU p := by
  rw [sigma2_single, one_smul]

/-- The rational operation of `ℕ[U ♮ X]`: the monomial on the `X`-letter named by the *value*, and
`0` when the value is `0`.  The latter is the axiom `RationalUSemiring.ratOp_zero`: in [JZLA20,
§4.2] the letters of `X` are indexed by the *non-zero* elements of the previous level, so there is
no letter `Xgen 0` (an `Xgen 0` would be a degenerate letter lying in `NUV V` for every `V`). -/
noncomputable def rNURatOp (U : Type) [Group U] (z : S2 U) : S2 U := by
  classical
  exact if sigma2 z = 0 then 0 else MonoidAlgebra.single (NU.Xgen (sigma2 z)) 1

theorem rNURatOp_of_ne {U : Type} [Group U] {z : S2 U} (h : sigma2 z ≠ 0) :
    rNURatOp U z = MonoidAlgebra.single (NU.Xgen (sigma2 z)) 1 := by
  rw [rNURatOp, if_neg h]

theorem rNURatOp_of_eq_zero {U : Type} [Group U] {z : S2 U} (h : sigma2 z = 0) :
    rNURatOp U z = 0 := by
  rw [rNURatOp, if_pos h]

theorem rNURatOp_zero (U : Type) [Group U] : rNURatOp U (0 : S2 U) = 0 :=
  rNURatOp_of_eq_zero (map_zero sigma2)

/-- The rational `U`-semiring structure on `ℕ[U ♮ X]`: the image of the group is the set of
monomials `single (Ugen u) 1`, and `⋄` is the monomial on the `X`-letter named by the value
(`0` when the value is `0`, see `rNURatOp`). -/
noncomputable def rNU : RationalUSemiring U (S2 U) where
  ratOp := rNURatOp U
  smul u z := MonoidAlgebra.single (NU.Ugen u) 1 * z
  smulRight z u := z * MonoidAlgebra.single (NU.Ugen u) 1
  smul_eq_mul u z := by rw [mul_one]
  smulRight_eq_mul z u := by rw [one_mul]
  smul_mul u v := by
    simp only [mul_one, MonoidAlgebra.single_mul_single, NU.Ugen_mul]
  smul_one_one := by
    rw [mul_one]
    exact MonoidAlgebra.one_def.symm
  smulRight_one_one := by
    rw [one_mul]
    exact MonoidAlgebra.one_def.symm
  smulRight_one u := by rw [one_mul, mul_one]
  ratOp_zero := rNURatOp_zero U
  rat_smul u v z := by
    have hsig : sigma2 (MonoidAlgebra.single (NU.Ugen u) 1
        * (z * MonoidAlgebra.single (NU.Ugen v) 1))
        = RatU.ofGroup u * (sigma2 z * RatU.ofGroup v) := by
      rw [map_mul, map_mul, sigma2_single_one, sigma2_single_one, evalNU_Ugen, evalNU_Ugen]
    by_cases hz : sigma2 z = 0
    · have hz' : sigma2 (MonoidAlgebra.single (NU.Ugen u) 1
          * (z * MonoidAlgebra.single (NU.Ugen v) 1)) = 0 := by rw [hsig, hz, zero_mul, mul_zero]
      rw [rNURatOp_of_eq_zero hz', rNURatOp_of_eq_zero hz]
      simp
    · have hz' : sigma2 (MonoidAlgebra.single (NU.Ugen u) 1
          * (z * MonoidAlgebra.single (NU.Ugen v) 1)) ≠ 0 := by
        rw [hsig]; exact fun h => hz ((RatU.ofGroup_mul_eq_zero_iff u v (sigma2 z)).mp h)
      rw [rNURatOp_of_ne hz', rNURatOp_of_ne hz, hsig]
      simp only [MonoidAlgebra.single_mul_single, one_mul, mul_one]
      congr 1
      rw [show NU.Ugen v⁻¹ * NU.Xgen (sigma2 z) * NU.Ugen u⁻¹
          = NU.Xgen (RatU.ofGroup u * (sigma2 z * RatU.ofGroup v)) by
        rw [NU.Ugen_mul_Xgen, NU.Xgen_mul_Ugen]
        congr 1
        simp only [actL, actR, inv_inv, mul_assoc]]

/-- The rational operation of the structure `rNU` is `rNURatOp`. -/
theorem rNU_ratOp_eq (z : S2 U) : rNU.ratOp z = rNURatOp U z := rfl

/-- The universal morphism `Rat(U) →+* ℕ[U ♮ X]`. -/
noncomputable def Psi : RatU U →+* S2 U := RatU.lift (S2 U) rNU

theorem sigma2_Psi (x : RatU U) : sigma2 (Psi x) = x := by
  have hid : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      (RingHom.id (RatU U)) := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hcomp : IsRationalUSemiringHom (RatU.rational (U := U)) (RatU.rational (U := U))
      (sigma2.comp Psi) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      show sigma2 (Psi (RatU.ratOp y)) = RatU.ratOp (sigma2 (Psi y))
      rw [show Psi (RatU.ratOp y) = rNU.ratOp (Psi y) from
        (RatU.lift_isHom (S2 U) rNU).map_rat y]
      rw [rNU_ratOp_eq]
      by_cases hy : sigma2 (Psi y) = 0
      · rw [rNURatOp_of_eq_zero hy, map_zero, hy, RatU.ratOp_zero]
      · rw [rNURatOp_of_ne hy]
        show sigma2 (MonoidAlgebra.single (NU.Xgen (sigma2 (Psi y))) 1) = _
        rw [sigma2_single_one, evalNU_Xgen]
    · intro u y
      show sigma2 (Psi (RatU.smul u y)) = RatU.smul u (sigma2 (Psi y))
      rw [show Psi (RatU.smul u y) = rNU.smul u (Psi y) from
        (RatU.lift_isHom (S2 U) rNU).map_smul u y]
      show sigma2 (MonoidAlgebra.single (NU.Ugen u) 1 * Psi y) = RatU.smul u (sigma2 (Psi y))
      rw [map_mul, sigma2_single_one, evalNU_Ugen, RatU.smul_eq_ofGroup_mul]
    · intro y u
      show sigma2 (Psi (RatU.smulRight y u)) = RatU.smulRight (sigma2 (Psi y)) u
      rw [show Psi (RatU.smulRight y u) = rNU.smulRight (Psi y) u from
        (RatU.lift_isHom (S2 U) rNU).map_smulRight y u]
      show sigma2 (Psi y * MonoidAlgebra.single (NU.Ugen u) 1) = RatU.smulRight (sigma2 (Psi y)) u
      rw [map_mul, sigma2_single_one, evalNU_Ugen, RatU.smulRight_eq_mul_ofGroup]
  have h1 : sigma2.comp Psi = RatU.lift (RatU U) (RatU.rational (U := U)) :=
    RatU.lift_unique (RatU U) (RatU.rational (U := U)) _ hcomp
  have h2 : RingHom.id (RatU U) = RatU.lift (RatU U) (RatU.rational (U := U)) :=
    RatU.lift_unique (RatU U) (RatU.rational (U := U)) _ hid
  have h3 : sigma2.comp Psi = RingHom.id (RatU U) := by rw [h1, ← h2]
  have h4 := congrArg (fun f : RatU U →+* RatU U => f x) h3
  simpa using h4

theorem Psi_injective : Function.Injective (Psi (U := U)) := by
  intro x y h
  have h' := congrArg sigma2 h
  simpa [sigma2_Psi] using h'

@[simp] theorem Psi_ofGroup (u : U) :
    Psi (RatU.ofGroup u) = MonoidAlgebra.single (NU.Ugen u) 1 := by
  have h : Psi (RatU.ofGroup u) = Psi (RatU.smul u 1) := by
    rw [show RatU.ofGroup u = RatU.smul u 1 by rw [RatU.smul_eq_ofGroup_mul, mul_one]]
  rw [h, show Psi (RatU.smul u 1) = rNU.smul u (Psi 1) from
    (RatU.lift_isHom (S2 U) rNU).map_smul u 1]
  show rNU.smul u (Psi 1) = MonoidAlgebra.single (NU.Ugen u) 1
  rw [map_one]
  simp only [rNU, mul_one]

/-- The image of a *non-zero* element under `Psi` is a monomial of `ℕ[U ♮ X]`.  The hypothesis
cannot be dropped: `Psi (⋄ 0) = Psi 0 = 0`, which is not a monomial. -/
@[simp] theorem Psi_ratOp {x : RatU U} (hx : x ≠ 0) :
    Psi (RatU.ratOp x) = MonoidAlgebra.single (NU.Xgen x) 1 := by
  rw [show Psi (RatU.ratOp x) = rNU.ratOp (Psi x) from
    (RatU.lift_isHom (S2 U) rNU).map_rat x]
  have hx' : sigma2 (Psi x) ≠ 0 := by rw [sigma2_Psi]; exact hx
  rw [rNU_ratOp_eq, rNURatOp_of_ne hx']
  show MonoidAlgebra.single (NU.Xgen (sigma2 (Psi x))) 1 = MonoidAlgebra.single (NU.Xgen x) 1
  rw [sigma2_Psi]

/-! ### The normal form of a word -/

theorem Psi_symVal (s : WordModel.PSym U) (hs : WordModel.symVal s ≠ 0) :
    ∃ w : NU U, Psi (WordModel.symVal s) = MonoidAlgebra.single w 1 := by
  cases s with
  | grp u => exact ⟨NU.Ugen u, Psi_ofGroup u⟩
  | lt A => cases A with
    | mk l =>
      refine ⟨NU.Xgen (WordModel.sumVal l), ?_⟩
      have hl : WordModel.sumVal l ≠ 0 := fun h0 =>
        hs (by rw [show WordModel.symVal (WordModel.PSym.lt (WordModel.PLetter.mk l))
              = RatU.ratOp (WordModel.sumVal l) from rfl, h0, RatU.ratOp_zero])
      exact Psi_ratOp hl

theorem Psi_wordVal (l : WordModel.PWord U) (hl : WordModel.wordVal l ≠ 0) :
    ∃ w : NU U, Psi (WordModel.wordVal l) = MonoidAlgebra.single w 1 := by
  induction l with
  | nil => exact ⟨1, by
      rw [show WordModel.wordVal ([] : WordModel.PWord U) = 1 from rfl, map_one]
      exact MonoidAlgebra.one_def⟩
  | cons s t ih =>
    have hst : WordModel.symVal s * WordModel.wordVal t ≠ 0 := hl
    have hs : WordModel.symVal s ≠ 0 := by
      intro h0
      exact hst (by rw [h0, zero_mul])
    have ht : WordModel.wordVal t ≠ 0 := by
      intro h0
      refine hst ((Rat.treeOfRat_eq_zero_iff U _).mp ?_)
      rw [Rat.treeOfRat_mul, h0, Rat.treeOfRat_zero, mul_zero]
    obtain ⟨w, hw⟩ := Psi_symVal s hs
    obtain ⟨w', hw'⟩ := ih ht
    exact ⟨w * w', by
      rw [show WordModel.wordVal (s :: t) = WordModel.symVal s * WordModel.wordVal t from rfl,
        map_mul, hw, hw', MonoidAlgebra.single_mul_single, mul_one]⟩

/-- `exists_nrm` for a *non-degenerate* word: a word whose value is non-zero has a normal form. -/
theorem exists_nrm {m : WordModel.Mword U} (hm : WordModel.Mval m ≠ 0) :
    ∃ w : NU U, Psi (WordModel.Mval m) = MonoidAlgebra.single w 1 := by
  have hout : WordModel.wordVal (Quotient.out m) ≠ 0 := fun h0 =>
    hm (by rw [WordModel.Mval_out, h0])
  obtain ⟨w, hw⟩ := Psi_wordVal (Quotient.out m) hout
  exact ⟨w, by rw [WordModel.Mval_out, hw]⟩

/-- `ofGroup u` is a non-zero element of `Rat(U)` (its complexity is the one-edge tree). -/
theorem ofGroup_ne_zero (u : U) : RatU.ofGroup u ≠ 0 := fun h =>
  Tree.one_ne_zero (by rw [← Rat.treeOfRat_ofGroup u, h, Rat.treeOfRat_zero])

theorem one_ne_zero_RatU : (1 : RatU U) ≠ 0 := by
  simpa using ofGroup_ne_zero (1 : U)

/-- The normal form of a word: the element `w` of `U ♮ X` with `Psi (Mval m) = single w 1` for a
non-degenerate word, and `1` for a degenerate word (`Mval m = 0`, which happens for words
containing a `⋄`-letter of value `0`).  The value at the degenerate words is a default: for those
there is no monomial representative, and `nrm` is *not* multiplicative on them (see
`nrm_mul`). -/
noncomputable def nrm (m : WordModel.Mword U) : NU U := by
  classical
  exact if h : WordModel.Mval m = 0 then 1 else Classical.choose (exists_nrm h)

theorem nrm_of_ne {m : WordModel.Mword U} (hm : WordModel.Mval m ≠ 0) :
    nrm m = Classical.choose (exists_nrm hm) := by
  rw [nrm, dif_neg hm]

theorem nrm_of_eq_zero {m : WordModel.Mword U} (hm : WordModel.Mval m = 0) : nrm m = 1 := by
  rw [nrm, dif_pos hm]

/-- **The normal form represents the value**: for a non-degenerate word, `Psi` of its value is the
monomial on its normal form. -/
theorem Psi_Mval {m : WordModel.Mword U} (hm : WordModel.Mval m ≠ 0) :
    Psi (WordModel.Mval m) = MonoidAlgebra.single (nrm m) 1 := by
  rw [nrm_of_ne hm]
  exact Classical.choose_spec (exists_nrm hm)

theorem nrm_mul {m m' : WordModel.Mword U} (hm : WordModel.Mval m ≠ 0)
    (hm' : WordModel.Mval m' ≠ 0) : nrm (m * m') = nrm m * nrm m' := by
  have hmm' : WordModel.Mval (m * m') ≠ 0 := by
    rw [WordModel.Mval_mul]
    intro h0
    have ht : Rat.treeOfRat U (WordModel.Mval m * WordModel.Mval m') = 0 := by
      rw [h0, Rat.treeOfRat_zero]
    rw [Rat.treeOfRat_mul] at ht
    rcases (Tree.mul_eq_zero _ _).mp ht with h | h
    · exact hm ((Rat.treeOfRat_eq_zero_iff U _).mp h)
    · exact hm' ((Rat.treeOfRat_eq_zero_iff U _).mp h)
  have h : MonoidAlgebra.single (nrm (m * m')) (1 : ℕ)
      = MonoidAlgebra.single (nrm m * nrm m') (1 : ℕ) := by
    rw [← Psi_Mval hmm', WordModel.Mval_mul, map_mul, Psi_Mval hm, Psi_Mval hm',
      MonoidAlgebra.single_mul_single, mul_one]
  exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h

theorem nrm_one : nrm (1 : WordModel.Mword U) = 1 := by
  have h : MonoidAlgebra.single (nrm (1 : WordModel.Mword U)) (1 : ℕ)
      = MonoidAlgebra.single (1 : NU U) (1 : ℕ) := by
    rw [← Psi_Mval (m := 1) (by rw [WordModel.Mval_one]; exact one_ne_zero_RatU),
      WordModel.Mval_one, map_one, MonoidAlgebra.one_def]
  exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h

/-- **Injectivity of the normal form on the non-degenerate words.**  It is *not* injective on the
whole of `Mword U`: a degenerate word (`Mval m = 0`) and a word of value `1` both have normal form
`1`. -/
theorem nrm_injective_of_ne {m m' : WordModel.Mword U} (hm : WordModel.Mval m ≠ 0)
    (hm' : WordModel.Mval m' ≠ 0) (h : nrm m = nrm m') : m = m' := by
  have h1 : Psi (WordModel.Mval m) = Psi (WordModel.Mval m') := by
    rw [Psi_Mval hm, Psi_Mval hm', h]
  exact WordModel.Mval_injective (Psi_injective h1)

theorem nrm_Mu (u : U) : nrm (WordModel.Mu u) = NU.Ugen u := by
  have h : MonoidAlgebra.single (nrm (WordModel.Mu u)) (1 : ℕ)
      = MonoidAlgebra.single (NU.Ugen u) (1 : ℕ) := by
    rw [← Psi_Mval (m := WordModel.Mu u) (by rw [WordModel.Mval_Mu]; exact ofGroup_ne_zero u),
      WordModel.Mval_Mu, Psi_ofGroup]
  exact MonoidAlgebra.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h

/-- **The letter of `rho a` evaluates to `a ⋄`**; this is the dictionary entry that turns the
first-letter equation of `Mword` into a `Rat(U)`-equation. -/
theorem Mval_letterOf_rho (a : RatU U) :
    WordModel.Mval (WordModel.letterOf (WordModel.rho a)) = RatU.ratOp a := by
  rw [WordModel.letterOf_val, WordModel.sumVal_toList, ← WordModel.sigma_apply,
    Work.ORHughesFree.Rat.WordModel.sigma_rho]

end FreeProduct
end Work.ORHughesFree.Rat
