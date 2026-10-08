import Mathlib
import Submission.Work.SmallRank.mulAut_not_dvd_of_abelian_card_dvd_prime_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Automorphisms of an elementary abelian `p`-group of order `p ^ 2` are `GL₂(𝔽_p)`

Let `p` be a prime and let `V` be a finite abelian group all of whose elements have order dividing
`p` (`∀ v, v ^ p = 1`) and whose cardinality is `p ^ 2`.  Then `V` is a two-dimensional vector
space over the field `𝔽_p = ZMod p`, and every additive (i.e. group) automorphism of `V` is
automatically `𝔽_p`-linear.  Choosing a basis, one obtains

`MulAut V ≃* GL (Fin 2) (ZMod p)`.

This is the elementary-abelian case of the classification of automorphism groups of finite abelian
`p`-groups, used in the analysis of the subgroup structure of `GL₂(𝔽_p)`.

## Main result

* `Work.GL2odd.nonempty_mulAut_equiv_GL2`
-/

set_option linter.style.haveILetI false

namespace Work.GL2odd

noncomputable section

/-- `V` and `Multiplicative (Additive V)` are isomorphic groups: the multiplicative structure of
`Multiplicative (Additive V)` is by definition the multiplicative structure of `V`. -/
def mulEquivMultiplicativeAdditive (V : Type*) [Mul V] : V ≃* Multiplicative (Additive V) where
  toFun v := Multiplicative.ofAdd (Additive.ofMul v)
  invFun m := Additive.toMul (Multiplicative.toAdd m)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Additive automorphisms of a `ZMod p`-module are exactly its `ZMod p`-linear automorphisms.
The group structure compared is composition on both sides. -/
def multAddAutMulEquivLinearEquiv {p : ℕ} (V : Type*) [AddCommGroup V] [Module (ZMod p) V] :
    Multiplicative (AddAut V) ≃* (V ≃ₗ[ZMod p] V) where
  toFun a := LinearEquiv.ofBijective
    (((Multiplicative.toAdd (α := AddAut V) a) : V →+ V).toZModLinearMap p)
    (Multiplicative.toAdd (α := AddAut V) a).bijective
  invFun f := Multiplicative.ofAdd f.toAddEquiv
  left_inv a := by ext x; simp [LinearEquiv.ofBijective]
  right_inv f := by ext x; simp [LinearEquiv.ofBijective]
  map_mul' a b := by ext x; simp [LinearEquiv.ofBijective]

/-- The matrix general linear group `GL (Fin 2) (ZMod p)` is the group of `ZMod p`-linear
automorphisms of `ZMod p ^ 2 = Fin 2 → ZMod p`. -/
def glMulEquivLinearAut (p : ℕ) :
    GL (Fin 2) (ZMod p) ≃* ((Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p)) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod p)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin 2 → ZMod p))

/-- Assemble the isomorphism `MulAut V ≃* GL (Fin 2) (ZMod p)` from a linear equivalence
`e : Additive V ≃ₗ[ZMod p] (Fin 2 → ZMod p)` (i.e. a choice of basis of `V` over `ZMod p`). -/
def mulAutMulEquivGL2 {p : ℕ} (V : Type*) [CommGroup V] [Module (ZMod p) (Additive V)]
    (e : Additive V ≃ₗ[ZMod p] (Fin 2 → ZMod p)) :
    MulAut V ≃* GL (Fin 2) (ZMod p) :=
  (MulAut.congr (mulEquivMultiplicativeAdditive V)).trans <|
  (MulAutMultiplicative (Additive V)).trans <|
  (multAddAutMulEquivLinearEquiv (p := p) (Additive V)).trans <|
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm.trans <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans <|
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin 2 → ZMod p))).trans <|
  (glMulEquivLinearAut p).symm

theorem nonempty_mulAut_equiv_GL2 {p : ℕ} [Fact p.Prime] {V : Type*} [CommGroup V] [Finite V]
    (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ 2) :
    Nonempty (MulAut V ≃* GL (Fin 2) (ZMod p)) := by
  -- `Additive V` is a module over `ZMod p`, because `p • x = 0` for all `x`.
  haveI : Fintype (Additive V) := Fintype.ofFinite _
  have hmod : ∀ x : Additive V, p • x = 0 := by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow]
    simp [hexp]
  haveI : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule (n := p) hmod
  -- Its cardinality is `p ^ 2`, hence its `ZMod p`-dimension is `2`.
  have hcardA : Nat.card (Additive V) = p ^ 2 :=
    (Nat.card_congr Additive.ofMul).symm.trans hcard
  have hfr : Module.finrank (ZMod p) (Additive V) = 2 := by
    haveI : Module.Free (ZMod p) (Additive V) := Module.Free.of_divisionRing _ _
    haveI : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    rw [hcardA] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  -- Choose a basis, giving `Additive V ≃ₗ[ZMod p] (Fin 2 → ZMod p)`.
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod p)
    (M := Additive V) (M' := (Fin 2 → ZMod p)) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hfr)
  exact ⟨mulAutMulEquivGL2 V e⟩

end

end Work.GL2odd
