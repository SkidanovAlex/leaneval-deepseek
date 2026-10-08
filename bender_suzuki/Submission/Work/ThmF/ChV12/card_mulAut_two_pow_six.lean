import Mathlib
import Submission.Work.GL2odd.nonempty_mulAut_equiv_GL2
import Submission.Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The automorphism group of an elementary abelian `2`-group of order `2 ^ 6`

`Nat.card (MulAut A) = 20158709760 = 2^15 * 3^4 * 5 * 7^2 * 31` when `A` is an abelian group of
exponent `2` with `Nat.card A = 2 ^ 6` (i.e. `A ≅ (𝔽₂)⁶`).

This is the generalised version of `Work.GL2odd.nonempty_mulAut_equiv_GL2`; the group
`MulAut A` is identified with `GL (Fin 6) (ZMod 2)` through a choice of basis of `A` over `𝔽₂`,
and `Matrix.card_GL_field` gives the cardinality.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

open Work.GL2odd

noncomputable section

/-- `GL (Fin n) (ZMod p)` is the group of `ZMod p`-linear automorphisms of `Fin n → ZMod p`. -/
def glMulEquivLinearAutN (p n : ℕ) :
    GL (Fin n) (ZMod p) ≃* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod p)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p))

/-- Assemble `MulAut V ≃* GL (Fin n) (ZMod p)` from a linear equivalence
`e : Additive V ≃ₗ[ZMod p] (Fin n → ZMod p)`. -/
def mulAutMulEquivGL {p n : ℕ} (V : Type*) [CommGroup V] [Module (ZMod p) (Additive V)]
    (e : Additive V ≃ₗ[ZMod p] (Fin n → ZMod p)) : MulAut V ≃* GL (Fin n) (ZMod p) :=
  (MulAut.congr (mulEquivMultiplicativeAdditive V)).trans <|
  (MulAutMultiplicative (Additive V)).trans <|
  (multAddAutMulEquivLinearEquiv (p := p) (Additive V)).trans <|
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V)).symm.trans <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans <|
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Fin n → ZMod p))).trans <|
  (glMulEquivLinearAutN p n).symm

/-- **The automorphism group of an elementary abelian `2`-group of order `2 ^ 6` has
cardinality `2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 = 20158709760`.** -/
theorem natCard_mulAut_two_pow_six {A : Type} [CommGroup A] [Finite A]
    (hexp : ∀ x : A, x ^ 2 = 1) (hcard : Nat.card A = 2 ^ 6) :
    Nat.card (MulAut A) = 20158709760 := by
  haveI : Fintype (Additive A) := Fintype.ofFinite _
  have hmod : ∀ x : Additive A, 2 • x = 0 := by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow]
    simp [hexp]
  haveI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule (n := 2) hmod
  have hcardA : Nat.card (Additive A) = 2 ^ 6 :=
    (Nat.card_congr Additive.ofMul).symm.trans hcard
  have hfr : Module.finrank (ZMod 2) (Additive A) = 6 := by
    haveI : Module.Free (ZMod 2) (Additive A) := Module.Free.of_divisionRing _ _
    haveI : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    rw [hcardA] at h
    exact (Nat.pow_right_injective (Fact.out : Nat.Prime 2).two_le h).symm
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod 2)
    (M := Additive A) (M' := (Fin 6 → ZMod 2)) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hfr)
  have heq : Nat.card (MulAut A) = Nat.card (GL (Fin 6) (ZMod 2)) :=
    Nat.card_congr (mulAutMulEquivGL A e).toEquiv
  rw [heq, Matrix.card_GL_field]
  decide

/-- **An odd-order subgroup of `GL₆(𝔽₂)` has order dividing `615195`.**

`D` embeds into `MulAut A ≅ GL₆(𝔽₂)` of order `20158709760 = 2 ^ 15 * 615195`; as `|D|` is odd it
divides `615195 = 3 ^ 4 * 5 * 7 ^ 2 * 31`. -/
theorem card_dvd_615195 {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hk : Nat.card A = 2 ^ 6) (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A)
    (hfaith : Function.Injective ρ) : Nat.card D ∣ 615195 := by
  letI : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have hexp : ∀ x : A, x ^ 2 = 1 := fun x => by rw [pow_two]; exact hA2 x
  have hMul : Nat.card (MulAut A) = 20158709760 := natCard_mulAut_two_pow_six hexp hk
  have hdiv : Nat.card D ∣ Nat.card (MulAut A) := by
    have h := Subgroup.card_subgroup_dvd_card ρ.range
    have hcard : Nat.card ↥ρ.range = Nat.card D :=
      (Nat.card_congr (MonoidHom.ofInjective hfaith).toEquiv).symm
    rwa [hcard] at h
  rw [hMul] at hdiv
  have h2 : ¬ 2 ∣ Nat.card D := by
    have hne : ¬ Even (Nat.card D) := Nat.not_even_iff_odd.mpr hodd
    rwa [even_iff_two_dvd] at hne
  have hnum : (20158709760 : ℕ) = 2 ^ 15 * 615195 := by norm_num
  rw [hnum] at hdiv
  have hdiv' : Nat.card D ∣ 615195 * 2 ^ 15 := by rwa [mul_comm] at hdiv
  exact dvd_of_dvd_mul_prime_pow (p := 2) (k := 15) (by norm_num) h2 hdiv'

end

end Work.ThmF.ChV12
