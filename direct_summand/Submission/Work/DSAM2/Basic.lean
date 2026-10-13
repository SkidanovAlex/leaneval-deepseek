import Submission.Work.DSAM2.Defs

/-!
# DSAM2 (curric-46): elementary API for `ModSplit`

Degenerate case (`A` the zero ring) and the coordinate transport
`TensorProduct.piScalarRight` for `1 ⊗ₜ y`.
-/

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Work.DSAM2

universe a

/-! ## The coordinate transport for the pure tensor `1 ⊗ₜ y` -/

/-- Under the coordinate isomorphism
`TensorProduct.piScalarRight B B' B' ι : B' ⊗[B] (ι → B) ≃ₗ[B'] (ι → B')`,
the pure tensor `1 ⊗ₜ y` corresponds to the entrywise base change of `y`. -/
theorem piScalarRight_tmul_one {B : Type*} [CommRing B] {B' : Type*} [CommRing B']
    [Algebra B B'] {κ : Type*} [Fintype κ] [DecidableEq κ] (y : κ → B) :
    TensorProduct.piScalarRight B B' B' κ ((1 : B') ⊗ₜ[B] y) =
      fun k => algebraMap B B' (y k) := by
  ext k
  simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

/-! ## The degenerate case `A = 0` -/

/-- A ring hom out of the zero ring forces the target to be the zero ring. -/
theorem subsingleton_of_subsingleton_of_ringHom {A : Type*} {S : Type*} [CommSemiring A]
    [Semiring S] (ψ : A →+* S) (h : Subsingleton A) : Subsingleton S :=
  ⟨fun x y => by
    have h1 : (1 : S) = 0 := by
      rw [← map_one ψ, ← map_zero ψ, Subsingleton.elim (1 : A) 0]
    rw [← mul_one x, ← mul_one y, h1]
    simp⟩

/-- Degenerate case of the almost-splitting predicate: if `A` is the zero ring then so is `S`
(any ring hom out of the zero ring forces `1 = 0`), so `S ⧸ J` is a subsingleton and the zero
splitting witnesses `ModSplit`. -/
theorem modSplit_of_subsingleton {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {S : Type a} [CommRing S] (ψ : A →+* S) (J : Ideal S) (c : S)
    (h : Subsingleton A) : DSMap.Mix.ModSplit P ε ψ J c := by
  have : Subsingleton S := subsingleton_of_subsingleton_of_ringHom ψ h
  have : Subsingleton (S ⧸ J) := inferInstance
  refine ⟨0, fun y => by simp, ?_⟩
  exact Subsingleton.elim 0 _

end Work.DSAM2
