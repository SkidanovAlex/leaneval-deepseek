import Mathlib
import Submission.Work.DSMap.Mix
import Submission.Work.DSAM2.Defs

namespace Work.DSAM2

universe a

/-! ## Auxiliary (generic) lemmas on base change of bases

These are the only structural facts used by `modSplit_iff_mulVec`: a `D`-linear map out of
`D ⊗[A] M` is determined by its values on the base-changed basis, and the value on `1 ⊗ x` is the
corresponding `D`-linear combination of those basis values. -/

/-- In `S ⊗[A] M`, the element `1 ⊗ₜ x` is the `S`-linear combination of the base-changed basis
`1 ⊗ₜ b i` given by the coordinates of `x`. -/
lemma tensor_tmul_eq_sum {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommMonoid M] [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M) (x : M) :
    (1 : S) ⊗ₜ[A] x = ∑ i, algebraMap A S (b.repr x i) • ((1 : S) ⊗ₜ[A] b i) := by
  conv_lhs => rw [← (b.baseChange S).sum_repr ((1 : S) ⊗ₜ[A] x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

/-- Evaluation of an `S`-linear map on `1 ⊗ₜ x` in terms of its values on the base-changed basis. -/
lemma tensor_eval {A S M N : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommMonoid M] [Module A M] {ι : Type*} [Fintype ι] (b : Module.Basis ι A M)
    [AddCommMonoid N] [Module S N] (s : TensorProduct A S M →ₗ[S] N) (x : M) :
    s ((1 : S) ⊗ₜ[A] x) = ∑ i, algebraMap A S (b.repr x i) • s ((1 : S) ⊗ₜ[A] b i) := by
  rw [tensor_tmul_eq_sum b x, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul s _ _

/-- The `S`-action on the quotient `S ⧸ J` is left multiplication by the class of the scalar. -/
lemma smul_mk_quotient {S : Type*} [CommRing S] (J : Ideal S) (r : S) (z : S ⧸ J) :
    r • z = Ideal.Quotient.mk J r * z := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [show r • Submodule.Quotient.mk w = Submodule.Quotient.mk (r • w) from
        Submodule.Quotient.mk_smul _ r w]
  simp [smul_eq_mul]

/-- `DSMap.Mix.ModSplit P ε ψ J c` (a splitting of the unit `ε 1` of a finite free model `(P, ε)`
modulo `J`, up to the factor `c`) is the solvability of the inhomogeneous linear system attached to
`(P, ε)` in bases `b0` of `P.X 0` and `b1` of `P.X (-1)`: the unknown `q i = s (1 ⊗ₜ b0 i)` and the
equations are `∑ i, (coord_i (d (b1 j))) • q i = 0` for each `j`, plus `∑ i, (coord_i (ε 1)) • q i = c`.
The point of this form is that it is stable under base change `A → S → S ⧸ J`. -/
theorem modSplit_iff_mulVec {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) {S : Type a} [CommRing S] (ψ : A →+* S) (J : Ideal S) (c : S)
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁]
    (b0 : Module.Basis ι₀ A (P.X 0)) (b1 : Module.Basis ι₁ A (P.X (-1))) :
    DSMap.Mix.ModSplit P ε ψ J c ↔
      ∃ q : ι₀ → S ⧸ J,
        ((Work.DSAM2.systemMatrix P ε b0 b1).map (fun x => Ideal.Quotient.mk J (ψ x))).mulVec q =
          (fun k => Ideal.Quotient.mk J (Work.DSAM2.systemRHS c k)) := by
  letI : Algebra A S := ψ.toAlgebra
  -- the scalar `A`-action on `S ⧸ J` is multiplication by the class of the image in `S`
  have hsmul : ∀ (x : A) (z : S ⧸ J), algebraMap A S x • z = Ideal.Quotient.mk J (ψ x) * z := by
    intro x z
    rw [show algebraMap A S x = ψ x from rfl]
    exact smul_mk_quotient J (ψ x) z
  rw [DSMap.Mix.ModSplit]
  constructor
  · -- a splitting `s` yields the solution vector `q i = s (1 ⊗ b0 i)`
    rintro ⟨s, hs1, hs2⟩
    refine ⟨fun i => s ((1 : S) ⊗ₜ[A] b0 i), ?_⟩
    have key : ∀ x : P.X 0, s ((1 : S) ⊗ₜ[A] x)
        = ∑ i, Ideal.Quotient.mk J (ψ (b0.repr x i)) * s ((1 : S) ⊗ₜ[A] b0 i) := by
      intro x
      rw [tensor_eval b0 s x]
      exact Finset.sum_congr rfl fun i _ => hsmul _ _
    funext k
    cases k with
    | none =>
      show (∑ i, Ideal.Quotient.mk J (ψ (b0.repr (ε.hom 1) i))
          * s ((1 : S) ⊗ₜ[A] b0 i)) = Ideal.Quotient.mk J c
      rw [← key (ε.hom 1), hs2]
    | some j =>
      show (∑ i, Ideal.Quotient.mk J (ψ (b0.repr (((P.d (-1) 0).hom (b1 j))) i))
          * s ((1 : S) ⊗ₜ[A] b0 i)) = Ideal.Quotient.mk J (0 : S)
      rw [← key ((P.d (-1) 0).hom (b1 j))]
      have h0 : s ((1 : S) ⊗ₜ[A] (P.d (-1) 0).hom (b1 j)) = 0 := by
        have hh := hs1 ((1 : S) ⊗ₜ[A] b1 j)
        rwa [LinearMap.baseChange_tmul] at hh
      rw [h0, map_zero]
  · -- conversely a solution vector `q` defines the splitting `s` by its values on the basis
    rintro ⟨q, hq⟩
    let s := (b0.baseChange S).constr S q
    have key : ∀ x : P.X 0, s ((1 : S) ⊗ₜ[A] x)
        = ∑ i, Ideal.Quotient.mk J (ψ (b0.repr x i)) * q i := by
      intro x
      rw [tensor_eval b0 s x]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hqi : s ((1 : S) ⊗ₜ[A] b0 i) = q i := by
        rw [← Module.Basis.baseChange_apply (S := S) (b := b0) (i := i)]
        exact Module.Basis.constr_basis (b0.baseChange S) S q i
      rw [hqi, hsmul]
    -- the `j`-th and unit rows of the system, extracted from `hq`
    have hqj : ∀ j : ι₁,
        (∑ i, Ideal.Quotient.mk J (ψ (b0.repr ((P.d (-1) 0).hom (b1 j)) i)) * q i) = 0 := by
      intro j
      have hh := congrFun hq (some j)
      simpa [Matrix.map_apply, Work.DSAM2.systemMatrix, Work.DSAM2.systemRHS, Matrix.mulVec,
        dotProduct] using hh
    have hqn : (∑ i, Ideal.Quotient.mk J (ψ (b0.repr (ε.hom 1) i)) * q i)
        = Ideal.Quotient.mk J c := by
      have hh := congrFun hq none
      simpa [Matrix.map_apply, Work.DSAM2.systemMatrix, Work.DSAM2.systemRHS, Matrix.mulVec,
        dotProduct] using hh
    refine ⟨s, ?_, ?_⟩
    · -- `s` kills the image of the differential
      intro y
      have hy : y = ∑ j, (b1.baseChange S).repr y j • ((1 : S) ⊗ₜ[A] b1 j) := by
        conv_lhs => rw [← (b1.baseChange S).sum_repr y]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Module.Basis.baseChange_apply]
      have hdy : (P.d (-1) 0).hom.baseChange S y
          = ∑ j, (b1.baseChange S).repr y j • ((1 : S) ⊗ₜ[A] (P.d (-1) 0).hom (b1 j)) := by
        conv_lhs => rw [hy]
        simp only [map_sum, map_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.baseChange_tmul]
      rw [hdy]
      simp only [map_sum, map_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [key, hqj, smul_zero]
    · -- `s` takes `1 ⊗ ε 1` to `c`
      rw [key (ε.hom 1), hqn]

end Work.DSAM2
