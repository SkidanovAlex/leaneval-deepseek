import Mathlib
import Submission.Work.KT.Fund.Laurent

namespace Work.KT.FP

open Work.KT LaurentPolynomial

set_option linter.style.haveILetI false

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-! ## `laurentMap` is injective

`laurentMap X : C(X, ℂ)[T;T⁻¹] → C(X × S¹, ℂ)` sends a Laurent polynomial `∑ aₖ Tᵏ` with
coefficients in `C(X, ℂ)` to the function `(x, z) ↦ ∑ aₖ(x) zᵏ` on the circle.  It is injective:
two Laurent polynomials with the same value everywhere on `X × S¹` are equal.

The proof is by "separating the variables".  For a fixed `x : X` we slice `X × S¹` at `{x} × S¹`,
obtaining a ring homomorphism `C(X × S¹, ℂ) → C(S¹, ℂ)`; on the image of `laurentMap X` this is
`ℂ[T;T⁻¹] → C(S¹, ℂ)`, `T ↦ z`, applied to the coefficientwise evaluation of the Laurent
polynomial at `x`.  The latter map is injective because `S¹` is infinite (a nonzero polynomial has
finitely many roots).  Varying `x` then separates the coefficients.
-/

/-- The unit circle `S¹ ⊆ ℂ` is infinite. -/
lemma infinite_sph_complex : Infinite (Sph ℂ) := by
  have hI : Infinite (Set.Ioc (-Real.pi) Real.pi) :=
    Set.infinite_coe_iff.mpr (Set.Ioc_infinite (by linarith [Real.pi_pos]))
  exact Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective

/-- The coordinate `z ↦ z` on `S¹`, as a unit of `C(S¹, ℂ)`. -/
def zSphUnit : (C(Sph ℂ, ℂ))ˣ where
  val := ⟨fun z => (z : ℂ), continuous_subtype_val⟩
  inv := ⟨fun z => ((z : ℂ))⁻¹, continuous_subtype_val.inv₀ (fun z => ne_zero_of_mem_unit_sphere z)⟩
  val_inv := by ext z; exact mul_inv_cancel₀ (ne_zero_of_mem_unit_sphere z)
  inv_val := by ext z; exact inv_mul_cancel₀ (ne_zero_of_mem_unit_sphere z)

@[simp] lemma zSphUnit_apply (z : Sph ℂ) : ((zSphUnit : C(Sph ℂ, ℂ)) z) = (z : ℂ) := rfl

/-- The `ℂ`-algebra map `ℂ[T;T⁻¹] → C(S¹, ℂ)` sending `T` to the coordinate `z`. -/
def stdLaurent : LaurentPolynomial ℂ →+* C(Sph ℂ, ℂ) :=
  LaurentPolynomial.eval₂ (algebraMap ℂ (C(Sph ℂ, ℂ))) zSphUnit

/-- Evaluation of an ordinary polynomial at the circle coordinate. -/
def polEval : Polynomial ℂ →+* C(Sph ℂ, ℂ) :=
  Polynomial.eval₂RingHom (algebraMap ℂ (C(Sph ℂ, ℂ))) (zSphUnit : C(Sph ℂ, ℂ))

@[simp] lemma stdLaurent_C (a : ℂ) :
    stdLaurent (LaurentPolynomial.C a) = ContinuousMap.const (Sph ℂ) a := by
  rw [stdLaurent, LaurentPolynomial.eval₂_C]; ext z; simp

@[simp] lemma stdLaurent_T (n : ℤ) :
    stdLaurent (LaurentPolynomial.T n) = ((zSphUnit) ^ n).val :=
  LaurentPolynomial.eval₂_T _ _ _

lemma polEval_apply (g : Polynomial ℂ) (z : Sph ℂ) :
    (polEval g) z = Polynomial.eval (z : ℂ) g := by
  have h : (ContinuousMap.evalAlgHom ℂ ℂ z).toRingHom.comp polEval =
      Polynomial.evalRingHom (z : ℂ) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [polEval]
    · simp [polEval]
  exact RingHom.congr_fun h g

/-- A nonzero polynomial over `ℂ` does not vanish identically on the circle. -/
lemma polEval_eq_zero (g : Polynomial ℂ) (h : polEval g = 0) : g = 0 := by
  haveI : Infinite (Sph ℂ) := infinite_sph_complex
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_
    (Set.infinite_range_of_injective (f := (Subtype.val : Sph ℂ → ℂ)) Subtype.coe_injective)
  rintro w ⟨z, rfl⟩
  show Polynomial.eval (z : ℂ) g = 0
  rw [← polEval_apply g z, h]
  rfl

lemma stdLaurent_toLaurent (g : Polynomial ℂ) :
    stdLaurent (Polynomial.toLaurent g) = polEval g :=
  LaurentPolynomial.eval₂_toLaurent (algebraMap ℂ (C(Sph ℂ, ℂ))) zSphUnit g

lemma stdLaurent_eq_zero (f : LaurentPolynomial ℂ) (h : stdLaurent f = 0) : f = 0 := by
  obtain ⟨n, g, hg⟩ := LaurentPolynomial.exists_T_pow f
  have h1 : polEval g = 0 := by
    rw [← stdLaurent_toLaurent g, hg, map_mul, h, zero_mul]
  have h2 : g = 0 := polEval_eq_zero g h1
  have h3 : f * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← hg, h2, map_zero]
  have hT : (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial ℂ) *
      LaurentPolynomial.T (-(n : ℤ)) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  calc f = f * 1 := (mul_one f).symm
    _ = f * (LaurentPolynomial.T (n : ℤ) * LaurentPolynomial.T (-(n : ℤ))) := by rw [hT]
    _ = (f * LaurentPolynomial.T (n : ℤ)) * LaurentPolynomial.T (-(n : ℤ)) := by rw [mul_assoc]
    _ = 0 := by rw [h3, zero_mul]

/-- `ℂ[T;T⁻¹] → C(S¹, ℂ)`, `T ↦ z`, is injective. -/
theorem stdLaurent_injective : Function.Injective stdLaurent := by
  intro f g hfg
  have h0 : stdLaurent (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have h1 := stdLaurent_eq_zero (f - g) h0
  rwa [sub_eq_zero] at h1

/-! ## Slicing `C(X × S¹, ℂ)` at `{x} × S¹` -/

/-- Evaluation at `x : X`, as a ring homomorphism `C(X, ℂ) →+* ℂ`. -/
def evalRingAt (x : X) : C(X, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom

/-- Restriction of a function on `X × S¹` to the slice `{x} × S¹`, as a ring homomorphism. -/
def sliceMap (x : X) : C(X × Sph ℂ, ℂ) →+* C(Sph ℂ, ℂ) :=
  (pullAlg (ContinuousMap.prodMk (ContinuousMap.const (Sph ℂ) x)
    (ContinuousMap.id (Sph ℂ)))).toRingHom

lemma evalRingAt_apply (x : X) (a : C(X, ℂ)) : evalRingAt X x a = a x :=
  ContinuousMap.evalAlgHom_apply ℂ ℂ x a

lemma mapRingHom_C (x : X) (a : C(X, ℂ)) :
    AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) (LaurentPolynomial.C a)
      = LaurentPolynomial.C (a x) := by
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single,
    LaurentPolynomial.single_eq_C]
  exact congrArg LaurentPolynomial.C (evalRingAt_apply X x a)

lemma mapRingHom_T (x : X) (n : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) (LaurentPolynomial.T n)
      = LaurentPolynomial.T n := by
  show AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) (AddMonoidAlgebra.single n 1)
      = AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single]
  exact congrArg (AddMonoidAlgebra.single n) (map_one (evalRingAt X x))

lemma sliceMap_laurentMap_C (x : X) (a : C(X, ℂ)) :
    sliceMap X x (laurentMap X (LaurentPolynomial.C a)) = ContinuousMap.const (Sph ℂ) (a x) := by
  rw [laurentMap_C]
  ext z
  simp [sliceMap, pullAlg, ContinuousMap.prod_eval, ContinuousMap.comp_apply]

lemma sliceMap_laurentMap_T (x : X) (n : ℤ) :
    sliceMap X x (laurentMap X (LaurentPolynomial.T n)) = ((zSphUnit) ^ n).val := by
  rw [laurentMap_T]
  have hψ : Units.map (sliceMap X x).toMonoidHom (zUnit X) = zSphUnit := by
    apply Units.ext
    ext z
    simp [sliceMap, pullAlg, ContinuousMap.prod_eval, ContinuousMap.comp_apply, zSphUnit, zUnit]
  calc sliceMap X x (((zUnit X) ^ n).val)
      = (Units.map (sliceMap X x).toMonoidHom ((zUnit X) ^ n)).val := (Units.coe_map _ _).symm
    _ = ((Units.map (sliceMap X x).toMonoidHom (zUnit X)) ^ n).val := by rw [map_zpow]
    _ = ((zSphUnit) ^ n).val := by rw [hψ]

/-- Slicing commutes with `laurentMap` in the expected way. -/
theorem sliceMap_laurentMap_eq (x : X) :
    (sliceMap X x).comp (laurentMap X) =
      stdLaurent.comp (AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x)) := by
  apply RingHom.ext
  intro r
  show sliceMap X x (laurentMap X r)
      = stdLaurent (AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) r)
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n a =>
      simp only [map_mul]
      rw [sliceMap_laurentMap_C, sliceMap_laurentMap_T, mapRingHom_C, mapRingHom_T,
        stdLaurent_C, stdLaurent_T]

lemma sliceMap_laurentMap_apply (x : X) (p : LaurentPolynomial C(X, ℂ)) :
    sliceMap X x (laurentMap X p)
      = stdLaurent (AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) p) := by
  have := congrArg (fun (f : LaurentPolynomial C(X, ℂ) →+* C(Sph ℂ, ℂ)) => f p)
    (sliceMap_laurentMap_eq X x)
  simpa only [RingHom.comp_apply] using this

end

theorem laurentMap_injective (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Function.Injective (Work.KT.laurentMap X) := by
  intro p q hpq
  -- slice at every `x : X`: the coefficientwise evaluation at `x` of `p` and `q` agree.
  have key : ∀ x : X, AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) p
      = AddMonoidAlgebra.mapRingHom ℤ (evalRingAt X x) q := by
    intro x
    apply stdLaurent_injective
    rw [← sliceMap_laurentMap_apply X x p, ← sliceMap_laurentMap_apply X x q, hpq]
  -- hence all coefficients agree as functions on `X`, so `p = q`.
  apply LaurentPolynomial.ext
  intro n
  apply ContinuousMap.ext
  intro x
  have h := congrArg (fun r : LaurentPolynomial ℂ => r.coeff n) (key x)
  simpa [AddMonoidAlgebra.coeff_mapRingHom, evalRingAt_apply] using h

end Work.KT.FP
