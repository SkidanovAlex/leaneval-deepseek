import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `λ`-vocabulary of the E5s realisation step

Extracted from `Submission/Work/SSGRoute/phi1_mono_step_in.lean` (content unchanged) so that the
*layer compatibility* lemmas about `deltaHom` and `lambdaOnRange` can be stated and proved in a file
lying *below* the assembly, and be used by the realisation step of `exists_realization_of_delta_lam`.

* `rangeLift` — the additive factorisation of a map through the range of another (`ker f ≤ ker g`);
* `phiAtHomRight` — the level pairing `h ↦ φ(x)(h)`, bundled as an additive map in `h`;
* `deltaHom` — the connecting map `δ_L : H¹(Gal(L/k), S.X₃) → H²(Gal(L/k), S.X₁)` of a short exact
  sequence `S` (`j ↦ j ∘ S.extClass`), bundled;
* `lambdaOnRange` — the descent of the level functional `h ↦ φ(y)(h)` through `δ_L` (well defined
  because `φ(y)` kills `ker δ_L`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-! ## General algebra: factoring an additive map through the range of another -/

section RangeLift

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- **Range lift.**  If `f : A →+ B` and `g : A →+ C` satisfy `ker f ≤ ker g`, then `g` factors
through the range of `f`, giving `f.range →+ C`. -/
noncomputable def rangeLift (f : A →+ B) (g : A →+ C) (h : f.ker ≤ g.ker) : f.range →+ C where
  toFun w := QuotientAddGroup.lift f.ker g h ((QuotientAddGroup.quotientKerEquivRange f).symm w)
  map_zero' := by simp
  map_add' w₁ w₂ := by simp

/-- The computation rule of `rangeLift` on the canonical image of `a`. -/
theorem rangeLift_apply (f : A →+ B) (g : A →+ C) (h : f.ker ≤ g.ker) (a : A) :
    rangeLift f g h (f.rangeRestrict a) = g a := by
  have hq : (QuotientAddGroup.quotientKerEquivRange f).symm (f.rangeRestrict a)
      = (QuotientAddGroup.mk a : A ⧸ f.ker) := by
    apply (QuotientAddGroup.quotientKerEquivRange f).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  show QuotientAddGroup.lift f.ker g h
    ((QuotientAddGroup.quotientKerEquivRange f).symm (f.rangeRestrict a)) = g a
  rw [hq, QuotientAddGroup.lift_mk]

end RangeLift

/-! ## The pairing, its additivity in the cohomology variable, and the `λ`-descent -/

section Pairing

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

section LevelGeneric

variable {L : Type} [Field L] [NumberField L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]

/-- **The level pairing is additive in the cohomology variable.**  For a fixed class
`x ∈ Ext^r_G(M, C_K)`, `h ↦ φ(x)(h)` is additive. -/
noncomputable def phiAtHomRight {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x : Abelian.Ext.{0} M (classesK k K) r) :
    extH (Rep.res (galRes k K L) M) s →+ extH (classesK k L) (s + r) where
  toFun h := phiAt (k := k) (K := K) (L := L) x h
  map_zero' := by
    show phiAt (k := k) (K := K) (L := L) x (0 : extH (Rep.res (galRes k K L) M) s) = 0
    simp only [phiAt, levelPair, Abelian.Ext.zero_comp]
  map_add' h₁ h₂ := by
    show phiAt (k := k) (K := K) (L := L) x (h₁ + h₂) = _
    simp only [phiAt, levelPair, Abelian.Ext.add_comp]

@[simp] theorem phiAtHomRight_apply {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x : Abelian.Ext.{0} M (classesK k K) r) (h : extH (Rep.res (galRes k K L) M) s) :
    phiAtHomRight (k := k) (K := K) (L := L) x h = phiAt (k := k) (K := K) (L := L) x h := rfl

/-- **The connecting map `δ_L`** of `S` at the level `L`: `h ↦ h ∪ S.extClass`, as a bundled
additive map `H¹(Gal(L/k),S.X₃) → H²(Gal(L/k),S.X₁)`. -/
noncomputable def deltaHom (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact) :
    extH (Rep.res (galRes k K L) S.X₃) 1 →+ extH (Rep.res (galRes k K L) S.X₁) 2 where
  toFun h := h.comp (extRes (galRes k K L) hS.extClass) (by norm_num)
  map_zero' := by
    show (0 : extH (Rep.res (galRes k K L) S.X₃) 1).comp
      (extRes (galRes k K L) hS.extClass) (by norm_num) = 0
    simp only [Abelian.Ext.zero_comp]
  map_add' h₁ h₂ := by
    show (h₁ + h₂).comp (extRes (galRes k K L) hS.extClass) (by norm_num) = _
    simp only [Abelian.Ext.add_comp]

@[simp] theorem deltaHom_apply (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K)))
    (hS : S.ShortExact) (h : extH (Rep.res (galRes k K L) S.X₃) 1) :
    deltaHom (k := k) (K := K) (L := L) S hS h
      = h.comp (extRes (galRes k K L) hS.extClass) (by norm_num) := rfl

/-- **The `λ`-descent.**  If the level-`L` functional `h ↦ φ(y)(h)` kills the kernel of the
connecting map `δ_L : H¹(Gal(L/k),S.X₃) → H²(Gal(L/k),S.X₁)`, it factors through `δ_L`, giving an
additive functional `λ_L` on the range `W_L = im δ_L`. -/
noncomputable def lambdaOnRange (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    (hy : ∀ h : extH (Rep.res (galRes k K L) S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L) S hS h = 0 → phiAt (k := k) (K := K) (L := L) y h = 0) :
    (deltaHom (k := k) (K := K) (L := L) S hS).range →+ extH (classesK k L) 2 :=
  rangeLift (deltaHom (k := k) (K := K) (L := L) S hS)
    (phiAtHomRight (k := k) (K := K) (L := L) y) (by
      intro h hh
      rw [AddMonoidHom.mem_ker] at hh ⊢
      exact hy h hh)

/-- The computation rule of `λ_L` on the `δ`-images. -/
theorem lambdaOnRange_apply (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    (hy : ∀ h : extH (Rep.res (galRes k K L) S.X₃) 1,
      deltaHom (k := k) (K := K) (L := L) S hS h = 0 → phiAt (k := k) (K := K) (L := L) y h = 0)
    (h : extH (Rep.res (galRes k K L) S.X₃) 1) :
    lambdaOnRange (k := k) (K := K) (L := L) S hS y hy
        ((deltaHom (k := k) (K := K) (L := L) S hS).rangeRestrict h)
      = phiAt (k := k) (K := K) (L := L) y h :=
  rangeLift_apply _ _ _ h

end LevelGeneric

end Pairing

end Work.SSGRoute
