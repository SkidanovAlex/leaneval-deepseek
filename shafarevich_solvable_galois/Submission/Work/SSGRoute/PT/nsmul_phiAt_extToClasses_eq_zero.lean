import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p • φ(extToClasses z)(h) = 0` for `p`-torsion coefficients

The pairing `phiAt x h = h ∪ infl(x)` is `ℕ`-bilinear (`Abelian.Ext` is `ℕ`-linear in both slots),
and the cohomology class `h ∈ H¹(Gal(L/k), res M)` is killed by `p` whenever the coefficients `M`
have exponent `p` (`Extⁿ` with `p`-torsion coefficients is `p`-torsion in every positive degree).
Hence `p • φ(x)(h) = (p • h) ∪ infl(x) = 0`.

The two ingredients are proved here from scratch (they are the generic `Ext`-calculus lemmas of
`Submission.Work.SSGRoute.ext_corestriction` / `Submission.Work.SSGRoute.e6_util`, restated locally
so that this module depends only on `PTDefs` and `PTDefsOmega`).
-/

open CategoryTheory

universe w v u1 u2 u3

namespace Work.SSGRoute.PT

open SSGRoute.PTExt

/-- Bilinearity of `Abelian.Ext.comp` in the *first* variable, for `ℕ`-multiples. -/
theorem nsmul_comp_aux_pt {C : Type u1} [Category.{w, u1} C] [Abelian C] [HasExt C]
    {X Y Z : C} {a b c : ℕ} (n : ℕ) (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b)
    (h : a + b = c) : (n • α).comp β h = n • (α.comp β h) := by
  have h1 : (n • α).comp β h = (Abelian.Ext.bilinearComp X Y Z a b c h (n • α)) β := rfl
  rw [h1, map_nsmul]
  rfl

/-- A representation morphism which is pointwise zero is zero. -/
theorem nsmul_id_eq_zero_pt {k : Type u1} [Semiring k] {G : Type v} [Monoid G]
    {X : Rep k G} (p : ℕ) (hX : ∀ x : X, p • x = 0) :
    (p : ℕ) • (𝟙 X) = 0 := by
  letI := X.hV2
  refine Rep.hom_ext ?_
  rw [Rep.nsmul_hom, Rep.zero_hom]
  refine Representation.IntertwiningMap.ext ?_
  ext x
  rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.coe_nsmul,
    Pi.smul_apply, Representation.IntertwiningMap.toLinearMap_apply]
  show p • ((𝟙 X : X ⟶ X) x) = 0
  rw [Rep.id_apply]
  exact hX x

/-- **`Ext`-cohomology with `p`-torsion coefficients is killed by `p`** (second-variable form):
`p • y = y ∘ mk₀ (p • 𝟙 A)` and `p • 𝟙 A = 0` because `A` has exponent `p`. -/
theorem extH_nsmul_eq_zero_of_ptorsion {G : Type} [Group G] {p : ℕ} (A : Rep.{0} Coeff G)
    (hA : ∀ a : A, p • a = 0) {n : ℕ} (h : extH A n) : p • h = 0 := by
  have hzero := nsmul_id_eq_zero_pt (G := G) (X := A) p hA
  have key : ∀ k : ℕ, h.comp (Abelian.Ext.mk₀ (k • (𝟙 A))) (add_zero n) = k • h := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, zero_nsmul]
    | succ k ih =>
        rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih, Abelian.Ext.comp_mk₀_id,
          succ_nsmul]
  rw [← key p, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

/-- A Yoneda product whose first factor is killed by `p` is killed by `p`. -/
theorem nsmul_comp_eq_zero_of_nsmul_left {C : Type u1} [Category.{w, u1} C] [Abelian C]
    [HasExt C] {X Y Z : C} {a b c : ℕ} (p : ℕ) (h : a + b = c)
    (α : Abelian.Ext X Y a) (β : Abelian.Ext Y Z b) (hα : p • α = 0) :
    p • (α.comp β h) = 0 := by
  rw [← nsmul_comp_aux_pt p α β h, hα]
  exact Abelian.Ext.zero_comp _ _ _ _ _

theorem nsmul_phiAt_extToClasses_eq_zero
    (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (hM : ∀ m : M, p • m = 0)
    (z : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.idelesK k K) 1)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1) :
    p • SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L)
      (SSGRoute.PTExt.extToClasses z) h = 0 := by
  classical
  have hph : p • h = 0 :=
    extH_nsmul_eq_zero_of_ptorsion (Rep.res (SSGRoute.PTExt.galRes k K L) M) (fun a => hM a) h
  rw [SSGRoute.PTExt.phiAt, SSGRoute.PTExt.levelPair]
  exact nsmul_comp_eq_zero_of_nsmul_left p rfl h _ hph

end Work.SSGRoute.PT
