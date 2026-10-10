import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The E7b base-case algebra `Ext¹_G(𝔽_p, X) ≅ H⁰(G,X) / p·H⁰(G,X)`

This file proves the *corrected* form of the statement requested as
`Work.SSGRoute.ext_zmod_prime_iso`.

The statement that was requested,

```
Nonempty (Ext¹_G(𝔽_p, X) ≃+ (extH X 0 ⧸ p • (⊤ : Submodule Coeff (extH X 0)))),
```

is **false**: the `p • ⊤` there is the *additive* `nsmul` of `Submodule` (whose addition is `⊔`),
so `p • ⊤ = ⊤` for `p ≠ 0` (this is `Submodule.add_eq_sup`), the right-hand side is the trivial
group `extH X 0 ⧸ ⊤`, and the statement would force `Ext¹_G(𝔽_p, X)` to be trivial for every `X`
with `H¹(G,X) = 0` — false, e.g. `G = 1`, `X = ℤ`: `Ext¹_ℤ(ℤ/p, ℤ) ≅ ℤ/p ≠ 0`.

The intended content is the quotient by the image of *multiplication by `p`* inside
`H⁰(G,X) = extH X 0`.  The map `(mk₀ (unitMulByP G p)).precomp X (zero_add 0)` below is exactly
that multiplication (`Coeff`-scalar, see `extFp_comp_eq_nsmul`), so the correct statement is

```
Ext¹_G(𝔽_p, X) ≅ extH X 0 ⧸ (range of multiplication by p on extH X 0).
```

The proof is the long exact sequence of the coefficient sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` in `Rep Coeff G` (which already exists on disk as
`SSGRoute.Phi1.coeffSES`, with `coeffSES_shortExact`, and is the same sequence used by
`Work.SSGRoute.Phi1.exists_pushClass`) in the first variable, together with
`H¹(G,X) = Ext¹_G(ℤ,X) = 0`.
-/

open CategoryTheory

namespace Work.SSGRoute

/-- The coefficient ring `ULift ℤ` of the `Ext` core (`SSGRoute.PTExt.Coeff`). -/
abbrev ExtFpCoeff : Type := SSGRoute.PTExt.Coeff

/-- **First isomorphism theorem for an additive map whose kernel is the range of an additive map.** -/
theorem extFp_quot_of_ker_eq_range {A C : Type*} [AddCommGroup A] [AddCommGroup C]
    (δ : A →+ C) (mp : A →+ A) (hker : δ.ker = mp.range)
    (hsurj : Function.Surjective δ) : Nonempty (C ≃+ (A ⧸ mp.range)) := by
  have hle : mp.range ≤ δ.ker := by rw [hker]
  have hf_mk : ∀ a : A, (QuotientAddGroup.lift mp.range δ hle)
      (QuotientAddGroup.mk a) = δ a := fun a => QuotientAddGroup.lift_mk _ _ a
  have hf_surj : Function.Surjective (QuotientAddGroup.lift mp.range δ hle) := by
    intro c
    obtain ⟨a, ha⟩ := hsurj c
    exact ⟨QuotientAddGroup.mk a, by rw [hf_mk a]; exact ha⟩
  have hf_inj : Function.Injective (QuotientAddGroup.lift mp.range δ hle) := by
    intro x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H b =>
        rw [QuotientAddGroup.eq_iff_sub_mem]
        have h2 : δ (a - b) = 0 := by
          rw [map_sub, ← hf_mk a, ← hf_mk b, hxy, sub_self]
        have h3 : a - b ∈ δ.ker := by rwa [AddMonoidHom.mem_ker]
        rwa [hker] at h3
  exact ⟨(AddEquiv.ofBijective (QuotientAddGroup.lift mp.range δ hle) ⟨hf_inj, hf_surj⟩).symm⟩

/-- The coefficient sequence's first map is multiplication by `p` on the trivial representation. -/
theorem extFp_unitMulByP_eq_smul (p : ℕ) (G : Type) [Group G] :
    SSGRoute.Phi1.unitMulByP G p = (p : ExtFpCoeff) • 𝟙 (SSGRoute.PTExt.unitRep G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.toLinearMap_apply,
    SSGRoute.Phi1.unitMulByP_apply, Rep.smul_hom, Rep.hom_id,
    Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.id_apply,
    smul_eq_mul]

/-- **The connecting map of the coefficient sequence is multiplication by `p` on `H⁰(G,X)`.** -/
theorem extFp_comp_eq_nsmul (p : ℕ) (G : Type) [Group G] (X : Rep.{0} ExtFpCoeff G)
    (y : SSGRoute.PTExt.extH X 0) :
    (Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP G p)).precomp X (zero_add 0) y
      = (p : ℕ) • y := by
  show (Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP G p)).comp y (zero_add 0) = (p : ℕ) • y
  rw [extFp_unitMulByP_eq_smul p G, Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp,
    Abelian.Ext.mk₀_id_comp]
  -- the `Coeff`-scalar on `Ext` is the `Ext`-module scalar; bridge it to the `ℤ`-action
  rw [show (p : ExtFpCoeff) = ((p : ℤ) : ExtFpCoeff) from rfl]
  rw [@Int.cast_smul_eq_zsmul ExtFpCoeff (SSGRoute.PTExt.extH X 0) _ _ Abelian.Ext.instModule
    (p : ℤ) y]
  rw [natCast_zsmul]

/-- The range of the multiplication-by-`p` map is the set of `p`-th multiples in `H⁰(G,X)`. -/
theorem extFp_mem_range_iff (p : ℕ) (G : Type) [Group G] (X : Rep.{0} ExtFpCoeff G)
    (x : SSGRoute.PTExt.extH X 0) :
    x ∈ ((Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP G p)).precomp X (zero_add 0)).range ↔
      ∃ y, (p : ℕ) • y = x := by
  rw [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy, extFp_comp_eq_nsmul p G X y]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [extFp_comp_eq_nsmul p G X y]; exact hy⟩

/-- **The corrected form of the E7b base case**: `Ext¹_G(𝔽_p, X) ≅ H⁰(G,X)/p·H⁰(G,X)` whenever
`H¹(G,X) = 0`.  The right-hand side is the quotient of `H⁰(G,X) = extH X 0` by the image of
multiplication by `p` (the map `(mk₀ (unitMulByP G p)).precomp X (zero_add 0)`, which acts by
`y ↦ p • y`, see `extFp_comp_eq_nsmul`). -/
theorem ext_zmod_prime_iso_corrected (p : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (X : Rep.{0} ExtFpCoeff G) (hX : Subsingleton (SSGRoute.PTExt.extH X 1)) :
    Nonempty (CategoryTheory.Abelian.Ext (Rep.trivial ExtFpCoeff G (ZMod p)) X 1 ≃+
      (SSGRoute.PTExt.extH X 0 ⧸
        ((Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP G p)).precomp X (zero_add 0)).range)) := by
  have hS : (SSGRoute.Phi1.coeffSES G p).ShortExact := SSGRoute.Phi1.coeffSES_shortExact G p
  have hsurj : Function.Surjective (hS.extClass.precomp X (by norm_num : 1 + 0 = 1)) := by
    intro y
    have h0 : ((Abelian.Ext.mk₀ (SSGRoute.Phi1.coeffSES G p).g).comp y (zero_add 1)) = 0 :=
      @Subsingleton.elim _ hX _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS X y h0 (n₀ := 0)
      (by norm_num)
    exact ⟨x, hx⟩
  have hkerS : (hS.extClass.precomp X (by norm_num : 1 + 0 = 1)).ker =
      ((Abelian.Ext.mk₀ (SSGRoute.Phi1.coeffSES G p).f).precomp X (zero_add 0)).range := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hx
      have hx' : hS.extClass.comp x (by norm_num : 1 + 0 = 1) = 0 := hx
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS X x (by norm_num) hx'
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS y (n' := 1) (h := by norm_num)
  have hker : (hS.extClass.precomp X (by norm_num : 1 + 0 = 1)).ker =
      ((Abelian.Ext.mk₀ (SSGRoute.Phi1.unitMulByP G p)).precomp X (zero_add 0)).range := hkerS
  exact extFp_quot_of_ker_eq_range _ _ hker hsurj

end Work.SSGRoute
