import Mathlib
import Submission.Work.Hering.AppVII.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary definitions for `collapse_solvable`

The configuration of Appendix VII is fixed by two families of subgroups of the acting group `A`:

* `⁅P,Q⁆`, whose fixed points in `K` form `appVIIF1 A P Q K`;
* the conjugates `P^x`, `x ∈ Q`, whose fixed points form `appVIIFx A P Q K x`.

Both are instances of the following uniform notion: for a subgroup `H ≤ A`, let `appVIIFC A H K`
be the subgroup of elements of `K` fixed by every element of `H`.  With this definition

* `appVIIF1 A P Q K = appVIIFC A ⁅P,Q⁆ K` and
* `appVIIFx A P Q K x = appVIIFC A (P^x) K`

hold by `rfl`, which makes the reduction `K ↦ K/N` uniform over the two families: it suffices to
know that `appVIIFC A H (–)` commutes with taking the quotient by an `A`-invariant normal
solvable subgroup `N ⊴ K`.

This file also contains the *easy* direction of that commutation (fixed points of `H` in `K`
surject onto fixed points of `H` in `K ⧸ N`); the converse direction is Gaschütz's lemma
`C_{K/N}(H) = C_K(H)·N/N` with the solvable coefficient `N`
(`Work.Coprime.cocycle_is_coboundary_aux` / `Work.Hering.AppVII.fixedPoints_quotient_of_solvable_coeff`).
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.Hering.AppVII

universe u v

/-- The subgroup of elements of `K` fixed by every element of the subgroup `H ≤ A` of the acting
group. -/
def appVIIFC (A : Type u) [Group A] (H : Subgroup A) (K : Type v) [Group K]
    [MulDistribMulAction A K] : Subgroup K where
  carrier := {k : K | ∀ y ∈ H, y • k = k}
  mul_mem' := by
    intro x y hx hy z hz
    rw [smul_mul', hx z hz, hy z hz]
  one_mem' := by intro z _; exact smul_one z
  inv_mem' := by intro x hx z hz; rw [smul_inv', hx z hz]

@[simp]
theorem mem_appVIIFC {A : Type u} [Group A] {H : Subgroup A} {K : Type v} [Group K]
    [MulDistribMulAction A K] {k : K} : k ∈ appVIIFC A H K ↔ ∀ y ∈ H, y • k = k :=
  Iff.rfl

theorem appVIIF1_eq_appVIIFC (A : Type u) [Group A] (P Q : Subgroup A) (K : Type v) [Group K]
    [MulDistribMulAction A K] : appVIIF1 A P Q K = appVIIFC A ⁅P, Q⁆ K := rfl

theorem appVIIFx_eq_appVIIFC (A : Type u) [Group A] (P Q : Subgroup A) (K : Type v) [Group K]
    [MulDistribMulAction A K] (x : ↥Q) :
    appVIIFx A P Q K x = appVIIFC A (P.map (MulAut.conj (x : A)).toMonoidHom) K := rfl

/-- `FT.IsInvariant` restricts to a subgroup of the acting group. -/
theorem isInvariant_restrict_act {A : Type u} {K : Type v} [Group A] [Group K]
    [MulDistribMulAction A K] (N : Subgroup K) [FT.IsInvariant A N] (H : Subgroup A) :
    FT.IsInvariant ↥H N :=
  ⟨fun h => (inferInstance : FT.IsInvariant A N).smul_eq_self (h : A)⟩

/-- The easy direction of `C_{K/N}(H) = C_K(H)·N/N`: the image of the fixed points of `H` in `K`
consists of fixed points of `H` in `K ⧸ N`. -/
theorem appVIIFC_map_le {A : Type u} [Group A] {K : Type v} [Group K]
    [MulDistribMulAction A K] (H : Subgroup A) (N : Subgroup K) [N.Normal]
    [FT.IsInvariant A N] :
    (appVIIFC A H K).map (QuotientGroup.mk' N) ≤ appVIIFC A H (K ⧸ N) := by
  intro x hx y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  rw [QuotientGroup.mk'_apply, FT.quotient_smul_mk, hk y hy]

/-! ## Transport of an action along group isomorphisms

The reduction of Appendix VII has to move a configuration `(A, K)` to a *model* of it living in
other universes, so that the induction hypothesis — whose universes are fixed by the statement of
`AppVIIStmt` — can be applied to that model, and the conclusion transported back.  The action has
to be transported alongside, which is what `transportAct` does. -/

/-- The `SMul` underlying `transportAct`. -/
def transportSMul {A A' K K' : Type*} [Group A] [Group A'] [Group K] [Group K']
    [MulDistribMulAction A K] (eA : A ≃* A') (eK : K ≃* K') : SMul A' K' :=
  ⟨fun a' k' => eK (eA.symm a' • eK.symm k')⟩

/-- The action of `A'` on `K'` transported from an action of `A` on `K` along group isomorphisms
`eA : A ≃* A'`, `eK : K ≃* K'`: `a' • k' = eK (eA.symm a' • eK.symm k')`. -/
def transportAct {A A' K K' : Type*} [Group A] [Group A'] [Group K] [Group K']
    [MulDistribMulAction A K] (eA : A ≃* A') (eK : K ≃* K') : MulDistribMulAction A' K' :=
  letI := transportSMul eA eK
  { one_smul := by
      intro k'
      change eK (eA.symm (1 : A') • eK.symm k') = k'
      simp
    mul_smul := by
      intro a' b' k'
      change eK (eA.symm (a' * b') • eK.symm k')
        = eK (eA.symm a' • eK.symm (eK (eA.symm b' • eK.symm k')))
      simp [mul_smul]
    smul_one := by
      intro a'
      change eK (eA.symm a' • eK.symm (1 : K')) = 1
      simp
    smul_mul := by
      intro a' x y
      change eK (eA.symm a' • eK.symm (x * y))
        = eK (eA.symm a' • eK.symm x) * eK (eA.symm a' • eK.symm y)
      simp [smul_mul'] }

/-- The compatibility of the transported action with the isomorphisms. -/
theorem transportAct_smul {A A' K K' : Type*} [Group A] [Group A'] [Group K] [Group K']
    [MulDistribMulAction A K] (eA : A ≃* A') (eK : K ≃* K') (a : A) (k : K) :
    (letI := transportAct eA eK; eK (a • k) = eA a • eK k) := by
  change eK (a • k) = eK (eA.symm (eA a) • eK.symm (eK k))
  simp

end Work.Hering.AppVII
