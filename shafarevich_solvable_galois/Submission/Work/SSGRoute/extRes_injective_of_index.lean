import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.Star
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.ext_corestriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction to a subgroup of index prime to `p` is injective on `p`-torsion `Ext¹`

`cor ∘ extRes = [G : S]` (from `Work.SSGRoute.ext_corestriction`), and `p • 𝟙 M = 0` because `M` is
`p`-torsion, so `p` and the index (prime to `p`) annihilate `x`; Bézout finishes.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

theorem extRes_injective_of_index (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (S : Subgroup G) [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    (hp : ¬ p ∣ S.index) (M : Rep Coeff G) [Finite M] (hM : ∀ m : M, p • m = 0)
    (A : Rep Coeff G) :
    Function.Injective (fun x : Abelian.Ext M A 1 => extRes S.subtype x) := by
  obtain ⟨cor, hcor⟩ := ext_corestriction (G := G) (S := S)
  let f : Abelian.Ext M A 1 →+ Abelian.Ext (Rep.res S.subtype M) (Rep.res S.subtype A) 1 :=
    (Rep.resFunctor S.subtype).mapExtAddHom M A 1
  change Function.Injective f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : extRes S.subtype x = 0 := hx
  have h1 : S.index • x = 0 := by
    rw [← hcor M A 1 x, hx']
    simp
  have hM0 : (p • (𝟙 M : M ⟶ M)) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro m
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 M)).toLinearMap m
        = p • ((Rep.Hom.hom (𝟙 M)).toLinearMap m) from rfl]
    simpa using hM m
  have h2 : p • x = 0 := by
    have hid : p • x = (Abelian.Ext.mk₀ (p • (𝟙 M : M ⟶ M))).comp x (zero_add 1) := by
      rw [mk₀_nsmul_aux p (𝟙 M : M ⟶ M),
        nsmul_comp_aux p (Abelian.Ext.mk₀ (𝟙 M : M ⟶ M)) x (zero_add 1),
        Abelian.Ext.mk₀_id_comp]
    rw [hid, hM0, Abelian.Ext.mk₀_zero]
    exact Abelian.Ext.zero_comp M _ _ _ rfl
  have hcop : Nat.Coprime p S.index := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
  have hbez : (p : ℤ) * (Nat.gcdA p S.index) + (S.index : ℤ) * (Nat.gcdB p S.index) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p S.index
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hpx : (p : ℤ) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h2
  have hidx : (S.index : ℤ) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h1
  calc x = (1 : ℤ) • x := (one_smul _ _).symm
    _ = ((p : ℤ) * (Nat.gcdA p S.index) + (S.index : ℤ) * (Nat.gcdB p S.index)) • x := by
          rw [hbez]
    _ = (Nat.gcdA p S.index) • ((p : ℤ) • x) +
          (Nat.gcdB p S.index) • ((S.index : ℤ) • x) := by
          rw [add_smul, mul_smul, mul_smul,
            smul_comm (p : ℤ) (Nat.gcdA p S.index) x,
            smul_comm (S.index : ℤ) (Nat.gcdB p S.index) x]
    _ = 0 := by rw [hpx, hidx]; simp

end Work.SSGRoute
