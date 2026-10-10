import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.extCor_yoneda_comp
import Submission.Work.SSGRoute.extRes_injective_of_index
import Submission.Work.SSGRoute.phi1_sylow_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E6: the Sylow descent for `φ¹` — infrastructure

This file develops the pieces of the Sylow descent `E6`/`E6Ω` of the Poitou–Tate `Ext` core
(`DESIGN_EXT.md`, `DESIGN_FIX.md`): the change of base field `k → k' = K^P`, the compatibility of
the level pairing with restriction of the Galois group, the transfer identities
`cor ∘ res = [G : S]`, `res ∘ cor = [G : S]` on derived `Ext`, and the uniqueness of the canonical
inclusion `C_K → C_L`.

Everything lives in the namespace `Work.SSGRoute.SylowDesc` so that it can be imported next to
`Work.SSGRoute.phi1_mono_sylow_in` without any name clash.

## What the transfer step needs (see `PHI1_SYLOW_TRANSFER_STATUS.md`)

* The **projection formula** `cor (b ∘ extRes x) = (cor b) ∘ x` — `Work.SSGRoute.extCor_yoneda_comp`
  (PROVED, in `Submission/Work/SSGRoute/extCor_yoneda_comp.lean`, imported here; the general form is
  `Work.SSGRoute.extCor_comp_extRes`) — is the formal half: it gives `cor (phiAt_{k'}(x'')(h)) = phiAt_k(x)(cor h)`,
  hence `cor v = 0` for the level-`L` value `v` of the descent, using the hypothesis over `k`.
* The step `cor v = 0 ⟹ v = 0` (`v ∈ H²(Gal(L/k'), C_L)`, `p`-torsion, `p ∤ [k' : k]`) is **not**
  formal: the "dual" identity `extRes ∘ extCor = [G : S] • id` is FALSE in general (double-coset
  formula; counterexample in the status note).  What is needed is the class-formation input
  `res (cor v) = [k' : k] • v` on `H²(·, C)`-values, equivalently the injectivity of `cor` on the
  `p`-primary part — i.e. the generator-free form of `inv ∘ cor = inv`.  It is not on disk.
* `p • h = 0` for `h ∈ extH M n` with `M` `p`-torsion is already available as
  `Work.SSGRoute.ext_nsmul_p_torsion` in `Submission/Work/SSGRoute/local_duality_ext.lean` (so the
  "the value is `p`-torsion" step needs no new lemma).
-/

set_option maxHeartbeats 800000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

namespace SylowDesc

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-! ## 1. The change of base field for the coefficient modules -/

section BaseChange

variable (k k' K : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Field K]
  [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k'] [IsScalarTower k k' K]

/-- The action of `Gal(K/k')` on `C_K`, viewed through `Gal(K/k') →* Gal(K/k)`, is the canonical
action of `Gal(K/k')` on `C_K`.  (Restatement of `classGroupRep_ρ_restrictScalars`.) -/
theorem classesK_rho_baseChange (σ : K ≃ₐ[k'] K) (q : NK.GlobalCFT.IdeleClassGroup K) :
    (NK.HassePrinciple.classGroupRep k K).ρ
        (AlgEquiv.restrictScalarsHom k σ) (Additive.ofMul q)
      = (NK.HassePrinciple.classGroupRep k' K).ρ σ (Additive.ofMul q) :=
  Work.SSGRoute.classGroupRep_ρ_restrictScalars.{0,0} k k' K σ q

/-- **Change of base field for `C_K`.**  For `k ⊆ k' ⊆ K` the restriction of the `Gal(K/k)`-module
`C_K` to `Gal(K/k')` is the `Gal(K/k')`-module `C_K` of `K/k'`. -/
noncomputable def classesK_baseChangeIso :
    Rep.res (AlgEquiv.restrictScalarsHom k : (K ≃ₐ[k'] K) →* (K ≃ₐ[k] K)) (classesK k K)
      ≅ classesK k' K := by
  have h : (NK.HassePrinciple.classGroupRep k K).ρ.comp
        (AlgEquiv.restrictScalarsHom k : (K ≃ₐ[k'] K) →* (K ≃ₐ[k] K)) =
      (NK.HassePrinciple.classGroupRep k' K).ρ := by
    ext σ x
    exact Work.SSGRoute.classGroupRep_ρ_restrictScalars.{0,0} k k' K σ x
  rw [show Rep.res (AlgEquiv.restrictScalarsHom k : (K ≃ₐ[k'] K) →* (K ≃ₐ[k] K)) (classesK k K)
      = Rep.of ((NK.HassePrinciple.classGroupRep k K).ρ.comp
          (AlgEquiv.restrictScalarsHom k : (K ≃ₐ[k'] K) →* (K ≃ₐ[k] K))) from rfl, h]
  exact Iso.refl _

end BaseChange

/-! ## 2. Composition of restriction on `Ext` -/

section Comp

variable {G G' G'' : Type} [Group G] [Group G'] [Group G'']

/-- Restriction along a composite of group homomorphisms is the composite of the restrictions. -/
theorem extRes_comp_aux (ψ : G' →* G) (φ : G'' →* G') {M A : Rep Coeff G} {n : ℕ}
    (x : Abelian.Ext M A n) :
    extRes (ψ.comp φ) x = extRes φ (extRes ψ x) := by
  rw [extRes, extRes, extRes]
  exact (ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor ψ) (Rep.resFunctor φ)
    n M A x).symm

end Comp


/-! ## 3. Restriction to a subgroup of index prime to `p` is injective on `p`-torsion -/

section PTorsion

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G)
  [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]

/-- **Restriction is injective on `p`-torsion when the index is prime to `p`.**  If
`p • x = 0` and `extRes_S x = 0` with `p ∤ [G : S]`, then `x = 0`.  (The coefficient module is
arbitrary; only the class is assumed `p`-torsion, which is what the `H²(C_L)`-application needs.) -/
theorem extRes_eq_zero_of_pTorsion (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ S.index)
    {M A : Rep Coeff G} {n : ℕ} (x : Abelian.Ext M A n) (hx : p • x = 0)
    (h0 : extRes S.subtype x = 0) : x = 0 := by
  obtain ⟨cor, hcor⟩ := ext_corestriction (G := G) (S := S)
  have h1 : S.index • x = 0 := by
    rw [← hcor M A n x, h0]
    simp
  have hcop : Nat.Coprime p S.index := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
  have hbez : (p : ℤ) * (Nat.gcdA p S.index) + (S.index : ℤ) * (Nat.gcdB p S.index) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p S.index
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hpx : (p : ℤ) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hx
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

end PTorsion

end SylowDesc

end Work.SSGRoute
