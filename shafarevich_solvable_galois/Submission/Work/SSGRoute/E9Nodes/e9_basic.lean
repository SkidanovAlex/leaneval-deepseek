import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_level_trivial_two
import Submission.Work.SSGRoute.phi1_lambda_defs
import Submission.Work.SSGRoute.phi0_pTor_scalar
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E9b: elementary `Ext`-torsion facts used by the local-decomposition construction

* `e9_ptorsion_extH` — `Extⁿ_G(ℤ, A)` is killed by `p` when the coefficients `A` are;
* `e9_classesK_two_card` — `|H²(Gal(L/k), C_L)| = [L : k]` (Hasse's fundamental class);
* `e9_classesK_two_pTorsion_eq_zero` — its `p`-torsion vanishes when `p ∤ [L : k]`;
* `e9_bad_level_subsingleton` — `H¹(Gal(L/k), M) = 0` for `M` `p`-torsion and `p ∤ [L : k]`;
* `e9_phiAt_eq_zero_of_not_dvd` — `φ¹(x)` vanishes at levels of degree prime to `p`.
-/

namespace Work.SSGRoute.E9Nodes

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **`Extⁿ_G(ℤ, A)` is killed by `p` when the coefficients are.**  Bilinearity of
`Abelian.Ext.comp` in the second variable (`Work.SSGRoute.comp_nsmul_aux`,
`Work.SSGRoute.mk₀_nsmul_aux`) reduces `p • y` to `y.comp (mk₀ (p • 𝟙 A))`, and `p • 𝟙 A = 0`
because `p • a = 0` for every `a : A`. -/
theorem e9_ptorsion_extH {G : Type} [Group G] (p : ℕ) {A : Rep.{0} Coeff G} {n : ℕ}
    (hA : ∀ a : A, p • a = 0) (y : SSGRoute.PTExt.extH A n) : p • y = 0 := by
  have hone : (p : ℕ) • (𝟙 A) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 A)).toLinearMap v
        = p • ((Rep.Hom.hom (𝟙 A)).toLinearMap v) from rfl]
    simpa using hA v
  have hid : p • y = y.comp (Abelian.Ext.mk₀ (p • (𝟙 A))) (add_zero n) := by
    rw [mk₀_nsmul_aux p (𝟙 A)]
    rw [comp_nsmul_aux p y (Abelian.Ext.mk₀ (𝟙 A)) (add_zero n)]
    rw [Abelian.Ext.comp_mk₀_id]
  rw [hid, hone, Abelian.Ext.mk₀_zero]
  exact Abelian.Ext.comp_zero y _ 0 n (add_zero n)

/-- **The order of `H²(Gal(L/k), C_L)` is `[L : k]`** (Hasse's fundamental class). -/
theorem e9_classesK_two_card (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) = Module.finrank k L := by
  have hFC := NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement
    NK.CFTLib.fundamentalClassElement
  obtain ⟨e⟩ := Work.SSGRoute.extH_classesK_two_addEquiv k L
  rw [Nat.card_congr e.toEquiv, hFC.order, IsGalois.card_aut_eq_finrank]

/-- `Nat.card` is invariant under the multiplicative type synonym. -/
theorem natCard_multiplicative (A : Type*) : Nat.card (Multiplicative A) = Nat.card A :=
  Nat.card_congr
    { toFun := Multiplicative.toAdd, invFun := Multiplicative.ofAdd
      left_inv := fun x => by cases x; rfl
      right_inv := fun _ => rfl }

/-- **The `p`-torsion of `H²(Gal(L/k), C_L)` vanishes when `p ∤ [L : k]`**: the group has order
`[L : k]`, and the order of an element divides the order of the group. -/
theorem e9_classesK_two_pTorsion_eq_zero (p : ℕ) [Fact p.Prime] (k L : Type) [Field k]
    [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (hp : ¬ p ∣ Module.finrank k L) (y : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2)
    (hy : p • y = 0) : y = 0 := by
  by_contra hne
  have hord : addOrderOf y = p := addOrderOf_eq_prime hy hne
  have hdvd : p ∣ Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) := by
    have h := orderOf_dvd_natCard (Multiplicative.ofAdd y)
    rw [orderOf_ofAdd_eq_addOrderOf, hord, natCard_multiplicative] at h
    exact h
  rw [e9_classesK_two_card k L] at hdvd
  exact hp hdvd

/-- **`H¹(Gal(L/k), M) = 0` when `p ∤ [L : k]`** for a `p`-torsion module `M`: the group is killed
by `p` (`e9_ptorsion_extH`) and by `|Gal(L/k)| = [L : k]`
(`Work.SSGRoute.extH_natCard_smul_eq_zero`), which are coprime. -/
theorem e9_bad_level_subsingleton (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hp : ¬ p ∣ Module.finrank k L) :
    Subsingleton (SSGRoute.PTExt.extH (Rep.res (galRes k K L) M) 1) := by
  have hzero : ∀ y : SSGRoute.PTExt.extH (Rep.res (galRes k K L) M) 1, y = 0 := by
    intro y
    have hpy : p • y = 0 := e9_ptorsion_extH p (A := Rep.res (galRes k K L) M)
      (fun a => hM a) y
    have hGy : Nat.card (L ≃ₐ[k] L) • y = 0 :=
      extH_natCard_smul_eq_zero (Rep.res (galRes k K L) M) (n := 1) (by norm_num) y
    have hcop : Nat.Coprime p (Nat.card (L ≃ₐ[k] L)) := by
      rw [IsGalois.card_aut_eq_finrank k L]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp
    have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card (L ≃ₐ[k] L)))
        + (Nat.card (L ≃ₐ[k] L) : ℤ) * (Nat.gcdB p (Nat.card (L ≃ₐ[k] L))) = 1 := by
      have h := Nat.gcd_eq_gcd_ab p (Nat.card (L ≃ₐ[k] L))
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      linarith [h]
    have hpy' : (p : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hpy
    have hGy' : (Nat.card (L ≃ₐ[k] L) : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card (L ≃ₐ[k] L))]; exact hGy
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((p : ℤ) * (Nat.gcdA p (Nat.card (L ≃ₐ[k] L)))
            + (Nat.card (L ≃ₐ[k] L) : ℤ) * (Nat.gcdB p (Nat.card (L ≃ₐ[k] L)))) • y := by
            rw [hbez]
      _ = (Nat.gcdA p (Nat.card (L ≃ₐ[k] L))) • ((p : ℤ) • y)
            + (Nat.gcdB p (Nat.card (L ≃ₐ[k] L))) • ((Nat.card (L ≃ₐ[k] L) : ℤ) • y) := by
            rw [add_smul, mul_smul, mul_smul,
              smul_comm (p : ℤ) (Nat.gcdA p (Nat.card (L ≃ₐ[k] L))) y,
              smul_comm (Nat.card (L ≃ₐ[k] L) : ℤ) (Nat.gcdB p (Nat.card (L ≃ₐ[k] L))) y]
      _ = 0 := by rw [hpy', hGy']; simp
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- **`φ¹(x)` vanishes at levels of degree prime to `p`.**  Its value is `p`-torsion (bilinearity
of the pairing and `p • h = 0`), and `H²(Gal(L/k), C_L)` has no `p`-torsion when `p ∤ [L : k]`. -/
theorem e9_phiAt_eq_zero_of_not_dvd (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext.{0} M (classesK k K) 1) (hp : ¬ p ∣ Module.finrank k L)
    (h : SSGRoute.PTExt.extH (Rep.res (galRes k K L) M) 1) :
    SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) x h = 0 := by
  have hpt : p • (SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) x h) = 0 := by
    have h2 := (Work.SSGRoute.phiAtHomRight (k := k) (K := K) (L := L) x).map_nsmul p h
    show p • (Work.SSGRoute.phiAtHomRight (k := k) (K := K) (L := L) x) h = 0
    rw [← h2, e9_ptorsion_extH p (A := Rep.res (galRes k K L) M) (fun a => hM a) h, map_zero]
  exact e9_classesK_two_pTorsion_eq_zero p k L hp _ hpt

end Work.SSGRoute.E9Nodes
