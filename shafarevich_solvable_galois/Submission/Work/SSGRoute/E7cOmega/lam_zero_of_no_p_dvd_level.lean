import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
import Submission.Work.SSGRoute.phi1_level_trivial_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `lam` vanishes at levels whose decomposition group has order prime to `p`

`lam L : H¹(Gal(L/k), M) → H²(Gal(L/k), C_L)` is locally determined at a place `w' | w` above `w`:
it kills the kernel of the restriction to the decomposition group `D = Stab(w')` of `w'`
(`hloc`).  Consequently `lam L h` is computed from `res_D h ∈ H¹(D, M)`.

But `M` has exponent `p` (`hM`), so every positive-degree `Ext`-cohomology group with
coefficients `M` is killed by `p`; and it is killed by `|D|` by the restriction–corestriction
argument (`Work.SSGRoute.extH_natCard_smul_eq_zero`).  If `p ∤ |D|` (`hno`) these two
annihilators are coprime, so `H¹(D, M) = 0` by Bézout, hence `res_D h = 0` for every `h`, and
`lam L h = 0`.
-/

namespace Work.SSGRoute.E7cOmega

open SSGRoute.PTExt CategoryTheory

noncomputable section

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Positive-degree `Ext`-cohomology with coefficients of exponent `p` is killed by `p`.**

`p • y = y ∘ mk₀ (p • 𝟙 A)` (`Work.SSGRoute.mk₀_nsmul_aux`,
`Work.SSGRoute.comp_nsmul_aux`) and `p • 𝟙 A = 0` because `A` has exponent `p`.  This is the
general-coefficient form of `Work.SSGRoute.extH_trivial_zmodp_smul_eq_zero`. -/
theorem extH_nsmul_eq_zero_of_pTorsion {G : Type} [Group G] {p : ℕ} (A : Rep Coeff G)
    (hA : ∀ a : A, p • a = 0) {n : ℕ} (y : extH A n) : p • y = 0 := by
  have hone : (p : ℕ) • (𝟙 A) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 A)).toLinearMap v
        = p • ((Rep.Hom.hom (𝟙 A)).toLinearMap v) from rfl]
    exact hA ((Rep.Hom.hom (𝟙 A)).toLinearMap v)
  have hid : p • y = y.comp (Abelian.Ext.mk₀ (p • (𝟙 A))) (add_zero n) := by
    rw [Work.SSGRoute.mk₀_nsmul_aux p (𝟙 A)]
    rw [Work.SSGRoute.comp_nsmul_aux p y (Abelian.Ext.mk₀ (𝟙 A)) (add_zero n)]
    rw [Abelian.Ext.comp_mk₀_id]
  rw [hid, hone, Abelian.Ext.mk₀_zero]
  exact Abelian.Ext.comp_zero y _ 0 n (add_zero n)

/-- **Bézout.**  An element of an abelian group killed by `p` and by `n`, with `n` coprime to
`p`, is zero. -/
theorem eq_zero_of_pTorsion_of_coprime {A : Type*} [AddCommGroup A] {p : ℕ} {x : A}
    (hpx : p • x = 0) {n : ℕ} (hn : n.Coprime p) (hnx : n • x = 0) : x = 0 := by
  have hbez := Nat.gcd_eq_gcd_ab n p
  have hgcd : (Nat.gcd n p : ℤ) = 1 := by rw [hn.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA n p : ℤ) * (n : ℤ) + (Nat.gcdB n p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA n p) (n : ℤ), mul_comm (Nat.gcdB n p) (p : ℤ)]
    exact hbez.symm
  have hx : x = (Nat.gcdA n p * (n : ℤ) + Nat.gcdB n p * (p : ℤ)) • x := by
    rw [hbez', one_smul]
  rw [hx, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hnx, hpx, smul_zero,
    smul_zero, add_zero]

theorem lam_zero_of_no_p_dvd_level {p : ℕ} [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1 →+
        SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k K) 2)
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1,
          SSGRoute.PTExt.extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0)
    (hno : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (w' : NK.GlobalCFT.Place L), NK.GlobalCFT.Place.LiesOver w' w →
        ¬ p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w')) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1), lam L h = 0 := by
  intro L _ _ _ h
  obtain ⟨w', hw'lies, hw'zero⟩ := hloc L
  refine hw'zero h ?_
  set D : Subgroup (↥L ≃ₐ[k] ↥L) := MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w' with hD
  haveI hfinD : Finite D := inferInstance
  haveI hftD : Fintype D := Fintype.ofFinite D
  -- `p` kills the restricted class because the coefficients have exponent `p`
  have hpy : p • SSGRoute.PTExt.extHRestrict D h = 0 :=
    extH_nsmul_eq_zero_of_pTorsion (p := p)
      (Rep.res D.subtype (Rep.res (SSGRoute.PTExt.galRes k K L) M))
      (fun a => hM a) (SSGRoute.PTExt.extHRestrict D h)
  -- `|D|` kills it by restriction–corestriction
  have hcard : Nat.card D • SSGRoute.PTExt.extHRestrict D h = 0 :=
    Work.SSGRoute.extH_natCard_smul_eq_zero
      (Rep.res D.subtype (Rep.res (SSGRoute.PTExt.galRes k K L) M))
      (n := 1) (by norm_num) (SSGRoute.PTExt.extHRestrict D h)
  -- `p` and `|D|` are coprime by `hno`
  have hcop : Nat.Coprime p (Nat.card D) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (hno L w' hw'lies)
  exact eq_zero_of_pTorsion_of_coprime (x := SSGRoute.PTExt.extHRestrict D h) hpy hcop.symm hcard

end

end Work.SSGRoute.E7cOmega
