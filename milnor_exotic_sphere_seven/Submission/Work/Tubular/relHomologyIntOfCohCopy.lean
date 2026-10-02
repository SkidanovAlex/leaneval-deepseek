import Mathlib
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.relComplexIsoDual
import Submission.Work.Cohomology.uctDual
import Submission.Work.ThomBordism.relHomAux
import Submission.Work.ThomBordism.relKronH_surjective
import Submission.Work.Tubular.RelAPI
import Submission.Work.ThomBordism.relKronH_kernel_eq_torsion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Tubular

open Work.Cohomology

noncomputable section

variable {X : TopCat} {A : Set X} {n : ℕ}

/-! ## Instance transports (all `ℤ`-module structures on a fixed abelian group agree) -/

theorem isTorsionFree_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.IsTorsionFree ℤ M _ _ i₁) : @Module.IsTorsionFree ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.IsTorsionFree ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

theorem free_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Free ℤ M _ _ i₁) : @Module.Free ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.Free ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

theorem finite_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.Finite ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

/-! ## Step 1: the vanishing hypothesis, transported to the dual complex -/

theorem isZero_dual_of_isZero_rel (hC0 : IsZero ((relComplex ℤ X A).homology (n + 1))) :
    IsZero ((dualComplex ℤ (relChains X A)).homology (n + 1)) := by
  obtain ⟨e⟩ := relComplexIsoDual X A
  exact IsZero.of_iso hC0 (HomologicalComplex.homologyMapIso e (n + 1)).symm

/-! ## Step 2: purity of the boundaries in the cycles -/

/-- The boundaries inside the cycles, mapped to the boundaries inside the chains. -/
def uctHToB : ↥(uctH (relChains X A) n) →ₗ[ℤ] ↥(uctB (relChains X A) n) where
  toFun b := ⟨(b : ↥((relChains X A).X n)), (mem_uctH _ n b.1).mp b.2⟩
  map_add' a b := rfl
  map_smul' c a := Subtype.ext (by simp [Submodule.coe_smul])

/-- The boundaries inside the chains, mapped to the boundaries inside the cycles. -/
def uctBToH : ↥(uctB (relChains X A) n) →ₗ[ℤ] ↥(uctH (relChains X A) n) where
  toFun b := ⟨⟨(b : ↥((relChains X A).X n)), uctB_le_uctZ _ n b.2⟩,
    (mem_uctH _ n ⟨(b : ↥((relChains X A).X n)), uctB_le_uctZ _ n b.2⟩).mpr b.2⟩
  map_add' a b := Subtype.ext (Subtype.ext rfl)
  map_smul' c a := Subtype.ext (Subtype.ext (by simp [Submodule.coe_smul]))

/-- The extension property for functionals on the boundaries (`B_n ⊆ C_n`), pointwise form. -/
theorem forall_extends_ext (hC0 : IsZero ((dualComplex ℤ (relChains X A)).homology (n + 1))) :
    ∀ φ : ↥(uctB (relChains X A) n) →ₗ[ℤ] ℤ,
      ∃ ψ : ↥((relChains X A).X n) →ₗ[ℤ] ℤ,
        ∀ b : ↥(uctB (relChains X A) n), ψ (b : ↥((relChains X A).X n)) = φ b := by
  intro φ
  obtain ⟨ψ, hψ⟩ := Work.ThomBordism.forall_extends_of_isZero_dual (relChains X A) n hC0 φ
  exact ⟨ψ, fun b => LinearMap.congr_fun hψ b⟩

/-- A functional on the boundaries (as cycles) extends to a functional on the cycles. -/
theorem extends_of_isZero_dual (hC0 : IsZero ((dualComplex ℤ (relChains X A)).homology (n + 1))) :
    ∀ φ : ↥(uctH (relChains X A) n) →ₗ[ℤ] ℤ,
      ∃ g : ↥(uctZ (relChains X A) n) →ₗ[ℤ] ℤ,
        ∀ b : ↥(uctH (relChains X A) n), g (b : ↥(uctZ (relChains X A) n)) = φ b := by
  intro φ
  obtain ⟨ψ, hψ⟩ := forall_extends_ext (X := X) (A := A) (n := n) hC0
    (φ.comp (uctBToH (X := X) (A := A) (n := n)))
  refine ⟨ψ.comp (uctZ (relChains X A) n).subtype, fun b => ?_⟩
  show ψ (b : ↥((relChains X A).X n)) = φ b
  show ψ ((uctHToB (X := X) (A := A) (n := n) b : ↥(uctB (relChains X A) n))
    : ↥((relChains X A).X n)) = φ b
  have h1 := hψ (uctHToB (X := X) (A := A) (n := n) b)
  simp only [LinearMap.comp_apply] at h1
  rw [h1]
  exact congrArg φ (Subtype.ext (Subtype.ext rfl))

/-- **Purity**: a free submodule along which all functionals extend is pure. -/
theorem pure_of_extends {Z : Type*} [AddCommGroup Z] [Module ℤ Z] [Module.IsTorsionFree ℤ Z]
    (B : Submodule ℤ Z) (hB : Module.Free ℤ ↥B)
    (hext : ∀ φ : ↥B →ₗ[ℤ] ℤ, ∃ ψ : Z →ₗ[ℤ] ℤ, ∀ b : ↥B, ψ ↑b = φ b)
    (z : Z) (N : ℕ) (hN : 0 < N) (hz : N • z ∈ B) : z ∈ B := by
  classical
  let b := Module.Free.chooseBasis ℤ ↥B
  choose ψ hψ using hext
  let c : Module.Free.ChooseBasisIndex ℤ ↥B →₀ ℤ := b.repr ⟨N • z, hz⟩
  have hc : ∀ i, c i = (N : ℤ) * ψ (b.coord i) z := by
    intro i
    rw [show c i = b.repr ⟨N • z, hz⟩ i from rfl,
      ← Module.Basis.coord_apply b i ⟨N • z, hz⟩, ← hψ (b.coord i) ⟨N • z, hz⟩,
      show ((⟨N • z, hz⟩ : ↥B) : Z) = N • z from rfl,
      map_nsmul, nsmul_eq_mul]
  let W : Z := ∑ i ∈ c.support, (ψ (b.coord i) z) • (b i : Z)
  have hW : W ∈ B := by
    rw [show W = ∑ i ∈ c.support, (ψ (b.coord i) z) • (b i : Z) from rfl]
    exact B.sum_mem (fun i _ => (B.toAddSubgroup).zsmul_mem (b i).2 (ψ (b.coord i) z))
  have hcoeffW : ∀ i, b.repr ⟨W, hW⟩ i = ψ (b.coord i) z := by
    intro i
    rw [← Module.Basis.coord_apply b i ⟨W, hW⟩, ← hψ (b.coord i) ⟨W, hW⟩]
    rw [show ((⟨W, hW⟩ : ↥B) : Z) = W from rfl,
      show W = ∑ i ∈ c.support, (ψ (b.coord i) z) • (b i : Z) from rfl, map_sum]
    have hterm : ∀ x ∈ c.support, (ψ (b.coord i)) ((ψ (b.coord x)) z • (b x : Z))
        = if x = i then (ψ (b.coord i)) z else 0 := by
      intro x hx
      rw [map_zsmul, hψ (b.coord i) (b x), Module.Basis.coord_apply, b.repr_self]
      by_cases hxi : x = i
      · rw [hxi, Finsupp.single_eq_same, zsmul_eq_mul, mul_one, if_pos rfl]
        exact_mod_cast rfl
      · rw [Finsupp.single_eq_of_ne (fun h => hxi h.symm), zsmul_zero, if_neg hxi]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hi : i ∈ c.support
    · rw [if_pos hi]
    · rw [if_neg hi]
      have hci : c i = 0 := Finsupp.notMem_support_iff.mp hi
      rw [hc i] at hci
      exact ((mul_eq_zero.mp hci).resolve_left (by exact_mod_cast hN.ne')).symm
  have hrepr : b.repr ⟨N • z, hz⟩
      = b.repr ⟨N • W, (B.toAddSubgroup).nsmul_mem hW N⟩ := by
    ext i
    rw [show b.repr ⟨N • z, hz⟩ i = c i from rfl, hc i]
    rw [show (⟨N • W, (B.toAddSubgroup).nsmul_mem hW N⟩ : ↥B) = N • ⟨W, hW⟩ from
      Subtype.ext rfl, map_nsmul (b.repr), Finsupp.nsmul_apply, hcoeffW i, nsmul_eq_mul]
  have hkey : N • z = N • W := congrArg Subtype.val (b.repr.injective hrepr)
  haveI : IsAddTorsionFree Z := IsAddTorsionFree.of_isTorsionFree ℤ Z
  have hzW : z = W := nsmul_right_injective hN.ne' hkey
  rw [hzW]
  exact hW

/-- **Purity of the boundaries in the cycles.** -/
theorem pure_uctH (hC0 : IsZero ((dualComplex ℤ (relChains X A)).homology (n + 1))) :
    ∀ z : ↥(uctZ (relChains X A) n), ∀ N : ℕ, 0 < N →
      N • z ∈ uctH (relChains X A) n → z ∈ uctH (relChains X A) n := by
  haveI hfr : Module.Free ℤ ↥((relChains X A).X n) := relChains_free X A n
  haveI hrz : Module.Free ℤ ↥(uctZ (relChains X A) n) :=
    free_congr (Work.ThomBordism.free_uctZ (relChains X A) (fun k => relChains_free X A k) n)
  haveI hB : Module.Free ℤ ↥(uctH (relChains X A) n) :=
    free_congr (Work.ThomBordism.free_uctH (relChains X A) (fun k => relChains_free X A k) n)
  intro z N hN hz
  exact pure_of_extends (B := uctH (relChains X A) n) hB
    (extends_of_isZero_dual (X := X) (A := A) (n := n) hC0) z N hN hz

/-! ## Step 3: a quotient by a pure submodule is torsion-free -/

theorem isAddTorsionFree_quot_of_pure {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    (B : Submodule ℤ Z)
    (h : ∀ z : Z, ∀ N : ℕ, 0 < N → N • z ∈ B → z ∈ B) :
    IsAddTorsionFree (Z ⧸ B) := by
  refine ⟨fun {n} hn a b hab => ?_⟩
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective B b
  have h1 : B.mkQ (n • x) = B.mkQ (n • y) := by
    rw [map_nsmul, map_nsmul]; exact hab
  have hmem : n • (x - y) ∈ B := by
    have h0 : B.mkQ (n • (x - y)) = 0 := by
      rw [nsmul_sub, map_sub, h1, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hxy : x - y ∈ B := h (x - y) n hn' hmem
  have hfin : B.mkQ x = B.mkQ y := by
    have h0 : B.mkQ (x - y) = 0 := by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  simpa using hfin

/-! ## Step 4: the homology in degree `n` is torsion-free -/

theorem isTorsionFree_homology (hC0 : IsZero ((relComplex ℤ X A).homology (n + 1))) :
    Module.IsTorsionFree ℤ ↥((relChains X A).homology n) := by
  have hpure := pure_uctH (X := X) (A := A) (n := n)
    (isZero_dual_of_isZero_rel (X := X) (A := A) (n := n) hC0)
  haveI hq : IsAddTorsionFree (↥(uctZ (relChains X A) n) ⧸ uctH (relChains X A) n) :=
    isAddTorsionFree_quot_of_pure (uctH (relChains X A) n) hpure
  obtain ⟨e⟩ := homology_iso_H (relChains X A) n
  have hadd : IsAddTorsionFree ↥((relChains X A).homology n) := by
    refine ⟨fun {k} hk a b hab => ?_⟩
    have h1 : k • e.hom.hom a = k • e.hom.hom b := by
      rw [← map_nsmul (e.hom.hom), ← map_nsmul (e.hom.hom)]
      exact congrArg (ModuleCat.Hom.hom e.hom) hab
    exact (ConcreteCategory.bijective_of_isIso e.hom).1
      (IsAddTorsionFree.nsmul_right_injective hk h1)
  exact isTorsionFree_congr (Module.isTorsionFree_int_iff_isAddTorsionFree.mpr hadd)

/-! ## Step 5: the dual of the homology is `ℤ` -/

theorem relKronH_bijective (hfin : ∀ j, Module.Finite ℤ ↥((relChains X A).homology j))
    (hC : Nonempty ((relComplex ℤ X A).homology n ≅ ModuleCat.of ℤ ℤ)) :
    Function.Bijective (relKronH X A n) := by
  constructor
  · intro α β hab
    have hsub : relKronH X A n (α - β) = 0 := by rw [map_sub, hab, sub_self]
    have hzero : α - β = 0 := by
      by_cases hnt : ∀ N : ℕ, 0 < N → (N : ℤ) • (α - β) ≠ 0
      · have hnt' : ∀ N : ℕ, 0 < N →
            @SMul.smul ℤ ↥(relCohomology ℤ X A n)
              (DistribMulAction.toDistribSMul.toSMul) (N : ℤ) (α - β) ≠ 0 := by
          intro N hN hzero
          exact hnt N hN
            (int_smul_eq_zsmul (inferInstance : Module ℤ ↥(relCohomology ℤ X A n)) (N : ℤ)
              (α - β) ▸ hzero)
        obtain ⟨β', hβ'⟩ := Work.ThomBordism.relKronH_kernel_eq_torsion (hfin (n - 1)) (α - β) hnt'
        exact absurd (by rw [hsub]; rfl) hβ'
      · push Not at hnt
        obtain ⟨N, hN, hN0⟩ := hnt
        obtain ⟨e⟩ := hC
        let e' := uctIsoToLinearEquiv e
        have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
        have hn : N • e'.toLinearMap (α - β) = 0 := by
          rw [← map_nsmul (e'.toLinearMap)]
          rw [show N • (α - β) = 0 from by rw [← natCast_zsmul]; exact hN0, map_zero]
        have hz : e'.toLinearMap (α - β) = 0 := by
          rw [nsmul_eq_mul] at hn
          exact (mul_eq_zero.mp hn).resolve_left hNne
        refine e'.injective ?_
        have hz' : e' (α - β) = 0 := hz
        rw [hz', map_zero]
    exact sub_eq_zero.mp hzero
  · exact Work.ThomBordism.relKronH_surjective X A n (fun m => relChains_free X A m)

/-- The evaluation pairing identifies `H^n(X,A;ℤ)` with the dual of `H_n`. -/
theorem nonempty_dual_homology_iso (hfin : ∀ j, Module.Finite ℤ ↥((relChains X A).homology j))
    (hCoh : Nonempty ((relComplex ℤ X A).homology n ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty ((Module.Dual ℤ ↥((relChains X A).homology n)) ≃ₗ[ℤ] ℤ) := by
  have hbij : Function.Bijective (relKronH X A n) := relKronH_bijective hfin hCoh
  obtain ⟨e⟩ := hCoh
  exact ⟨((LinearEquiv.ofBijective (relKronH X A n) hbij).symm).trans
    (uctIsoToLinearEquiv e)⟩

/-! ## Step 6: the double dual of the homology -/

/-- `ℤ` is its own dual. -/
def dualSelf : Module.Dual ℤ ℤ ≃ₗ[ℤ] ℤ where
  toFun f := f 1
  invFun n := n • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
  left_inv f := by
    apply LinearMap.ext
    intro x
    show ((f 1) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) x = f x
    have hx : f x = x * f 1 := by
      have h1 : f x = f (x • (1 : ℤ)) := by rw [smul_eq_mul, mul_one]
      rw [h1, map_smul, smul_eq_mul]
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, hx, mul_comm]
  right_inv n := by
    show (n • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) 1 = n
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
  map_add' f g := by simp
  map_smul' c f := by simp

theorem nonempty_homology_iso_int (hfin : ∀ j, Module.Finite ℤ ↥((relChains X A).homology j))
    (hC : Nonempty ((relComplex ℤ X A).homology n ≅ ModuleCat.of ℤ ℤ))
    (hC0 : IsZero ((relComplex ℤ X A).homology (n + 1))) :
    Nonempty (↥((relChains X A).homology n) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨d⟩ := nonempty_dual_homology_iso (X := X) (A := A) (n := n) hfin hC
  haveI : Module.Finite ℤ ↥((relChains X A).homology n) := hfin n
  haveI : Module.IsTorsionFree ℤ ↥((relChains X A).homology n) :=
    isTorsionFree_homology (X := X) (A := A) (n := n) hC0
  haveI hfree : Module.Free ℤ ↥((relChains X A).homology n) :=
    Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective ℤ ↥((relChains X A).homology n) := Module.Projective.of_free
  haveI : Module.IsReflexive ℤ ↥((relChains X A).homology n) := inferInstance
  exact ⟨(Module.evalEquiv ℤ ↥((relChains X A).homology n)).trans
    ((LinearEquiv.dualMap d).symm.trans dualSelf)⟩

/-! ## The target -/

/-- **Cohomology `≅ ℤ` in degree `n`, vanishing in degree `n+1`, and finitely generated homology
force the homology in degree `n` to be `ℤ`.**  This is the integral universal coefficient
comparison for the relative chain complex of a pair. -/
theorem relHomologyIntOfCohCopy {X : TopCat} {A : Set X} {n : ℕ}
    (hfin : ∀ j, Module.Finite ℤ ↥((Work.Cohomology.relChains X A).homology j))
    (hC : Nonempty ((Work.Cohomology.relComplex ℤ X A).homology n ≅ ModuleCat.of ℤ ℤ))
    (hC0 : CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℤ X A).homology (n + 1))) :
    Nonempty ((Work.Cohomology.relChains X A).homology n ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := nonempty_homology_iso_int (X := X) (A := A) (n := n) hfin hC hC0
  exact ⟨e.toModuleIso⟩

end

end Work.Tubular
