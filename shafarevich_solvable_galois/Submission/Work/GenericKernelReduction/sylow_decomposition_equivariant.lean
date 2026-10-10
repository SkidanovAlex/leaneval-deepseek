import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.Fitting.iSup_sylow_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Equivariant Sylow decomposition of a finite nilpotent group

A finite nilpotent group `N` is the direct product of its Sylow subgroups, and each of these is
characteristic.  Consequently any action `φ : G →* MulAut N` of a group `G` on `N` restricts to
an action on each Sylow subgroup, and the direct-product decomposition
`N ≃* ∏ p, P p` is `G`-equivariant.

This file provides the required statement
`Work.GenericKernelReduction.sylow_decomposition_equivariant`, together with the elementary
helper constructions (`restrictMulAut`, `restrictActionHom`) restricting an automorphism to a
characteristic subgroup.
-/

namespace Work.GenericKernelReduction

open scoped Classical

variable {N : Type*} [Group N]

/-- The automorphism of a characteristic subgroup `H ≤ N` induced by an automorphism of `N`. -/
noncomputable def restrictMulAut (H : Subgroup N) (hH : H.Characteristic) (a : MulAut N) :
    MulAut H :=
  (a.subgroupMap H).trans (MulEquiv.subgroupCongr (by
    rw [Subgroup.map_equiv_eq_comap_symm]
    exact Subgroup.characteristic_iff_comap_eq.mp hH a.symm))

/-- The induced automorphism really is the restriction of `a`. -/
lemma coe_restrictMulAut_apply (H : Subgroup N) (hH : H.Characteristic) (a : MulAut N)
    (x : H) : ((restrictMulAut H hH a x : H) : N) = a (x : N) := by
  rw [restrictMulAut, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

lemma restrictMulAut_one (H : Subgroup N) (hH : H.Characteristic) :
    restrictMulAut H hH 1 = 1 := by
  apply MulEquiv.ext; intro x; apply Subtype.ext
  rw [coe_restrictMulAut_apply]; simp

lemma restrictMulAut_mul (H : Subgroup N) (hH : H.Characteristic) (a b : MulAut N) :
    restrictMulAut H hH (a * b) = restrictMulAut H hH a * restrictMulAut H hH b := by
  apply MulEquiv.ext; intro x; apply Subtype.ext
  rw [coe_restrictMulAut_apply]
  simp only [MulAut.mul_apply]
  rw [coe_restrictMulAut_apply, coe_restrictMulAut_apply]

/-- The action of `G` on `N` restricts to a characteristic subgroup `H ≤ N`. -/
noncomputable def restrictActionHom {G : Type*} [Group G] (H : Subgroup N)
    (hH : H.Characteristic) (φ : G →* MulAut N) : G →* MulAut H where
  toFun g := restrictMulAut H hH (φ g)
  map_one' := by rw [map_one, restrictMulAut_one]
  map_mul' g h := by rw [map_mul, restrictMulAut_mul]

@[simp] lemma restrictActionHom_apply {G : Type*} [Group G] (H : Subgroup N)
    (hH : H.Characteristic) (φ : G →* MulAut N) (g : G) :
    restrictActionHom H hH φ g = restrictMulAut H hH (φ g) := rfl

lemma piCongrRight_mulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    (es : ∀ i, M i ≃* M i) (i : ι) (y : M i) :
    ((MulEquiv.piCongrRight es : (∀ i, M i) →* (∀ i, M i))) (Pi.mulSingle i y)
      = Pi.mulSingle i (es i y) := by
  change MulEquiv.piCongrRight es (Pi.mulSingle i y) = Pi.mulSingle i (es i y)
  ext j
  rw [MulEquiv.piCongrRight_apply]
  by_cases h : j = i
  · subst h; rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]

theorem sylow_decomposition_equivariant {N : Type*} [Group N] [Finite N]
    (hN : Group.IsNilpotent N) {G : Type*} [Group G] (φ : G →* MulAut N) :
    ∃ (P : ∀ p : (Nat.card N).primeFactors, Subgroup N)
      (_ : ∀ p : (Nat.card N).primeFactors, IsPGroup (p : ℕ) (P p))
      (_ : ∀ p : (Nat.card N).primeFactors, (P p).Normal)
      (ψ : ∀ p : (Nat.card N).primeFactors, G →* MulAut ↥(P p))
      (e : N ≃* (∀ p, ↥(P p))),
      (∀ (g : G) (n : N),
        e (φ g n) = (MulEquiv.piCongrRight (fun p => ψ p g)) (e n)) ∧
      (∀ (g : G) (p : (Nat.card N).primeFactors) (x : ↥(P p)),
        ((ψ p g x : ↥(P p)) : N) = φ g (x : N)) := by
  classical
  haveI := hN
  let P : ∀ p : (Nat.card N).primeFactors, Subgroup N :=
    fun p => ↑(default : Sylow (p : ℕ) N)
  have hpg : ∀ p : (Nat.card N).primeFactors, IsPGroup (p : ℕ) (P p) :=
    fun p => (default : Sylow (p : ℕ) N).isPGroup'
  have hnorm : ∀ p : (Nat.card N).primeFactors, (P p).Normal := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact inferInstance
  have hchar : ∀ p : (Nat.card N).primeFactors, (P p).Characteristic := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact Sylow.characteristic_of_normal (default : Sylow (p : ℕ) N) (hnorm p)
  have hcomm : Pairwise fun p q : (Nat.card N).primeFactors =>
      ∀ x y : N, x ∈ P p → y ∈ P q → Commute x y := by
    intro p q hpq x y hx hy
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    exact Subgroup.commute_of_normal_of_disjoint (P p) (P q) (hnorm p) (hnorm q)
      (IsPGroup.disjoint_of_ne (p : ℕ) (q : ℕ) (fun h => hpq (Subtype.ext h)) (P p) (P q)
        (hpg p) (hpg q)) x y hx hy
  haveI hFp : ∀ p : (Nat.card N).primeFactors, Fintype ↥(P p) := fun _ => Fintype.ofFinite _
  have hind : iSupIndep P := by
    apply Subgroup.independent_of_coprime_order hcomm
    intro p q hpq
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    haveI : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    exact IsPGroup.coprime_card_of_ne (p : ℕ) (q : ℕ) (fun h => hpq (Subtype.ext h))
      (P p) (P q) (hpg p) (hpg q)
  let F : (∀ p : (Nat.card N).primeFactors, ↥(P p)) →* N := Subgroup.noncommPiCoprod hcomm
  have hinj : Function.Injective F := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hrange : F.range = ⨆ p : (Nat.card N).primeFactors, P p :=
    Subgroup.noncommPiCoprod_range
  have htop : (⨆ p : (Nat.card N).primeFactors, P p) = ⊤ :=
    Work.Fitting.iSup_sylow_eq_top
  have hsurj : Function.Surjective F := by
    intro n
    have hn : n ∈ F.range := by rw [hrange, htop]; exact Subgroup.mem_top n
    exact MonoidHom.mem_range.mp hn
  have hbij : Function.Bijective F := ⟨hinj, hsurj⟩
  let ψ : ∀ p : (Nat.card N).primeFactors, G →* MulAut ↥(P p) :=
    fun p => restrictActionHom (P p) (hchar p) φ
  refine ⟨P, hpg, hnorm, ψ, (MulEquiv.ofBijective F hbij).symm, ?_, ?_⟩
  · -- equivariance of the product decomposition
    intro g n
    apply hinj
    simp only [ψ, restrictActionHom_apply]
    rw [MulEquiv.ofBijective_apply_symm_apply F hbij]
    have hcomp : F.comp ((MulEquiv.piCongrRight
          (fun p => restrictMulAut (P p) (hchar p) (φ g))) :
            (∀ p : (Nat.card N).primeFactors, ↥(P p)) →*
              (∀ p : (Nat.card N).primeFactors, ↥(P p)))
        = ((φ g : MulAut N) : N →* N).comp F := by
      apply MonoidHom.pi_ext
      intro i y
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, piCongrRight_mulSingle]
      simp only [F, Subgroup.noncommPiCoprod_mulSingle]
      exact coe_restrictMulAut_apply (P i) (hchar i) (φ g) y
    have hstep : F ((MulEquiv.piCongrRight
          (fun p => restrictMulAut (P p) (hchar p) (φ g)))
            ((MulEquiv.ofBijective F hbij).symm n))
        = φ g (F ((MulEquiv.ofBijective F hbij).symm n)) := by
      have hh := DFunLike.congr_fun hcomp ((MulEquiv.ofBijective F hbij).symm n)
      simp only [MonoidHom.comp_apply] at hh
      exact hh
    rw [hstep, MulEquiv.ofBijective_apply_symm_apply F hbij]
  · -- the restricted action is the restriction of `φ`
    intro g p x
    simp only [ψ, restrictActionHom_apply]
    exact coe_restrictMulAut_apply (P p) (hchar p) (φ g) x

end Work.GenericKernelReduction
