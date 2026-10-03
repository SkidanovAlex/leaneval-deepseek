/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Bieri-Strebel extension theorem: FP2 groups are quotients by k-perfect subgroups

This file proves Work.ORFP2.exists_extension_of_isFP2: a group of type FP2 over k is the
quotient of a finitely presented group by a normal subgroup N with N_ab tensor k = 0
(Bieri-Strebel, Lemma 2.1, the forward direction; JL Lemma 4.3).
-/
import Mathlib
import Submission.Work.ORFP2.Basic
import Submission.Work.ORFP2.ExtFin
import Submission.Work.ORFP2.exists_surj_freeGroup_fin
import Submission.Work.ORFP2.isFinitelyPresented_quot_normalClosure
import Submission.Work.ORFP2.Ext.sum_cls_eq_zero_of_sum_foxGamma_eq_zero
import Submission.Work.ORFP2.isFP2_iff_relationModule_fg
import Submission.Work.ORFP2.augIdeal_freeGroup_injective
import Submission.Work.ORFP2.augIdeal_freeGroup_surjective
import Submission.Work.ORFP2.group_fg_of_augIdeal_fg

/-- v4.35 port: `TensorProduct.induction_on` lost `@[elab_as_elim]` when deprecated. -/
@[elab_as_elim] private theorem tpInductionOn' {R M N : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] {motive : TensorProduct R M N → Prop}
    (z : TensorProduct R M N) (zero : motive 0) (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z zero tmul add


set_option autoImplicit false

namespace Work.ORFP2

open MonoidAlgebra

namespace Ext

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type*} [Group G] (φ : FreeGroup (Fin n) →* G)

/-- The classes cls x span N_ab ⊗_ℤ k over k. -/
theorem span_cls_eq_top : Submodule.span k (Set.range (cls k φ)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro m
  refine tpInductionOn' m ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a c
    obtain ⟨x, hx⟩ : ∃ x : ↥(φ.ker), Additive.ofMul (Abelianization.of x) = a := by
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (commutator ↥(φ.ker)) (Additive.toMul a)
      refine ⟨y, ?_⟩
      have hy' : Abelianization.of y = Additive.toMul a := hy
      rw [hy', ofMul_toMul]
    rw [← hx, ← smul_cls k φ c x]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨x, rfl⟩)
  · intro a b ha hb
    exact Submodule.add_mem _ ha hb

/-- H1Vanishes is inherited by quotients: a surjection N ->* N induces a surjection of the
tensor products, so vanishing on the source gives vanishing on the target. -/
lemma h1Vanishes_of_surjective {N N' : Type*} [Group N] [Group N'] (π : N →* N')
    (hπ : Function.Surjective π) (h : H1Vanishes k N) : H1Vanishes k N' := by
  haveI : Subsingleton (TensorProduct ℤ (Additive (Abelianization N)) k) := h
  have hsurj : Function.Surjective (TensorProduct.map
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map π)))
      (LinearMap.id : k →ₗ[ℤ] k)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
        obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator N') (Additive.toMul a)
        obtain ⟨m, hm⟩ := hπ n
        refine ⟨Additive.ofMul (Abelianization.of m) ⊗ₜ[ℤ] c, ?_⟩
        rw [TensorProduct.map_tmul]
        have h1 : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map π)))
            (Additive.ofMul (Abelianization.of m)) = a := by
          show Additive.ofMul (Abelianization.map π (Abelianization.of m)) = a
          rw [Abelianization.map_of, hm]
          have h2 : Abelianization.of n = Additive.toMul a := hn
          rw [h2, ofMul_toMul]
        rw [h1]
        simp only [LinearMap.id_apply]
    | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        exact ⟨x' + y', by rw [map_add, hx', hy']⟩
  exact hsurj.subsingleton

end Ext

universe v

/-- The hypothesis FreeGroupAugIdealBasis at the universe of Fin n: the augmentation ideal of
k[F(alpha)] is free on the elements x - 1. -/
theorem freeGroupAugIdealBasis_zero (k : Type v) [CommRing k] :
    FreeGroupAugIdealBasis.{v, 0} k := by
  intro α _
  have hinj : Function.Injective (Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
      (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) := by
    intro c d h
    refine augIdeal_freeGroup_injective k α ?_
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at h
    simpa only [smul_eq_mul] using h
  refine ⟨LinearEquiv.ofBijective
    ((Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
        (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)).codRestrict
      (augIdeal k (FreeGroup α)) (fun c => by
        rw [← augIdeal_freeGroup_surjective k α]; exact LinearMap.mem_range_self _ c))
    ⟨fun c d h => hinj (Subtype.ext_iff.mp h),
      fun y => by
        have hy : (y : MonoidAlgebra k (FreeGroup α)) ∈
            LinearMap.range (Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
              (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) := by
          rw [augIdeal_freeGroup_surjective k α]; exact y.2
        obtain ⟨c, hc⟩ := hy
        exact ⟨c, Subtype.ext hc⟩⟩, ?_⟩
  · intro c
    show ((Finsupp.linearCombination (MonoidAlgebra k (FreeGroup α))
        (fun a : α => MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1)) c) =
      c.sum (fun a x => x * (MonoidAlgebra.single (FreeGroup.of a) (1 : k) - 1))
    rw [Finsupp.linearCombination_apply]
    exact Finsupp.sum_congr fun a _ => by rw [smul_eq_mul]

/-- Bieri-Strebel [BS78, Lemma 2.1] = JL Lemma 4.3, forward direction.  A group of type FP2 over
k (with 1 ≠ 0) is the quotient of a finitely presented group by a normal subgroup N with
N_ab ⊗_ℤ k = 0. -/
theorem exists_extension_of_isFP2 (k : Type*) [CommRing k] [Nontrivial k]
    (hbasis : FreeGroupAugIdealBasis k) (G : Type*) [Group G] (h : IsFP2 k G) :
    HasFP2Extension k G := by
  classical
  -- the basis hypothesis at the universe of Fin n
  have hbas := freeGroupAugIdealBasis_zero k
  -- Step 1: G is finitely generated.
  have hfgG : Group.FG G := by
    haveI : Module.FinitePresentation (MonoidAlgebra k G) (augIdeal k G) := h
    exact group_fg_of_augIdeal_fg k G (Module.Finite.iff_fg.mp inferInstance)
  -- Step 2: choose a free presentation.
  obtain ⟨n, φ, hφ⟩ := exists_surj_freeGroup_fin hfgG
  -- Step 3: the relation module is a finitely generated k[G]-module.
  have hKfg : (relationModule k G φ).FG := (isFP2_iff_relationModule_fg k G φ hφ).mp h
  -- Step 4: finitely many relators whose classes span N_ab ⊗ k.
  obtain ⟨R₀, hR₀ker, hR₀⟩ := Ext.exists_finset_relators k hbas φ hφ hKfg
  -- Step 5: the extension E = F / <<R₀>>.
  let R : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure (R₀ : Set (FreeGroup (Fin n)))
  have hle : R ≤ φ.ker := Subgroup.normalClosure_le_normal (by simpa using hR₀ker)
  let E := FreeGroup (Fin n) ⧸ R
  let f : E →* G := QuotientGroup.lift R φ hle
  have hfsurj : Function.Surjective f := by
    intro g
    obtain ⟨w, hw⟩ := hφ g
    refine ⟨QuotientGroup.mk w, ?_⟩
    show f (QuotientGroup.mk w) = g
    rw [show f = QuotientGroup.lift R φ hle from rfl, QuotientGroup.lift_mk', hw]
  have hfp : Group.IsFinitelyPresented E :=
    isFinitelyPresented_quot_normalClosure (R₀ : Set (FreeGroup (Fin n))) R₀.finite_toSet
  -- Step 6: lift E to the ambient universe of the existential quantifier.
  let f' : ULift E →* G := f.comp MulEquiv.ulift.toMonoidHom
  have hf'surj : Function.Surjective f' := by
    intro g
    obtain ⟨x, hx⟩ := hfsurj g
    exact ⟨ULift.up x, hx⟩
  have hfp' : Group.IsFinitelyPresented (ULift E) := by
    haveI : Group.IsFinitelyPresented E := hfp
    exact Group.IsFinitelyPresented.equiv MulEquiv.ulift.symm
  refine ⟨ULift E, inferInstance, f', hf'surj, hfp', ?_⟩
  -- Step 7: N_ab ⊗ k = 0 for N = ker f, transferred from ker f ≅ ker f'.
  have hker : ↥(MonoidHom.ker f) ≃* ↥(MonoidHom.ker f') :=
    { toFun := fun y => ⟨ULift.up y.1, y.2⟩
      invFun := fun x => ⟨ULift.down x.1, x.2⟩
      left_inv := fun y => Subtype.ext (by obtain ⟨e, _⟩ := y; rfl)
      right_inv := fun x => Subtype.ext (by obtain ⟨u, _⟩ := x; cases u with | up e => rfl)
      map_mul' := fun y z => Subtype.ext rfl }
  refine Ext.h1Vanishes_of_surjective k hker.toMonoidHom hker.surjective ?_
  -- the projection ker φ -> N
  let π' : ↥(φ.ker) →* ↥(MonoidHom.ker f) :=
    { toFun := fun x => ⟨QuotientGroup.mk (x : FreeGroup (Fin n)), by
        rw [MonoidHom.mem_ker]
        rw [show f = QuotientGroup.lift R φ hle from rfl, QuotientGroup.lift_mk',
          MonoidHom.mem_ker.mp x.2]⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hπ'surj : Function.Surjective π' := by
    intro y
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective R y.1
    have hwker : w ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h3 : f (QuotientGroup.mk w) = φ w := by
        rw [show f = QuotientGroup.lift R φ hle from rfl, QuotientGroup.lift_mk']
      have h2 : (QuotientGroup.mk w : E) = y.1 := hw
      rw [← h3, h2]
      exact MonoidHom.mem_ker.mp y.2
    refine ⟨⟨w, hwker⟩, ?_⟩
    ext
    exact hw
  -- the comparison map ker φ_ab ⊗ k -> N_ab ⊗ k
  let Φ := TensorProduct.map
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map π')))
      (LinearMap.id : k →ₗ[ℤ] k)
  have hΦsmul : ∀ (c : k) (m : Ext.KerMod k φ), Φ (c • m) = c • Φ m := by
    intro c m
    induction m using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul a d =>
        rw [Ext.smul_tmul_int, TensorProduct.map_tmul, TensorProduct.map_tmul, Ext.smul_tmul_int]
        simp only [LinearMap.id_apply]
    | add x y hx hy =>
        calc Φ (c • (x + y)) = Φ (c • x + c • y) := by rw [smul_add]
          _ = Φ (c • x) + Φ (c • y) := by rw [map_add]
          _ = c • Φ x + c • Φ y := by rw [hx, hy]
          _ = c • (Φ x + Φ y) := by rw [smul_add]
          _ = c • Φ (x + y) := by rw [map_add]
  have hΦcls : ∀ x : ↥(φ.ker), Φ (Ext.cls k φ x) = 0 := by
    intro x
    obtain ⟨ι, hι, y, d, hy, hxy⟩ := hR₀ (Ext.foxGamma k hbas n φ (x : FreeGroup (Fin n)))
      (Ext.foxGamma_mem k hbas n φ (x : FreeGroup (Fin n)) x.2)
    haveI := hι
    have hxy' : Ext.foxGamma k hbas n φ (x : FreeGroup (Fin n)) =
        ∑ i, d i • Ext.foxGamma k hbas n φ ((y i : ↥(φ.ker)) : FreeGroup (Fin n)) := by
      rw [hxy]
      exact Finset.sum_congr (Finset.ext fun j => by simp) fun j _ => rfl
    let Z : Option ι → ↥(φ.ker) := fun j => Option.elim j x y
    let C : Option ι → k := fun j => Option.elim j (-1 : k) d
    have hzero : ∑ j : Option ι, C j • Ext.foxGamma k hbas n φ (Z j : FreeGroup (Fin n))
        = 0 := by
      rw [Fintype.sum_option]
      dsimp only [C, Z]
      simp only [Option.elim_none, Option.elim_some]
      rw [← hxy', neg_one_smul, neg_add_cancel]
    have hcls := Ext.sum_cls_eq_zero_of_sum_foxGamma_eq_zero k hbas φ hφ Finset.univ Z C hzero
    rw [Fintype.sum_option] at hcls
    dsimp only [C, Z] at hcls
    simp only [Option.elim_none, Option.elim_some] at hcls
    have hclsx : Ext.cls k φ x = ∑ i, d i • Ext.cls k φ (y i) := by
      rw [neg_one_smul, neg_add_eq_zero] at hcls
      exact hcls
    rw [hclsx, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hyi : ((y i : ↥(φ.ker)) : FreeGroup (Fin n)) ∈ R := hy i
    have hπ : π' (y i) = 1 := by
      ext
      show QuotientGroup.mk ((y i : ↥(φ.ker)) : FreeGroup (Fin n)) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hyi
    have hπ' : Abelianization.map π' (Abelianization.of (y i)) = 1 := by
      rw [Abelianization.map_of, hπ, map_one]
    have hthis : Φ (Ext.cls k φ (y i)) = 0 := by
      rw [show Ext.cls k φ (y i)
        = (Additive.ofMul (Abelianization.of (y i))) ⊗ₜ[ℤ] (1 : k) from rfl]
      show TensorProduct.map
            (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map π')))
            (LinearMap.id : k →ₗ[ℤ] k)
            ((Additive.ofMul (Abelianization.of (y i))) ⊗ₜ[ℤ] (1 : k)) = 0
      rw [TensorProduct.map_tmul]
      show Additive.ofMul (Abelianization.map π' (Abelianization.of (y i))) ⊗ₜ[ℤ]
            ((LinearMap.id : k →ₗ[ℤ] k) (1 : k)) = 0
      rw [hπ']
      simp
    rw [hΦsmul, hthis, smul_zero]
  have hΦzero : Φ = 0 := by
    apply LinearMap.ext
    intro m
    have hm : m ∈ Submodule.span k (Set.range (Ext.cls k φ)) := by
      rw [Ext.span_cls_eq_top k φ]
      trivial
    refine Submodule.span_induction (p := fun m _ => Φ m = 0) ?_ ?_ ?_ ?_ hm
    · rintro x ⟨y, rfl⟩
      exact hΦcls y
    · exact map_zero Φ
    · intro a b ha hb iha ihb
      rw [map_add, iha, ihb, add_zero]
    · intro c a ha iha
      rw [hΦsmul, iha, smul_zero]
  have hΦsurj : LinearMap.range Φ = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro t
    rw [LinearMap.mem_range]
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
        obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Abelianization ↥(φ.ker),
            Abelianization.map π' b₀ = Additive.toMul a := by
          obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (commutator ↥(MonoidHom.ker f))
            (Additive.toMul a)
          obtain ⟨w, hw⟩ := hπ'surj z
          exact ⟨Abelianization.of w, by rw [Abelianization.map_of, hw]; exact hz⟩
        refine ⟨Additive.ofMul b₀ ⊗ₜ[ℤ] c, ?_⟩
        show TensorProduct.map
              (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Abelianization.map π')))
              (LinearMap.id : k →ₗ[ℤ] k)
              (Additive.ofMul b₀ ⊗ₜ[ℤ] c) = a ⊗ₜ[ℤ] c
        rw [TensorProduct.map_tmul]
        show Additive.ofMul (Abelianization.map π' b₀) ⊗ₜ[ℤ] ((LinearMap.id : k →ₗ[ℤ] k) c)
          = a ⊗ₜ[ℤ] c
        rw [hb₀, ofMul_toMul]
        simp only [LinearMap.id_apply]
    | add x y hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨s', hs'⟩ := hy
        exact ⟨s + s', by rw [map_add, hs, hs']⟩
  have hz0 : ∀ y : Ext.KerMod k φ, Φ y = 0 := by
    intro y
    rw [hΦzero]
    simp
  change Subsingleton (TensorProduct ℤ (Additive (Abelianization ↥(MonoidHom.ker f))) k)
  refine Subsingleton.intro fun a b => ?_
  have ha : a ∈ LinearMap.range Φ := by rw [hΦsurj]; exact Submodule.mem_top
  have hb : b ∈ LinearMap.range Φ := by rw [hΦsurj]; exact Submodule.mem_top
  obtain ⟨ya, hya⟩ := LinearMap.mem_range.mp ha
  obtain ⟨yb, hyb⟩ := LinearMap.mem_range.mp hb
  rw [← hya, ← hyb]
  simp only [hz0]

end Work.ORFP2
