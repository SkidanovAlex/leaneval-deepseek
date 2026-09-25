/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CFT.Ledger
-/
import Mathlib
import Submission.Work.CFT.Ledger.Coind

/-!
# `Ĥ⁻¹` of a coinduced representation: Shapiro's lemma in degree `-1`

For an injective homomorphism `φ : G →* H` of finite groups and a `ℤ`-linear representation
`A` of `G`, this file proves Shapiro's lemma in degree `-1` of Tate cohomology, in the form
`Hm1Quotient (coind φ A) ≃+ Hm1Quotient A`, where `Hm1Quotient A = ker N_A ⧸ I_G A` presents
`Ĥ⁻¹(G, A)`.

The proof uses the two maps `iota q₀ : A → coind φ A` (the section supported on the trivial
coset), which on `ker N_A` lands in `ker N_B`, and `evalSum : coind φ A → A` (the sum over coset
representatives), which on `ker N_B` lands in `ker N_A` and is a left inverse of `iota q₀` up to
`I_B`. The comparison isomorphism is `a ↦ [iota q₀ a]` on kernels.

## Main results

* `Work.CFT.Ledger.evalSum_augIdeal_le` — `evalSum` maps `I_B` into `I_A`;
* `Work.CFT.Ledger.evalSum_sub_mem_augIdeal` — `x - iota q₀ (evalSum x) ∈ I_B`;
* `Work.CFT.Ledger.Hm1Quotient_coind` — `Hm1Quotient (coind φ A) ≃+ Hm1Quotient A`.
-/

open scoped Classical
open CategoryTheory

namespace Work.CFT.Ledger

noncomputable section

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]

section NormInv

variable (A : Rep ℤ G)

/-- The norm `N_A x = ∑ g, g • x` is `G`-invariant. -/
lemma normMap_mem_invariants (x : A.V) :
    Work.CFT.IdeleClassGroup.normMap A x ∈ Work.CFT.IdeleClassGroup.invariants A := by
  letI : Module ℤ A.V := A.hV2
  rw [Work.CFT.IdeleClassGroup.mem_invariants]
  intro g
  rw [Work.CFT.IdeleClassGroup.normMap_apply,
    map_sum (A.ρ g) (fun h => (A.ρ h) x) Finset.univ]
  refine Fintype.sum_bijective (fun h : G => g * h)
    ⟨fun a b hab => mul_left_cancel hab, fun b => ⟨g⁻¹ * b, by group⟩⟩
    (fun h : G => (A.ρ g) ((A.ρ h) x)) (fun h : G => (A.ρ h) x) ?_
  intro h
  rw [map_mul, Module.End.mul_apply]

/-- A finite sum of elements of the augmentation subgroup lies in it. -/
lemma finset_sum_mem_augIdeal {α : Type*} (s : Finset α) (f : α → A.V)
    (h : ∀ x ∈ s, f x ∈ augIdeal A) : ∑ x ∈ s, f x ∈ augIdeal A := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact AddSubgroup.add_mem _ (h a (Finset.mem_insert_self a s))
        (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

end NormInv

section Main

variable (φ : G →* H) (A : Rep ℤ G)

/-- Evaluation at `1`, as an additive map on `coind φ A`. -/
noncomputable def coindEvalOne : (Rep.coind φ A).V →+ A.V where
  toFun f := coindEval φ A f 1
  map_zero' := rfl
  map_add' f g := rfl

lemma coindEvalOne_apply (f : (Rep.coind φ A).V) :
    coindEvalOne φ A f = coindEval φ A f 1 := rfl

lemma coindEvalOne_iota (hφ : Function.Injective φ) (a : A.V) :
    coindEvalOne φ A (iota φ A hφ (oneCoset φ) a) = a :=
  coindEval_iota_oneCoset φ A hφ a

/-- The reindexed form of `evalSum` applied to a translate. -/
lemma evalSum_smul_eq (hφ : Function.Injective φ) (h : H) (x : (Rep.coind φ A).V) :
    evalSum φ A ((Rep.coind φ A).ρ h x)
      = ∑ q : CosetIdx φ, A.ρ (gCoord φ hφ (cosetRep φ q * h))
          (coindEval φ A x (cosetRep φ (cosetSmul φ h q))) := by
  rw [evalSum_coindEval]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [coindEval_smul]
  conv_lhs => rw [← phi_gCoord_mul_cosetRep φ hφ (cosetRep φ q * h)]
  rw [coindEval_equivariant, ← cosetSmul_apply_cosetRep φ h q]

/-- `evalSum` maps the augmentation subgroup of `coind φ A` into the augmentation subgroup
of `A`. -/
lemma evalSum_augIdeal_le (hφ : Function.Injective φ) {y : (Rep.coind φ A).V}
    (hy : y ∈ augIdeal (Rep.coind φ A)) : evalSum φ A y ∈ augIdeal A := by
  have hgen : ∀ (h : H) (x : (Rep.coind φ A).V),
      evalSum φ A ((Rep.coind φ A).ρ h x - x) ∈ augIdeal A := by
    intro h x
    rw [map_sub, evalSum_smul_eq φ A hφ h x, evalSum_coindEval]
    let e : CosetIdx φ ≃ CosetIdx φ :=
      Equiv.ofBijective (cosetSmul φ h) (cosetSmul_bijective φ h)
    have he : ∀ q : CosetIdx φ, e q = cosetSmul φ h q := fun q => rfl
    rw [show (∑ q : CosetIdx φ, A.ρ (gCoord φ hφ (cosetRep φ q * h))
            (coindEval φ A x (cosetRep φ (cosetSmul φ h q))))
        = ∑ q : CosetIdx φ, A.ρ (gCoord φ hφ (cosetRep φ q * h))
            (coindEval φ A x (cosetRep φ (e q))) by simp only [he]]
    rw [show (∑ q : CosetIdx φ, A.ρ (gCoord φ hφ (cosetRep φ q * h))
            (coindEval φ A x (cosetRep φ (e q))))
        = ∑ q : CosetIdx φ, A.ρ (gCoord φ hφ (cosetRep φ (e.symm q) * h))
            (coindEval φ A x (cosetRep φ q)) from
      (Fintype.sum_equiv e.symm _ _
        (fun q => by simp only [Equiv.apply_symm_apply])).symm]
    rw [← Finset.sum_sub_distrib]
    exact finset_sum_mem_augIdeal A Finset.univ _
      (fun q _ => smul_sub_self_mem_augIdeal A _ _)
  rw [augIdeal] at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz => obtain ⟨⟨h, x⟩, rfl⟩ := hz; exact hgen h x
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact AddSubgroup.add_mem _ ihx ihy
  | neg x hx ih => rw [map_neg]; exact AddSubgroup.neg_mem _ ih

/-- Every element of `coind φ A` differs from `iota q₀ (evalSum ·)` by an element of the
augmentation subgroup. -/
lemma evalSum_sub_mem_augIdeal (hφ : Function.Injective φ) (x : (Rep.coind φ A).V) :
    x - iota φ A hφ (oneCoset φ) (evalSum φ A x) ∈ augIdeal (Rep.coind φ A) := by
  have h2 : iota φ A hφ (oneCoset φ) (evalSum φ A x)
      = ∑ q : CosetIdx φ,
          iota φ A hφ (oneCoset φ) (coindEval φ A x (cosetRep φ q)) := by
    rw [evalSum_coindEval]
    exact map_sum (iota φ A hφ (oneCoset φ))
      (fun q => coindEval φ A x (cosetRep φ q)) Finset.univ
  rw [h2]
  nth_rewrite 1 [← sum_iota φ A hφ x]
  rw [← Finset.sum_sub_distrib]
  exact finset_sum_mem_augIdeal (Rep.coind φ A) Finset.univ
    (fun q => iota φ A hφ q (coindEval φ A x (cosetRep φ q))
      - iota φ A hφ (oneCoset φ) (coindEval φ A x (cosetRep φ q)))
    (fun q _ => iota_sub_mem_augIdeal φ A hφ q _)

/-- `evalSum` sends the kernel of the norm of `coind φ A` into the kernel of the norm of `A`. -/
lemma evalSum_mem_ker (hφ : Function.Injective φ) {g : (Rep.coind φ A).V}
    (hg : g ∈ (Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker) :
    evalSum φ A g ∈ (Work.CFT.IdeleClassGroup.normMap A).ker := by
  rw [AddMonoidHom.mem_ker]
  rw [← normMap_coindEval_one φ A hφ g, hg, coindEval_zero]
  rfl

/-- `iota q₀` sends the kernel of the norm of `A` into the kernel of the norm of
`coind φ A`. -/
lemma iota_oneCoset_mem_ker (hφ : Function.Injective φ) {a : A.V}
    (ha : a ∈ (Work.CFT.IdeleClassGroup.normMap A).ker) :
    iota φ A hφ (oneCoset φ) a
      ∈ (Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker := by
  letI : Module ℤ A.V := A.hV2
  have hinv : ∀ h : H,
      (Rep.coind φ A).ρ h (Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)
        (iota φ A hφ (oneCoset φ) a))
        = Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a) :=
    (Work.CFT.IdeleClassGroup.mem_invariants _ _).mp
      (normMap_mem_invariants (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a))
  rw [AddMonoidHom.mem_ker]
  apply Subtype.ext
  funext x
  change coindEval φ A (Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)
      (iota φ A hφ (oneCoset φ) a)) x = coindEval φ A (0 : (Rep.coind φ A).V) x
  rw [coindEval_eq_one_of_invariant φ A _ hinv x, coindEval_zero,
    normMap_coindEval_one φ A hφ, evalSum_iota φ A hφ]
  rw [ha]
  rfl

section QuotientIso

variable (φ : G →* H) (A : Rep ℤ G)

/-- `iota q₀`, restricted to the kernels of the norm maps. -/
noncomputable def iotaKernel (hφ : Function.Injective φ) :
    ↥((Work.CFT.IdeleClassGroup.normMap A).ker) →+
      ↥((Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker) :=
  (((iota φ A hφ (oneCoset φ)).comp (AddSubgroup.subtype _)).codRestrict
    ((Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker)
    (fun a => iota_oneCoset_mem_ker φ A hφ a.2))

lemma iotaKernel_apply (hφ : Function.Injective φ)
    (a : ↥((Work.CFT.IdeleClassGroup.normMap A).ker)) :
    (iotaKernel φ A hφ a).1 = iota φ A hφ (oneCoset φ) a.1 := rfl

/-- The comparison map on the kernels of the norm maps: `a ↦ [iota q₀ a]`. -/
noncomputable def hm1Map (hφ : Function.Injective φ) :
    ↥((Work.CFT.IdeleClassGroup.normMap A).ker) →+
      Hm1Quotient (Rep.coind φ A) :=
  (QuotientAddGroup.mk' (Hm1Sub (Rep.coind φ A))).comp (iotaKernel φ A hφ)

lemma hm1Map_apply (hφ : Function.Injective φ)
    (a : ↥((Work.CFT.IdeleClassGroup.normMap A).ker)) :
    hm1Map φ A hφ a = QuotientAddGroup.mk' (Hm1Sub (Rep.coind φ A)) (iotaKernel φ A hφ a) :=
  rfl

/-- `hm1Map` is surjective. -/
lemma hm1Map_surjective (hφ : Function.Injective φ) : Function.Surjective (hm1Map φ A hφ) := by
  intro g
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (Hm1Sub (Rep.coind φ A)) g
  refine ⟨⟨evalSum φ A y.1, evalSum_mem_ker φ A hφ y.2⟩, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [mem_Hm1Sub]
  show iota φ A hφ (oneCoset φ) (evalSum φ A y.1) - y.1 ∈ augIdeal (Rep.coind φ A)
  have h := evalSum_sub_mem_augIdeal φ A hφ y.1
  have h' : -(y.1 - iota φ A hφ (oneCoset φ) (evalSum φ A y.1))
      = iota φ A hφ (oneCoset φ) (evalSum φ A y.1) - y.1 := by abel
  rw [← h']
  exact AddSubgroup.neg_mem (augIdeal (Rep.coind φ A)) h

/-- The kernel of `hm1Map` is the augmentation subgroup of `ker N_A`, i.e. `I_A`. -/
lemma hm1Map_ker (hφ : Function.Injective φ) : (hm1Map φ A hφ).ker = Hm1Sub A := by
  ext a
  rw [AddMonoidHom.mem_ker, mem_Hm1Sub]
  constructor
  · intro h
    have h2 : (⟨iota φ A hφ (oneCoset φ) a.1, iota_oneCoset_mem_ker φ A hφ a.2⟩ :
        ↥((Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker))
        - 0 ∈ Hm1Sub (Rep.coind φ A) := QuotientAddGroup.eq_iff_sub_mem.mp h
    rw [sub_zero, mem_Hm1Sub] at h2
    rw [← evalSum_iota φ A hφ (oneCoset φ) a.1]
    exact evalSum_augIdeal_le φ A hφ h2
  · intro ha
    have h2 : (⟨iota φ A hφ (oneCoset φ) a.1, iota_oneCoset_mem_ker φ A hφ a.2⟩ :
        ↥((Work.CFT.IdeleClassGroup.normMap (Rep.coind φ A)).ker))
        ∈ Hm1Sub (Rep.coind φ A) := by
      rw [mem_Hm1Sub]
      exact iota_augIdeal_le φ A hφ ha
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by rw [sub_zero]; exact h2)

/-- **Shapiro's lemma for `Ĥ⁻¹`**: the kernels of the norm maps modulo the augmentation
subgroups of `A` and of `coind φ A` are isomorphic. -/
noncomputable def Hm1Quotient_coind (hφ : Function.Injective φ) :
    ↥((Work.CFT.IdeleClassGroup.normMap A).ker) ⧸ Hm1Sub A ≃+
      Hm1Quotient (Rep.coind φ A) :=
  (hm1Map_ker φ A hφ) ▸ QuotientAddGroup.quotientKerEquivOfSurjective (hm1Map φ A hφ)
    (hm1Map_surjective φ A hφ)

theorem Hm1Quotient_coind_nonempty (hφ : Function.Injective φ) :
    Nonempty (Hm1Quotient A ≃+ Hm1Quotient (Rep.coind φ A)) :=
  ⟨Hm1Quotient_coind φ A hφ⟩

theorem card_Hm1Quotient_coind (hφ : Function.Injective φ) :
    Nat.card (Hm1Quotient (Rep.coind φ A)) = Nat.card (Hm1Quotient A) :=
  (Nat.card_congr (Hm1Quotient_coind φ A hφ).toEquiv).symm

end QuotientIso

end Main

end

end Work.CFT.Ledger
