
/-
# Descent of finite generation along `k[H] → k[G]`

This file contains the technical heart of the transfer
`coherence of k[G] ⟹ FP₂ of a finitely generated subgroup H`.

Write `A = k[H]`, `B = k[G]` and fix a finite generating set `S` of `H`.  We consider

* `augMapA : A^S → A`, `e_s ↦ s - 1`, with kernel `N = ker augMapA`;
* `augMapB : B^S → B`, `e_s ↦ s - 1`, with kernel `K = ker augMapB`.

The two maps are related by the (coefficientwise) inclusion `θ : A^S → B^S`:
`augMapB ∘ θ = transferHom ∘ augMapA`, so that `θ` maps `N` into `K`.  The main result of the
file, `fg_ker_augMapA_of_fg_ker_augMapB`, is the converse descent: if `K` is finitely generated
over `B`, then `N` is finitely generated over `A`.  The proof uses the coset decomposition of
`k[G]` over `k[H]` (the projection `projH` and the decomposition `sum_coset_comp_eq_self`).
-/
import Mathlib
import Submission.Work.ORFP2.CosetProj
import Submission.Work.ORFP2.projH_transferHom
import Submission.Work.ORFP2.projH_mul_transferHom
import Submission.Work.ORFP2.eq_zero_of_sum_coset_eq_zero
import Submission.Work.ORFP2.sum_coset_comp_eq_self
import Submission.Work.ORFP2.range_augMapA_eq_augIdeal

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MonoidAlgebra

namespace Work.ORFP2

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-! ### The coefficientwise inclusion `A^S → B^S` and projection `B^S → A^S` -/

/-- The coefficientwise inclusion `A^S → B^S` induced by `transferHom : A → B`. -/
noncomputable def theta (G : Type*) [Group G] (H : Subgroup G) (S : Finset H) :
    (S →₀ MonoidAlgebra k H) →+ (S →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.addMonoidHom (transferHom k H).toRingHom.toAddMonoidHom

/-- The coefficientwise projection `B^S → A^S` induced by `projH`. -/
noncomputable def tau (G : Type*) [Group G] (H : Subgroup G) (S : Finset H) :
    (S →₀ MonoidAlgebra k G) →+ (S →₀ MonoidAlgebra k H) :=
  Finsupp.mapRange.addMonoidHom (projH_addHom k H)

@[simp]
lemma theta_apply (H : Subgroup G) (S : Finset H) (v : S →₀ MonoidAlgebra k H) (s : S) :
    theta k G H S v s = transferHom k H (v s) := by
  simp [theta, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply,
    MonoidAlgebra.mapDomainAlgHom_apply]

@[simp]
lemma tau_apply (H : Subgroup G) (S : Finset H) (w : S →₀ MonoidAlgebra k G) (s : S) :
    tau k G H S w s = projH k H (w s) := by
  simp [tau, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_apply]

lemma tau_theta (H : Subgroup G) (S : Finset H) (v : S →₀ MonoidAlgebra k H) :
    tau k G H S (theta k G H S v) = v := by
  ext s
  simp [projH_transferHom]

lemma theta_smul (H : Subgroup G) (S : Finset H) (c : MonoidAlgebra k H)
    (v : S →₀ MonoidAlgebra k H) :
    theta k G H S (c • v) = transferHom k H c • theta k G H S v := by
  ext s
  simp [Finsupp.smul_apply, smul_eq_mul, map_mul]

/-! ### The augmentation maps in coordinates -/

lemma augMapA_eq_sum (H : Type*) [Group H] (S : Finset H) (v : S →₀ MonoidAlgebra k H) :
    augMapA k H S v = ∑ s : S, v s * (MonoidAlgebra.single (s : H) (1 : k) - 1) := by
  rw [show augMapA k H S v
      = ∑ s : S, v s • (MonoidAlgebra.single (s : H) (1 : k) - 1) from by
    rw [augMapA, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype v (fun (s : ↥S) (a : MonoidAlgebra k H) =>
        a • (MonoidAlgebra.single (s : H) (1 : k) - 1)) (fun s => by rw [zero_smul])]]
  exact Finset.sum_congr rfl fun s _ => by rw [smul_eq_mul]

lemma augMapB_eq_sum (H : Subgroup G) (S : Finset H) (v : S →₀ MonoidAlgebra k G) :
    augMapB k G H S v
      = ∑ s : S, v s * (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by
  rw [show augMapB k G H S v
      = ∑ s : S, v s • (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) from by
    rw [augMapB, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype v (fun (s : ↥S) (a : MonoidAlgebra k G) =>
        a • (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1)) (fun s => by rw [zero_smul])]]
  exact Finset.sum_congr rfl fun s _ => by rw [smul_eq_mul]

lemma transferHom_single_sub_one (H : Subgroup G) (S : Finset H) (s : S) :
    transferHom k H (MonoidAlgebra.single (s : H) (1 : k) - 1)
      = MonoidAlgebra.single ((s : H) : G) (1 : k) - 1 := by
  rw [map_sub, map_one, transferHom_single]

lemma augMapB_theta (H : Subgroup G) (S : Finset H) (v : S →₀ MonoidAlgebra k H) :
    augMapB k G H S (theta k G H S v) = transferHom k H (augMapA k H S v) := by
  rw [augMapA_eq_sum, map_sum, augMapB_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [theta_apply, map_mul, transferHom_single_sub_one]

/-! ### The coset decomposition in coordinates -/

/-- `comp q x` vanishes when the coset `q` does not meet the support of `x`. -/
lemma comp_eq_zero_of_notMem_cosetSupport (H : Subgroup G) (x : MonoidAlgebra k G)
    {q : G ⧸ H} (hq : q ∉ cosetSupport k H x) : comp k H q x = 0 := by
  rw [comp, projH_eq_zero_iff]
  intro g hg
  rw [MonoidAlgebra.coeff_single_mul_apply]
  simp only [inv_inv, one_mul]
  by_contra h
  have hmem : q ∈ cosetSupport k H x := by
    have h1 : QuotientGroup.mk (Quotient.out q * (g : G)) ∈ cosetSupport k H x :=
      (mem_cosetSupport (k := k) (H := H) (x := x)).mpr
        ⟨Quotient.out q * (g : G), Finsupp.mem_support_iff.mpr h, rfl⟩
    have h2 : QuotientGroup.mk (Quotient.out q * (g : G)) = q :=
      (Quotient.sound (show QuotientGroup.leftRel H (Quotient.out q * (g : G)) (Quotient.out q) from by
        rw [QuotientGroup.leftRel_apply, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact H.inv_mem hg)).trans (Quotient.out_eq q)
    rwa [h2] at h1
  exact hq hmem

/-- The coordinatewise coset decomposition of `k[G]^S` over `k[H]^S`. -/
lemma theta_eq_sum_comp (H : Subgroup G) (S : Finset H) (t : S →₀ MonoidAlgebra k G)
    (Q : Finset (G ⧸ H)) (hQ : ∀ s : S, cosetSupport k H (t s) ⊆ Q) :
    (∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : k) •
        theta k G H S (Finsupp.equivFunOnFinite.symm (fun s => comp k H q (t s)))) = t := by
  classical
  apply Finsupp.ext
  intro s
  rw [Finsupp.finsetSum_apply (N := MonoidAlgebra k G) Q
    (fun q => MonoidAlgebra.single (Quotient.out q) (1 : k) •
        theta k G H S (Finsupp.equivFunOnFinite.symm (fun s => comp k H q (t s)))) s]
  have hterm : ∀ q : G ⧸ H, (MonoidAlgebra.single (Quotient.out q) (1 : k) •
        theta k G H S (Finsupp.equivFunOnFinite.symm (fun s => comp k H q (t s)))) s
      = MonoidAlgebra.single (Quotient.out q) (1 : k) * transferHom k H (comp k H q (t s)) := by
    intro q
    rw [Finsupp.smul_apply, smul_eq_mul, theta_apply]
    rfl
  refine (Finset.sum_congr rfl (fun q _ => hterm q)).trans
    ((Finset.sum_subset (hQ s) ?_).symm.trans ?_)
  · intro q _ hq
    simp [comp_eq_zero_of_notMem_cosetSupport k H (t s) hq]
  · exact sum_coset_comp_eq_self k H (t s)

/-- **Flatness of `k[G]` over `k[H]`.** -/
lemma exists_flat_witnesses (H : Subgroup G) (S : Finset H) (t : S →₀ MonoidAlgebra k G)
    (ht : augMapB k G H S t = 0) :
    ∃ Y : Finset (S →₀ MonoidAlgebra k H),
      (∀ y ∈ Y, augMapA k H S y = 0) ∧
      t ∈ Submodule.span (MonoidAlgebra k G)
            (Set.range fun y : {z : S →₀ MonoidAlgebra k H // z ∈ Y} =>
              theta k G H S (y : S →₀ MonoidAlgebra k H)) := by
  classical
  set Q : Finset (G ⧸ H) := Finset.univ.biUnion (fun s : S => cosetSupport k H (t s)) with hQ
  set w : G ⧸ H → (S →₀ MonoidAlgebra k H) :=
    fun q => Finsupp.equivFunOnFinite.symm (fun s => comp k H q (t s)) with hw
  have hw_apply : ∀ q s, w q s = comp k H q (t s) := fun q s => rfl
  have hmain : ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : k) *
      transferHom k H (augMapA k H S (w q)) = 0 := by
    have h1 : ∀ q : G ⧸ H, MonoidAlgebra.single (Quotient.out q) (1 : k) *
        transferHom k H (augMapA k H S (w q))
        = ∑ s : S, MonoidAlgebra.single (Quotient.out q) (1 : k) *
            (transferHom k H (comp k H q (t s)) *
              (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1)) := by
      intro q
      rw [augMapA_eq_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hw_apply, map_mul, transferHom_single_sub_one]
    have hcs : ∀ s : S, (∑ q ∈ cosetSupport k H (t s),
          (MonoidAlgebra.single (Quotient.out q) (1 : k) *
            transferHom k H (comp k H q (t s))) *
              (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1))
        = ∑ q ∈ Q, (MonoidAlgebra.single (Quotient.out q) (1 : k) *
            transferHom k H (comp k H q (t s))) *
              (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by
      intro s
      refine Finset.sum_subset ?_ ?_
      · intro q hq
        exact Finset.subset_biUnion_of_mem (fun s : S => cosetSupport k H (t s))
          (Finset.mem_univ s) hq
      · intro q _ hq
        simp [comp_eq_zero_of_notMem_cosetSupport k H (t s) hq]
    have h2 : (∑ q ∈ Q, ∑ s : S, MonoidAlgebra.single (Quotient.out q) (1 : k) *
            (transferHom k H (comp k H q (t s)) *
              (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1)))
        = ∑ s : S, t s * (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      calc ∑ q ∈ Q, MonoidAlgebra.single (Quotient.out q) (1 : k) *
              (transferHom k H (comp k H q (t s)) *
                (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1))
          = ∑ q ∈ Q, (MonoidAlgebra.single (Quotient.out q) (1 : k) *
              transferHom k H (comp k H q (t s))) *
                (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) :=
            Finset.sum_congr rfl fun q _ => (mul_assoc _ _ _).symm
        _ = ∑ q ∈ cosetSupport k H (t s), (MonoidAlgebra.single (Quotient.out q) (1 : k) *
              transferHom k H (comp k H q (t s))) *
                (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := (hcs s).symm
        _ = (∑ q ∈ cosetSupport k H (t s), MonoidAlgebra.single (Quotient.out q) (1 : k) *
              transferHom k H (comp k H q (t s))) *
                (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by rw [Finset.sum_mul]
        _ = t s * (MonoidAlgebra.single ((s : H) : G) (1 : k) - 1) := by
              rw [sum_coset_comp_eq_self k H (t s)]
    rw [← ht, augMapB_eq_sum, ← h2]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have hb : ∀ q ∈ Q, augMapA k H S (w q) = 0 :=
    eq_zero_of_sum_coset_eq_zero k H Q (fun q => augMapA k H S (w q)) hmain
  refine ⟨Q.image w, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hb q hq
  · rw [← theta_eq_sum_comp k H S t Q
        (fun s => Finset.subset_biUnion_of_mem (fun s : S => cosetSupport k H (t s))
          (Finset.mem_univ s))]
    refine Submodule.sum_mem _ fun q hq => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨w q, Finset.mem_image_of_mem w hq⟩, rfl⟩

/-! ### The descent -/

lemma tau_smul_single_theta (H : Subgroup G) (S : Finset H) (g : G)
    (z : S →₀ MonoidAlgebra k H) :
    tau k G H S (MonoidAlgebra.single g (1 : k) • theta k G H S z)
      = projH k H (MonoidAlgebra.single g (1 : k)) • z := by
  ext s
  simp only [tau_apply, Finsupp.smul_apply, smul_eq_mul, theta_apply, projH_mul_transferHom]

/-- `tau` of a `B`-multiple of `theta y` lies in the `A`-span of `y`. -/
lemma tau_smul_theta_mem (H : Subgroup G) (S : Finset H) (c : MonoidAlgebra k G)
    (y : S →₀ MonoidAlgebra k H) :
    tau k G H S (c • theta k G H S y)
      ∈ Submodule.span (MonoidAlgebra k H) ({y} : Set (S →₀ MonoidAlgebra k H)) := by
  classical
  rw [← sum_coset_comp_eq_self k H c, Finset.sum_smul, map_sum]
  refine Submodule.sum_mem _ fun q hq => ?_
  rw [mul_smul, ← theta_smul, tau_smul_single_theta]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton y)))

/-- **Descent of finite generation.** -/
theorem fg_ker_augMapA_of_fg_ker_augMapB (H : Subgroup G) (S : Finset H)
    (hK : (LinearMap.ker (augMapB k G H S)).FG) :
    (LinearMap.ker (augMapA k H S)).FG := by
  classical
  obtain ⟨T, hT⟩ := hK
  have hwit : ∀ t : S →₀ MonoidAlgebra k G, t ∈ T → ∃ Y : Finset (S →₀ MonoidAlgebra k H),
      (∀ y ∈ Y, augMapA k H S y = 0) ∧
      t ∈ Submodule.span (MonoidAlgebra k G)
            (Set.range fun y : {z : S →₀ MonoidAlgebra k H // z ∈ Y} =>
              theta k G H S (y : S →₀ MonoidAlgebra k H)) := by
    intro t ht
    refine exists_flat_witnesses k H S t ?_
    exact LinearMap.mem_ker.mp (by rw [← hT]; exact Submodule.subset_span ht)
  choose Y hYsub hYmem using hwit
  set YY : Finset (S →₀ MonoidAlgebra k H) := T.attach.biUnion (fun t => Y t.1 t.2) with hYY
  have hsub : ∀ t ∈ T, t ∈ Submodule.span (MonoidAlgebra k G)
      (Set.range fun y : {z : S →₀ MonoidAlgebra k H // z ∈ YY} =>
        theta k G H S (y : S →₀ MonoidAlgebra k H)) := by
    intro t ht
    refine Submodule.span_mono ?_ (hYmem t ht)
    rintro z ⟨y, rfl⟩
    exact ⟨⟨y, Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, y.2⟩⟩, rfl⟩
  have hspan : LinearMap.ker (augMapB k G H S) ≤ Submodule.span (MonoidAlgebra k G)
      (Set.range fun y : {z : S →₀ MonoidAlgebra k H // z ∈ YY} =>
        theta k G H S (y : S →₀ MonoidAlgebra k H)) := by
    rw [← hT]
    exact Submodule.span_le.mpr (fun x hx => hsub x hx)
  have hN : LinearMap.ker (augMapA k H S)
      = Submodule.span (MonoidAlgebra k H) (YY : Set (S →₀ MonoidAlgebra k H)) := by
    refine le_antisymm ?_ ?_
    · intro n hn
      have hnK : theta k G H S n ∈ LinearMap.ker (augMapB k G H S) := by
        rw [LinearMap.mem_ker, augMapB_theta, LinearMap.mem_ker.mp hn, map_zero]
      have hmem := hspan hnK
      rw [← Finsupp.range_linearCombination (MonoidAlgebra k G)
            (v := fun y : {z : S →₀ MonoidAlgebra k H // z ∈ YY} =>
              theta k G H S (y : S →₀ MonoidAlgebra k H))] at hmem
      obtain ⟨c, hc⟩ := hmem
      rw [← tau_theta k H S n, ← hc, Finsupp.linearCombination_apply]
      rw [show c.sum (fun i a => a • theta k G H S (i : S →₀ MonoidAlgebra k H))
            = ∑ i ∈ c.support, c i • theta k G H S (i : S →₀ MonoidAlgebra k H) from rfl]
      rw [map_sum]
      refine Submodule.sum_mem _ fun y hy => ?_
      refine Submodule.span_mono ?_ (tau_smul_theta_mem k H S (c y) (y : S →₀ MonoidAlgebra k H))
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact y.2
    · rw [Submodule.span_le]
      rintro y hy
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      obtain ⟨t, ht, hy'⟩ := Finset.mem_biUnion.mp hy
      exact hYsub t.1 t.2 y hy'
  rw [hN]
  exact Submodule.fg_span (YY.finite_toSet)

end Work.ORFP2
