/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# `H¹(S¹; ℚ) ≅ ℚ`

The circle is covered by the two open caps `capPlus 0`, `capMinus 0` of `S¹` (contractible, hence
acyclic in positive degrees) whose intersection is the doubly punctured circle `DPset 0`, homotopy
equivalent to `S⁰`.  The associated Mayer–Vietoris sequence of
`Submission/Work/Sphere/Suspension.lean` reads

`H⁰(A) ⊕ H⁰(B) →^{β} H⁰(A ∩ B) →^{δ} H¹(small) → 0`

with `H⁰(A) ≅ H⁰(B) ≅ H⁰(small) ≅ ℚ` and `H⁰(A ∩ B) ≅ H⁰(S⁰) ≅ ℚ ⊕ ℚ`.  Since the image of `β`
is one-dimensional (it is the image of a map out of `ℚ ⊕ ℚ` with one-dimensional kernel, as
`H⁰(small) → H⁰(A) ⊕ H⁰(B)` is injective with one-dimensional image), `H¹(small) ≅
H⁰(A∩B)/im β` is a quotient of the two-dimensional space `H⁰(A∩B) ≅ ℚ × ℚ` by a one-dimensional
subspace, hence isomorphic to `ℚ`.  Finally the small-simplex theorem identifies
`H¹(small) ≅ H¹(S¹)`.
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Sphere.H_sph_zero
import Submission.Work.Sphere.pathConnected_sph
import Submission.Work.Cohomology.H_zero_connected
import Submission.Work.Cohomology.mvAlphaH_ker_eq_range
import Submission.Work.Cohomology.mvBetaH_ker_eq_range
import Submission.Work.Cohomology.mvConnecting_ker_eq_range

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-! ## Elementary linear algebra

* a nonzero element of a space isomorphic to `ℚ` spans it;
* in a space isomorphic to `ℚ²`, the quotient by the span of a nonzero element is `ℚ`. -/

lemma ker_eq_span_pair {a b x y : ℚ} (hab : (a, b) ≠ 0) (h : b * x = a * y) :
    (x, y) ∈ Submodule.span ℚ ({(a, b)} : Set (ℚ × ℚ)) := by
  rw [Submodule.mem_span_singleton]
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb; exact hab (by ext <;> simp [ha, hb])
    have hx : x = 0 := by
      have h' : b * x = 0 := by rw [h, ha]; ring
      exact (mul_eq_zero.mp h').resolve_left hb
    refine ⟨y / b, ?_⟩
    ext
    · simp [ha, hx]
    · simp only [Prod.smul_snd, ha, smul_eq_mul]
      field_simp
  · refine ⟨x / a, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith [h]

lemma psi_ne_zero {a b : ℚ} (hab : (a, b) ≠ 0) :
    (b • LinearMap.fst ℚ ℚ ℚ - a • LinearMap.snd ℚ ℚ ℚ : ℚ × ℚ →ₗ[ℚ] ℚ) ≠ 0 := by
  intro h
  have h1 : b = 0 := by
    have := congrArg (fun (g : ℚ × ℚ →ₗ[ℚ] ℚ) => g (1, 0)) h
    simpa using this
  have h2 : a = 0 := by
    have := congrArg (fun (g : ℚ × ℚ →ₗ[ℚ] ℚ) => g (0, 1)) h
    simpa using this
  exact hab (by ext <;> simp [h1, h2])

lemma quot_span_singleton_rat {V : Type*} [AddCommGroup V] [Module ℚ V]
    (e : V ≃ₗ[ℚ] ℚ × ℚ) (w : V) (hw : w ≠ 0) :
    Nonempty ((V ⧸ Submodule.span ℚ ({w} : Set V)) ≃ₗ[ℚ] ℚ) := by
  have hp0 : e w ≠ 0 := fun h => hw (e.injective (by rw [h]; simp))
  have hab : ((e w).1, (e w).2) ≠ 0 := by
    intro h
    exact hp0 (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let ψ : ℚ × ℚ →ₗ[ℚ] ℚ := (e w).2 • LinearMap.fst ℚ ℚ ℚ - (e w).1 • LinearMap.snd ℚ ℚ ℚ
  have hψ0 : ψ (e w) = 0 := by
    show (e w).2 * (e w).1 - (e w).1 * (e w).2 = 0
    ring
  have hker : LinearMap.ker ψ = Submodule.span ℚ ({(e w)} : Set (ℚ × ℚ)) := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv
      have hv'' : (e w).2 * v.1 - (e w).1 * v.2 = 0 := by
        simpa [ψ, LinearMap.fst, LinearMap.snd] using hv
      exact ker_eq_span_pair hab (sub_eq_zero.mp hv'')
    · intro v hv
      rw [LinearMap.mem_ker]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp only [map_smul, hψ0, smul_zero]
  let φ : V →ₗ[ℚ] ℚ :=
    { toFun := fun v => ψ (e v)
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by intro c x; simp only [map_smul, RingHom.id_apply] }
  have hφval : ∀ v : V, φ v = ψ (e v) := fun v => rfl
  have hφker : LinearMap.ker φ = Submodule.span ℚ ({w} : Set V) := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv
      have hev : e v ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker, ← hφval v]
        exact hv
      rw [hker, Submodule.mem_span_singleton] at hev
      obtain ⟨c, hc⟩ := hev
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      apply e.injective
      rw [map_smul, hc]
    · intro v hv
      rw [LinearMap.mem_ker, hφval]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp only [map_smul, hψ0, smul_zero]
  have hφne : φ ≠ 0 := by
    intro h
    apply psi_ne_zero hab
    apply LinearMap.ext
    intro y
    have h1 : φ (e.symm y) = 0 := by rw [h]; rfl
    rw [hφval, e.apply_symm_apply] at h1
    exact h1
  have hsurj : Function.Surjective φ := by
    obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      apply hφne
      ext x
      by_contra hx
      exact (h ⟨x, hx⟩).elim
    intro r
    exact ⟨(r / φ x₀) • x₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx₀]⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hφker).symm.trans (LinearMap.quotKerEquivOfSurjective φ hsurj)⟩

lemma span_singleton_eq_top_of_equiv {V : Type*} [AddCommGroup V] [Module ℚ V]
    (e : V ≃ₗ[ℚ] ℚ) {w : V} (hw : w ≠ 0) : Submodule.span ℚ ({w} : Set V) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hew : e w ≠ 0 := fun h => hw (e.injective (by rw [h, map_zero]))
  rw [Submodule.mem_span_singleton]
  refine ⟨e x / e w, ?_⟩
  apply e.injective
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hew]

lemma span_singleton_eq_of_equiv {V : Type*} [AddCommGroup V] [Module ℚ V]
    {p : Submodule ℚ V} (e : p ≃ₗ[ℚ] ℚ) {w : V} (hw : w ∈ p) (hw0 : w ≠ 0) :
    Submodule.span ℚ ({w} : Set V) = p := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hw
  · intro x hx
    have hew : e ⟨w, hw⟩ ≠ 0 := by
      intro h
      have h2 : (⟨w, hw⟩ : p) = 0 := by
        apply e.injective
        rw [h, map_zero]
      exact hw0 (congrArg Subtype.val h2)
    rw [Submodule.mem_span_singleton]
    refine ⟨e ⟨x, hx⟩ / e ⟨w, hw⟩, ?_⟩
    have h1 : (⟨(e ⟨x, hx⟩ / e ⟨w, hw⟩) • w, p.smul_mem _ hw⟩ : p) = ⟨x, hx⟩ := by
      apply e.injective
      show e ((e ⟨x, hx⟩ / e ⟨w, hw⟩) • (⟨w, hw⟩ : p)) = e ⟨x, hx⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hew]
    exact Subtype.ext_iff.mp h1

/-! ## `H⁰` of the caps and of the small complex -/

theorem contr_capPlus : ContractibleSpace ↥(Submission.Sphere.capPlus 0) :=
  Eq.mp (congrArg (fun s : Set ↥(Submission.Sphere.Sph 1) => ContractibleSpace ↥s)
      (Submission.Sphere.capPlus_eq 0).symm)
    (Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := 1)
      (Submission.Sphere.polePt 1)))

theorem contr_capMinus : ContractibleSpace ↥(Submission.Sphere.capMinus 0) :=
  Eq.mp (congrArg (fun s : Set ↥(Submission.Sphere.Sph 1) => ContractibleSpace ↥s)
      (Submission.Sphere.capMinus_eq 0).symm)
    (Classical.choice (Work.Sphere.contractibleSpace_sph_compl (n := 1)
      (Submission.Sphere.negPolePt 1)))

theorem H_capAsub_zero : Nonempty (H (Submission.Sphere.capAsub 0) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  haveI : PathConnectedSpace ↥(Submission.Sphere.capPlus 0) := by
    haveI := contr_capPlus; infer_instance
  have e1 : H (Submission.Sphere.capAsub 0) ℚ 0
      ≃ₗ[ℚ] H (Submission.Sphere.capPlusSub 0) ℚ 0 :=
    Classical.choice (Submission.Sphere.H_iso_of_iso
      (Submission.Sphere.preimageIso (Submission.Sphere.smallSub 0)
        (Submission.Sphere.capPlusSub 0) le_sup_left) 0)
  have e2 : H (Submission.Sphere.capPlusSub 0) ℚ 0
      ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopCat.of ↥(Submission.Sphere.capPlus 0))) ℚ 0 :=
    Classical.choice (Submission.Sphere.H_iso_of_iso
      (Classical.choice (Work.Cohomology.singIn_iso (Submission.Sphere.Sph 1)
        (Submission.Sphere.capPlus 0))) 0)
  exact ⟨e1.trans (e2.trans (Classical.choice (Work.Cohomology.H_zero_connected
    (TopCat.of ↥(Submission.Sphere.capPlus 0)))))⟩

theorem H_capBsub_zero : Nonempty (H (Submission.Sphere.capBsub 0) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  haveI : PathConnectedSpace ↥(Submission.Sphere.capMinus 0) := by
    haveI := contr_capMinus; infer_instance
  have e1 : H (Submission.Sphere.capBsub 0) ℚ 0
      ≃ₗ[ℚ] H (Submission.Sphere.capMinusSub 0) ℚ 0 :=
    Classical.choice (Submission.Sphere.H_iso_of_iso
      (Submission.Sphere.preimageIso (Submission.Sphere.smallSub 0)
        (Submission.Sphere.capMinusSub 0) le_sup_right) 0)
  have e2 : H (Submission.Sphere.capMinusSub 0) ℚ 0
      ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopCat.of ↥(Submission.Sphere.capMinus 0))) ℚ 0 :=
    Classical.choice (Submission.Sphere.H_iso_of_iso
      (Classical.choice (Work.Cohomology.singIn_iso (Submission.Sphere.Sph 1)
        (Submission.Sphere.capMinus 0))) 0)
  exact ⟨e1.trans (e2.trans (Classical.choice (Work.Cohomology.H_zero_connected
    (TopCat.of ↥(Submission.Sphere.capMinus 0)))))⟩

theorem H_smallSub_zero : Nonempty (H (Submission.Sphere.smallSub 0) ℚ 0 ≃ₗ[ℚ] ℚ) := by
  haveI : PathConnectedSpace ↥(Submission.Sphere.Sph 1) :=
    Work.Sphere.pathConnected_sph 1 le_rfl
  have e1 : H (Submission.Sphere.smallSub 0) ℚ 0 ≃ₗ[ℚ] H (Submission.Sphere.singSph 1) ℚ 0 :=
    Submission.Sphere.smallSphereIso 0 0
  exact ⟨e1.trans (Classical.choice (Work.Cohomology.H_zero_connected
    (Submission.Sphere.Sph 1)))⟩

theorem H_capCsub_zero :
    Nonempty (H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ) := by
  have e0 : H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0
      ≃ₗ[ℚ] H (Submission.Sphere.capCsub 0) ℚ 0 := Submission.Sphere.capCIso 0 0
  have e1 := Submission.Sphere.capPrimeIso 0 0
  have e2 := Submission.Sphere.dpSpaceIso 0 0
  have e3 := Submission.Sphere.dpSphereIso 0 0
  have e4 : H (Submission.Sphere.singSph 0) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ := (Work.Sphere.H_sph_zero).2.some
  exact ⟨e0.trans (e1.trans (e2.trans (e3.trans e4)))⟩

/-! ## The main theorem -/

theorem H_one_circle :
    Nonempty (Submission.Cohomology.H (Submission.Sphere.singSph 1) ℚ 1 ≃ₗ[ℚ] ℚ) := by
  have hAB : Submission.Sphere.capAsub 0 ⊔ Submission.Sphere.capBsub 0 = ⊤ :=
    Submission.Sphere.capAsub_sup_capBsub 0
  obtain ⟨hS⟩ : Nonempty (H (Submission.Sphere.smallC 0) ℚ 0 ≃ₗ[ℚ] ℚ) := H_smallSub_zero
  obtain ⟨hA⟩ : Nonempty (H (Submission.Sphere.capAsub 0) ℚ 0 ≃ₗ[ℚ] ℚ) := H_capAsub_zero
  obtain ⟨hB⟩ : Nonempty (H (Submission.Sphere.capBsub 0) ℚ 0 ≃ₗ[ℚ] ℚ) := H_capBsub_zero
  obtain ⟨eAB⟩ : Nonempty (H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
      (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ) := H_capCsub_zero
  have hsurj : Function.Surjective (mvConnecting (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0) :=
    Work.Cohomology.mvConnecting_surjective _ _ _ hAB 0
      (Submission.Sphere.subsingleton_H_capAsub 0 1 (by norm_num))
      (Submission.Sphere.subsingleton_H_capBsub 0 1 (by norm_num))
  have hkerδ := Work.Cohomology.mvConnecting_ker_eq_range (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
  have hkerβ := Work.Cohomology.mvBetaH_ker_eq_range (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
  have hαinj : Function.Injective (mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) :=
    mvAlphaH_injective_zero _ _ _ hAB
  let α := mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0
  let β := mvBetaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0
  let δ := mvConnecting (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
  -- y0
  let y0 : H (Submission.Sphere.smallC 0) ℚ 0 := hS.symm 1
  have hy0 : y0 ≠ 0 := by
    intro h
    have h2 : (1 : ℚ) = 0 := by
      rw [← LinearEquiv.apply_symm_apply hS 1, show hS.symm 1 = 0 from h, map_zero]
    exact one_ne_zero h2
  -- w'
  let w' : H (Submission.Sphere.capAsub 0) ℚ 0 × H (Submission.Sphere.capBsub 0) ℚ 0 := α y0
  have hw' : w' ≠ 0 := by
    intro h
    change α y0 = 0 at h
    exact hy0 (hαinj (by rw [h, map_zero]))
  have hspan : Submodule.span ℚ ({y0} : Set (H (Submission.Sphere.smallC 0) ℚ 0)) = ⊤ :=
    span_singleton_eq_top_of_equiv hS hy0
  have hrangeα : LinearMap.range α = Submodule.span ℚ ({w'} : Set _) := by
    rw [LinearMap.range_eq_map, ← hspan, Submodule.map_span]
    simp only [Set.image_singleton]
    rfl
  -- range β ≅ ℚ
  have hkerβ' : LinearMap.ker β = Submodule.span ℚ ({w'} : Set _) := by
    rw [show LinearMap.ker β = LinearMap.ker (mvBetaH (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) from rfl, hkerβ]
    exact hrangeα
  have heAB2 : (H (Submission.Sphere.capAsub 0) ℚ 0 × H (Submission.Sphere.capBsub 0) ℚ 0)
      ≃ₗ[ℚ] (ℚ × ℚ) := hA.prodCongr hB
  obtain ⟨eQ1⟩ : Nonempty (((H (Submission.Sphere.capAsub 0) ℚ 0 ×
      H (Submission.Sphere.capBsub 0) ℚ 0) ⧸ Submodule.span ℚ ({w'} : Set _)) ≃ₗ[ℚ] ℚ) :=
    quot_span_singleton_rat heAB2 w' hw'
  have eRange : (LinearMap.range β) ≃ₗ[ℚ] ℚ :=
    (LinearMap.quotKerEquivRange β).symm.trans ((Submodule.quotEquivOfEq _ _ hkerβ').trans eQ1)
  let w : H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
      (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 := (eRange.symm 1 : LinearMap.range β)
  have hwmem : w ∈ LinearMap.range β := (eRange.symm 1).2
  have hwne : w ≠ 0 := by
    intro h
    have h1 : eRange (eRange.symm 1) = 0 := by
      have hz : eRange.symm 1 = 0 := by
        apply Subtype.ext
        exact h
      rw [hz, map_zero]
    rw [LinearEquiv.apply_symm_apply] at h1
    exact one_ne_zero h1
  have hspw : Submodule.span ℚ ({w} : Set _) = LinearMap.range β :=
    span_singleton_eq_of_equiv eRange hwmem hwne
  obtain ⟨eQ2⟩ : Nonempty (((H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
      (Submission.Sphere.smallC 0).Subcomplex) ℚ 0) ⧸
      Submodule.span ℚ ({w} : Set _)) ≃ₗ[ℚ] ℚ) :=
    quot_span_singleton_rat eAB w hwne
  have hδker : LinearMap.ker δ = Submodule.span ℚ ({w} : Set _) := by
    rw [show LinearMap.ker δ = LinearMap.ker (mvConnecting (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0) from rfl, hkerδ]
    exact hspw.symm
  have h1 : H (Submission.Sphere.smallC 0) ℚ 1 ≃ₗ[ℚ]
      (H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ⧸ LinearMap.ker δ) :=
    (LinearMap.quotKerEquivOfSurjective δ hsurj).symm
  have h2 : (H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ⧸ LinearMap.ker δ) ≃ₗ[ℚ]
      (H (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ⧸ Submodule.span ℚ ({w} : Set _)) :=
    Submodule.quotEquivOfEq _ _ hδker
  exact ⟨(Submission.Sphere.smallSphereIso 0 1).symm.trans (h1.trans (h2.trans eQ2))⟩

end

end Work.Sphere
