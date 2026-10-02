import Mathlib
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Koszul differential of the tensor product, in components

`Work.Kunneth.tpD C K n` is the Koszul differential `x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y` of the
tensor product of two chain complexes of `ℤ`-modules (`Submission/Work/Kunneth/TensorDefs.lean`),
defined as the sum `DirectSum.toModule ℤ (tpIdx (n+1)) (tpX C K n) (tpDpq C K n)` of its bidegree
summands `tpDpq`.  The element of the direct sum `tpX C K (n+1) = ⨁_{p+q=n+1} C_p ⊗ K_q` is a
"matrix" of tensor products, and this file records the resulting **component formula**: the
`(p,q)`-component of `tpD C K n x` (`p + q = n`) only involves the two matrix entries that map to
the `(p,q)` summand, namely the `(p, q+1)`-entry (hit by `1 ⊗ d_K`) and the `(p+1, q)`-entry (hit
by `d_C ⊗ 1`, with the Koszul sign `(-1)^p` from `tpDpq`):

`(tpD C K n x) rs = (-1)^p • (1 ⊗ d_K)(x (p, q+1)) + (d_C ⊗ 1)(x (p+1, q))`.

This is the ingredient a colleague needs (`Work.Serre.tpDApplyComp`, see the bottom of the file)
to evaluate the Koszul differential in the Eilenberg–Zilber / Künneth machinery.

## A note on instances

As in the rest of the `Work.Kunneth` chapter, the generic `AddCommGroup.toIntModule` instance is
removed, so that typeclass search picks the scalar structures (`DirectSum.instModule`,
`ModuleCat.isModule`) that the definitions in that chapter were elaborated with.  Statements
written in this file are *definitionally identical* with and without that line (it only changes
which of several propositionally equal instances typeclass search finds while proving).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct
open Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## 1. Elementary facts about the direct sum -/

/-- The structure maps of the direct sum reconstruct an element: `∑ j, tpLof j (z j) = z`. -/
theorem tpX_sum_lof (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (z : tpX C K n) :
    ∑ j : tpIdx n, tpLof C K n j (z j) = z := by
  apply DirectSum.ext
  intro k
  rw [← DirectSum.coeFnLinearMap_apply (R := ℤ)
    (v := ∑ j : tpIdx n, tpLof C K n j (z j))]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · simp only [DirectSum.coeFnLinearMap_apply, DirectSum.lof_apply]
  · intro j _ hj
    change DirectSum.component ℤ (tpIdx n)
      (fun rs => tpSummand C K rs.1.1 rs.1.2) k
        (DirectSum.lof ℤ (tpIdx n)
          (fun rs => tpSummand C K rs.1.1 rs.1.2) j (z j)) = 0
    rw [DirectSum.component.of]
    simp [hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- A summand generator has zero component away from its own index. -/
theorem lof_apply_eq_zero {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)] {i j : ι} (h : i ≠ j) (b : M i) :
    ((DirectSum.lof ℤ ι M i) b) j = 0 := by
  change DirectSum.component ℤ ι M j (DirectSum.lof ℤ ι M i b) = 0
  rw [DirectSum.component.of, dif_neg h]

/-- The `ℤ`-action on a direct sum is pointwise, in the `ZSMul`-derived form used by the
definitions of the `Work.Kunneth` chapter. -/
theorem zsmul_ds_apply {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (c : ℤ) (v : DirectSum ι M) (i : ι) : (c • v) i = c • v i := rfl

/-! ## 2. The two surviving matrix entries -/

/-- **The `(p, q+1)`-entry.**  The component in bidegree `(p,q)` of the Koszul differential of the
generator placed in bidegree `(p, q+1)` is `(-1)^p` times `1 ⊗ d_K`. -/
theorem tpD_tpLof_snd (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (rs : tpIdx n)
    (z : tpSummand C K rs.1.1 (rs.1.2 + 1)) :
    (tpD C K n (tpLof C K (n+1) ⟨(rs.1.1, rs.1.2 + 1), by omega⟩ z)) rs
      = (-1 : ℤ) ^ rs.1.1 •
          (TensorProduct.map LinearMap.id ((K.d (rs.1.2 + 1) rs.1.2).hom) z) := by
  have hBkey : (((-1 : ℤ) ^ (rs.1.1)) •
      (((tpLof C K n (⟨(rs.1.1, rs.1.2 + 1 - 1), by omega⟩ : tpIdx n)) ∘ₗ
        (TensorProduct.map LinearMap.id
          (ModuleCat.Hom.hom (K.d (rs.1.2 + 1) (rs.1.2 + 1 - 1))))) z)) rs
      = (-1 : ℤ) ^ rs.1.1 •
        (TensorProduct.map LinearMap.id ((K.d (rs.1.2 + 1) rs.1.2).hom) z) := by
    rw [zsmul_ds_apply, LinearMap.comp_apply]
    congr 1
    exact DirectSum.lof_apply ℤ (ι := tpIdx n) (M := fun rs => tpSummand C K rs.1.1 rs.1.2) rs
      ((TensorProduct.map LinearMap.id
        (ModuleCat.Hom.hom (K.d (rs.1.2 + 1) (rs.1.2 + 1 - 1)))) z)
  rw [tpD, DirectSum.toModule_lof, tpDpq]
  simp only [LinearMap.add_apply]
  split_ifs with hp hq
  · rw [DirectSum.add_apply, smul_lmap_apply]
    have hneA : (⟨(rs.1.1 - 1, rs.1.2 + 1), by omega⟩ : tpIdx n) ≠ rs := by
      intro h
      have h2 : rs.1.2 + 1 = rs.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
      exact Nat.succ_ne_self rs.1.2 h2
    have hA : (((tpLof C K n (⟨(rs.1.1 - 1, rs.1.2 + 1), by omega⟩ : tpIdx n)) ∘ₗ
        (TensorProduct.map (ModuleCat.Hom.hom (C.d (rs.1.1) (rs.1.1 - 1))) LinearMap.id)) z) rs
        = 0 := by
      rw [LinearMap.comp_apply]
      exact lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hneA _
    erw [hA, hBkey, zero_add]
  · exfalso; omega
  · rw [DirectSum.add_apply, smul_lmap_apply, LinearMap.zero_apply,
      DFinsupp.zero_apply, zero_add]
    exact hBkey
  · exfalso; omega

/-- **The `(p+1, q)`-entry.**  The component in bidegree `(p,q)` of the Koszul differential of the
generator placed in bidegree `(p+1, q)` is `d_C ⊗ 1`. -/
theorem tpD_tpLof_fst (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (rs : tpIdx n)
    (z : tpSummand C K (rs.1.1 + 1) rs.1.2) :
    (tpD C K n (tpLof C K (n+1) ⟨(rs.1.1 + 1, rs.1.2), by omega⟩ z)) rs
      = TensorProduct.map ((C.d (rs.1.1 + 1) rs.1.1).hom) LinearMap.id z := by
  rw [tpD, DirectSum.toModule_lof, tpDpq]
  simp only [LinearMap.add_apply]
  split_ifs with hp hq
  · rw [DirectSum.add_apply, smul_lmap_apply, LinearMap.comp_apply]
    have hA : ((tpLof C K n (⟨(rs.1.1 + 1 - 1, rs.1.2), by omega⟩ : tpIdx n))
        ((TensorProduct.map
          (ModuleCat.Hom.hom (C.d (rs.1.1+1) (rs.1.1+1-1))) LinearMap.id) z)) rs
        = (TensorProduct.map (ModuleCat.Hom.hom (C.d (rs.1.1 + 1) rs.1.1)) LinearMap.id) z :=
      DirectSum.lof_apply ℤ (ι := tpIdx n) (M := fun rs => tpSummand C K rs.1.1 rs.1.2) rs
        ((TensorProduct.map
          (ModuleCat.Hom.hom (C.d (rs.1.1+1) (rs.1.1+1-1))) LinearMap.id) z)
    have hne : (⟨(rs.1.1 + 1, rs.1.2 - 1), by omega⟩ : tpIdx n) ≠ rs := by
      intro h
      have h2 : rs.1.1 + 1 = rs.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
      exact Nat.succ_ne_self rs.1.1 h2
    have hB : (((-1 : ℤ) ^ (rs.1.1 + 1)) •
        (((tpLof C K n (⟨(rs.1.1 + 1, rs.1.2 - 1), by omega⟩ : tpIdx n)) ∘ₗ
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom (K.d (rs.1.2) (rs.1.2 - 1))))) z)) rs = 0 := by
      rw [zsmul_ds_apply, LinearMap.comp_apply,
        lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hne, zsmul_zero]
    erw [hA, hB, add_zero]
  · rw [DirectSum.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      DFinsupp.zero_apply, add_zero]
    exact DirectSum.lof_apply ℤ (ι := tpIdx n) (M := fun rs => tpSummand C K rs.1.1 rs.1.2) rs
      ((TensorProduct.map (ModuleCat.Hom.hom (C.d (rs.1.1+1) (rs.1.1+1-1))) LinearMap.id) z)
  · exact absurd (show 1 ≤ rs.1.1 + 1 by omega) hp
  · exact absurd (show 1 ≤ rs.1.1 + 1 by omega) hp

/-- **All other entries die.**  A generator placed in a bidegree different from `(p, q+1)` and
`(p+1, q)` has zero component in bidegree `(p,q)`. -/
theorem tpD_tpLof_eq_zero (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (rs : tpIdx n)
    (pq : tpIdx (n + 1))
    (h1 : pq ≠ ⟨(rs.1.1, rs.1.2 + 1), by omega⟩)
    (h2 : pq ≠ ⟨(rs.1.1 + 1, rs.1.2), by omega⟩)
    (z : tpSummand C K pq.1.1 pq.1.2) :
    (tpD C K n (tpLof C K (n + 1) pq z)) rs = 0 := by
  rw [tpD, DirectSum.toModule_lof, tpDpq]
  simp only [LinearMap.add_apply]
  split_ifs with hp hq
  · rw [DirectSum.add_apply, smul_lmap_apply]
    have hA : (((tpLof C K n (⟨(pq.1.1 - 1, pq.1.2), by omega⟩ : tpIdx n)) ∘ₗ
        (TensorProduct.map (ModuleCat.Hom.hom (C.d (pq.1.1) (pq.1.1 - 1))) LinearMap.id)) z)
        rs = 0 := by
      have hneA : (⟨(pq.1.1 - 1, pq.1.2), by omega⟩ : tpIdx n) ≠ rs := by
        intro h
        have hf : pq.1.1 - 1 = rs.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
        have hs : pq.1.2 = rs.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
        apply h2
        apply Subtype.ext
        apply Prod.ext
        · show pq.1.1 = rs.1.1 + 1
          omega
        · exact hs
      rw [LinearMap.comp_apply]
      exact lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hneA _
    have hB : (((-1 : ℤ) ^ (pq.1.1)) •
        (((tpLof C K n (⟨(pq.1.1, pq.1.2 - 1), by omega⟩ : tpIdx n)) ∘ₗ
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom (K.d (pq.1.2) (pq.1.2 - 1))))) z)) rs = 0 := by
      have hneB : (⟨(pq.1.1, pq.1.2 - 1), by omega⟩ : tpIdx n) ≠ rs := by
        intro h
        have hf : pq.1.1 = rs.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
        have hs : pq.1.2 - 1 = rs.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
        apply h1
        apply Subtype.ext
        apply Prod.ext
        · exact hf
        · show pq.1.2 = rs.1.2 + 1
          omega
      rw [zsmul_ds_apply, LinearMap.comp_apply,
        lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hneB, zsmul_zero]
    erw [hA, hB, add_zero]
  · rw [DirectSum.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
      DFinsupp.zero_apply, add_zero]
    have hA : (((tpLof C K n (⟨(pq.1.1 - 1, pq.1.2), by omega⟩ : tpIdx n)) ∘ₗ
        (TensorProduct.map (ModuleCat.Hom.hom (C.d (pq.1.1) (pq.1.1 - 1))) LinearMap.id)) z)
        rs = 0 := by
      have hneA : (⟨(pq.1.1 - 1, pq.1.2), by omega⟩ : tpIdx n) ≠ rs := by
        intro h
        have hf : pq.1.1 - 1 = rs.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
        have hs : pq.1.2 = rs.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
        apply h2
        apply Subtype.ext
        apply Prod.ext
        · show pq.1.1 = rs.1.1 + 1
          omega
        · exact hs
      rw [LinearMap.comp_apply]
      exact lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hneA _
    exact hA
  · rw [DirectSum.add_apply, smul_lmap_apply, LinearMap.zero_apply,
      DFinsupp.zero_apply, zero_add]
    have hB : (((-1 : ℤ) ^ (pq.1.1)) •
        (((tpLof C K n (⟨(pq.1.1, pq.1.2 - 1), by omega⟩ : tpIdx n)) ∘ₗ
          (TensorProduct.map LinearMap.id
            (ModuleCat.Hom.hom (K.d (pq.1.2) (pq.1.2 - 1))))) z)) rs = 0 := by
      have hneB : (⟨(pq.1.1, pq.1.2 - 1), by omega⟩ : tpIdx n) ≠ rs := by
        intro h
        have hf : pq.1.1 = rs.1.1 := congrArg (fun x : tpIdx n => x.1.1) h
        have hs : pq.1.2 - 1 = rs.1.2 := congrArg (fun x : tpIdx n => x.1.2) h
        apply h1
        apply Subtype.ext
        apply Prod.ext
        · exact hf
        · show pq.1.2 = rs.1.2 + 1
          omega
      rw [zsmul_ds_apply, LinearMap.comp_apply,
        lof_apply_eq_zero (M := fun rs => tpSummand C K rs.1.1 rs.1.2) hneB, zsmul_zero]
    exact hB
  · rw [DirectSum.add_apply]
    simp

/-! ## 3. The component formula -/

/-- **The Koszul differential of the tensor product, in components.** -/
theorem tpDApplyComp (C K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (rs : Work.Kunneth.tpIdx n)
    (x : Work.Kunneth.tpX C K (n + 1)) :
    (Work.Kunneth.tpD C K n x) rs =
      (-1 : ℤ) ^ rs.1.1 •
          (TensorProduct.map (LinearMap.id) ((K.d (rs.1.2 + 1) rs.1.2).hom)
            (x ⟨(rs.1.1, rs.1.2 + 1), by omega⟩))
        + (TensorProduct.map ((C.d (rs.1.1 + 1) rs.1.1).hom) (LinearMap.id)
            (x ⟨(rs.1.1 + 1, rs.1.2), by omega⟩)) := by
  have hrec : (∑ pq : tpIdx (n+1), tpLof C K (n+1) pq (x pq)) = x := tpX_sum_lof C K (n+1) x
  have hi12 : (⟨(rs.1.1, rs.1.2 + 1), by omega⟩ : tpIdx (n+1)) ≠
      ⟨(rs.1.1 + 1, rs.1.2), by omega⟩ := by
    intro h
    have hh : rs.1.1 = rs.1.1 + 1 := congrArg (fun y : tpIdx (n+1) => y.1.1) h
    exact Nat.succ_ne_self rs.1.1 hh.symm
  have hzero : ∀ pq ∈ (Finset.univ : Finset (tpIdx (n+1))),
      pq ∉ ({⟨(rs.1.1, rs.1.2 + 1), by omega⟩, ⟨(rs.1.1 + 1, rs.1.2), by omega⟩} :
        Finset (tpIdx (n+1))) →
      (tpD C K n (tpLof C K (n+1) pq (x pq))) rs = 0 := by
    intro pq _ hpq
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hpq
    exact tpD_tpLof_eq_zero C K n rs pq hpq.1 hpq.2 (x pq)
  have hv1 : (tpD C K n (tpLof C K (n+1) ⟨(rs.1.1, rs.1.2 + 1), by omega⟩
        (x ⟨(rs.1.1, rs.1.2 + 1), by omega⟩))) rs
      = (-1 : ℤ) ^ rs.1.1 •
          (TensorProduct.map (LinearMap.id) ((K.d (rs.1.2 + 1) rs.1.2).hom)
            (x ⟨(rs.1.1, rs.1.2 + 1), by omega⟩)) :=
    tpD_tpLof_snd C K n rs (x ⟨(rs.1.1, rs.1.2 + 1), by omega⟩)
  have hv2 : (tpD C K n (tpLof C K (n+1) ⟨(rs.1.1 + 1, rs.1.2), by omega⟩
        (x ⟨(rs.1.1 + 1, rs.1.2), by omega⟩))) rs
      = (TensorProduct.map ((C.d (rs.1.1 + 1) rs.1.1).hom) (LinearMap.id)
            (x ⟨(rs.1.1 + 1, rs.1.2), by omega⟩)) :=
    tpD_tpLof_fst C K n rs (x ⟨(rs.1.1 + 1, rs.1.2), by omega⟩)
  have hsub : (∑ pq ∈ ({⟨(rs.1.1, rs.1.2 + 1), by omega⟩, ⟨(rs.1.1 + 1, rs.1.2), by omega⟩} :
        Finset (tpIdx (n+1))), (tpD C K n (tpLof C K (n+1) pq (x pq))) rs)
      = ∑ pq ∈ (Finset.univ : Finset (tpIdx (n+1))),
          (tpD C K n (tpLof C K (n+1) pq (x pq))) rs :=
    Finset.sum_subset (Finset.subset_univ _) hzero
  conv_lhs => rw [← hrec]
  rw [map_sum]
  rw [← DirectSum.coeFnLinearMap_apply (R := ℤ)
    (v := ∑ pq : tpIdx (n+1), tpD C K n (tpLof C K (n+1) pq (x pq)))]
  rw [map_sum, Finset.sum_apply]
  simp only [DirectSum.coeFnLinearMap_apply]
  rw [← hsub]
  rw [Finset.sum_pair hi12]
  rw [hv1, hv2]

end

end Work.Serre
