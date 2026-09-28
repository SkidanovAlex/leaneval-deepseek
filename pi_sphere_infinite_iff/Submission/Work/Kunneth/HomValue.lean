import Mathlib
import Submission.Work.Kunneth.HomQuot
import Submission.Work.Kunneth.EZAWTensor

/-!
# Value rules for the homology class map

`Work.Kunneth.homQuotIso` identifies the homology of a chain complex of `ℤ`-modules with the
concrete quotient `Zₙ ⧸ Bₙ`, with the computation rule `Work.Kunneth.homQuotIso_apply`: the class
of a cycle is the class of the same element.

This file extracts the consequences used by the cross-product form of the Künneth theorem:

* `Work.Kunneth.cycleOf` — an element of the cycle module `Zₙ` named by its underlying element;
* `Work.Kunneth.homologyMap_apply_homologyπ` — the class of a cycle under a chain map is the class
  of its image;
* `Work.Kunneth.exists_d_eq_of_homologyπ_eq` — **cycles with the same homology class differ by a
  boundary**, and its converse `Work.Kunneth.homologyπ_eq_of_sub_eq_d`;
* `Work.Kunneth.homologyπ_eq_zero_of_d_eq` — a cycle whose underlying element is a boundary
  represents zero;
* `Work.Kunneth.tpLof_tmul_d_eq_smul_tpD` — the Koszul boundary identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

/-! ## Isomorphisms of `ModuleCat`, on elements -/

/-- The inverse of a `ModuleCat`-isomorphism composed with it is the identity, on elements. -/
theorem homIso_inv_apply {M N : ModuleCat ℤ} (e : M ≅ N) (x : ↥M) :
    e.inv.hom (e.hom.hom x) = x := by
  have h1 : e.inv.hom.comp e.hom.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp e.hom e.inv, Iso.hom_inv_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 x

/-- The interpretation rule of an isomorphism: `e (e⁻¹ y) = y`. -/
theorem homIso_hom_apply {M N : ModuleCat ℤ} (e : M ≅ N) (y : ↥N) :
    e.hom.hom (e.inv.hom y) = y := by
  have h1 : e.hom.hom.comp e.inv.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp e.inv e.hom, Iso.inv_hom_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 y

/-! ## Naming cycles -/

/-- **The cycle with a prescribed underlying element.**  The element `z` of `Zₙ = ker ∂ₙ` is
carried to a genuine cycle of the complex through the concrete identification
`Work.Kunneth.cycIso`. -/
noncomputable def cycleOf (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z : ↥(cycKer K n)) : ↥(K.cycles n) :=
  (cycIso K n).inv.hom z

/-- The defining equation of `cycleOf`, in the spelling of the identification `cycIso`. -/
theorem cycleOf_eq (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) (z : ↥(cycKer K n)) :
    cycleOf K n z = (cycIso K n).inv.hom z := rfl

/-- The underlying element of `cycleOf` is the prescribed one. -/
theorem iCycles_cycleOf (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z : ↥(cycKer K n)) :
    (K.iCycles n).hom (cycleOf K n z) = (z : ↥(K.X n)) := by
  have h := cycIso_hom_val K n (cycleOf K n z)
  have h2 : (cycIso K n).hom.hom ((cycIso K n).inv.hom z) = z := homIso_hom_apply (cycIso K n) z
  rw [cycleOf_eq] at h ⊢
  exact h.symm.trans (congrArg (fun w => ((w : ↥(cycKer K n)) : ↥(K.X n))) h2)

/-- The homology class of `cycleOf z` is the class of `z` in `Zₙ ⧸ Bₙ`. -/
theorem homologyπ_cycleOf (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z : ↥(cycKer K n)) :
    (K.homologyπ n).hom (cycleOf K n z)
      = (homQuotIso K n).inv.hom ((homBnd K n).mkQ z) := by
  have h := homQuotIso_apply K n (cycleOf K n z)
  have h2 : (cycIso K n).hom.hom ((cycIso K n).inv.hom z) = z := homIso_hom_apply (cycIso K n) z
  rw [cycleOf_eq] at h ⊢
  rw [h2] at h
  have h3 := congrArg (fun x => (homQuotIso K n).inv.hom x) h
  rw [homIso_inv_apply] at h3
  exact h3

/-! ## The class of a cycle under a chain map -/

/-- **A chain map sends the class of a cycle to the class of the image cycle.** -/
theorem homologyMap_apply_homologyπ (K L : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (f : K ⟶ L)
    (n : ℕ) (z : ↥(K.cycles n)) :
    (HomologicalComplex.homologyMap f n).hom ((K.homologyπ n).hom z)
      = (L.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom z) := by
  have h := congrArg (fun (m : K.cycles n ⟶ L.homology n) => ModuleCat.Hom.hom m z)
    (HomologicalComplex.homologyπ_naturality f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The underlying element of the image cycle of a chain map. -/
theorem iCycles_cyclesMap (K L : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (f : K ⟶ L) (n : ℕ)
    (z : ↥(K.cycles n)) :
    (L.iCycles n).hom ((HomologicalComplex.cyclesMap f n).hom z)
      = (f.f n).hom ((K.iCycles n).hom z) := by
  have h := congrArg (fun (m : K.cycles n ⟶ L.X n) => ModuleCat.Hom.hom m z)
    (HomologicalComplex.cyclesMap_i f n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-! ## Boundaries and homology classes -/

/-- **Cycles with the same homology class differ by a boundary.** -/
theorem exists_d_eq_of_homologyπ_eq (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z z' : ↥(K.cycles n)) (h : (K.homologyπ n).hom z = (K.homologyπ n).hom z') :
    ∃ w : ↥(K.X (n + 1)), (K.d (n + 1) n).hom w
      = (K.iCycles n).hom z - (K.iCycles n).hom z' := by
  have h2 := congrArg (fun x => (homQuotIso K n).hom.hom x) h
  rw [homQuotIso_apply K n z, homQuotIso_apply K n z'] at h2
  have h4 : (homBnd K n).mkQ ((cycIso K n).hom z - (cycIso K n).hom z') = 0 := by
    rw [map_sub, h2, sub_self]
  have h5 : (cycIso K n).hom z - (cycIso K n).hom z' ∈ homBnd K n := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h4
    exact h4
  have h6 := (mem_homBnd_iff K n _).mp h5
  obtain ⟨w, hw⟩ := h6
  have hw' : (K.d (n + 1) n).hom w = (K.iCycles n).hom z - (K.iCycles n).hom z' := by
    rw [hw, Submodule.coe_sub, cycIso_hom_val, cycIso_hom_val]
  exact ⟨w, hw'⟩

/-- A cycle whose underlying element is a boundary represents the zero homology class. -/
theorem homologyπ_eq_zero_of_d_eq (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z : ↥(K.cycles n)) (w : ↥(K.X (n + 1)))
    (h : (K.d (n + 1) n).hom w = (K.iCycles n).hom z) : (K.homologyπ n).hom z = 0 := by
  have hmem : (cycIso K n).hom z ∈ homBnd K n := by
    rw [mem_homBnd_iff K n]
    rw [cycIso_hom_val]
    exact ⟨w, h⟩
  have h2 : (homQuotIso K n).hom.hom ((K.homologyπ n).hom z) = 0 := by
    rw [homQuotIso_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  have h3 := congrArg (fun x => (homQuotIso K n).inv.hom x) h2
  simp only [map_zero] at h3
  rwa [homIso_inv_apply] at h3

/-- Two cycles whose underlying elements differ by a boundary have the same homology class. -/
theorem homologyπ_eq_of_sub_eq_d (K : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z z' : ↥(K.cycles n)) (w : ↥(K.X (n + 1)))
    (h : (K.iCycles n).hom z - (K.iCycles n).hom z' = (K.d (n + 1) n).hom w) :
    (K.homologyπ n).hom z = (K.homologyπ n).hom z' := by
  have h1 : (K.homologyπ n).hom z - (K.homologyπ n).hom z' = 0 := by
    have h2 := homologyπ_eq_zero_of_d_eq K n (z - z') w (by rw [map_sub, h])
    rw [map_sub] at h2
    exact h2
  exact sub_eq_zero.mp h1

/-! ## The Koszul boundary identity -/

/-- **The Koszul differential on a boundary.**  For a cycle `x` of `C`, the chain `x ⊗ ∂w` of the
tensor product is, up to the sign `(-1)^p`, the boundary of `x ⊗ w`. -/
theorem tpLof_tmul_d_eq_smul_tpD (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (pq : tpIdx (n + 1)) (hq : 1 ≤ pq.1.2) (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2))
    (hx : (C.d pq.1.1 (pq.1.1 - 1)).hom x = 0) :
    tpLof C D n ⟨(pq.1.1, pq.1.2 - 1), by omega⟩
        (x ⊗ₜ[ℤ] ((D.d pq.1.2 (pq.1.2 - 1)).hom y))
      = (-1 : ℤ) ^ pq.1.1 • tpD C D n (tpLof C D (n + 1) pq (x ⊗ₜ[ℤ] y)) := by
  rw [tpD_lof_tmul C D n pq x y]
  rw [dif_pos hq]
  have hfirst : (if hp : 1 ≤ pq.1.1 then
      (tpLof C D n ⟨(pq.1.1 - 1, pq.1.2), by omega⟩
        (((C.d pq.1.1 (pq.1.1 - 1)).hom x) ⊗ₜ[ℤ] y)) else 0) = 0 := by
    by_cases hp : 1 ≤ pq.1.1
    · rw [dif_pos hp, hx, TensorProduct.zero_tmul, map_zero]
    · rw [dif_neg hp]
  have hp : (-1 : ℤ) ^ pq.1.1 * (-1 : ℤ) ^ pq.1.1 = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨pq.1.1, rfl⟩
  rw [hfirst, zero_add, smul_smul, hp, one_smul]

end

end Work.Kunneth
