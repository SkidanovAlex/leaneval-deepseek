/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# `H¹(S¹ × S^q; ℚ) ≅ ℚ` for `q ≥ 2`

The circle `S¹` is covered by the two contractible caps `capPlus 0`, `capMinus 0`, whose
intersection is the doubly punctured circle, homotopy equivalent to `S⁰`.  Pulling this cover back
to `S¹ × S^q` gives the two-piece cover of `X × S^q` (`Work.Sphere.fstSmall`) whose pieces are
`cap ± × S^q` (homotopy equivalent to `S^q`) and whose intersection is `(S¹ ∖ {±e}) × S^q`,
homotopy equivalent to `S⁰ × S^q`, hence a space with two path components each of which is
homotopy equivalent to `S^q`.

The Mayer–Vietoris sequence in degree `0` therefore reads

`H⁰(small) → H⁰(A) ⊕ H⁰(B) → H⁰(A ∩ B) → H¹(small) → H¹(A) ⊕ H¹(B) = 0`

with `H⁰` of the first three terms `≅ ℚ` and `H⁰(A ∩ B) ≅ ℚ × ℚ`; the connecting map is
surjective and its kernel is a one-dimensional subspace of `ℚ × ℚ`, so
`H¹(small) ≅ ℚ × ℚ ⧸ line ≅ ℚ`.  The small-simplex theorem identifies `H¹(small) ≅ H¹(S¹ × S^q)`.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.CircleH1
import Submission.Work.Sphere.H_one_circle
import Submission.Work.Sphere.SphZeroTwoPoints
import Submission.Work.Cohomology.H_zero_two_points

open CategoryTheory Simplicial Opposite
open Submission.Cohomology Submission.Sphere

namespace Work.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## Plumbing: `Subsingleton` transfers across a linear equivalence -/

theorem subsingleton_of_linEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (h : Subsingleton W) : Subsingleton V :=
  ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-! ## The unit interval is preconnected -/

theorem preconnected_I : PreconnectedSpace ↥(TopCat.I) := by
  haveI : PreconnectedSpace unitInterval :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  rw [preconnectedSpace_iff_univ]
  have h4 := (Homeomorph.ulift.symm.isPreconnected_image (s := Set.univ)).mpr
    (isPreconnected_univ (α := unitInterval))
  rw [Set.image_univ, Set.range_eq_univ.mpr Homeomorph.ulift.symm.surjective] at h4
  exact h4

/-! ## Two specific `0`-cochains on `S⁰ × Y` -/

/-- The `0`-cochain which is `1` on `{pole} × Y` and `0` elsewhere, as a function on the points
of `S⁰ × Y`. -/
def chiPlus (Y : TopCat.{0}) : ↥(TopProd (Sph 0) Y) → ℚ :=
  fun z => if z.1 = polePt 0 then 1 else 0

/-- The `0`-cochain which is `0` on `{pole} × Y` and `1` elsewhere. -/
def chiMinus (Y : TopCat.{0}) : ↥(TopProd (Sph 0) Y) → ℚ :=
  fun z => if z.1 = polePt 0 then 0 else 1

/-- A function on the points of `Z = S⁰ × Y` gives a `0`-cochain of the singular complex of `Z`
(in degree `0` cochains are functions on the points). -/
def chiCochain (Y : TopCat.{0}) (χ : ↥(TopProd (Sph 0) Y) → ℚ) :
    Cochain (TopCat.toSSet.obj (TopProd (Sph 0) Y)) ℚ 0 :=
  fun σ => χ (TopCat.toSSetObj₀Equiv σ)

lemma chiPlus_const (Y : TopCat.{0}) (f : TopCat.I ⟶ TopProd (Sph 0) Y) :
    chiPlus Y (f 0) = chiPlus Y (f 1) := by
  haveI hdisc : DiscreteTopology ↥(Sph 0) := discreteTopology_sph_zero SphZeroTwoPoints
  haveI hpre : PreconnectedSpace ↥(TopCat.I) := preconnected_I
  have hconst : (f 0).1 = (f 1).1 := by
    have h := PreconnectedSpace.constant hpre (continuous_fst.comp f.hom.continuous)
      (x := (0 : ↥(TopCat.I))) (y := 1)
    simpa using h
  show (if (f 0).1 = polePt 0 then (1 : ℚ) else 0)
      = (if (f 1).1 = polePt 0 then (1 : ℚ) else 0)
  rw [hconst]

lemma chiMinus_const (Y : TopCat.{0}) (f : TopCat.I ⟶ TopProd (Sph 0) Y) :
    chiMinus Y (f 0) = chiMinus Y (f 1) := by
  haveI hdisc : DiscreteTopology ↥(Sph 0) := discreteTopology_sph_zero SphZeroTwoPoints
  haveI hpre : PreconnectedSpace ↥(TopCat.I) := preconnected_I
  have hconst : (f 0).1 = (f 1).1 := by
    have h := PreconnectedSpace.constant hpre (continuous_fst.comp f.hom.continuous)
      (x := (0 : ↥(TopCat.I))) (y := 1)
    simpa using h
  show (if (f 0).1 = polePt 0 then (0 : ℚ) else 1)
      = (if (f 1).1 = polePt 0 then (0 : ℚ) else 1)
  rw [hconst]

lemma chiCochain_mem_cycles (Y : TopCat.{0}) (χ : ↥(TopProd (Sph 0) Y) → ℚ)
    (hχ : ∀ f : TopCat.I ⟶ TopProd (Sph 0) Y, χ (f 0) = χ (f 1)) :
    chiCochain Y χ ∈ cycles (TopCat.toSSet.obj (TopProd (Sph 0) Y)) ℚ 0 := by
  rw [Submission.Cohomology.mem_cycles_iff]
  ext σ
  rw [Work.Cohomology.coboundary_zero_apply]
  show χ (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopProd (Sph 0) Y)).δ 0 σ))
      - χ (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopProd (Sph 0) Y)).δ 1 σ)) = 0
  rw [← TopCat.toSSetObj₁Equiv_apply_one σ, ← TopCat.toSSetObj₁Equiv_apply_zero σ]
  rw [hχ (TopCat.toSSetObj₁Equiv σ)]
  ring

/-- A chosen point of a path-connected space. -/
noncomputable def y0 (Y : TopCat.{0}) [PathConnectedSpace Y] : ↥Y :=
  Classical.choice (PathConnectedSpace.nonempty (X := ↥Y))

/-- Evaluation of `H⁰(S⁰ × Y; ℚ)` at the two points `(pole, y₀)` and `(-pole, y₀)`. -/
noncomputable def psi (Y : TopCat.{0}) [PathConnectedSpace Y] :
    H (TopCat.toSSet.obj (TopProd (Sph 0) Y)) ℚ 0 →ₗ[ℚ] ℚ × ℚ :=
  { toFun := fun z => (HzeroEval (TopProd (Sph 0) Y) z (polePt 0, y0 Y),
      HzeroEval (TopProd (Sph 0) Y) z (negPolePt 0, y0 Y))
    map_add' := by intro a b; simp
    map_smul' := by intro c a; simp }

lemma psi_apply (Y : TopCat.{0}) [PathConnectedSpace Y]
    (z : H (TopCat.toSSet.obj (TopProd (Sph 0) Y)) ℚ 0) :
    psi Y z = (HzeroEval (TopProd (Sph 0) Y) z (polePt 0, y0 Y),
      HzeroEval (TopProd (Sph 0) Y) z (negPolePt 0, y0 Y)) := rfl

/-- **`H⁰(S⁰ × Y; ℚ) ≅ ℚ × ℚ`** for a path-connected space `Y`: a degree `0` class is
determined by its values on the two points `(±pole, y₀)`, and every pair of values is realised,
because `S⁰ × Y` has the two path components `{±pole} × Y`. -/
theorem H_zero_prod_sph_zero (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph 0) Y)) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ) := by
  have hua := chiCochain_mem_cycles Y (chiPlus Y) (chiPlus_const Y)
  have hub := chiCochain_mem_cycles Y (chiMinus Y) (chiMinus_const Y)
  have hcover : ∀ z : ↥(TopProd (Sph 0) Y),
      Nonempty (Path (polePt 0, y0 Y) z) ∨ Nonempty (Path (negPolePt 0, y0 Y) z) := by
    rintro ⟨x, y⟩
    rcases SphZeroTwoPoints x with hx | hx
    · left
      rw [hx]
      exact ⟨(Path.refl (polePt 0)).prod (PathConnectedSpace.somePath y (y0 Y)).symm⟩
    · right
      rw [hx]
      exact ⟨(Path.refl (negPolePt 0)).prod (PathConnectedSpace.somePath y (y0 Y)).symm⟩
  have hinj : Function.Injective (psi Y) := by
    intro a b hab
    have hab' : (HzeroEval (TopProd (Sph 0) Y) a (polePt 0, y0 Y),
        HzeroEval (TopProd (Sph 0) Y) a (negPolePt 0, y0 Y))
        = (HzeroEval (TopProd (Sph 0) Y) b (polePt 0, y0 Y),
        HzeroEval (TopProd (Sph 0) Y) b (negPolePt 0, y0 Y)) := by
      rw [← psi_apply, ← psi_apply]; exact hab
    exact Work.Cohomology.H_zero_two_points (X := TopProd (Sph 0) Y) _ _ hcover hab'
  have hA1 : HzeroEval (TopProd (Sph 0) Y) (H.mk (chiCochain Y (chiPlus Y)) hua)
      (polePt 0, y0 Y) = 1 := by
    rw [Submission.Cohomology.HzeroEval_mk]
    show chiPlus Y (TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm (polePt 0, y0 Y))) = 1
    rw [Equiv.apply_symm_apply]
    simp [chiPlus]
  have hA2 : HzeroEval (TopProd (Sph 0) Y) (H.mk (chiCochain Y (chiPlus Y)) hua)
      (negPolePt 0, y0 Y) = 0 := by
    rw [Submission.Cohomology.HzeroEval_mk]
    show chiPlus Y (TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm (negPolePt 0, y0 Y))) = 0
    rw [Equiv.apply_symm_apply]
    show (if negPolePt 0 = polePt 0 then (1 : ℚ) else 0) = 0
    rw [if_neg (fun h => polePt_ne_negPolePt 0 h.symm)]
  have hB1 : HzeroEval (TopProd (Sph 0) Y) (H.mk (chiCochain Y (chiMinus Y)) hub)
      (polePt 0, y0 Y) = 0 := by
    rw [Submission.Cohomology.HzeroEval_mk]
    show chiMinus Y (TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm (polePt 0, y0 Y))) = 0
    rw [Equiv.apply_symm_apply]
    simp [chiMinus]
  have hB2 : HzeroEval (TopProd (Sph 0) Y) (H.mk (chiCochain Y (chiMinus Y)) hub)
      (negPolePt 0, y0 Y) = 1 := by
    rw [Submission.Cohomology.HzeroEval_mk]
    show chiMinus Y (TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm (negPolePt 0, y0 Y))) = 1
    rw [Equiv.apply_symm_apply]
    show (if negPolePt 0 = polePt 0 then (0 : ℚ) else 1) = 1
    rw [if_neg (fun h => polePt_ne_negPolePt 0 h.symm)]
  have hA : psi Y (H.mk (chiCochain Y (chiPlus Y)) hua) = (1, 0) := by
    rw [psi_apply, Prod.mk.injEq]
    exact ⟨hA1, hA2⟩
  have hB : psi Y (H.mk (chiCochain Y (chiMinus Y)) hub) = (0, 1) := by
    rw [psi_apply, Prod.mk.injEq]
    exact ⟨hB1, hB2⟩
  have hsurj : Function.Surjective (psi Y) := by
    intro t
    refine ⟨t.1 • H.mk (chiCochain Y (chiPlus Y)) hua
      + t.2 • H.mk (chiCochain Y (chiMinus Y)) hub, ?_⟩
    rw [map_add, map_smul, map_smul, hA, hB]
    ext <;> simp
  exact ⟨LinearEquiv.ofBijective (psi Y) ⟨hinj, hsurj⟩⟩


/-! ## The main result -/

theorem H1_prod_sph_circle (q : ℕ) (hq : 2 ≤ q) :
    Nonempty (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph 1) (Submission.Sphere.Sph q))) ℚ 1
      ≃ₗ[ℚ] ℚ) := by
  classical
  haveI hpcX : PathConnectedSpace ↥(Sph 1) := pathConnected_sph 1 (by norm_num)
  haveI hpcY : PathConnectedSpace ↥(Sph q) := pathConnected_sph q (by omega)
  haveI hpcP : PathConnectedSpace ↥(TopProd (Sph 1) (Sph q)) := inferInstance
  haveI hcP : ContractibleSpace ↥(capPlus 0) := capPlus_contractible 0
  haveI hcM : ContractibleSpace ↥(capMinus 0) := capMinus_contractible 0
  have hopen₁ : IsOpen (capPlus 0 : Set ↥(Sph 1)) := isOpen_capPlus 0
  have hopen₂ : IsOpen (capMinus 0 : Set ↥(Sph 1)) := isOpen_capMinus 0
  have hcov : ∀ x : ↥(Sph 1),
      x ∈ (capPlus 0 : Set ↥(Sph 1)) ∨ x ∈ (capMinus 0 : Set ↥(Sph 1)) :=
    fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus 0) x
  obtain ⟨eSmall⟩ := H_fstSmall_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0)
    hopen₁ hopen₂ hcov 1
  obtain ⟨eSmall0⟩ := H_fstSmall_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0)
    hopen₁ hopen₂ hcov 0
  have hS : H (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ≃ₗ[ℚ] ℚ :=
    eSmall0.symm.trans (Classical.choice
      (Work.Cohomology.H_zero_connected (TopProd (Sph 1) (Sph q))))
  have hA0 : H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ≃ₗ[ℚ] ℚ :=
    (Classical.choice (H_fstAsub_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0) 0)).trans
      ((Classical.choice (H_fstSub_contractible_iso (X := Sph 1) (Y := Sph q)
        (capPlus 0) 0)).trans
        (Classical.choice (Work.Cohomology.H_zero_connected (Sph q))))
  have hB0 : H (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ≃ₗ[ℚ] ℚ :=
    (Classical.choice (H_fstBsub_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0) 0)).trans
      ((Classical.choice (H_fstSub_contractible_iso (X := Sph 1) (Y := Sph q)
        (capMinus 0) 0)).trans
        (Classical.choice (Work.Cohomology.H_zero_connected (Sph q))))
  -- `H⁰` of the intersection piece is `ℚ × ℚ`
  have hC : H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) ⊓
      fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) :
      ((fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) : SSet.{0}).Subcomplex) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ := by
    have e0 : H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) ⊓
        fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) :
        ((fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) : SSet.{0}).Subcomplex) ℚ 0
        ≃ₗ[ℚ] H (fstCsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 :=
      Classical.choice (Submission.Sphere.H_iso_of_iso (SSet.Subcomplex.eqToIso
        (fstAsub_inf_fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))) 0)
    have e1 : H (fstCsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0
        ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopProd (TopCat.of ↥(capPlus 0 ∩ capMinus 0))
          (Sph q))) ℚ 0 :=
      Classical.choice (H_fstCsub_homeo (Sph 1) (Sph q) (capPlus 0) (capMinus 0) 0)
    rw [capPlus_inter_capMinus_eq_DPset 0] at e1
    have e2 : H (TopCat.toSSet.obj (TopProd (TopCat.of ↥(DPset 0)) (Sph q))) ℚ 0
        ≃ₗ[ℚ] H (TopCat.toSSet.obj (TopProd (Sph 0) (Sph q))) ℚ 0 :=
      Classical.choice (H_DPset_prod_iso 0 (Sph q) 0)
    have e3 : H (TopCat.toSSet.obj (TopProd (Sph 0) (Sph q))) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ :=
      Classical.choice (H_zero_prod_sph_zero (Sph q))
    exact e0.trans (e1.trans (e2.trans e3))
  -- the two pieces are acyclic in degree `1`
  have hq1 : Subsingleton (H (singSph q) ℚ 1) := by
    have h := H_one_sph_succ (q - 2)
    rwa [Nat.sub_add_cancel hq] at h
  have hA1 : Subsingleton (H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 1) :=
    subsingleton_of_linEquiv
      (Classical.choice (H_fstAsub_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0) 1))
      (subsingleton_of_linEquiv
        (Classical.choice (H_fstSub_contractible_iso (X := Sph 1) (Y := Sph q)
          (capPlus 0) 1)) hq1)
  have hB1 : Subsingleton (H (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 1) :=
    subsingleton_of_linEquiv
      (Classical.choice (H_fstBsub_iso (Sph 1) (Sph q) (capPlus 0) (capMinus 0) 1))
      (subsingleton_of_linEquiv
        (Classical.choice (H_fstSub_contractible_iso (X := Sph 1) (Y := Sph q)
          (capMinus 0) 1)) hq1)
  -- the two-piece cover of the small complex
  have hAB : fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) ⊔
      fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) = ⊤ :=
    fstAsub_sup_fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)
  let α := mvAlphaH (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) 0
  let β := mvBetaH (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) 0
  let δ := mvConnecting (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
    (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) hAB 0
  have hαinj : Function.Injective α :=
    Submission.Cohomology.mvAlphaH_injective_zero
      (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) hAB
  have hkerα : LinearMap.ker α = ⊥ := LinearMap.ker_eq_bot.mpr hαinj
  have hkerβs : LinearMap.ker β = LinearMap.range α :=
    Work.Cohomology.mvBetaH_ker_eq_range
      (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) hAB 0
  have hkerδ : LinearMap.ker δ = LinearMap.range β :=
    Work.Cohomology.mvConnecting_ker_eq_range
      (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) hAB 0
  have hδsurj : Function.Surjective δ :=
    Work.Cohomology.mvConnecting_surjective
      (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0))
      (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) hAB 0 hA1 hB1
  -- a generator of `H⁰(small)`
  let y0' : H (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 := hS.symm 1
  have hy0' : y0' ≠ 0 := by
    intro h
    have h2 : (1 : ℚ) = 0 := by
      rw [← LinearEquiv.apply_symm_apply hS 1, show hS.symm 1 = 0 from h, map_zero]
    exact one_ne_zero h2
  let w' : H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ×
      H (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 := α y0'
  have hw' : w' ≠ 0 := by
    intro h
    change α y0' = 0 at h
    exact hy0' (hαinj (by rw [h, map_zero]))
  have hspan : Submodule.span ℚ
      ({y0'} : Set (H (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0)) = ⊤ :=
    span_singleton_eq_top_of_equiv hS hy0'
  have hrangeα : LinearMap.range α = Submodule.span ℚ ({w'} : Set _) := by
    rw [LinearMap.range_eq_map, ← hspan, Submodule.map_span]
    simp only [Set.image_singleton]
    rfl
  have hkerβ' : LinearMap.ker β = Submodule.span ℚ ({w'} : Set _) := by
    rw [hkerβs]; exact hrangeα
  have heAB : (H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ×
      H (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0) ≃ₗ[ℚ] ℚ × ℚ :=
    hA0.prodCongr hB0
  obtain ⟨eQ1⟩ : Nonempty (((H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0 ×
      H (fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 0) ⧸
      Submodule.span ℚ ({w'} : Set _)) ≃ₗ[ℚ] ℚ) := quot_span_singleton_rat heAB w' hw'
  have eRangeβ : LinearMap.range β ≃ₗ[ℚ] ℚ :=
    (LinearMap.quotKerEquivRange β).symm.trans
      ((Submodule.quotEquivOfEq (LinearMap.ker β)
        (Submodule.span ℚ ({w'} : Set _)) hkerβ').trans eQ1)
  -- a generator of `range β`
  let w : H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) ⊓
      fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) :
      ((fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) : SSet.{0}).Subcomplex) ℚ 0 :=
    (eRangeβ.symm 1 : LinearMap.range β)
  have hwmem : w ∈ LinearMap.range β := (eRangeβ.symm 1).2
  have hwne : w ≠ 0 := by
    intro h
    have h1 : eRangeβ (eRangeβ.symm 1) = 0 := by
      have hz : eRangeβ.symm 1 = 0 := by
        apply Subtype.ext
        exact h
      rw [hz, map_zero]
    rw [LinearEquiv.apply_symm_apply] at h1
    exact one_ne_zero h1
  have hspw : Submodule.span ℚ ({w} : Set _) = LinearMap.range β :=
    span_singleton_eq_of_equiv eRangeβ hwmem hwne
  have hδker : LinearMap.ker δ = Submodule.span ℚ ({w} : Set _) := by
    rw [hkerδ]; exact hspw.symm
  obtain ⟨eQ2⟩ : Nonempty ((H (fstAsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) ⊓
      fstBsub (Sph 1) (Sph q) (capPlus 0) (capMinus 0) :
      ((fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) : SSet.{0}).Subcomplex) ℚ 0 ⧸
      Submodule.span ℚ ({w} : Set _)) ≃ₗ[ℚ] ℚ) :=
    quot_span_singleton_rat hC w hwne
  have e1 : H (fstSmall (Sph 1) (Sph q) (capPlus 0) (capMinus 0)) ℚ 1 ≃ₗ[ℚ] ℚ :=
    (LinearMap.quotKerEquivOfSurjective δ hδsurj).symm.trans
      ((Submodule.quotEquivOfEq (LinearMap.ker δ) (Submodule.span ℚ ({w} : Set _))
        hδker).trans eQ2)
  exact ⟨eSmall.trans e1⟩

end

end Work.Sphere
