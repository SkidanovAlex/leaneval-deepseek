/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# `H¹(S^p × S^q; ℚ) = 0` for `2 ≤ p < q`

The degree-one cohomology of a product of two spheres of dimension `≥ 2` vanishes.  This is the
"degree one" base case of the computation of the cohomology of `S^p × S^q` (the general degree
`≥ 2` cases are obtained from the two degree shifts `prod_fst_shift`/`prod_snd_shift` of
`Submission/Work/Sphere/ProdRec.lean`, whose recursion starts here).

The proof is the degree-zero Mayer–Vietoris analysis of the cover of `X × Y`
(`X = S^{a+1}`, `Y = S^q`) pulled back from the two caps of the first factor
(`Submission/Work/Sphere/ProdSetup.lean`).  Write `S` for the "small" complex, `A`, `B` for the two
pieces and `C = A ⊓ B` for their intersection.  The pieces are acyclic in degree `1`
(`H¹(cap × Y) = H¹(Y) = 0`, using that the caps are contractible, so that a product with a
contractible factor is homotopy equivalent to the other factor, `H_fstSub_contractible_iso`), so
the restriction `mvAlphaH S A B 1` is zero, and exactness of the Mayer–Vietoris sequence at
`H¹(S)` (`mvAlphaH_ker_eq_range`) identifies `H¹(S)` with the range of the connecting map
`mvConnecting S A B 0 : H⁰(C) → H¹(S)`.  By exactness at `H⁰(C)`
(`mvConnecting_ker_eq_range`), the connecting map vanishes as soon as `mvBetaH S A B 0` is onto:
and indeed `H⁰(C) ≅ ℚ` (`H_zero_fstAsub_inf_fstBsub`, as `C ≃ S^a × Y` is path connected) while
the restriction `H⁰(A) → H⁰(C)` is nonzero — it sends the class of the constant `1`-cochain to the
class of `1`, which is nonzero because `C` has a `0`-simplex
(`nonempty_fstAsub_inf_fstBsub_zero`) — so it is surjective, and
`mvBetaH S A B 0 (x, 0) = x|`.  Hence `mvConnecting S A B 0 = 0`, `ker (mvAlphaH S A B 1) = 0`
and `H¹(S) = 0`.  Finally `H¹(S^p × S^q) ≅ H¹(S)` by the small-simplex theorem
(`H_fstSmall_iso`).
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.H_one_sph_succ
import Submission.Work.Sphere.pathConnected_sph
import Submission.Work.Sphere.nonempty_fstAsub_inf_fstBsub_zero
import Submission.Work.Sphere.H_zero_fstAsub_inf_fstBsub

open CategoryTheory Simplicial Opposite

namespace Work.Sphere

open Submission.Cohomology
open Submission.Sphere

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- `Subsingleton` transfers across a `ℚ`-linear equivalence. -/
private theorem subsingleton_of_linEquiv {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e : V ≃ₗ[ℚ] W) (h : Subsingleton W) : Subsingleton V :=
  ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-- A piece of the cover of `X × Y` pulled back from a contractible subset `W ⊆ X` is acyclic in
degree `1` as soon as `H¹(Y) = 0`: `W × Y` is homotopy equivalent to `Y`. -/
private theorem fstSub_one_subsingleton {X : TopCat.{0}} (Y : TopCat.{0}) (W : Set X)
    [ContractibleSpace ↥W] (hY : Subsingleton (H (TopCat.toSSet.obj Y) ℚ 1)) :
    Subsingleton (H (fstSub X Y W) ℚ 1) :=
  subsingleton_of_linEquiv (Classical.choice (H_fstSub_contractible_iso (X := X) (Y := Y) W 1)) hY

/-- **`mvBetaH` in degree `0` is onto for the two-cap cover of `S^{a+1} × Y`.**  The restriction
`H⁰(A) → H⁰(A ⊓ B)` is a nonzero map between one-dimensional spaces (the class of the constant
`1`-cochain restricts to the nonzero class of `1`, as the intersection has a `0`-simplex), hence
it is onto, and `mvBetaH S A B 0 (x, 0) = x|`. -/
private theorem mvBetaH_zero_surjective_fstSmall (a : ℕ) (ha : 1 ≤ a) (Y : TopCat.{0})
    [PathConnectedSpace ↥Y] :
    Function.Surjective (mvBetaH (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) 0) := by
  classical
  obtain ⟨eC⟩ := H_zero_fstAsub_inf_fstBsub a ha Y
  have hne : (H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left :
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a) ⊓
       fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a) :
        ((fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a)) : SSet).Subcomplex) ≤
      fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))) 0) ≠ 0 := by
    intro h0
    have hz : (H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left :
        (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a) ⊓
         fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a) :
          ((fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a)) : SSet).Subcomplex) ≤
        fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))) 0)
        (H.mk (1 : Cochain (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a)) ℚ 0)
          (oneCochain_mem_cycles _)) ≠ 0 := by
      rw [H_map_oneCochain]
      exact H_mk_oneCochain_ne_zero_of _ (nonempty_fstAsub_inf_fstBsub_zero a Y) _
    rw [h0] at hz
    exact hz rfl
  have hsurj : Function.Surjective (H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left :
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a) ⊓
       fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a) :
        ((fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a)) : SSet).Subcomplex) ≤
      fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))) 0) :=
    surjective_of_ne_zero_equiv_rat eC hne
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨(x, 0), by rw [mvBetaH_apply, hx, map_zero, sub_zero]⟩

/-- **The degree-one cohomology of the small complex of the two-cap cover of `S^{a+1} × Y`
vanishes** when `a ≥ 1` and `H¹(Y) = 0`. -/
private theorem subsingleton_H_one_fstSmall (a : ℕ) (ha : 1 ≤ a) (Y : TopCat.{0})
    [PathConnectedSpace ↥Y] (hY : Subsingleton (H (TopCat.toSSet.obj Y) ℚ 1)) :
    Subsingleton (H (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a)) ℚ 1) := by
  classical
  have hAB := fstAsub_sup_fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)
  -- the two pieces of the cover are acyclic in degree `1`
  have hA1 : Subsingleton (H (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a)) ℚ 1) := by
    haveI : ContractibleSpace ↥(capPlus a) := capPlus_contractible a
    exact subsingleton_of_linEquiv (Classical.choice (H_fstAsub_iso _ _ _ _ 1))
      (fstSub_one_subsingleton (Y := Y) (W := capPlus a) hY)
  have hB1 : Subsingleton (H (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) ℚ 1) := by
    haveI : ContractibleSpace ↥(capMinus a) := capMinus_contractible a
    exact subsingleton_of_linEquiv (Classical.choice (H_fstBsub_iso _ _ _ _ 1))
      (fstSub_one_subsingleton (Y := Y) (W := capMinus a) hY)
  -- hence the restriction `mvAlphaH S A B 1` vanishes
  have hzero : mvAlphaH (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) 1 = 0 :=
    LinearMap.ext fun z => Prod.ext (hA1.elim _ _) (hB1.elim _ _)
  -- so the connecting map `mvConnecting S A B 0`, whose range is `H¹(S)`, is zero
  have hconn : mvConnecting (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) hAB 0 = 0 := by
    rw [← LinearMap.ker_eq_top, Work.Cohomology.mvConnecting_ker_eq_range]
    exact LinearMap.range_eq_top.mpr (mvBetaH_zero_surjective_fstSmall a ha Y)
  refine ⟨fun x y => ?_⟩
  have hxy : x - y ∈ LinearMap.ker (mvAlphaH (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) 1) := by
    rw [hzero, LinearMap.ker_zero]; trivial
  rw [Work.Cohomology.mvAlphaH_ker_eq_range (fstSmall (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstAsub (Sph (a+1)) Y (capPlus a) (capMinus a))
      (fstBsub (Sph (a+1)) Y (capPlus a) (capMinus a)) hAB 0, hconn,
    LinearMap.range_zero, Submodule.mem_bot] at hxy
  exact sub_eq_zero.mp hxy

theorem H1_prod_sph_high (p q : ℕ) (hp : 2 ≤ p) (hpq : p < q) :
    Subsingleton (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph p) (Submission.Sphere.Sph q))) ℚ 1) := by
  -- write `p = a + 1` with `a ≥ 1`
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  have hq : 1 ≠ q := by omega
  haveI : PathConnectedSpace ↥(Sph q) := pathConnected_sph q (by omega)
  have hY : Subsingleton (Submission.Cohomology.H (singSph q) ℚ 1) :=
    sphere_subsingleton q 1 (by norm_num) hq
  have hsmall : Subsingleton (H (fstSmall (Sph (a+1)) (Sph q) (capPlus a) (capMinus a)) ℚ 1) :=
    subsingleton_H_one_fstSmall a (by omega) (Sph q) hY
  -- the small-simplex theorem identifies `H¹(S^p × S^q)` with `H¹(small)`
  exact subsingleton_of_linEquiv
    (Classical.choice (H_fstSmall_iso (Sph (a+1)) (Sph q) (capPlus a) (capMinus a)
      (isOpen_capPlus a) (isOpen_capMinus a)
      (fun x => Set.eq_univ_iff_forall.mp (capPlus_union_capMinus a) x) 1)) hsmall

end

end Work.Sphere
