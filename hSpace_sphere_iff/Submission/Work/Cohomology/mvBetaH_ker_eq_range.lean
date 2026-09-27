/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Exactness of the Mayer–Vietoris sequence at the middle term, on cohomology

For a simplicial set `S` and two subcomplexes `A, B ⊆ S` with `A ⊔ B = ⊤`, the Mayer–Vietoris
sequence of cohomology groups

`H^j(S) --mvAlphaH--> H^j(A) × H^j(B) --mvBetaH--> H^j(A ⊓ B)`

is exact at the middle term: the kernel of `mvBetaH` (the difference of the two restrictions) is
the range of `mvAlphaH` (the pair of restrictions).  This is the cohomological counterpart of
`Work.Cohomology.mvBeta_ker_eq_range`, which is the same statement for the two cochain complexes
themselves.

The inclusion `range mvAlphaH ⊆ ker mvBetaH` is formal: on the class of a cocycle `u` on `S`,
both composites `pullbackCo (A ⊓ B ⊆ A) (pullbackCo (A ⊆ S) u)` and
`pullbackCo (A ⊓ B ⊆ B) (pullbackCo (B ⊆ S) u)` are the restriction of `u` to the intersection,
so they cancel (`mvBeta_comp_mvAlpha`).

The reverse inclusion is the interesting one.  Given `z = (x, y)` with
`mvBetaH z = 0` and representatives `u ∈ Z^j(A)`, `v ∈ Z^j(B)`, the cochain
`mvBeta (u, v) = pullbackCo (A ⊓ B ⊆ A) u - pullbackCo (A ⊓ B ⊆ B) v` is a coboundary of `A ⊓ B`.
In positive degree, say `j = m + 1`, write it as `∂c` with `c` of degree `m`, lift `c` to a pair
`(a, b)` on `A` resp. `B` (`mvLift`), and correct: `(u - ∂a, v - ∂b)` is then a cocycle pair
whose `mvBeta` vanishes, so by the cochain-level exactness (`mvExact`) it is the pair of
restrictions of a cochain `w` on `S`.  Since `mvAlpha` is injective, `w` is a cocycle, and
`u - (u - ∂a) = ∂a` is a coboundary, so `w` restricts to `x` and `y` in cohomology: `z` lies in
the range of `mvAlphaH`.  In degree `0` the boundaries of `A ⊓ B` are zero, so one can glue
`(u, v)` directly.
-/
import Mathlib
import Submission.Work.Cohomology.MVH
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Cohomology

/-! ## Elementary algebra of the quotient model of cohomology -/

/-- The difference of two cohomology classes is represented by the difference of cocycles. -/
private lemma Hmk_sub {S : SSet.{0}} {j : ℕ} (u v : Cochain S ℚ j)
    (hu : u ∈ cycles S ℚ j) (hv : v ∈ cycles S ℚ j) :
    H.mk u hu - H.mk v hv = H.mk (u - v) (Submodule.sub_mem _ hu hv) := by
  rw [H.mk, H.mk, H.mk]
  rw [← Submodule.Quotient.mk_sub]
  congr 1

/-- A cocycle whose class vanishes is a coboundary. -/
private lemma mem_boundaries_of_mk_eq_zero {S : SSet.{0}} {j : ℕ} {u : Cochain S ℚ j}
    (hu : u ∈ cycles S ℚ j) (h : H.mk u hu = 0) : u ∈ boundaries S ℚ j := by
  have h0 : (0 : H S ℚ j) = H.mk 0 (Submodule.zero_mem _) :=
    (Submodule.Quotient.mk_zero _).symm
  rw [h0, H.mk_eq_mk_iff] at h
  simpa using h

/-- A cocycle which is zero has vanishing class. -/
private lemma Hmk_zero_of_eq_zero {S : SSet.{0}} {j : ℕ} {u : Cochain S ℚ j}
    (hu : u ∈ cycles S ℚ j) (h : u = 0) : H.mk u hu = 0 := by
  subst h
  exact Submodule.Quotient.mk_zero _

/-! ## The gluing argument -/

/-- A cochain on `S` whose restrictions to the two pieces are given cocycles is itself a
cocycle: `mvAlpha` is injective and commutes with the coboundary, and the two components are
cocycles. -/
private lemma mem_cycles_of_mvAlpha_eq (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ)
    {w : Cochain S ℚ j} {u : Cochain A ℚ j} {v : Cochain B ℚ j}
    (hu : u ∈ cycles A ℚ j) (hv : v ∈ cycles B ℚ j) (h : mvAlpha S A B j w = (u, v)) :
    w ∈ cycles S ℚ j := by
  have hu0 : coboundary A ℚ j u = 0 := by simpa using hu
  have hv0 : coboundary B ℚ j v = 0 := by simpa using hv
  rw [mem_cycles_iff]
  apply mvAlpha_injective S A B hAB (j+1)
  rw [mvAlpha_coboundary, h, map_zero]
  apply Prod.ext
  · simpa using hu0
  · simpa using hv0

/-- **Exactness at the middle term, pointwise.**  A pair of cohomology classes on `A` and `B`
whose difference vanishes on `A ⊓ B` is the pair of restrictions of a class on `S`. -/
lemma mvBetaH_eq_zero_mem_range (S : SSet.{0}) (A B : S.Subcomplex)
    (hAB : A ⊔ B = ⊤) (j : ℕ) (z : H A ℚ j × H B ℚ j)
    (hz : mvBetaH S A B j z = 0) :
    z ∈ (mvAlphaH S A B j).range := by
  obtain ⟨x, y⟩ := z
  obtain ⟨u, hu, hx⟩ : ∃ u : Cochain A ℚ j, ∃ hu : u ∈ cycles A ℚ j, H.mk u hu = x :=
    ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩
  obtain ⟨v, hv, hy⟩ : ∃ v : Cochain B ℚ j, ∃ hv : v ∈ cycles B ℚ j, H.mk v hv = y :=
    ⟨(Quot.out y).1, (Quot.out y).2, Quot.out_eq y⟩
  rw [← hx, ← hy] at hz ⊢
  -- the difference of the two representatives is a coboundary on `A ⊓ B`
  have hr : mvBeta S A B j (u, v) ∈ boundaries (A ⊓ B : S.Subcomplex) ℚ j := by
    rw [mvBetaH_mk] at hz
    rw [Hmk_sub] at hz
    have hmem := mem_boundaries_of_mk_eq_zero
      (S := (A ⊓ B : S.Subcomplex)) (j := j)
      (u := pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) u
        - pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) v)
      (Submodule.sub_mem _ (pullbackCo_mem_cycles _ hu) (pullbackCo_mem_cycles _ hv)) hz
    simpa [mvBeta_apply] using hmem
  rcases j with _ | m
  · -- degree `0`: the boundaries on `A ⊓ B` are zero, so the pair glues as it is
    rw [show boundaries (A ⊓ B : S.Subcomplex) ℚ 0
        = (⊥ : Submodule ℚ (Cochain (A ⊓ B : S.Subcomplex) ℚ 0)) from rfl,
      Submodule.mem_bot] at hr
    have hmem : (u, v) ∈ (mvAlpha S A B 0).range := by
      rw [← mvExact S A B hAB 0]
      exact hr
    obtain ⟨w, hw⟩ := hmem
    have hpu : pullbackCo ℚ A.ι w = u := by
      have h := congrArg Prod.fst hw
      simpa using h
    have hpv : pullbackCo ℚ B.ι w = v := by
      have h := congrArg Prod.snd hw
      simpa using h
    have hwcyc : w ∈ cycles S ℚ 0 := mem_cycles_of_mvAlpha_eq S A B hAB 0 hu hv hw
    refine ⟨H.mk w hwcyc, ?_⟩
    rw [mvAlphaH_mk]
    apply Prod.ext
    · rw [H.mk_eq_mk_iff, hpu, sub_self]
      exact Submodule.zero_mem _
    · rw [H.mk_eq_mk_iff, hpv, sub_self]
      exact Submodule.zero_mem _
  · -- positive degree: correct the pair by the differential of a lift of a primitive of `mvBeta`
    obtain ⟨c, hc⟩ := (mem_boundaries_succ (mvBeta S A B (m+1) (u, v))).mp hr
    have hbeta0 : mvBeta S A B (m+1)
        (u - coboundary A ℚ m (mvLift S A B m c).1,
         v - coboundary B ℚ m (mvLift S A B m c).2) = 0 := by
      have hsub : (u - coboundary A ℚ m (mvLift S A B m c).1,
                   v - coboundary B ℚ m (mvLift S A B m c).2)
          = (u, v) - mvD S A B m (mvLift S A B m c) := by
        apply Prod.ext <;> simp [mvD_fst, mvD_snd]
      rw [hsub, map_sub, mvBeta_coboundary, mvBeta_mvLift, ← hc, sub_self]
    have hu0 : coboundary A ℚ (m+1) u = 0 := by simpa using hu
    have hv0 : coboundary B ℚ (m+1) v = 0 := by simpa using hv
    have hu' : u - coboundary A ℚ m (mvLift S A B m c).1 ∈ cycles A ℚ (m+1) := by
      rw [mem_cycles_iff, map_sub, hu0, coboundary_coboundary, sub_zero]
    have hv' : v - coboundary B ℚ m (mvLift S A B m c).2 ∈ cycles B ℚ (m+1) := by
      rw [mem_cycles_iff, map_sub, hv0, coboundary_coboundary, sub_zero]
    have hmem : (u - coboundary A ℚ m (mvLift S A B m c).1,
                 v - coboundary B ℚ m (mvLift S A B m c).2)
        ∈ (mvAlpha S A B (m+1)).range := by
      rw [← mvExact S A B hAB (m+1)]
      exact hbeta0
    obtain ⟨w, hw⟩ := hmem
    have hpu : pullbackCo ℚ A.ι w = u - coboundary A ℚ m (mvLift S A B m c).1 := by
      have h := congrArg Prod.fst hw
      simpa using h
    have hpv : pullbackCo ℚ B.ι w = v - coboundary B ℚ m (mvLift S A B m c).2 := by
      have h := congrArg Prod.snd hw
      simpa using h
    have hwcyc : w ∈ cycles S ℚ (m+1) :=
      mem_cycles_of_mvAlpha_eq S A B hAB (m+1) hu' hv' hw
    -- `u` and its correction differ by the coboundary `∂a`, hence have the same class
    have hAuth : H.mk u hu = H.mk (u - coboundary A ℚ m (mvLift S A B m c).1) hu' := by
      rw [H.mk_eq_mk_iff]
      exact ⟨(mvLift S A B m c).1, by abel⟩
    have hBth : H.mk v hv = H.mk (v - coboundary B ℚ m (mvLift S A B m c).2) hv' := by
      rw [H.mk_eq_mk_iff]
      exact ⟨(mvLift S A B m c).2, by abel⟩
    refine ⟨H.mk w hwcyc, ?_⟩
    rw [mvAlphaH_mk]
    apply Prod.ext
    · apply Eq.trans ?_ hAuth.symm
      rw [H.mk_eq_mk_iff, hpu, sub_self]
      exact Submodule.zero_mem _
    · apply Eq.trans ?_ hBth.symm
      rw [H.mk_eq_mk_iff, hpv, sub_self]
      exact Submodule.zero_mem _

/-- The composite of the two maps of the Mayer–Vietoris sequence is zero on cohomology. -/
lemma mvBetaH_mvAlphaH_eq_zero (S : SSet.{0}) (A B : S.Subcomplex) (j : ℕ) (x : H S ℚ j) :
    mvBetaH S A B j (mvAlphaH S A B j x) = 0 := by
  obtain ⟨u, hu, hx⟩ : ∃ u : Cochain S ℚ j, ∃ hu : u ∈ cycles S ℚ j, H.mk u hu = x :=
    ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩
  rw [← hx, mvAlphaH_mk, mvBetaH_mk]
  rw [Hmk_sub]
  have hzero : pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) (pullbackCo ℚ A.ι u)
      - pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) (pullbackCo ℚ B.ι u)
      = 0 := by
    show mvBeta S A B j (mvAlpha S A B j u) = 0
    exact LinearMap.congr_fun (mvBeta_comp_mvAlpha S A B j) u
  exact Hmk_zero_of_eq_zero _ hzero

/-- **Exactness of the Mayer–Vietoris sequence at the middle term, on cohomology.**  For
subcomplexes `A, B` covering `S`, the kernel of `mvBetaH` (the difference of the two
restrictions to `A ⊓ B`) is the range of `mvAlphaH` (the pair of restrictions to `A` and `B`). -/
theorem mvBetaH_ker_eq_range (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ) :
    LinearMap.ker (Submission.Cohomology.mvBetaH S A B j)
      = (Submission.Cohomology.mvAlphaH S A B j).range := by
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    exact mvBetaH_eq_zero_mem_range S A B hAB j z hz
  · rintro z ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    exact mvBetaH_mvAlphaH_eq_zero S A B j y

end Work.Cohomology
