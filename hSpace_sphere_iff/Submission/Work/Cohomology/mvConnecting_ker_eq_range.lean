/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Exactness of the Mayer–Vietoris sequence at the middle cohomology group

For a simplicial set `S` and subcomplexes `A, B ⊆ S` covering `S`, the long exact Mayer–Vietoris
sequence reads

`⋯ ⟶ H A ℚ j × H B ℚ j --mvBetaH--> H (A ⊓ B) ℚ j --mvConnecting--> H S ℚ (j+1) ⟶ ⋯`

The map `mvBetaH` is the difference of the two restrictions to `A` and to `B`, and
`mvConnecting = mvDelta` is the connecting map constructed in `MayerVietoris.lean` from a chosen
splitting of `mvBeta` and a chosen retraction of `mvAlpha`.  This file proves exactness at
`H (A ⊓ B) ℚ j`, i.e.

`LinearMap.ker (mvConnecting S A B hAB j) = (mvBetaH S A B j).range`.

The two inclusions are proved by explicit computation with the representatives:

* `range (mvBetaH) ⊆ ker (mvConnecting)`: it suffices to show that the connecting map kills the
  image of `H.map` along `A ⊓ B ↪ A` (and along `A ⊓ B ↪ B`).  If `a` is a cocycle on `A` and
  `c = pullbackCo A a`, then the pair `(a, 0)` maps to `c` under `mvBeta`, so
  `mvLift c - (a, 0) ∈ ker mvBeta = range mvAlpha`: `mvLift c = (a, 0) + mvAlpha w`.  Hence
  `mvD (mvLift c) = mvAlpha (δw)` because `a` is a cocycle, so
  `mvDeltaRep c = mvProj (mvD (mvLift c)) = δw` is a coboundary.  (See
  `mvDeltaRep_eq_coboundary_of_lift`; the version for `B` takes the pair `(0, -b)`.)

* `ker (mvConnecting) ⊆ range (mvBetaH)`: given a cocycle `c` on `A ⊓ B` with
  `mvConnecting (H.mk c hc) = 0`, the cocycle `mvDeltaRep c` is a coboundary `δq` on `S`; with
  `p := mvLift c - mvAlpha q` we get `mvD p = 0` (using `mvAlpha_mvDeltaRep`) and
  `mvBeta p = mvBeta (mvLift c) = c`.  So `p` is a pair of cocycles on `A` and `B` and
  `H.mk c hc = mvBetaH (H.mk p.1 hp1, H.mk p.2 hp2)`.
-/
import Mathlib
import Submission.Work.Cohomology.MVH
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

/-! ## Elementary lemmas about the class of a cocycle -/

lemma Hmk_irrel {S : SSet.{0}} {n : ℕ} (u : Cochain S ℚ n)
    (h1 h2 : u ∈ cycles S ℚ n) : H.mk u h1 = H.mk u h2 := by
  simp only [H.mk]

/-- A cocycle that is a coboundary has vanishing cohomology class. -/
lemma Hmk_eq_zero_of_mem_boundaries {S : SSet.{0}} {n : ℕ} {z : Cochain S ℚ n}
    (hz : z ∈ cycles S ℚ n) (hb : z ∈ boundaries S ℚ n) : H.mk z hz = 0 := by
  rw [H.mk, Submodule.Quotient.mk_eq_zero, boundariesInCycles, Submodule.mem_comap]
  simpa using hb

/-- The cohomology class of a cocycle vanishes exactly when the cocycle is a coboundary. -/
lemma Hmk_eq_zero_iff {S : SSet.{0}} {n : ℕ} (z : Cochain S ℚ n) (hz : z ∈ cycles S ℚ n) :
    H.mk z hz = 0 ↔ z ∈ boundaries S ℚ n := by
  rw [show (0 : H S ℚ n) = H.mk 0 (Submodule.zero_mem _) from rfl, H.mk_eq_mk_iff]
  simp

/-- The class of a difference of cocycles is the difference of the classes. -/
lemma Hmk_sub {S : SSet.{0}} {n : ℕ} (u v : Cochain S ℚ n) (hu : u ∈ cycles S ℚ n)
    (hv : v ∈ cycles S ℚ n) :
    H.mk u hu - H.mk v hv = H.mk (u - v) (Submodule.sub_mem _ hu hv) := by
  show Submodule.Quotient.mk (p := boundariesInCycles S ℚ n) ⟨u, hu⟩
      - Submodule.Quotient.mk (p := boundariesInCycles S ℚ n) ⟨v, hv⟩
      = Submodule.Quotient.mk (p := boundariesInCycles S ℚ n)
        ⟨u - v, Submodule.sub_mem _ hu hv⟩
  rw [← Submodule.mkQ_apply (boundariesInCycles S ℚ n) (⟨u,hu⟩ : cycles S ℚ n),
    ← Submodule.mkQ_apply (boundariesInCycles S ℚ n) (⟨v,hv⟩ : cycles S ℚ n),
    ← Submodule.mkQ_apply (boundariesInCycles S ℚ n)
      (⟨u-v, Submodule.sub_mem _ hu hv⟩ : cycles S ℚ n), ← map_sub]
  congr 1

/-- Pullback of cochains preserves `0`. -/
lemma mvPullbackCo_zero {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n : ℕ} :
    pullbackCo R f (0 : Cochain T R n) = 0 := by
  ext σ; rfl

/-- Pullback of cochains preserves negation. -/
lemma mvPullbackCo_neg {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n : ℕ}
    (u : Cochain T R n) : pullbackCo R f (-u) = - pullbackCo R f u := by
  ext σ; rfl

/-! ## The connecting map of a piecewise-acyclic cocycle is a coboundary -/

/-- If a cocycle `c` on `A ⊓ B` admits a pair `p` on `A × B` with `mvBeta p = c` and
`mvD p = 0` (i.e. whose two components are cocycles), then `mvDeltaRep c` is a coboundary
on `S`.  Indeed `mvLift c - p ∈ ker mvBeta = range mvAlpha`, so `mvLift c = p + mvAlpha w`,
and since `mvD p = 0` we get `mvD (mvLift c) = mvAlpha (δw)`, whence
`mvDeltaRep c = mvProj (mvD (mvLift c)) = δw`. -/
lemma mvDeltaRep_eq_coboundary_of_lift (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤)
    (j : ℕ) {c : Cochain (A ⊓ B : S.Subcomplex) ℚ j}
    {p : Cochain A ℚ j × Cochain B ℚ j} (hbeta : mvBeta S A B j p = c)
    (hp : mvD S A B j p = 0) :
    ∃ w : Cochain S ℚ j, mvDeltaRep S A B hAB j c = coboundary S ℚ j w := by
  have hmem : mvLift S A B j c - p ∈ LinearMap.ker (mvBeta S A B j) := by
    rw [LinearMap.mem_ker, map_sub, mvBeta_mvLift, hbeta, sub_self]
  rw [mvExact S A B hAB j] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, ?_⟩
  have hsplit : mvLift S A B j c = p + mvAlpha S A B j w := by
    rw [hw]; abel
  have hD : mvD S A B j (mvLift S A B j c) = mvAlpha S A B (j+1) (coboundary S ℚ j w) := by
    rw [hsplit, map_add, mvAlpha_coboundary, hp, zero_add]
  rw [mvDeltaRep, LinearMap.comp_apply, LinearMap.comp_apply, hD, mvProj_mvAlpha]

/-- The connecting map kills the restriction of a cocycle of `A` to `A ⊓ B`. -/
lemma mvDeltaRep_pullbackCo_left_mem_boundaries (S : SSet.{0}) (A B : S.Subcomplex)
    (hAB : A ⊔ B = ⊤) (j : ℕ) {a : Cochain A ℚ j} (ha : a ∈ cycles A ℚ j) :
    mvDeltaRep S A B hAB j (pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) a)
      ∈ boundaries S ℚ (j+1) := by
  have hbeta : mvBeta S A B j (a, (0 : Cochain B ℚ j))
      = pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) a := by
    rw [mvBeta_apply, mvPullbackCo_zero, sub_zero]
  have hp : mvD S A B j (a, (0 : Cochain B ℚ j)) = 0 := by
    apply Prod.ext
    · rw [mvD_fst]; simp only [Prod.fst_zero]; exact (mem_cycles_iff a).mp ha
    · rw [mvD_snd]; simp only [Prod.snd_zero]; simp
  obtain ⟨w, hw⟩ := mvDeltaRep_eq_coboundary_of_lift S A B hAB j hbeta hp
  rw [hw]
  exact (mem_boundaries_succ _).mpr ⟨w, rfl⟩

/-- The connecting map kills the restriction of a cocycle of `B` to `A ⊓ B`. -/
lemma mvDeltaRep_pullbackCo_right_mem_boundaries (S : SSet.{0}) (A B : S.Subcomplex)
    (hAB : A ⊔ B = ⊤) (j : ℕ) {b : Cochain B ℚ j} (hb : b ∈ cycles B ℚ j) :
    mvDeltaRep S A B hAB j (pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) b)
      ∈ boundaries S ℚ (j+1) := by
  have hbeta : mvBeta S A B j ((0 : Cochain A ℚ j), -b)
      = pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) b := by
    rw [mvBeta_apply, mvPullbackCo_zero, mvPullbackCo_neg, sub_neg_eq_add, zero_add]
  have hp : mvD S A B j ((0 : Cochain A ℚ j), -b) = 0 := by
    apply Prod.ext
    · rw [mvD_fst]; simp only [Prod.fst_zero]; simp
    · rw [mvD_snd]; simp only [Prod.snd_zero]
      rw [map_neg, (mem_cycles_iff b).mp hb, neg_zero]
  obtain ⟨w, hw⟩ := mvDeltaRep_eq_coboundary_of_lift S A B hAB j hbeta hp
  rw [hw]
  exact (mem_boundaries_succ _).mpr ⟨w, rfl⟩

/-- The connecting map vanishes on the image of `H.map` along `A ⊓ B ↪ A`. -/
lemma mvConnecting_Hmap_left (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ)
    (u : H A ℚ j) :
    mvConnecting S A B hAB j (H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) j u)
      = 0 := by
  obtain ⟨a, ha, rfl⟩ : ∃ (a : Cochain A ℚ j) (ha : a ∈ cycles A ℚ j), H.mk a ha = u :=
    ⟨(Quot.out u).1, (Quot.out u).2, Quot.out_eq u⟩
  rw [H.map_mk, mvConnecting_mk]
  exact Hmk_eq_zero_of_mem_boundaries _
    (mvDeltaRep_pullbackCo_left_mem_boundaries S A B hAB j ha)

/-- The connecting map vanishes on the image of `H.map` along `A ⊓ B ↪ B`. -/
lemma mvConnecting_Hmap_right (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ)
    (u : H B ℚ j) :
    mvConnecting S A B hAB j (H.map ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) j u)
      = 0 := by
  obtain ⟨b, hb, rfl⟩ : ∃ (b : Cochain B ℚ j) (hb : b ∈ cycles B ℚ j), H.mk b hb = u :=
    ⟨(Quot.out u).1, (Quot.out u).2, Quot.out_eq u⟩
  rw [H.map_mk, mvConnecting_mk]
  exact Hmk_eq_zero_of_mem_boundaries _
    (mvDeltaRep_pullbackCo_right_mem_boundaries S A B hAB j hb)

/-! ## Exactness at `H (A ⊓ B)` -/

theorem mvConnecting_ker_eq_range (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ) :
    LinearMap.ker (Submission.Cohomology.mvConnecting S A B hAB j)
      = (Submission.Cohomology.mvBetaH S A B j).range := by
  apply le_antisymm
  · -- `ker (mvConnecting) ⊆ range (mvBetaH)`
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨c, hc, rfl⟩ : ∃ (c : Cochain (A ⊓ B : S.Subcomplex) ℚ j),
        ∃ hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ j, H.mk c hc = x :=
      ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩
    rw [mvConnecting_mk] at hx
    -- the connecting map of `c` is a coboundary on `S`
    have hbound : mvDeltaRep S A B hAB j c ∈ boundaries S ℚ (j+1) :=
      (Hmk_eq_zero_iff (mvDeltaRep S A B hAB j c) _).mp hx
    obtain ⟨q, hq⟩ := (mem_boundaries_succ (mvDeltaRep S A B hAB j c)).mp hbound
    -- the corrected lift `p = mvLift c - mvAlpha q` is a pair of cocycles
    set p : Cochain A ℚ j × Cochain B ℚ j := mvLift S A B j c - mvAlpha S A B j q with hpdef
    have hpd : mvD S A B j p = 0 := by
      rw [hpdef, map_sub]
      have h1 : mvD S A B j (mvLift S A B j c)
          = mvAlpha S A B (j+1) (mvDeltaRep S A B hAB j c) :=
        (mvAlpha_mvDeltaRep S A B hAB j (fun i => mvExact S A B hAB i) hc).symm
      have h2 : mvD S A B j (mvAlpha S A B j q)
          = mvAlpha S A B (j+1) (mvDeltaRep S A B hAB j c) := by
        rw [← mvAlpha_coboundary S A B j q, hq]
      rw [h1, h2, sub_self]
    have hp1 : p.1 ∈ cycles A ℚ j := by
      have h := congrArg Prod.fst hpd; simpa using h
    have hp2 : p.2 ∈ cycles B ℚ j := by
      have h := congrArg Prod.snd hpd; simpa using h
    have hc_eq : mvBeta S A B j p = c := by
      rw [hpdef, map_sub, mvBeta_mvLift]
      have h0 : mvBeta S A B j (mvAlpha S A B j q) = 0 := by
        have h := LinearMap.congr_fun (mvBeta_comp_mvAlpha S A B j) q
        simpa [LinearMap.comp_apply] using h
      rw [h0, sub_zero]
    refine ⟨(H.mk p.1 hp1, H.mk p.2 hp2), ?_⟩
    rw [mvBetaH_mk, Hmk_sub]
    rw [H.mk_eq_mk_iff]
    rw [show pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) p.1
          - pullbackCo ℚ (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) p.2
        = mvBeta S A B j p from (mvBeta_apply S A B j p).symm, hc_eq, sub_self]
    exact Submodule.zero_mem _
  · -- `range (mvBetaH) ⊆ ker (mvConnecting)`
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, mvBetaH_apply]
    rw [map_sub, mvConnecting_Hmap_left S A B hAB j y.1,
      mvConnecting_Hmap_right S A B hAB j y.2, sub_zero]

end Work.Cohomology
