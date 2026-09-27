/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The connecting map of the Mayer–Vietoris sequence over `ℚ`

For a simplicial set `S` with two subcomplexes `A, B` covering `S`, the short exact sequence of
cochain complexes

`0 ⟶ C^•(S) --α--> C^•(A) ⊕ C^•(B) --β--> C^•(A ∩ B) ⟶ 0`

of `MVBasic.lean` produces the connecting map

`δ : H (A ∩ B) ℚ k ⟶ H S ℚ (k+1)`

on cohomology: given a cocycle `c` on `A ∩ B`, lift it to a pair `(a,b)` on `A`, `B` via a chosen
linear splitting of `β`, apply the differential, and push the result back to `S` via a chosen
linear retraction of `α` (this is possible because `ker β = range α`, see
`Work.Cohomology.mvBeta_ker_eq_range`).  The result is a cocycle, and the construction kills
coboundaries, so it descends to cohomology.

Everything in this file is stated with the exactness hypothesis
`hker : LinearMap.ker (mvBeta S A B n) = (mvAlpha S A B n).range` as an explicit argument, so that
the file does not depend on `Work.Cohomology.mvBeta_ker_eq_range`.
-/
import Mathlib
import Submission.Work.Cohomology.MVBasic

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Cohomology

noncomputable section

variable {S : SSet.{0}}

/-! ## Chosen linear inverses -/

/-- A chosen `ℚ`-linear splitting of the surjection `mvBeta`: it lifts a cochain on the
intersection of the two pieces to a pair of cochains on the pieces. -/
def mvLift (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    Cochain (A ⊓ B : S.Subcomplex) ℚ n →ₗ[ℚ] (Cochain A ℚ n × Cochain B ℚ n) :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (mvBeta S A B n)
    (LinearMap.range_eq_top.mpr (mvBeta_surjective S A B n)))

/-- The splitting property of `mvLift`. -/
lemma mvBeta_comp_mvLift (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ) :
    (mvBeta S A B n).comp (mvLift S A B n) = LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective (mvBeta S A B n)
    (LinearMap.range_eq_top.mpr (mvBeta_surjective S A B n)))

@[simp] lemma mvBeta_mvLift (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (c : Cochain (A ⊓ B : S.Subcomplex) ℚ n) : mvBeta S A B n (mvLift S A B n c) = c :=
  LinearMap.ext_iff.mp (mvBeta_comp_mvLift S A B n) c

/-- A chosen `ℚ`-linear retraction of the injection `mvAlpha`. -/
def mvProj (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ) :
    (Cochain A ℚ n × Cochain B ℚ n) →ₗ[ℚ] Cochain S ℚ n :=
  Classical.choose (LinearMap.exists_leftInverse_of_injective (mvAlpha S A B n)
    (LinearMap.ker_eq_bot.mpr (mvAlpha_injective S A B hAB n)))

/-- The retraction property of `mvProj`. -/
lemma mvProj_comp_mvAlpha (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ) :
    (mvProj S A B hAB n).comp (mvAlpha S A B n) = LinearMap.id :=
  Classical.choose_spec (LinearMap.exists_leftInverse_of_injective (mvAlpha S A B n)
    (LinearMap.ker_eq_bot.mpr (mvAlpha_injective S A B hAB n)))

@[simp] lemma mvProj_mvAlpha (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ)
    (u : Cochain S ℚ n) : mvProj S A B hAB n (mvAlpha S A B n u) = u :=
  LinearMap.ext_iff.mp (mvProj_comp_mvAlpha S A B hAB n) u

/-- `mvProj` is a retraction of `mvAlpha` on the range of `mvAlpha`. -/
lemma mvAlpha_mvProj (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (n : ℕ)
    {y : Cochain A ℚ n × Cochain B ℚ n} (hy : y ∈ (mvAlpha S A B n).range) :
    mvAlpha S A B n (mvProj S A B hAB n y) = y := by
  obtain ⟨u, rfl⟩ := hy
  rw [mvProj_mvAlpha]

/-! ## The connecting map on representatives -/

/-- The connecting map `δ` on representatives: lift, differentiate, and push back. -/
def mvDeltaRep (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ) :
    Cochain (A ⊓ B : S.Subcomplex) ℚ k →ₗ[ℚ] Cochain S ℚ (k+1) :=
  (mvProj S A B hAB (k+1)).comp ((mvD S A B k).comp (mvLift S A B k))

/-- The differential of the lifted cochain lies in the range of `mvAlpha` whenever the input is a
cocycle; this is where the exactness `ker mvBeta = range mvAlpha` is used. -/
lemma mvD_mvLift_mem_range (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k) :
    mvD S A B k (mvLift S A B k c) ∈ (mvAlpha S A B (k+1)).range := by
  rw [← hker (k+1), LinearMap.mem_ker, mvBeta_coboundary, mvBeta_mvLift]
  exact hc

/-- The defining property of the connecting map on a cocycle. -/
lemma mvAlpha_mvDeltaRep (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k) :
    mvAlpha S A B (k+1) (mvDeltaRep S A B hAB k c) = mvD S A B k (mvLift S A B k c) := by
  rw [mvDeltaRep, LinearMap.comp_apply, LinearMap.comp_apply]
  exact mvAlpha_mvProj S A B hAB (k+1) (mvD_mvLift_mem_range S A B hAB k hker hc)

/-- The connecting map of a cocycle is a cocycle. -/
lemma mvDeltaRep_mem_cycles (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k) :
    mvDeltaRep S A B hAB k c ∈ cycles S ℚ (k+1) := by
  rw [mem_cycles_iff]
  refine mvAlpha_injective S A B hAB (k+1+1) ?_
  rw [mvAlpha_coboundary, mvAlpha_mvDeltaRep S A B hAB k hker hc, mvD_mvD, map_zero]

/-- The connecting map of a coboundary is a coboundary: `mvDeltaRep` descends to cohomology. -/
lemma mvDeltaRep_mem_boundaries (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ boundaries (A ⊓ B : S.Subcomplex) ℚ k) :
    mvDeltaRep S A B hAB k c ∈ boundaries S ℚ (k+1) := by
  rcases k with _ | m
  · rw [boundaries, Submodule.mem_bot] at hc
    rw [hc, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨c', hc'⟩ := (mem_boundaries_succ c).mp hc
    have hzero : mvBeta S A B (m+1)
        (mvLift S A B (m+1) c - mvD S A B m (mvLift S A B m c')) = 0 := by
      rw [map_sub, mvBeta_mvLift, mvBeta_coboundary, mvBeta_mvLift, ← hc']
      exact sub_self _
    have hmem : mvLift S A B (m+1) c - mvD S A B m (mvLift S A B m c')
        ∈ LinearMap.ker (mvBeta S A B (m+1)) := LinearMap.mem_ker.mpr hzero
    rw [hker (m+1)] at hmem
    obtain ⟨w, hw⟩ := hmem
    have hlift : mvLift S A B (m+1) c
        = mvD S A B m (mvLift S A B m c') + mvAlpha S A B (m+1) w := by
      rw [hw]; abel
    refine ⟨w, ?_⟩
    rw [mvDeltaRep, LinearMap.comp_apply, LinearMap.comp_apply, hlift, map_add, mvD_mvD, zero_add,
      ← mvAlpha_coboundary, mvProj_mvAlpha]

/-! ## The connecting map on cohomology -/

/-- The connecting map, on cocycles. -/
def mvDeltaCycles (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range) :
    cycles (A ⊓ B : S.Subcomplex) ℚ k →ₗ[ℚ] cycles S ℚ (k+1) where
  toFun c := ⟨mvDeltaRep S A B hAB k c.1, mvDeltaRep_mem_cycles S A B hAB k hker c.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' r x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]

/-- `mvDeltaCycles` sends coboundaries to coboundaries. -/
lemma boundariesInCycles_le_ker_mvDeltaCycles (S : SSet.{0}) (A B : S.Subcomplex)
    (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range) :
    boundariesInCycles (A ⊓ B : S.Subcomplex) ℚ k ≤
      LinearMap.ker ((Submodule.mkQ (boundariesInCycles S ℚ (k+1))).comp
        (mvDeltaCycles S A B hAB k hker)) := by
  intro c hc
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  change Submodule.Quotient.mk (mvDeltaCycles S A B hAB k hker c) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_comap.mpr
    (mvDeltaRep_mem_boundaries S A B hAB k hker (Submodule.mem_comap.mp hc))

/-- **The connecting map of the Mayer–Vietoris sequence** over `ℚ`. -/
def mvDelta (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range) :
    H (A ⊓ B : S.Subcomplex) ℚ k →ₗ[ℚ] H S ℚ (k+1) :=
  (boundariesInCycles (A ⊓ B : S.Subcomplex) ℚ k).liftQ
    ((Submodule.mkQ (boundariesInCycles S ℚ (k+1))).comp (mvDeltaCycles S A B hAB k hker))
    (boundariesInCycles_le_ker_mvDeltaCycles S A B hAB k hker)

/-- The computation rule for the connecting map on the class of a cocycle. -/
lemma mvDelta_mk (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hker : ∀ j : ℕ, LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k) :
    mvDelta S A B hAB k hker (H.mk c hc)
      = H.mk (mvDeltaRep S A B hAB k c) (mvDeltaRep_mem_cycles S A B hAB k hker hc) := by
  rw [show mvDelta S A B hAB k hker (H.mk c hc)
      = (boundariesInCycles (A ⊓ B : S.Subcomplex) ℚ k).liftQ
          ((Submodule.mkQ (boundariesInCycles S ℚ (k+1))).comp
            (mvDeltaCycles S A B hAB k hker))
          (boundariesInCycles_le_ker_mvDeltaCycles S A B hAB k hker)
          (Submodule.Quotient.mk ⟨c, hc⟩) from rfl]
  rw [Submodule.liftQ_apply]
  rfl

end

end Submission.Cohomology
