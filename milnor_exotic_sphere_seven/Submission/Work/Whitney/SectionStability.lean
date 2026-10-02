import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Stability of the Chern classes, in the form needed for the Whitney formula

Let `Z` be a complex gluing-data bundle of rank `m + 1` over `B`, presented in the *standard* fibre
`EuclideanSpace ℂ (Fin (m+1))`, and let `σ : B → ↥(zeroComplement (realification Z))` be a
**continuous nowhere-zero section** of `Z` (i.e. a continuous section of the projection whose value
in each fibre is non-zero).  Then

  `c_j(Z) = c_j(σ^*(Q_Z))`   for all `j`,

where `Q_Z = Work.Thom.tautQuotient Z` is the tautological quotient of `Z` over the punctured total
space `Z∖0` (`Submission/Work/Thom/chernClass.lean`) and `σ^*(Q_Z)` is its pullback along `σ` — a
bundle over `B` of rank `m`, on the same base, indexed by `ι × Fin (m+1)`.

This is the **class-level form of stability**: the recursion (`Work.Thom.chernClass`) defines
`c_j(Z)` for `j ≤ m` as the *unique* class whose pullback along `π : Z∖0 → B` is `c_j(Q_Z)`, so
pulling that defining equation back along a section of `π` computes `c_j(Z)` out of the *quotient*
`σ^*(Q_Z)`; the top class `c_{m+1}(Z) = e(Z_ℝ)` vanishes because `σ` is nowhere zero, and so does
`c_{m+1}(σ^*(Q_Z))` (above the rank of `σ^*(Q_Z)`).

The special case in which `Z` is presented as a sum with a trivial summand and `σ` is the unit
section is the stability theorem `Work.Thom.chernClass_sumEps` of ADDENDUM 24 — here it is proved
for *any* nowhere-zero section, which is what the Whitney sum formula needs: over the punctured
total space of `F`, the pullback `π_F^*F` is a bundle with the *tautological* nowhere-zero section,
and the theorem identifies its Chern classes with those of the tautological quotient `Q_F`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **Stability of the Chern classes along a nowhere-zero section.**  For a complex bundle `Z` of
rank `m+1` in the standard fibre and a continuous nowhere-zero section `σ`, the Chern classes of `Z`
are those of the pullback of the tautological quotient along `σ`. -/
theorem chernClass_eq_of_nowhereZeroSection {m : ℕ} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (σ : C(B, ↥(zeroComplement (realification Z))))
    (hσ : ∀ b, ((σ b : ↥(zeroComplement (realification Z))) :
      (realification Z).TotalSpace).1 = b) (j : ℕ) :
    Work.Thom.chernClass (m + 1) j Z
      = Work.Thom.chernClass m j (Work.Thom.bundleComap (Work.Thom.tautQuotient Z) σ) := by
  -- `σ` is a section of the projection of the punctured total space.
  have hcomp : ((Work.Thom.bundleProj (realification Z)).comp
        (Work.Thom.subtypeMap (zeroComplement (realification Z)))).comp σ
      = ContinuousMap.id B := by
    ext b
    exact hσ b
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- degree `0`: `c_0 = 1` on both sides
    rw [Work.Thom.chernClass_zero_eq_oneH, Work.Thom.chernClass_zero_eq_oneH]
  · by_cases hj : j ≤ m
    · -- the descent equation for `Z`, pushed forward along the section `σ`
      have hdes : (Work.Thom.CohMap ((Work.Thom.bundleProj (realification Z)).comp
            (Work.Thom.subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom
            (Work.Thom.chernClass (m + 1) j Z)
          = Work.Thom.chernClass m j (Work.Thom.tautQuotient Z) := by
        rw [Work.Thom.chernClass_succ_of_le Z hj]
        exact LinearEquiv.apply_symm_apply
          (LinearEquiv.ofBijective
            ((Work.Thom.CohMap ((Work.Thom.bundleProj (realification Z)).comp
              (Work.Thom.subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom)
            (Work.Thom.bijective_proj_zeroComplementA (realification Z)
              (finrank_real_euclidean_complex (m + 1))
              (Work.Thom.thomClassRank (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) Z)
              (by omega)))
          (Work.Thom.chernClass m j (Work.Thom.tautQuotient Z))
      rw [Work.Thom.chernClass_comap (Z := Work.Thom.tautQuotient Z) (f := σ) (j := j), ← hdes]
      have key : (Work.Thom.CohMap (((Work.Thom.bundleProj (realification Z)).comp
              (Work.Thom.subtypeMap (zeroComplement (realification Z)))).comp σ) ℤ (2 * j)).hom
            (Work.Thom.chernClass (m + 1) j Z)
          = (Work.Thom.CohMap σ ℤ (2 * j)).hom
              ((Work.Thom.CohMap ((Work.Thom.bundleProj (realification Z)).comp
                (Work.Thom.subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j)).hom
                (Work.Thom.chernClass (m + 1) j Z)) := by
        rw [Work.Thom.CohMap_comp σ ((Work.Thom.bundleProj (realification Z)).comp
            (Work.Thom.subtypeMap (zeroComplement (realification Z)))) ℤ (2 * j),
          ModuleCat.hom_comp]
        rfl
      rw [← key, hcomp, Work.Thom.CohMap_id]
      rfl
    · -- degree above the rank of the quotient: both sides vanish
      rcases eq_or_lt_of_le (by omega : m + 1 ≤ j) with heq | hgt
      · subst heq
        rw [Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection (Nat.succ_le_succ (Nat.zero_le m))
            Z ((Work.Thom.subtypeMap (zeroComplement (realification Z))).comp σ)]
        · exact (Work.Thom.chernClass_eq_zero_of_lt _ (Nat.lt_succ_self m)).symm
        · intro b
          exact hσ b
        · intro b
          exact (σ b).2
      · rw [Work.Thom.chernClass_eq_zero_of_lt Z hgt,
          Work.Thom.chernClass_eq_zero_of_lt _ (by omega : m < j)]

end

end Work.Whitney
