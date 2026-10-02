import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.thomClassOf
import Submission.Work.Thom.tautQuotientCore_comap
import Submission.Work.Thom.tautQuotientComap
import Submission.Work.Thom.complexPullback
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.chernClass_zero_eq_oneH
import Submission.Work.Thom.chernClass_rank_zero_of_ne
import Submission.Work.Thom.thomClassOf_comapAux
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the Chern classes under pullback (the splitting principle, G2b)

For a complex vector bundle `Z` of rank `m` over `B` presented by gluing data over a finite index
type and a continuous map `f : B' → B`,

  `c_j(f^*Z) = f^*(c_j(Z))`   in `H^{2j}(B';ℤ)`.

The proof is the induction on the rank that mirrors the recursion defining `Work.Thom.chernClass`:

* rank `0`: `c_0 = 1` (`Work.Thom.chernClass_zero_eq_oneH`) and `f^*1 = 1`
  (`Work.Thom.CohMap_oneH`), `c_j = 0` for `j ≠ 0`;
* descent `j ≤ m`: the recursion, `Work.Thom.tautQuotientCore_comap`
  (`f^*(π^*Z/ℂ·s) = π^*(f^*Z)/ℂ·s`), the induction hypothesis, and the commutativity of the Gysin
  descent with pullback (`Work.Thom.descent_symm_general`);
* top `j = m+1`: `c_m(V) = e(V_ℝ)`, and the Euler class of the canonical Thom class is natural
  (`Work.Thom.thomClassOf_comap`);
* above the rank: both sides are `0`.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **Naturality of the Euler class of the canonical Thom class of the realification.** -/
theorem thomClassRank_eulerClass_comap {m : ℕ} {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι) (f : C(B',B)) :
    (thomClassRank (m+1) (Nat.succ_le_succ (Nat.zero_le m)) (bundleComap Z f)).eulerClass
      = (CohMap f ℤ (2*(m+1))).hom
          ((thomClassRank (m+1) (Nat.succ_le_succ (Nat.zero_le m)) Z).eulerClass) := by
  have htau := thomClassOf_comap_via_cover (m := m+1) (Nat.succ_le_succ (Nat.zero_le m)) Z f
  have hmap : (totalMapR Z f).comp
      (zeroSection (realification (bundleComap Z f)))
      = (zeroSection (realification Z)).comp f := by
    apply ContinuousMap.ext; intro x
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, totalMapR_apply, zeroSection_apply]
    rfl
  show (CohMap (zeroSection (realification (bundleComap Z f))) ℤ (2*(m+1))).hom
        ((openToAbs (realification (bundleComap Z f)) (2*(m+1))).hom
          (thomClassOf (Nat.succ_le_succ (Nat.zero_le m)) (bundleComap Z f)).τ)
      = (CohMap f ℤ (2*(m+1))).hom
        ((CohMap (zeroSection (realification Z)) ℤ (2*(m+1))).hom
          ((openToAbs (realification Z) (2*(m+1))).hom
            (thomClassOf (Nat.succ_le_succ (Nat.zero_le m)) Z).τ))
  rw [← htau]
  rw [relCohMap_relToAbs_apply (totalMapR Z f)
      (zeroComplement (realification (bundleComap Z f))) (zeroComplement (realification Z))
      (fun _ hp => hp) ℤ (2*(m+1)) (thomClassOf (Nat.succ_le_succ (Nat.zero_le m)) Z).τ]
  rw [CohMap_comp_apply (zeroSection (realification (bundleComap Z f)))
      (totalMapR Z f) ℤ (2*(m+1)) _]
  rw [hmap]
  rw [CohMap_comp_apply f (zeroSection (realification Z)) ℤ (2*(m+1)) _]

/-- **Naturality of the Chern classes under pullback**, by induction on the rank. -/
theorem chernClass_comap_aux :
    (m : ℕ) → ∀ {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (f : C(B', B)) (j : ℕ),
      chernClass m j (bundleComap Z f) = (CohMap f ℤ (2 * j)).hom (chernClass m j Z) := by
  intro m
  induction m with
  | zero =>
    intro B B' _ _ ι _ Z f j
    by_cases hj : j = 0
    · subst hj
      rw [chernClass_zero_eq_oneH, chernClass_zero_eq_oneH]
      exact (CohMap_oneH f).symm
    · rw [chernClass_rank_zero_of_ne (bundleComap Z f) hj, chernClass_rank_zero_of_ne Z hj,
        map_zero]
  | succ m ih =>
    intro B B' _ _ ι _ Z f j
    by_cases hle : j ≤ m
    · rw [chernClass_succ_of_le Z hle, chernClass_succ_of_le (bundleComap Z f) hle]
      have e1 : tautQuotient (bundleComap Z f)
          = bundleComap (tautQuotient Z) (punctMap Z f) := by
        rw [tautQuotient, tautQuotient]
        exact (tautQuotientCore_comap Z f).symm
      rw [e1, ih (tautQuotient Z) (punctMap Z f) j]
      exact descent_symm_general Z f _ _ rfl rfl _
    · by_cases htop : j = m + 1
      · subst htop
        rw [chernClass_succ_top', chernClass_succ_top']
        exact thomClassRank_eulerClass_comap Z f
      · rw [chernClass_succ_of_gt (bundleComap Z f) (by omega), chernClass_succ_of_gt Z (by omega),
          map_zero]

/-- **Naturality of the Chern classes under pullback** (the splitting principle for the Chern
recursion). -/
theorem chernClass_comap {m j : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (f : C(B', B)) :
    Work.Thom.chernClass m j (Work.Thom.bundleComap Z f)
      = (Work.Thom.CohMap f ℤ (2 * j)).hom (Work.Thom.chernClass m j Z) :=
  chernClass_comap_aux m Z f j

end

end Work.Thom
