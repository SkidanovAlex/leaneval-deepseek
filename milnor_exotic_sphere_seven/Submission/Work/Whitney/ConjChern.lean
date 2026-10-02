import Mathlib
import Submission.Work.Whitney.ConjTop
import Submission.Work.Whitney.nonempty_bundleIso_conjCore_tautQuotient
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-!
# The sign rule for the Chern classes of the conjugate bundle

`Work.Whitney.chernClass_conjCore` is the complete form of deliverable item 4 of the WHITNEY
subproject:

  `c_j(Z̄) = (-1)^j c_j(Z)`   for every complex bundle `Z` and every `j`.

The proof is strong induction on the rank.  For `j = rank` this is
`Work.Whitney.chernClass_conjCore_top` (the Euler class of the realification, with the conjugation
gauge of determinant `(-1)^m`); for `j ≤ rank − 1` one pulls the descent equation
`π^*c_j = c_j(Q)` (`Work.Thom.chernClass_succ_of_le`) of `Z̄` back along the conjugation
homeomorphism of the punctured total spaces, and identifies the tautological quotient of `Z̄` with
the conjugate of the tautological quotient of `Z`
(`Work.Whitney.nonempty_bundleIso_conjCore_tautQuotient`), which puts the induction hypothesis in
play; above the rank both sides vanish.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- The two punctured projections are intertwined by the conjugation map of the punctured total
spaces. -/
theorem punctProjE_comp_conjPunctCM {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι) :
    (punctProjE (conjCore Z)).comp (conjPunctCM Z) = punctProjE Z := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- An auxiliary bookkeeping fact: for an additive map of cohomology modules, the `ℤ`-scalar
`(-1)^j` commutes with the map (the scalar action here is the one of the additive group, so this is
not `LinearMap.map_smul`). -/
theorem zsmul_neg_one_pow_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n k : ℕ}
    (P : (↥(Work.Thom.Coh ℤ n X)) →ₗ[ℤ] (↥(Work.Thom.Coh ℤ k Y))) (j : ℕ)
    (x : ↥(Work.Thom.Coh ℤ n X)) :
    ((-1 : ℤ) ^ j) • P x = P (((-1 : ℤ) ^ j) • x) := by
  rcases Nat.even_or_odd j with hev | hodd
  · rw [hev.neg_one_pow, show (1 : ℤ) • P x = P x from by simp,
      show (1 : ℤ) • x = x from by simp]
  · rw [hodd.neg_one_pow, show (-1 : ℤ) • P x = -P x from by simp,
      show (-1 : ℤ) • x = -x from by simp, map_neg]

/-- **The sign rule for the conjugate bundle**: `c_j(Z̄) = (-1)^j c_j(Z)`. -/
theorem chernClass_conjCore (m : ℕ) {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (j : ℕ) :
    Work.Thom.chernClass m j (conjCore Z) = ((-1 : ℤ) ^ j) • Work.Thom.chernClass m j Z := by
  induction m generalizing B ι with
  | zero =>
    rw [Work.Thom.chernClass_zero_rank, Work.Thom.chernClass_zero_rank]
    by_cases h : j = 0
    · subst h
      simp [Work.Thom.chernClassZero]
    · rw [show Work.Thom.chernClassZero j (conjCore Z) = 0 from by
            simp [Work.Thom.chernClassZero, h],
          show Work.Thom.chernClassZero j Z = 0 from by simp [Work.Thom.chernClassZero, h]]
      rcases Nat.even_or_odd j with hev | hodd
      · rw [hev.neg_one_pow]; simp
      · rw [hodd.neg_one_pow]; simp
  | succ m' ih =>
    by_cases hj : j = m' + 1
    · subst hj
      exact chernClass_conjCore_top (m := m' + 1) (Nat.succ_le_succ (Nat.zero_le m')) Z
    · by_cases hj' : j ≤ m'
      · -- the descent over the punctured total spaces
        have hbij : Function.Bijective
            ((Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom) :=
          Work.Thom.bijective_proj_zeroComplementA (k := 2 * j) (Work.Thom.realification Z)
            (Work.Thom.finrank_real_euclidean_complex (m' + 1))
            (Work.Thom.thomClassRank (m' + 1) (Nat.succ_le_succ (Nat.zero_le m')) Z) (by omega)
        refine hbij.1 ?_
        -- the descent equation of `Z`
        have hZπ : (Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom
              (Work.Thom.chernClass (m' + 1) j Z)
            = Work.Thom.chernClass m' j (Work.Thom.tautQuotient (m := m') Z) := by
          have h := congrArg ((Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom)
            (Work.Thom.chernClass_succ_of_le (m := m') Z hj')
          simpa using h
        -- the descent equation of `Z̄`
        have hZbπ : (Work.Thom.CohMap (punctProjE (conjCore Z)) ℤ (2 * j)).hom
              (Work.Thom.chernClass (m' + 1) j (conjCore Z))
            = Work.Thom.chernClass m' j (Work.Thom.tautQuotient (m := m') (conjCore Z)) := by
          have h := congrArg ((Work.Thom.CohMap (punctProjE (conjCore Z)) ℤ (2 * j)).hom)
            (Work.Thom.chernClass_succ_of_le (m := m') (conjCore Z) hj')
          simpa using h
        -- the projection of `Z̄` factors through the conjugation homeomorphism
        have hcomp : ((Work.Thom.CohMap (conjPunctCM Z) ℤ (2 * j)).hom)
              (((Work.Thom.CohMap (punctProjE (conjCore Z)) ℤ (2 * j)).hom)
                (Work.Thom.chernClass (m' + 1) j (conjCore Z)))
            = (Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom
                (Work.Thom.chernClass (m' + 1) j (conjCore Z)) := by
          rw [Work.Thom.CohMap_comp_apply (conjPunctCM Z) (punctProjE (conjCore Z)) ℤ (2 * j),
            punctProjE_comp_conjPunctCM (m := m') Z]
        -- the quotient of `Z̄` is the conjugate of the quotient of `Z`
        have hQ : (Work.Thom.CohMap (conjPunctCM Z) ℤ (2 * j)).hom
              (Work.Thom.chernClass m' j (Work.Thom.tautQuotient (m := m') (conjCore Z)))
            = ((-1 : ℤ) ^ j) •
                Work.Thom.chernClass m' j (Work.Thom.tautQuotient (m := m') Z) := by
          rw [← Work.Thom.chernClass_comap (Work.Thom.tautQuotient (m := m') (conjCore Z))
            (conjPunctCM Z)]
          have hiso : Work.Thom.chernClass m' j
                (Work.Thom.bundleComap (Work.Thom.tautQuotient (m := m') (conjCore Z))
                  (conjPunctCM Z))
              = Work.Thom.chernClass m' j (conjCore (Work.Thom.tautQuotient (m := m') Z)) := by
            obtain ⟨e⟩ := nonempty_bundleIso_conjCore_tautQuotient (m := m') Z
            exact Work.Thom.chernClass_BundleIso _ _ e
          rw [hiso, ih (Work.Thom.tautQuotient (m := m') Z)]
        calc (Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom
              (Work.Thom.chernClass (m' + 1) j (conjCore Z))
            = ((Work.Thom.CohMap (conjPunctCM Z) ℤ (2 * j)).hom)
                (((Work.Thom.CohMap (punctProjE (conjCore Z)) ℤ (2 * j)).hom)
                  (Work.Thom.chernClass (m' + 1) j (conjCore Z))) := hcomp.symm
          _ = ((Work.Thom.CohMap (conjPunctCM Z) ℤ (2 * j)).hom)
                (Work.Thom.chernClass m' j
                  (Work.Thom.tautQuotient (m := m') (conjCore Z))) := by
              rw [hZbπ]
          _ = ((-1 : ℤ) ^ j) • Work.Thom.chernClass m' j
                (Work.Thom.tautQuotient (m := m') Z) := hQ
          _ = ((-1 : ℤ) ^ j) • (Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom
                (Work.Thom.chernClass (m' + 1) j Z) := by
              rw [hZπ]
          _ = (Work.Thom.CohMap (punctProjE Z) ℤ (2 * j)).hom
                (((-1 : ℤ) ^ j) • Work.Thom.chernClass (m' + 1) j Z) :=
              zsmul_neg_one_pow_map _ j _
      · -- above the rank both sides vanish
        have hgt : m' + 1 < j := by omega
        rw [Work.Thom.chernClass_succ_of_gt Z hgt,
          Work.Thom.chernClass_succ_of_gt (conjCore Z) hgt]
        rcases Nat.even_or_odd j with hev | hodd
        · rw [hev.neg_one_pow]; simp
        · rw [hodd.neg_one_pow]; simp

end

end Work.Whitney
