import Mathlib
import Submission.Work.Whitney.WSumChars

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney

open Work.Thom
open CategoryTheory

/-! ## Auxiliary lemmas for the assembly

The five groups of lemmas below are the bookkeeping that the assembly
`Work.Whitney.chernClass_whitneySum_top_of_thomProduct` needs: the general-rank form of the top
Chern class recursion, the behaviour of `relToAbs` under the two casts occurring in
`Work.Whitney.wsumCast`, the computation of `relToAbs` on `wsumCup` and on the two pulled-back Thom
classes, and the zero-section identities `πᵢ ∘ z_V = z_{Vᵢ}`. -/

noncomputable section

variable {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-- **The top Chern class in arbitrary rank `m ≥ 1` is the Euler class of the realification.**
`Work.Thom.chernClass_succ_top'` is stated for a bundle in the standard fibre
`EuclideanSpace ℂ (Fin (m+1))`; this is the form for an arbitrary rank at least one. -/
theorem chernClass_top_eq_eulerClass {m : ℕ} {ι : Type} [Fintype ι]
    (hm : 1 ≤ m) (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.Thom.chernClass m m Z = (Work.Thom.thomClassRank m hm Z).eulerClass := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [Work.Thom.chernClass_succ_top']

/-- **`relToAbs` does not see the relative set**: transporting a relative class along an equality of
the closed sets and then forgetting the relative structure is the same as forgetting it first. -/
theorem relToAbs_set_subst {X : Type} [TopologicalSpace X] {A A' : Set X} (h : A = A') (n : ℕ)
    (y : Work.Thom.RelCoh ℤ n X A) :
    (Work.Thom.relToAbs ℤ A' n).hom (h ▸ y) = (Work.Thom.relToAbs ℤ A n).hom y := by
  cases h; rfl

/-- **`relToAbs` commutes with the transport of the degree.**  (`Work.Thom.relToAbs_cast` of
`Submission/Work/Thom/Gysin.lean`, restated here in the `▸`-form used by `Work.Whitney.wsumCast`.) -/
theorem relToAbs_degree_subst {X : Type} [TopologicalSpace X] (A : Set X) {m m' : ℕ} (h : m = m')
    (x : Work.Thom.RelCoh ℤ m X A) :
    (Work.Thom.relToAbs ℤ A m').hom (h ▸ x)
      = h ▸ ((Work.Thom.relToAbs ℤ A m).hom x) := by
  cases h; rfl

/-- The `Eq.rec` transport of an absolute class is the transport `Work.Thom.cohTransport`
(`Work.LerayHirsch.eqRec_eq_cohTransport` under `Work.Whitney`). -/
theorem eqRec_eq_cohTransport_subst {n n' : ℕ} (h : n = n') (x : Work.Thom.Coh ℤ n B) :
    (h ▸ x) = Work.Thom.cohTransport h x := by
  cases h; rfl

/-- **The two casts of `Work.Whitney.wsumCast` are invisible to `relToAbs`**: forgetting the
relative structure of the transported class gives the degree transport of the forgotten class. -/
theorem relToAbs_wsumCast
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hset : Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
      = Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
    (y : Work.Thom.RelCoh ℤ (2 * m₁ + 2 * m₂)
      (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace
      (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)) :
    (Work.Thom.relToAbs ℤ
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
        (2 * (m₁ + m₂))).hom (Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset y)
      = Work.Thom.cohTransport (Nat.mul_add 2 m₁ m₂).symm
          ((Work.Thom.relToAbs ℤ
            (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
            (2 * m₁ + 2 * m₂)).hom y) := by
  unfold Work.Whitney.wsumCast
  rw [relToAbs_set_subst, relToAbs_degree_subst]
  exact eqRec_eq_cohTransport_subst _ _

/-- **The computation rule of `Work.Whitney.wsumCup`**: forgetting its relative structure gives the
absolute cup product of the two forgotten pulled-back Thom classes. -/
theorem relToAbs_wsumCup
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)) :
    (Work.Thom.relToAbs ℤ
        (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂)
        (2 * m₁ + 2 * m₂)).hom
      (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
    = (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB
          (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
          (2 * m₁) (2 * m₂))
        ((Work.Thom.relToAbs ℤ (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) (2 * m₁)).hom
          (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁))
        ((Work.Thom.relToAbs ℤ (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) (2 * m₂)).hom
          (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂)) := by
  unfold Work.Whitney.wsumCup
  exact Work.Whitney.tcmRelCup_relToAbs _ _ hAopen hCopen (2 * m₁) (2 * m₂) _ _

/-- **The first pulled-back Thom class forgets to the pullback of the first Thom class**:
`relToAbs (π₁^*τ_{Z₁}) = π₁^*(relToAbs τ_{Z₁})`. -/
theorem relToAbs_wsumRelTau1
    (hm₁ : 1 ≤ m₁)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace)) :
    (Work.Thom.relToAbs ℤ (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) (2 * m₁)).hom
        (Work.Whitney.wsumRelTau1 hm₁ Z₁ Z₂ π₁)
      = (Work.Thom.CohMap π₁ ℤ (2 * m₁)).hom
          ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (Work.Thom.realification Z₁))
            (2 * m₁)).hom (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ) := by
  unfold Work.Whitney.wsumRelTau1
  exact Work.Thom.relCohMap_relToAbs_apply π₁ _ _ (fun _ hx => hx) ℤ (2 * m₁) _

/-- **The second pulled-back Thom class forgets to the pullback of the second Thom class**. -/
theorem relToAbs_wsumRelTau2
    (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace)) :
    (Work.Thom.relToAbs ℤ (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) (2 * m₂)).hom
        (Work.Whitney.wsumRelTau2 hm₂ Z₁ Z₂ π₂)
      = (Work.Thom.CohMap π₂ ℤ (2 * m₂)).hom
          ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (Work.Thom.realification Z₂))
            (2 * m₂)).hom (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ) := by
  unfold Work.Whitney.wsumRelTau2
  exact Work.Thom.relCohMap_relToAbs_apply π₂ _ _ (fun _ hx => hx) ℤ (2 * m₂) _

/-- **The first coordinate projection carries the zero section to the zero section**:
`π₁ ∘ z_V = z_{V₁}`, from the defining formula of `π₁`. -/
theorem zeroSection_comp_pi1
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩) :
    π₁.comp (Work.Thom.zeroSection (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
      = Work.Thom.zeroSection (Work.Thom.realification Z₁) := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, Work.Thom.zeroSection_apply]
  show π₁ ⟨x, (0 : EuclideanSpace ℂ (Fin (m₁ + m₂)))⟩ = _
  rw [hπ₁, Work.Thom.zeroSection_apply]
  show (⟨x, ((Work.Whitney.sumFibreC m₁ m₂).symm 0).1⟩ : (Work.Thom.realification Z₁).TotalSpace)
    = ⟨x, (0 : EuclideanSpace ℂ (Fin m₁))⟩
  rw [map_zero]
  rfl

/-- **The second coordinate projection carries the zero section to the zero section**:
`π₂ ∘ z_V = z_{V₂}`. -/
theorem zeroSection_comp_pi2
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩) :
    π₂.comp (Work.Thom.zeroSection (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
      = Work.Thom.zeroSection (Work.Thom.realification Z₂) := by
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply, Work.Thom.zeroSection_apply]
  show π₂ ⟨x, (0 : EuclideanSpace ℂ (Fin (m₁ + m₂)))⟩ = _
  rw [hπ₂, Work.Thom.zeroSection_apply]
  show (⟨x, ((Work.Whitney.sumFibreC m₁ m₂).symm 0).2⟩ : (Work.Thom.realification Z₂).TotalSpace)
    = ⟨x, (0 : EuclideanSpace ℂ (Fin m₂))⟩
  rw [map_zero]
  rfl

/-- **The assembly: from the relative Thom product formula to the top Chern class of a sum.**

Given the relative Thom product formula (the conclusion of
`Work.Whitney.thomClassRank_whitneySum_rel`, which is exactly the hypothesis `h` below), deduce

  `c_{m1+m2}(Z1 (+) Z2) = c_{m1}(Z1) cup c_{m2}(Z2)`.

The two coordinate projections `π1`, `π2` of the total spaces enter as *parameters* together with
their defining formulas.  The vocabulary (`Work.Whitney.wsumCup`, `wsumTau`, `wsumCast`) is
`Submission/Work/Whitney/WSumChars.lean`.

ROUTE.  From `h`, the conclusion is obtained by `relToAbs` (the defining equation of `chernClass` at
the top degree is `Work.Thom.chernClass_succ_top'`, with the rank `m1+m2` rewritten as a successor by
`Nat.exists_eq_succ_of_ne_zero` and `Nat.le_trans hm1 (Nat.le_add_right m1 m2)`), the computation
rule `Work.Whitney.tcmRelCup_relToAbs`, the naturality `Work.Thom.relCohMap_relToAbs`, the graded
naturality `Work.Thom.CohMap_cupH'_apply` / `Work.Whitney.cupChern_CohMap`, the zero-section
identities `πi ∘ z_V = z_{Vi}` (from `hπ1`, `hπ2`), and the degree bookkeeping of
`Work.Whitney.cupChern_def` (which carries the `Nat.mul_add` transport of degrees).  Concretely:
`chernClass (m1+m2) (m1+m2) V = eulerClass (V_R) = z_V^* (relToAbs (wsumTau ...))`, and
`relToAbs (wsumCup ...) = pr1^*(relToAbs tau_{Z1}) cup pr2^*(relToAbs tau_{Z2})` by
`tcmRelCup_relToAbs`; pulling this back along `z_V` and using `πi ∘ z_V = z_{Vi}` gives
`e(Z1_R) cup e(Z2_R) = cupChern m1 m2 (chernClass m1 m1 Z1) (chernClass m2 m2 Z2)`.

The openness hypotheses `hAopen`, `hCopen` and the set identity `hset` are *not* needed for this
step (only for the relative formula itself); they are kept so that the hypothesis `h` has exactly the
shape produced by `Work.Whitney.thomClassRank_whitneySum_rel`.  The cases `m1 = 0` / `m2 = 0` are
excluded by `hm1`/`hm2` and are handled separately by
`Work.Whitney.chernClass_whitneySum_rank_zero`. -/
theorem chernClass_whitneySum_top_of_thomProduct {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩)
    (hset : Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
      = Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
    (hAopen : IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁))
    (hCopen : IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂))
    (h : Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
        (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen)
      = Work.Whitney.wsumTau hm₁ hm₂ Z₁ Z₂) :
    Work.Thom.chernClass (m₁ + m₂) (m₁ + m₂) (Work.Whitney.whitneySum Z₁ Z₂)
      = Work.Whitney.cupChern m₁ m₂ (Work.Thom.chernClass m₁ m₁ Z₁)
          (Work.Thom.chernClass m₂ m₂ Z₂) := by
  -- The relative Thom class, forgotten, is the transported cup of the two pulled-back classes.
  have hrel : (Work.Thom.relToAbs ℤ
        (Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))
        (2 * (m₁ + m₂))).hom
      (Work.Thom.thomClassRank (m₁ + m₂) (Nat.le_trans hm₁ (Nat.le_add_right m₁ m₂))
        (Work.Whitney.whitneySum Z₁ Z₂)).τ
    = Work.Thom.cohTransport (Nat.mul_add 2 m₁ m₂).symm
        ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB
            (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace)
            (2 * m₁) (2 * m₂))
          ((Work.Thom.CohMap π₁ ℤ (2 * m₁)).hom
            ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (Work.Thom.realification Z₁))
              (2 * m₁)).hom (Work.Thom.thomClassRank m₁ hm₁ Z₁).τ))
          ((Work.Thom.CohMap π₂ ℤ (2 * m₂)).hom
            ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement (Work.Thom.realification Z₂))
              (2 * m₂)).hom (Work.Thom.thomClassRank m₂ hm₂ Z₂).τ))) := by
    rw [show (Work.Thom.thomClassRank (m₁ + m₂) (Nat.le_trans hm₁ (Nat.le_add_right m₁ m₂))
          (Work.Whitney.whitneySum Z₁ Z₂)).τ = Work.Whitney.wsumTau hm₁ hm₂ Z₁ Z₂ from rfl]
    rw [show Work.Whitney.wsumTau hm₁ hm₂ Z₁ Z₂
        = Work.Whitney.wsumCast Z₁ Z₂ π₁ π₂ hset
            (Work.Whitney.wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen) from h.symm]
    rw [relToAbs_wsumCast]
    rw [relToAbs_wsumCup hm₁ hm₂ Z₁ Z₂ π₁ π₂ hAopen hCopen]
    rw [relToAbs_wsumRelTau1 hm₁ Z₁ Z₂ π₁, relToAbs_wsumRelTau2 hm₂ Z₁ Z₂ π₂]
  -- Replace the three top Chern classes by the Euler classes of the realifications.
  rw [chernClass_top_eq_eulerClass hm₁ Z₁, chernClass_top_eq_eulerClass hm₂ Z₂,
      chernClass_top_eq_eulerClass (Nat.le_trans hm₁ (Nat.le_add_right m₁ m₂))
        (Work.Whitney.whitneySum Z₁ Z₂)]
  -- Unfold the Euler classes and the graded product.
  rw [Work.Thom.ThomClass.eulerClass_def, Work.Thom.ThomClass.eulerClass_def,
      Work.Thom.ThomClass.eulerClass_def]
  rw [Work.Whitney.cupChern_def]
  -- The forgotten Thom class of the sum.
  rw [hrel]
  -- Bring the pullback along the zero section inside the transport and the cup product.
  rw [Work.Thom.cohTransport_CohMap]
  rw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (Work.Thom.zeroSection
      (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)))) (2 * m₁) (2 * m₂) _ _]
  -- Identify the pullbacks with the zero sections of the two summands.
  rw [Work.Thom.CohMap_comp_apply (Work.Thom.zeroSection
        (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))) π₁ ℤ (2 * m₁),
      Work.Thom.CohMap_comp_apply (Work.Thom.zeroSection
        (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))) π₂ ℤ (2 * m₂)]
  rw [zeroSection_comp_pi1 Z₁ Z₂ π₁ hπ₁, zeroSection_comp_pi2 Z₁ Z₂ π₂ hπ₂]

end

end Work.Whitney
