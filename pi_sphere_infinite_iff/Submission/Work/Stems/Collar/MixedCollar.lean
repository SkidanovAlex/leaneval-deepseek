import Mathlib
import Submission.Work.Stems.Collar.Plumbing

/-!
# The mixed-degree derivation property of the collar transgression

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md` §3 and §7.)*

The collar transgression `Σ_m : H^{m+b}(C) → H^{m+1}(Y)` (`Work.StemsB.Rat.collarSigma`,
`Work.StemsB.Rat.collarSigmaLow` for the top degree `b - 1`) satisfies the derivation property

  `Σ (X ⌣ Y) = (± σ^*X) ⌣ Σ Y + (± σ^*Y) ⌣ Σ X`.

The tree has the two **extreme** cases:

* `Work.StemsB.Rat.collarSigma_cup_low` — both factors of degree `b - 1`;
* `Work.StemsB.Rat.collarSigma_cup_rat` — both factors of degree `m + b`, `m ≥ 0`.

The `K(ℤ,n)` computation (`C2ODD_PLAN.md` §3/§7) needs the **mixed** case: one factor of degree
`b - 1` (the fundamental class of the fibre) and the other of degree `m + b`.  It is the missing
input of the unbounded odd step: `θ(x³) = 3 x² θ(x)` is exactly this case, and every higher power
`θ(x^k)`, `k ≥ 4`, follows from it and the high-degree case.

This file proves it, first at the level of the connecting homomorphism `δ` of the collar pair
(`collarDPairCupMixed`, the mixed analogue of `Work.StemsB.Rat.collarDPairCupLow` and of the
`private` `collar_pairδ_cup` of `collarSigma_cup_rat.lean`), then — in
`Submission/Work/Stems/Collar/MixedCollarSigma.lean` — at the level of `Σ`.

The argument is the same in every case: split the low class by
`Work.StemsB.Rat.collarSplitLow` and the high one by `Work.StemsB.Rat.collarSplit`,
expand the cup product into its four terms, and apply the one-sided Leibniz rule
`Work.StemsB.pairDelta_mixedCup_general_R` to the two cross terms (the other two vanish, one because
restrictions are `δ`-closed, the other because `s ⌣ s = 0`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.Collar

open Work.StemsB.Rat
open Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## The mixed cross terms -/

/-- **The mixed cross term with the `s`-part on the right**:
`δ (i^*a ⌣ v) = (-1)^{b-1} π^*(σ^*X) ⌣ δ Y'`. -/
lemma mixed_delta_restr_zeta (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (m : ℕ) (X : (CollKC b Y).homology (b - 1)) (Y' : (CollKC b Y).homology (m + b))
    (a : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (b - 1))
    (ha : a = piStar b Y (b - 1) (sgStar b hb Y (b - 1) X)) :
    dPair b Y ((b - 1) + (m + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
          (iStar b Y (b - 1) a) (collarSPart b hb Y τ hτ s m Y'))
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((m + b) + 1))
            (piStar b Y (b - 1) (sgStar b hb Y (b - 1) X))
            (dPair b Y (m + b) Y')) := by
  have hC := Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (b - 1) (m + b)
    a (collarSPart b hb Y τ hτ s m Y')
  rw [hC]
  rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (m + b)).hom
        (collarSPart b hb Y τ hτ s m Y') = dPair b Y (m + b) Y' from
    collarDelta_collarSPart b hb Y τ hτ s hs m Y']
  rw [ha]

/-- **The mixed cross term with the `s`-part on the left**:
`δ (u ⌣ i^*b') = ± π^*(σ^*Y') ⌣ δ X`. -/
lemma mixed_delta_zeta_restr (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : CollarTransgresses b hb (Y := Y) s τ)
    (m : ℕ) (X : (CollKC b Y).homology (b - 1)) (Y' : (CollKC b Y).homology (m + b))
    (b' : (Work.Cohomology.singularCochainComplex ℚ (CollQ b Y)).homology (m + b))
    (hb' : b' = piStar b Y (m + b) (sgStar b hb Y (m + b) Y')) :
    dPair b Y ((b - 1) + (m + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
          (collarSPartLow b hb Y τ hτ s X) (iStar b Y (m + b) b'))
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            (congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm)))
          (((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
            ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + b) ((b - 1) + 1))
              (piStar b Y (m + b) (sgStar b hb Y (m + b) Y'))
              (dPair b Y (b - 1) X))) := by
  rw [gradedComm_coll b Y (b - 1) (m + b)
    (collarSPartLow b hb Y τ hτ s X) (iStar b Y (m + b) b')]
  rw [dPair_eqToHom_cast b Y (Nat.add_comm (b - 1) (m + b)).symm]
  have hinner : dPair b Y ((m + b) + (b - 1))
        (((-1 : ℚ) ^ ((b - 1) * (m + b))) •
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + b) (b - 1))
            (iStar b Y (m + b) b') (collarSPartLow b hb Y τ hτ s X)))
      = ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + b) ((b - 1) + 1))
            (piStar b Y (m + b) (sgStar b hb Y (m + b) Y'))
            (dPair b Y (b - 1) X)) := by
    rw [dPair_smul]
    rw [Work.StemsB.pairDelta_mixedCup_general_R ℚ (CollQ b Y) (CollA b Y) (m + b) (b - 1)
      b' (collarSPartLow b hb Y τ hτ s X)]
    rw [show (Work.Cohomology.pairδ ℚ (CollQ b Y) (CollA b Y) (b - 1)).hom
          (collarSPartLow b hb Y τ hτ s X) = dPair b Y (b - 1) X from
      pairδ_collarSPartLow b hb Y τ hτ s hs X]
    rw [hb']
    rw [smul_smul, ← pow_add]
  rw [hinner]

/-- **The mixed `s`-`s` term vanishes**: `δ ((π^*(Σ_lo X) ⌣ s) ⌣ (π^*(Σ Y') ⌣ s)) = 0`. -/
lemma mixed_delta_zeta_cup (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (m : ℕ) (X : (CollKC b Y).homology (b - 1)) (Y' : (CollKC b Y).homology (m + b)) :
    dPair b Y ((b - 1) + (m + b))
      ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
        (collarSPartLow b hb Y τ hτ s X) (collarSPart b hb Y τ hτ s m Y')) = 0 := by
  have h1 : 0 + (b - 1) = b - 1 := Nat.zero_add (b - 1)
  have h2 : (m + 1) + (b - 1) = m + b := by omega
  set A : Work.Thom.Coh ℚ 0 ↥(sphLoopCollarProd b Y) :=
    collarProjC (Y := Y) b 0 (collarSigmaLow b hb Y τ hτ X) with hA
  set B :=
    (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ (CollQ b Y) (CollA b Y)) (m + 1)).hom
      ((Work.Thom.CohMap (collarProjY (Y := Y) b) ℚ (m + 1)).hom (collarSigma b hb Y τ hτ m Y'))
    with hB
  set W1 : (CollKC b Y).homology (0 + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) 0 (b - 1)) A s with hW1
  set W2 : (CollKC b Y).homology ((m + 1) + (b - 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + 1) (b - 1)) B s with hW2
  set Y2 : (CollKC b Y).homology ((m + 1) + (b - 1)) := ((-1 : ℚ) ^ (m + 1)) • W2 with hY2
  have hu : collarSPartLow b hb Y τ hτ s X = (h1 ▸ W1) := by
    rw [collarSPartLow_apply b hb Y τ hτ s X, ← hA, ← hW1]
    exact eqToHom_singCoh_eq_cast h1 W1
  have hv0 : collarSPart b hb Y τ hτ s m Y' = (h2 ▸ (((-1 : ℚ) ^ (m + 1)) • W2)) := by
    rw [collarSPart_apply b hb Y τ hτ s m Y']
    rw [collarProjC_eq_restr_apply, ← hB, ← hW2]
    rw [collarRelEqS_apply b hb Y m h2 _]
    exact eqToHom_homology_eq_cast (CollKC b Y) h2 _
  have hv : collarSPart b hb Y τ hτ s m Y' = (h2 ▸ Y2) := hv0.trans (by rw [hY2])
  have hkill : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y))
      (0 + (b - 1)) ((m + 1) + (b - 1))) W1 Y2 = 0 := by
    rw [hY2, map_smul, hW1, hW2]
    rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y))
        (0 + (b - 1)) ((m + 1) + (b - 1)))
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) 0 (b - 1)) A s)
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (m + 1) (b - 1)) B s)
        = 0 from cupH'_sq_kill 0 (m + 1) (b - 1) A B s hssq]
    exact smul_zero _
  have hcastL : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
        (h1 ▸ W1) (h2 ▸ Y2)
      = (congrArg (fun t => t + (m + b)) h1) ▸
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (0 + (b - 1)) (m + b))
            W1 (h2 ▸ Y2)) :=
    cupH'_cast_left (c := m + b) h1 W1 (h2 ▸ Y2)
  have hcastR : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (0 + (b - 1)) (m + b))
        W1 (h2 ▸ Y2)
      = (congrArg (fun t => (0 + (b - 1)) + t) h2) ▸
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (0 + (b - 1))
            ((m + 1) + (b - 1))) W1 Y2) :=
    cupH'_cast_right (c := 0 + (b - 1)) (b := (m + 1) + (b - 1)) (b' := m + b) h2 W1 Y2
  have hgoal : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
      (collarSPartLow b hb Y τ hτ s X) (collarSPart b hb Y τ hτ s m Y') = 0 := by
    rw [hu, hv, hcastL, hcastR, hkill]
    exact cast_cast_zero (F := fun t => (CollKC b Y).homology t)
      (congrArg (fun t => (0 + (b - 1)) + t) h2) (congrArg (fun t => t + (m + b)) h1)
  rw [hgoal]
  exact map_zero _

/-! ## The mixed `δ`-computation -/

/-- **The derivation property of the collar connecting map, mixed degrees.**

`δ (X ⌣ Y') = (-1)^{b-1} (π^*(σ^*X) ⌣ δ Y') + (-1)^{(b-1)(m+b)+(m+b)} (π^*(σ^*Y') ⌣ δ X)`
for `X` of degree `b - 1` and `Y'` of degree `m + b`; the second term carries the degree cast
`((m+b)+(b-1))+1 → ((b-1)+(m+b))+1`. -/
theorem collarDPairCupMixed (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(sphLoopCollarProd b Y))
    (hs : CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : cupT ↥(sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(sphLoopCollarProd b Y))
            (TopCat.ofHom (collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (m : ℕ) (X : (CollKC b Y).homology (b - 1)) (Y' : (CollKC b Y).homology (m + b)) :
    dPair b Y ((b - 1) + (m + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) X Y')
      = ((-1 : ℚ) ^ (b - 1)) •
          ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (b - 1) ((m + b) + 1))
            (piStar b Y (b - 1) (sgStar b (by omega) Y (b - 1) X))
            (dPair b Y (m + b) Y'))
        + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
              (congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm)))
            (((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
              ((Work.Cohomology.mixedCupR ℚ (CollQ b Y) (CollA b Y) (m + b) ((b - 1) + 1))
                (piStar b Y (m + b) (sgStar b (by omega) Y (m + b) Y'))
                (dPair b Y (b - 1) X))) := by
  have hb1 : 1 ≤ b := by omega
  obtain ⟨a, ha⟩ := collarSplitLow b hb1 Y τ hτ s hs X
  obtain ⟨b', hb'⟩ := collarSplit b hb1 Y τ hτ s hs m Y'
  set u := collarSPartLow b hb1 Y τ hτ s X with hu
  set v := collarSPart b hb1 Y τ hτ s m Y' with hv
  have hae : a = piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X) :=
    split_base_low b hb1 Y τ hτ s hσ X a (by rw [← hu]; exact ha)
  have hbe : b' = piStar b Y (m + b) (sgStar b hb1 Y (m + b) Y') :=
    collarSplit_base b hb1 Y τ hτ s hσ m Y' b' (by rw [← hv]; exact hb')
  have hX : X = iStar b Y (b - 1) a + u := by
    rw [← sub_eq_iff_eq_add, hu]
    exact ha
  have hY' : Y' = iStar b Y (m + b) b' + v := by
    rw [← sub_eq_iff_eq_add, hv]
    exact hb'
  have hW : (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) X Y'
      = (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
          (iStar b Y (b - 1) a) (iStar b Y (m + b) b')
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
          (iStar b Y (b - 1) a) v
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
          u (iStar b Y (m + b) b')
        + (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) u v := by
    rw [hX, hY', Work.Cohomology.cupH'_add_left, Work.Cohomology.cupH'_add_right,
      Work.Cohomology.cupH'_add_right]
    abel
  have hD : dPair b Y ((b - 1) + (m + b))
        ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) X Y')
      = dPair b Y ((b - 1) + (m + b))
          ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
            (iStar b Y (b - 1) a) (iStar b Y (m + b) b'))
        + dPair b Y ((b - 1) + (m + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
              (iStar b Y (b - 1) a) v)
        + dPair b Y ((b - 1) + (m + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b))
              u (iStar b Y (m + b) b'))
        + dPair b Y ((b - 1) + (m + b))
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) u v) := by
    rw [hW, dPair_add, dPair_add, dPair_add]
  rw [hD, hu, hv]
  rw [delta_restr_cup b Y (b - 1) (m + b) a b',
    mixed_delta_restr_zeta b hb1 Y τ hτ s hs m X Y' a hae,
    mixed_delta_zeta_restr b hb1 Y τ hτ s hs m X Y' b' hbe,
    mixed_delta_zeta_cup b hb1 Y τ hτ s hssq m X Y']
  abel

end

end Work.Stems.Collar
