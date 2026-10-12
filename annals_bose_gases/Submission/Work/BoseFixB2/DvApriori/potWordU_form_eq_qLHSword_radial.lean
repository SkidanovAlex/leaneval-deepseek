import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.potBracketG_eq_potWordU
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseKinLoc.Sector.potWordU_slotComb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_of_radial` — the **repaired** word identity

The requested identity

    ∫_{abox n ℓ} (Φ x)² · potWordU n v (g₀ v h) ℓ μ 0 x
      = qLHSword (N := n) ℓ μ (wPairC ℓ v) (wPairC ℓ (g₀ v h)) Φ

is **false** without the hypothesis `IsRadial v` (see the sibling file
`Submission/Work/BoseFixB2/DvApriori/potWordU_form_eq_qLHSword.lean` for the finding, the
counterexample construction, and the machine-checked evidence).  The reason is that
`potWordU` (FS `eq:Def_HB`) writes the two-body interaction with the *ordered* index set
`{i < j}`, while `qLHSword` writes it with the *unordered* one, `(1/2) Σ_{i≠j}`, so the two
sides agree pointwise exactly when the pair kernel `wPairC ℓ v` is symmetric, i.e. exactly when
`v` is even.

This file proves the repaired statement: the same identity with `hvrad : IsRadial v` (which is
in force at the top level — `Challenge.lean`'s `theorem_1_2` carries `hv_radial : IsRadial v`)
and `hℓ : 0 < ℓ` (needed because the one-body fibres of `qLHSword` run over the box `acube ℓ`
while `potWordU` integrates over all of `ℝ³`; the window `χ_0 = χ((ℓ⁻¹)•·)` vanishes off
`acube ℓ` only for `ℓ > 0`).  For `ℓ ≤ 0` the box `abox n ℓ` is a null set for `n ≥ 1` and both
integrands vanish identically for `n = 0`, so the identity holds there too; that degenerate
branch is not treated here.

The content is `Work.BoseBox.potBracketG_eq_potWordU` (the bracket identity, which is exactly
where `hvrad` is used) together with the two dictionary steps

* box fibre integral of `wLevel` on the right ↔ whole-space fibre integral on the left:
  `w1Fibre ℓ (wPairC ℓ g) a = potBr ℓ g 0 a = ∫_{ℝ³} wLoc ℓ g 0 a y`  (needs `0 < ℓ`);
* `wLoc ℓ h 0 = wPairC ℓ h`  (definitional, `u = 0`).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- With translation parameter `u = 0` the localisation kernel `wLoc` *is* the χ-renormalised
two-body kernel `wPairC`: both equal `χ_ℓ(x)·h(x−y)/(χ⋆χ)_ℓ(x−y)·χ_ℓ(y)`. -/
lemma wLoc_zero_eq_wPairC (ℓ : ℝ) (h : ℝ³ → ℝ) (a b : ℝ³) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  unfold Submission.BoseGases.wLoc Submission.BoseGases.wPairC Submission.BoseGases.wPair
    Submission.BoseGases.wScaled Submission.BoseGases.chiU Submission.BoseGases.chiScale
  simp only [sub_zero]

/-- The box fibre integral of `wLoc ℓ g 0` equals the whole-space fibre integral `potBr ℓ g 0`:
for `0 < ℓ` the window `χ_0` of `wLoc` vanishes off the box `acube ℓ`. -/
lemma w1Fibre_wLoc_eq_potBr {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ³ → ℝ) (a : ℝ³) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) a
      = Work.BoseBox.potBr ℓ g 0 a := by
  unfold Submission.BoseGases.w1Fibre Work.BoseBox.potBr
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
  have h : Submission.BoseGases.chiU ℓ 0 y = 0 :=
    Work.BoseKinLoc.Sector.chiU_zero_of_notMem_acube hℓ hy
  simp [Submission.BoseGases.wLoc, h]

/-- The box fibre integral of the `wPairC`-kernel equals the whole-space fibre integral
`potBr ℓ g 0` of the `wLoc`-kernel (`wLoc ℓ g 0 = wPairC ℓ g`). -/
lemma w1Fibre_wPairC_eq_potBr {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ³ → ℝ) (a : ℝ³) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ g) a
      = Work.BoseBox.potBr ℓ g 0 a := by
  rw [← w1Fibre_wLoc_eq_potBr hℓ g a]
  unfold Submission.BoseGases.w1Fibre
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    (fun y _ => ?_)
  exact (wLoc_zero_eq_wPairC ℓ g a y).symm

/-- **The pointwise density identity.**  For radial `v` and `0 < ℓ`, the diagonal density of
`qLHSword` with the `wPairC` kernels (box fibre integrals, `(1/2) Σ_{i≠j}` pair convention)
equals FS `eq:Def_HB`'s multiplicative potential word `potWordU` (whole-space fibre integrals,
`Σ_{i<j}` pair convention), at every configuration. -/
lemma qLHSden_wPairC_eq_potWordU {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ μ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (x : Submission.BoseGases.X n) :
    Submission.BoseGases.qLHSden n ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) x
      = Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x := by
  -- `potBracketG` is the `potBr`/`wLoc` spelling of the same bracket
  have hbr := Work.BoseBox.potBracketG_eq_potWordU (N := n) (ℓ := ℓ) (μ := μ) (v := v)
    (h := h) hvrad 0 x
  rw [show Work.BoseBox.potBracketG n ℓ μ v (Submission.BoseGases.g0 v h) 0 x
      = - μ * (∑ i : Fin n, Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)) from rfl] at hbr
  -- rewrite `qLHSden` (`wPairC`, box fibres) into the `potBr`/`wLoc` form
  rw [show Submission.BoseGases.qLHSden n ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) x
      = - μ * (∑ i : Fin n, Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)) from by
      simp only [Submission.BoseGases.qLHSden]
      rw [show (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
            = ∑ i : Fin n, Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i) from
          Finset.sum_congr rfl
            (fun i _ => w1Fibre_wPairC_eq_potBr hℓ (Submission.BoseGases.g0 v h) (x i)),
        show (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2))
            = ∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2) from
          Finset.sum_congr rfl
            (fun p _ => (wLoc_zero_eq_wPairC ℓ v (x p.1) (x p.2)).symm)]]
  exact hbr

/-- **The repaired word identity** (the requested statement plus the two missing hypotheses
`IsRadial v` and `0 < ℓ`): for radial `v` and positive side `ℓ`, the box integral of
`(Φ x)² · potWordU` equals the corpus word `qLHSword` built from the `wPairC` kernels. -/
theorem potWordU_form_eq_qLHSword_of_radial {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} (hvrad : _root_.BoseGases.IsRadial v)
    {μ : ℝ} {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x)^2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      = Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by
  rw [Submission.BoseGases.qLHSword_eq_integral_qLHSden]
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    (fun x _ => ?_)
  rw [qLHSden_wPairC_eq_potWordU hvrad hℓ x]

end Work.BoseFixB2.DvApriori
