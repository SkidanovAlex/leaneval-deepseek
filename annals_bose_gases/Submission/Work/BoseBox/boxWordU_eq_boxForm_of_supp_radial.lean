import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.potBracketG_eq_potWordU
import Submission.Work.BoseKinLoc.Sector.potWordU_slotComb
import Submission.Work.BoseKinLoc.Word.boxFormB_eq_boxForm_of_supp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BoseBox

open Submission.BoseGases
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The box fibre integral `w1Fibre ℓ (wLoc ℓ g 0) a = ∫_{acube ℓ} wLoc ℓ g 0 a y` agrees with the
whole-space fibre integral `potBr ℓ g 0 a = ∫_{ℝ³} wLoc ℓ g 0 a y`: for `0 < ℓ` the window factor
`χ_0(y)` of `wLoc ℓ g 0 a y` vanishes off `acube ℓ`. -/
lemma w1Fibre_wLoc_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (g : ℝ³ → ℝ) (a : ℝ³) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ g 0) a = potBr ℓ g 0 a := by
  unfold Submission.BoseGases.w1Fibre potBr
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
  have h : Submission.BoseGases.chiU ℓ 0 y = 0 :=
    Work.BoseKinLoc.Sector.chiU_zero_of_notMem_acube hℓ hy
  simp [Submission.BoseGases.wLoc, h]

/-- The bracket of `qLHSword` (box fibre integrals, `1/2 Σ_{i≠j}` pair convention) agrees
pointwise with `potWordU` (whole-space fibre integrals, `Σ_{i<j}` pair convention) — given
radiality of `v`, so that the two-body kernel `wLoc ℓ v 0` is symmetric. -/
lemma bracket_qLHSword_eq_potWordU {n : ℕ} {ℓ μ : ℝ} {v : ℝ³ → ℝ} (hℓ : 0 < ℓ)
    (h : Work.UBB.ScatSol v) (hvrad : BoseGases.IsRadial v) (x : X n) :
    (- μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)))
      = Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x := by
  have h1 : (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
      = ∑ i : Fin n, potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i) :=
    Finset.sum_congr rfl (fun i _ => w1Fibre_wLoc_zero hℓ (Submission.BoseGases.g0 v h) (x i))
  have hb := potBracketG_eq_potWordU (N := n) (ℓ := ℓ) (μ := μ) (v := v) (h := h) hvrad 0 x
  unfold potBracketG at hb
  rw [h1]
  exact hb

/-- **The corrected box-word bridge** (the requested statement plus the missing hypothesis
`IsRadial v`, and `0 < ℓ`): for every state `Φ` supported in the configuration box `abox n ℓ`, the
localised box word `boxWordU` (FS `eq:DefT` + `eq:Def_HB`, i.e. `tKinWord + qLHSword` with the
`1/2 Σ_{i≠j}` interaction convention) agrees with the whole-space localised form `boxForm` at
`u = 0` (which uses FS's `Σ_{i<j}` convention).

The two ingredients are `bracket_qLHSword_eq_potWordU` (the box and whole-space fibre integrals
coincide, and (⋆) holds for the symmetric kernel `wLoc ℓ v 0`) and the support hypothesis, which
replaces the box integral by the whole-space integral. -/
theorem boxWordU_eq_boxForm_of_supp_of_radial {n : ℕ} {ℓ μ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : BoseGases.IsRadial v) {Φ : Submission.BoseGases.X n → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) :
    Work.BoseBox.boxWordU n ℓ μ d s eT b v h 0 Φ
      = Work.BoseKinLoc.boxForm n v (Submission.BoseGases.g0 v h) ℓ μ d s eT b 0 Φ := by
  have hpot : Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wLoc ℓ v 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ
      = ∫ x : Submission.BoseGases.X n, (Φ x) ^ 2
          * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x := by
    rw [show Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wLoc ℓ v 0)
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
            * (- μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
                  Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))) from rfl]
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
            * (- μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
                  (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
                  Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))))
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2
            * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x from
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
        (fun x _ => by rw [bracket_qLHSword_eq_potWordU hℓ h hvrad x])]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [Work.BoseKinLoc.Word.eq_zero_of_not_mem_abox hsupp hx]; ring)
  rw [Work.BoseBox.boxWordU, Work.BoseBox.tKinWord, Work.BoseKinLoc.boxForm, hpot]

end Work.BoseBox
