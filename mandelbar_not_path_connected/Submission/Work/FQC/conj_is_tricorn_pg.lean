/-
# `Work.FQC.conj_is_tricorn_pg` — the conjugate of `Tantibar c` is again a `Tantibar`

The principal solution `φ = principal (muQC d fl hfl.Pg t)` of the invariant Beltrami
coefficient of the deformation conjugates the antipolynomial `Tantibar c` to another
antipolynomial `Tantibar c₂` (`Work.MRMT.Found.antiholo_conj`, item M2′ of MRMT, says that
`star ∘ φ ∘ Tantibar c ∘ φ.symm` is entire; the normalisation `φ z = z + O(1/‖z‖)` of the
principal solution says that this entire function differs from `w ↦ w²` by a bounded amount,
whence it is `w ↦ w² + a` by Liouville).
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.Petal
import Submission.Work.FQC.Ell
import Submission.Work.FQC.muQC_invariant_pg
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.principal_conj_Tantibar_bounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- The antipolynomial `Tantibar c` is anti-holomorphic: `star ∘ Tantibar c` is the entire map
`z ↦ z ^ 2 + star c`. -/
theorem differentiable_star_comp_Tantibar (c : ℂ) : Differentiable ℂ (star ∘ Tantibar c) := by
  have h : (star ∘ Tantibar c) = fun z : ℂ => z ^ 2 + star c := by
    funext z
    simp [LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow]
  rw [h]
  fun_prop

/-- An entire function differing from `w ↦ w ^ 2` by a bounded amount *is* `w ↦ w ^ 2 + a`
(Liouville). -/
theorem exists_eq_sq_add_of_bounded {Ψ : ℂ → ℂ} (hΨ : Differentiable ℂ Ψ) {M : ℝ}
    (hM : ∀ w : ℂ, ‖Ψ w - w ^ 2‖ ≤ M) : ∃ a : ℂ, ∀ w : ℂ, Ψ w = w ^ 2 + a := by
  have hg : Differentiable ℂ (fun w : ℂ => Ψ w - w ^ 2) := hΨ.sub (differentiable_id.pow 2)
  have hbdd : Bornology.IsBounded (Set.range fun w : ℂ => Ψ w - w ^ 2) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * M, fun x y => ?_⟩
    rw [dist_eq_norm]
    calc ‖(Ψ x - x ^ 2) - (Ψ y - y ^ 2)‖ ≤ ‖Ψ x - x ^ 2‖ + ‖Ψ y - y ^ 2‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM x) (hM y)
      _ = 2 * M := by ring
  obtain ⟨a, ha⟩ := hg.exists_const_forall_eq_of_bounded hbdd
  exact ⟨a, fun w => by rw [← ha w]; ring⟩

theorem conj_is_tricorn_pg {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁) (hfl : Work.FQC.PetalInput d fl) (t : ℝ) : ∃ c₂ : ℂ, ∀ z : ℂ, Work.MRMT.Found.principal (Work.FQC.muQC d fl hfl.Pg t) (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (Work.MRMT.Found.principal (Work.FQC.muQC d fl hfl.Pg t) z) := by
  have hμ : Work.MRMT.Found.Admissible (muQC d fl hfl.Pg t) := muQC_admissible_pg d fl hfl t
  have hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      muQC d fl hfl.Pg t z =
        star (muQC d fl hfl.Pg t (Tantibar c z)) * Work.MRMT.dzbar (Tantibar c) z /
          star (Work.MRMT.dzbar (Tantibar c) z) := by
    simpa only [pullAnti] using muQC_invariant_pg d fl hfl t
  have hanti := principal_antiholo_conj (μ := muQC d fl hfl.Pg t) hμ
    (f := Tantibar c) (differentiable_star_comp_Tantibar c) hinv
  obtain ⟨M, hM⟩ := principal_conj_Tantibar_bounded c hμ
  obtain ⟨a, ha⟩ := exists_eq_sq_add_of_bounded hanti hM
  refine ⟨star a, fun z => ?_⟩
  have hz : star (Work.MRMT.Found.principal (muQC d fl hfl.Pg t) (Tantibar c z)) =
      ((Work.MRMT.Found.principal (muQC d fl hfl.Pg t)) z) ^ 2 + a := by
    have h := ha (Work.MRMT.Found.principal (muQC d fl hfl.Pg t) z)
    simpa [Function.comp_def, Homeomorph.symm_apply_apply] using h
  have h4 : Work.MRMT.Found.principal (muQC d fl hfl.Pg t) (Tantibar c z) =
      star (((Work.MRMT.Found.principal (muQC d fl hfl.Pg t)) z) ^ 2 + a) := by
    rw [← hz, star_star]
  rw [h4]
  simp [LeanEval.ComplexAnalysis.Tantibar]

end Work.FQC

end
