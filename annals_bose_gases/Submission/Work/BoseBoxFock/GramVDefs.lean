import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.ModeFam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.GramVDefs` — the coordinate rows of the honest mode family

This module packages the two arithmetic/rewriting facts that the Gram computation
`Work.BoseBoxFock.gramFamV` needs, and introduces the *coordinate rows*
`CoordRow`/`GRow` in which the right-hand side of `gramFamV` becomes uniform:

* `Work.BoseB4.gram_comm` / `Work.BoseB4.realIP_comm` are the symmetry of the two
  forms (`gram` is Mathlib's `∑ l, f l * g l`; `realIP f g = ∫ Re(conj f · g)`);
* `kmomLab_zero`, `thetaExp_zero`: the θ-mode at the label `0` of the cube is the
  condensate `θ_Λ` (`kmomLab ℓ N 0 = 0` and `θ_0 = 1_Λ`);
* `GRow` is the θ-fibre coordinate family of `HonestModes`: the rows `g s` for the
  non-zero labels, and the condensate row `δ_0 = (1 at 0, 0 elsewhere)` at the label
  `0`.  With `h g0` (`g s 0 = 0`) this makes the whole θ-fibre behave as if `g 0`
  were the condensate row — exactly what makes both the physical Gram
  (`realIP`) and the coordinate Gram (`gram`) of the family uniform;
* `CoordRow` is the corresponding row of `CoordV` (`f` on the χ-fibre, `GRow` on
  the θ-fibre), so that `CoordV i l = ℓ^{3/2} · CoordRow i l` (`CoordV_eq_row`);
* `ellH_prod`: `(ℓ^{3/2})² = ℓ³` for `ℓ = ellH v μ > 0`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- The label `0` of the cube carries momentum `0`: `kmomLab ℓ N 0 = 0`. -/
lemma kmomLab_zero (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  have h0 : labVec N (0 : Lab N) = 0 := by
    funext i
    simp [labVec]
  rw [kmomLab, h0]
  ext i
  simp [Work.BoseB4.vec]

/-- The θ-mode at momentum `0` is the condensate: `θ_0 = e^{i·0·x}1_Λ = 1_Λ`. -/
lemma thetaExp_zero (ℓ : ℝ) :
    Work.BoseK15.corpusBox.thetaExp ℓ 0 = Work.BoseK15.corpusBox.thetaFun ℓ := by
  funext x
  simp [Work.BoseB4.BoxData.thetaExp_apply]

/-- The θ-fibre coordinate family of `HonestModes`: `g` at the non-zero labels, and
the condensate row `δ_0` at the label `0`. -/
def GRow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    Lab HM.N → Fin HM.m → ℝ :=
  fun s l => if s = 0 then (if l = 0 then 1 else 0) else HM.g s l

/-- The coordinate rows of the physical family `FamV` in the model basis
`Fin HM.m → ℂ`: the χ-rows `f k`, then the θ-rows `GRow s`. -/
def CoordRow (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    Lab HM.N ⊕ Lab HM.N → Fin HM.m → ℝ :=
  fun i => match i with
    | Sum.inl k => HM.f k
    | Sum.inr s => GRow v μ HM s

/-- **`CoordV` is `ℓ^{3/2}` times the real row `CoordRow`**
(`ℓ = ellH v μ`). -/
lemma CoordV_eq_row (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) (l : Fin HM.m) :
    CoordV v μ HM i l
      = (((ellH v μ) ^ (3 / 2 : ℝ) * CoordRow v μ HM i l : ℝ) : ℂ) := by
  rcases i with k | s
  · rfl
  · by_cases hs : s = 0
    · subst hs
      by_cases hl : l = 0 <;>
        simp [CoordV, CoordRow, GRow, hl]
    · simp [CoordV, CoordRow, GRow, hs]

/-- `(ℓ^{3/2})² = ℓ³` at the box side `ℓ = ellH v μ > 0`. -/
lemma ellH_prod (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    (ellH v μ) ^ (3 / 2 : ℝ) * (ellH v μ) ^ (3 / 2 : ℝ) = (ellH v μ) ^ 3 := by
  rw [← Real.rpow_add (ellH_pos v μ) (3 / 2) (3 / 2)]
  norm_num

/-- The physical θ-vector at the label `0` is the condensate `θ_Λ`. -/
lemma FamV_inr_zero (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    FamV v μ HM (Sum.inr (0 : Lab HM.N)) = Work.BoseK15.corpusBox.thetaFun (ellH v μ) := by
  rw [FamV, kmomLab_zero (ellH v μ) HM.N, thetaExp_zero]

end Work.BoseBoxFock
