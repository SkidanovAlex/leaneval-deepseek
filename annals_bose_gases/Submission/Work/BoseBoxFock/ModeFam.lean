import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.corpusBox_gram_values
import Submission.Work.BoseBoxFock.memLp_modes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ModeFam` — the physical mode family of the honest box model

This module **pins the vocabulary** of the mode-ONB lemma
(`Work.BoseBoxFock.modeONBCplx`, see `BRIDGE_DICT_NOTE.md` §2):

* `FamV v μ HM` — the physical family of `L²(Λ)` one-particle vectors, indexed by
  `Lab N ⊕ Lab N`: the χ-modes `Q(e^{ikx}χ_Λ)` on the left summand and the θ-modes
  `e^{isx}θ_Λ` on the right (the label `0` on the right is the condensate `θ_Λ`,
  since `kmomLab ℓ N 0 = 0`);
* `CoordV v μ HM` — its coordinates in the model basis `Fin m → ℂ`: `ℓ^{3/2}·f`,
  `ℓ^{3/2}·g` for non-zero labels and the condensate row `ℓ^{3/2}·δ_0` for the label
  `0`, with `ℓ = ellH v μ`.

The content of the lemma is that the *complex* Gram matrix of `FamV` equals the
Gram matrix of `CoordV` (`Work.BoseBoxFock.gramFamV`), i.e. that the coordinates
`f`, `g` really are the coordinates of the physical modes after complexification;
`HonestModes` only pins the real parts (`realIP`) of those pairings.

The support fact `support_FamV` (every physical mode is supported in the box
`Λ(ℓ)`) is recorded here because the assembly uses it to show that functions
supported *off* the box are orthogonal to the whole physical family.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **The physical mode family** of the honest box model: the χ-modes
`qVec ℓ (kmomLab ℓ N k) = Q(e^{ikx}χ_Λ)` on the left summand of the index and the
θ-modes `thetaExp ℓ (kmomLab ℓ N s) = e^{isx}θ_Λ` on the right.  The label `0` of
the right summand is the condensate: `thetaExp ℓ 0 = thetaFun ℓ`, and
`kmomLab ℓ N 0 = 0`. -/
def FamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    Lab HM.N ⊕ Lab HM.N → (EuclideanSpace ℝ (Fin 3) → ℂ) := fun i =>
  match i with
  | Sum.inl k => Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) HM.N k)
  | Sum.inr s => Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N s)

/-- **The coordinates** of the physical mode family `FamV` in the model basis
`Fin m → ℂ`, in the normalisation of `HonestModes`: `ℓ^{3/2}` times the real
coordinate rows `f` (χ-modes) and `g` (θ-modes, non-zero labels), and the
condensate row `ℓ^{3/2}·δ_0` for the label `0` — consistently with
`HonestModes.hf0`/`hg0` (`f k 0 = 0`, `g s 0 = 0` for `s ≠ 0`) and with the
requirement `⟨e 0, θ⟩ = ℓ^{3/2}`, `⟨e l, θ⟩ = 0` for `l ≠ 0`. -/
def CoordV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ) :
    Lab HM.N ⊕ Lab HM.N → (Fin HM.m → ℂ) := fun i =>
  match i with
  | Sum.inl k => fun l => (((ellH v μ) ^ (3 / 2 : ℝ)) * HM.f k l : ℝ)
  | Sum.inr s =>
      if s = 0 then
        fun l => if l = 0 then (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) else 0
      else fun l => (((ellH v μ) ^ (3 / 2 : ℝ)) * HM.g s l : ℝ)

/-- `Q(e^{ikx}χ_Λ)` is supported in the box `Λ(ℓ)`: both `e^{ikx}χ_Λ` (through the
support of `χ_Λ`) and `θ_Λ` are. -/
lemma support_qVec_subset {ℓ : ℝ} (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    Function.support (Work.BoseK15.corpusBox.qVec ℓ k) ⊆
      Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := by
  intro x hx
  by_contra hxb
  have hchi : Work.BoseK15.corpusBox.chiLam ℓ x = 0 := by
    by_contra hc
    exact hxb (Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ hc)
  have hθ : Work.BoseK15.corpusBox.thetaFun ℓ x = 0 := by
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    exact if_neg hxb
  exact hx (by
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, hchi, hθ]
    simp)

/-- The θ-mode `e^{isx}θ_Λ` is supported in the box `Λ(ℓ)`. -/
lemma support_thetaExp_subset {ℓ : ℝ} (s : EuclideanSpace ℝ (Fin 3)) :
    Function.support (Work.BoseK15.corpusBox.thetaExp ℓ s) ⊆
      Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := by
  intro x hx
  by_contra hxb
  exact hx (by
    rw [Work.BoseB4.BoxData.thetaExp_apply, Work.BoseB4.BoxData.thetaFun_apply]
    exact if_neg hxb ▸ mul_zero _)

/-- The condensate `θ_Λ` is supported in the box `Λ(ℓ)`. -/
lemma support_thetaFun_subset {ℓ : ℝ} :
    Function.support (Work.BoseK15.corpusBox.thetaFun ℓ) ⊆
      Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ := by
  intro x hx
  by_contra hxb
  exact hx (by
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    exact if_neg hxb)

/-- Every vector of the physical family `FamV` is supported in the box `Λ(ℓ)`. -/
lemma support_FamV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (i : Lab HM.N ⊕ Lab HM.N) :
    Function.support (FamV v μ HM i) ⊆
      Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox (ellH v μ) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  rcases i with k | s
  · exact support_qVec_subset hℓ (kmomLab (ellH v μ) HM.N k)
  · exact support_thetaExp_subset (kmomLab (ellH v μ) HM.N s)

end Work.BoseBoxFock
