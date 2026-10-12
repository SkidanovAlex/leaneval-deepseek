import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRowDefs2` — the pinned modes and the `μ`-form of the FS `Q₁` χ-row

* `chiMode ℓ N = χ_Λ² − θ_Λ − chiTail` is the *complex* function that the pinned superposed
  χ-mode `ℓ^{3/2}·η_C` equals a.e.; `thMode` is its `χ²`-row twin (with `thetaTail`).
* `muForm ℓ w Φ = 2Σ_j∫(P_jΦ)·Φ·w(x_j)` is the `μ`-line of the χ-sandwich, and
  `muCorr ℓ w Φ = 2Σ_j∫(P_jΦ)²·w(x_j)` the difference to the "diagonal" form `muLine`:
  pointwise `(P_jΦ)·Φ = (Q_jΦ)(P_jΦ) + (P_jΦ)²`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- The **pinned `χ`-row mode**: the complex function `χ_Λ² − θ_Λ − chiTail` which the pinned
superposed mode `ℓ^{3/2}η_C = ∑_k hatChi_k qVec_k` equals a.e. -/
noncomputable def chiMode (ℓ : ℝ) (N : ℕ) : Sp → ℂ := fun z =>
  ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) ^ 2
    - Work.BoseK15.corpusBox.thetaFun ℓ z - chiTail ℓ N z

/-- The **pinned θ-row (`χ²`-row) mode**: `χ_Λ² − θ_Λ − thetaTail`. -/
noncomputable def thMode (ℓ : ℝ) (N : ℕ) : Sp → ℂ := fun z =>
  ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) ^ 2
    - Work.BoseK15.corpusBox.thetaFun ℓ z - thetaTail ℓ N z

/-- **The `μ`-form of the χ-sandwich**: `2Σ_j∫_{abox}(P_jΦ)·Φ·w(x_j)`. -/
noncomputable def muForm (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  2 * ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) * Φ x * w (x j)

/-- **The `μ`-correction**: `2Σ_j∫_{abox}(P_jΦ)²·w(x_j)`, the difference between `muForm` and
`muLine`. -/
noncomputable def muCorr (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  2 * ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 * w (x j)


/-- The first half of the pair slot form: the `n₀ ∘ |η_w⟩⟨e₀|` orientation. -/
noncomputable def pairHalfOne (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, Φ x *
    (∑ i : Fin n, (aP ℓ i
      (fun y : X n => ∑ j : Fin n, w (y j) * aP ℓ j Φ y)) x)

/-- The second half of the pair slot form: the `|e₀⟩⟨η_w| ∘ n₀` orientation. -/
noncomputable def pairHalfTwo (n : ℕ) (ℓ : ℝ) (w : Sp → ℝ) (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, Φ x *
    (∑ i : Fin n, (aP ℓ i
      (fun y : X n => w (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x)

/-- The real part of the pinned χ-mode, off the cube. -/
lemma chiMode_re (ℓ : ℝ) (N : ℕ) (z : Sp) :
    (chiMode ℓ N z).re
      = (Work.BoseK15.corpusBox.chiLam ℓ z) ^ 2 - (Work.BoseK15.corpusBox.thetaFun ℓ z).re
          - (chiTail ℓ N z).re := by
  simp only [chiMode, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- On the cube, the real part of the pinned χ-mode is the χ-row weight `chiW`. -/
lemma chiMode_re_of_theta_eq_one (ℓ : ℝ) (N : ℕ) {z : Sp}
    (hz : Work.BoseK15.corpusBox.thetaFun ℓ z = 1) :
    (chiMode ℓ N z).re = chiW ℓ N z := by
  rw [chiMode_re, hz]
  simp only [Complex.one_re, chiW, chiCube]

/-- On the cube, the real part of the pinned θ-row mode is the weight `thW`. -/
lemma thMode_re_of_theta_eq_one (ℓ : ℝ) (N : ℕ) {z : Sp}
    (hz : Work.BoseK15.corpusBox.thetaFun ℓ z = 1) :
    (thMode ℓ N z).re = thW ℓ N z := by
  simp only [thMode, thW, chiCube, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hz, Complex.one_re]

end Work.BoseBoxFock
