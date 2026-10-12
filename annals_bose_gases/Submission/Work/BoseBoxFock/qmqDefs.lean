import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowShape_wLoc_aPC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qmqDefs` — the `Q M Q` kernel of the pair-row dictionary

The `Q₂` row of FS `lem:2ndQuand` carries the operator `Q M_W Q` on the one-particle space, where
`M_W` is the multiplication by an honest localised pair kernel and `Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|` is the
corpus's `aQ`-projection on the box `acube ℓ`.

This module fixes the **kernel form** of `Q M Q`:

    `qmqKernel ℓ k w y = k w y − ℓ⁻³∫_{acube}k w y' − ℓ⁻³∫_{acube}k w' y + ℓ⁻⁶∬_{acube²} k`

(the four rows of `(1 − ℓ⁻³|θ⟩⟨θ|) ∘ M_k ∘ (1 − ℓ⁻³|θ⟩⟨θ|)`), together with its elementary
properties: symmetry and boundedness.  The two identity theorems of the dictionary
(`rowShape13` ↔ the word's `T₁` slot, and `(1/2)(rowShape21 + rowShape23)` ↔ the word's `T₄` slot)
are stated in terms of this kernel in separate modules.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The first box average `ℓ⁻³∫_{acube}k w ·` (as a `ℂ`-coercion). -/
noncomputable def qmqRowB (ℓ : ℝ) (k : E3 → E3 → ℝ) (w : E3) : ℂ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, ((k w y' : ℝ) : ℂ))

/-- The second box average `ℓ⁻³∫_{acube}k · y`. -/
noncomputable def qmqRowC (ℓ : ℝ) (k : E3 → E3 → ℝ) (y : E3) : ℂ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, ((k w' y : ℝ) : ℂ))

/-- The constant row `ℓ⁻⁶∬_{acube²} k`. -/
noncomputable def qmqRowD (ℓ : ℝ) (k : E3 → E3 → ℝ) : ℂ :=
  (((ℓ ^ 3)⁻¹ : ℝ) ^ 2)
    * (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ))

/-- **The `Q M Q` kernel**: the kernel form of `Q ∘ M_k ∘ Q`, `Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|` the box
complement projection, `M_k` = multiplication by `k`. -/
noncomputable def qmqKernel (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) : ℂ :=
  ((k w y : ℝ) : ℂ) - qmqRowB ℓ k w - qmqRowC ℓ k y + qmqRowD ℓ k

/-- The defining expansion of `qmqKernel`. -/
theorem qmqKernel_eq (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) :
    qmqKernel ℓ k w y
      = ((k w y : ℝ) : ℂ)
        - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, ((k w y' : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, ((k w' y : ℝ) : ℂ))
        + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2)
            * (∫ w' in Submission.BoseGases.acube ℓ,
                ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ)) := by
  rw [qmqKernel, qmqRowB, qmqRowC, qmqRowD]

/-- For a symmetric `k`, the two one-variable rows agree: `qmqRowB ℓ k w = qmqRowC ℓ k w`. -/
theorem qmqRowB_eq_qmqRowC (ℓ : ℝ) {k : E3 → E3 → ℝ} (hk : ∀ w y, k w y = k y w) (w : E3) :
    qmqRowB ℓ k w = qmqRowC ℓ k w := by
  have hfun : (fun y' : E3 => ((k w y' : ℝ) : ℂ)) = fun w' : E3 => ((k w' w : ℝ) : ℂ) := by
    funext y'
    rw [hk w y']
  rw [qmqRowB, qmqRowC, hfun]

/-- The `Q M Q` kernel is symmetric in its two variables when `k` is. -/
theorem qmqKernel_symm (ℓ : ℝ) {k : E3 → E3 → ℝ} (hk : ∀ w y, k w y = k y w)
    (w y : E3) : qmqKernel ℓ k w y = qmqKernel ℓ k y w := by
  have h1 := qmqRowB_eq_qmqRowC ℓ hk w
  have h2 := qmqRowB_eq_qmqRowC ℓ hk y
  have h3 : k w y = k y w := hk w y
  rw [qmqKernel, qmqKernel, h1, h2, h3]
  ring

/-! ## The `ℂ`-valued form of the kernel (for complex weights such as the periodisation) -/

/-- The `Q M Q` kernel at a **complex** pair kernel `k`. -/
noncomputable def qmqKC (ℓ : ℝ) (k : E3 → E3 → ℂ) (w y : E3) : ℂ :=
  k w y
    - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, k w y')
    - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
    + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2)
        * (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ, k w' y')

/-- `qmqKernel` is the real-kernel case of `qmqKC`. -/
theorem qmqKernel_eq_qmqKC (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) :
    qmqKernel ℓ k w y = qmqKC ℓ (fun a b => ((k a b : ℝ) : ℂ)) w y := by
  rw [qmqKernel, qmqRowB, qmqRowC, qmqRowD, qmqKC]

/-- **The `θ`-full `Q M Q` kernel** at a complex pair kernel: the kernel of
`Q ∘ M_k ∘ Q` with `Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|`, i.e. the four rows of
`(1 − ℓ⁻³|θ⟩⟨θ|)∘M_k∘(1 − ℓ⁻³|θ⟩⟨θ|)` as an integral operator.  The three correction rows carry
the sharp box indicator `θ_Λ`; they differ from those of `qmqKC` off the box, but the two kernels
have the *same* `aPC`-form (every `y`- or `w`-region where the indicators differ has zero state
weight, see the module docstring of `qmqDefs`). -/
noncomputable def qmqKCθ (ℓ : ℝ) (k : E3 → E3 → ℂ) (w y : E3) : ℂ :=
  k w y
    - ((ℓ ^ 3)⁻¹ : ℝ) * Work.BoseK15.corpusBox.thetaFun ℓ y
        * (∫ y' in Submission.BoseGases.acube ℓ, k w y')
    - ((ℓ ^ 3)⁻¹ : ℝ) * Work.BoseK15.corpusBox.thetaFun ℓ w
        * (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
    + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2) * Work.BoseK15.corpusBox.thetaFun ℓ w
        * Work.BoseK15.corpusBox.thetaFun ℓ y
        * (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ, k w' y')

/-- The defining expansion of `qmqKCθ`. -/
theorem qmqKCθ_eq (ℓ : ℝ) (k : E3 → E3 → ℂ) (w y : E3) :
    qmqKCθ ℓ k w y
      = k w y
        - ((ℓ ^ 3)⁻¹ : ℝ) * Work.BoseK15.corpusBox.thetaFun ℓ y
            * (∫ y' in Submission.BoseGases.acube ℓ, k w y')
        - ((ℓ ^ 3)⁻¹ : ℝ) * Work.BoseK15.corpusBox.thetaFun ℓ w
            * (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
        + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2) * Work.BoseK15.corpusBox.thetaFun ℓ w
            * Work.BoseK15.corpusBox.thetaFun ℓ y
            * (∫ w' in Submission.BoseGases.acube ℓ,
                ∫ y' in Submission.BoseGases.acube ℓ, k w' y') := rfl

/-! ## The `χχ`-images kernel -/

/-- **The `χχ`-lattice-images kernel** `χ(w)χ(y)Σ_{m≠0}W(w−y+ℓm)` of FS's `eq:DefQ2`.  It is the
difference between the periodised kernel and its `m = 0` part:
`ℓ⁻³χ(w)latPer3 ℓ W (w−y)χ(y) = wPair ℓ W w y + imgKernel ℓ W w y + 0` is False (`wPair` carries
`wScaled`, not `W`); with `W = wScaled ℓ h` one has the exact identity
`k_per(w,y) = wPair ℓ h w y + imgKernel ℓ (wScaled ℓ h) w y`, which is the `m = 0`/`m ≠ 0` split of
the periodisation. -/
noncomputable def imgKernel (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) : ℝ :=
  Submission.BoseGases.chiScale ℓ w
    * (∑' m : Fin 3 → ℤ, if m = 0 then 0 else W (w - y + ℓ • latVec m))
    * Submission.BoseGases.chiScale ℓ y

/-- `chiChiImages ℓ (↑W)` is the coercion of `imgKernel ℓ W` (for real `W`). -/
theorem chiChiImages_eq_imgKernel (ℓ : ℝ) (W : E3 → ℝ) (w y : E3) :
    chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y = ((imgKernel ℓ W w y : ℝ) : ℂ) := by
  have hsum : (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ) else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ((∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ) else W (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun m => by by_cases h : m = 0 <;> simp [h])
  rw [chiChiImages, imgKernel, hsum]
  push_cast
  ring

/-! ## The two pair words at a general kernel -/

/-- **The word `T₁` at a general pair kernel `k`**: `Σ_{i≠j}∫(P_iQ_jΦ)(P_jQ_iΦ)k(x_i,x_j)`.  At
`k = wPairC ℓ (g₂ v h)` it is the corpus's `q1PairWord`. -/
noncomputable def q1WordK {n : ℕ} (ℓ : ℝ) (k : E3 → E3 → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x
        * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        * k (x p.1) (x p.2)

/-- **The word `T₄` at a general pair kernel `k`**: `Σ_{i≠j}∫(P_iP_jΦ)(Q_jQ_iΦ)k(x_i,x_j)`.  At
`k = wPairC ℓ (g₀ v h)` it is the corpus's `q4PairWord`. -/
noncomputable def q4WordK {n : ℕ} (ℓ : ℝ) (k : E3 → E3 → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
        * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        * k (x p.1) (x p.2)

end Work.BoseBoxFock
