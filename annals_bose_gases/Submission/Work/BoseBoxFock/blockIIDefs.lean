import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.block13_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.blockIIDefs` — the **real** `Q M Q` kernel and its two-variable box projection

`qmqKernel ℓ k` (`qmqDefs`) is the kernel form of `Q M_k Q`, `Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|`, for a
**real** pair kernel `k` cast to `ℂ`.  For the dictionary `blockII_dict` the kernel has to be
handled as a real object, so this module fixes

* `qmqKR ℓ k` — the same kernel as a real-valued function, with the cast lemma
  `qmqKernel_eq_ofRealKR` (the `block13_aux` name `qmqKernel_eq_ofReal`, for its
  definitionally identical `qmqKernelR`, is not redeclared here — see the note below);
* `boxP1`, `boxP2`, `boxP12`, `boxProj` — the same object written as the two-variable box
  projection `(1 − P₁)(1 − P₂)` on `acube ℓ × acube ℓ`, where
  `P₁ f a b = ℓ⁻³∫_{a'∈acube} f a' b`, `P₂ f a b = ℓ⁻³∫_{b'∈acube} f a b'`,
  `P₁P₂ f a b = ℓ⁻⁶∫_{a'}∫_{b'} f a' b'`; and the identification
  `boxProj ℓ k = qmqKR ℓ k`;
* the symmetry `qmqKR_symm` for symmetric `k`.

Everything is `sorry`-free.
-/

noncomputable section
open MeasureTheory

set_option linter.unusedVariables false

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The real `Q M Q` kernel**: `qmqKernel ℓ k` at a real kernel `k`, as a real number. -/
noncomputable def qmqKR (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) : ℝ :=
  k w y
    - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, k w y')
    - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, k w' y)
    + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2)
        * (∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, k w' y')

/-- `qmqKernel` at a real kernel is the coercion of `qmqKR`.

⚠ The name carries the `KR` suffix because `block13_aux.lean` already declares the same
statement for its own (definitionally identical) real kernel `qmqKernelR`
(`Work.BoseBoxFock.qmqKernel_eq_ofReal`); two declarations of the same name in two modules of one
import cone are a hard Lean error (`environment already contains …`), so this copy is renamed.
Both statements are interchangeable by definitional unfolding of `qmqKR`/`qmqKernelR`. -/
theorem qmqKernel_eq_ofRealKR (ℓ : ℝ) (k : E3 → E3 → ℝ) (w y : E3) :
    qmqKernel ℓ k w y = ((qmqKR ℓ k w y : ℝ) : ℂ) := by
  rw [qmqKernel, qmqRowB, qmqRowC, qmqRowD, qmqKR]
  have h1 : (∫ y' in Submission.BoseGases.acube ℓ, ((k w y' : ℝ) : ℂ))
      = ((∫ y' in Submission.BoseGases.acube ℓ, k w y' : ℝ) : ℂ) := integral_ofReal
  have h2 : (∫ w' in Submission.BoseGases.acube ℓ, ((k w' y : ℝ) : ℂ))
      = ((∫ w' in Submission.BoseGases.acube ℓ, k w' y : ℝ) : ℂ) := integral_ofReal
  have h3 : (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ))
      = (((∫ w' in Submission.BoseGases.acube ℓ,
          ∫ y' in Submission.BoseGases.acube ℓ, k w' y' : ℝ)) : ℂ) := by
    rw [show (fun w' : E3 => ∫ y' in Submission.BoseGases.acube ℓ, ((k w' y' : ℝ) : ℂ))
          = fun w' => ((∫ y' in Submission.BoseGases.acube ℓ, k w' y' : ℝ) : ℂ) from by
        funext w'; exact integral_ofReal]
    exact integral_ofReal
  rw [h1, h2, h3]
  push_cast
  ring

/-- `qmqKR` is symmetric for a symmetric kernel. -/
theorem qmqKR_symm (ℓ : ℝ) {k : E3 → E3 → ℝ} (hk : ∀ w y, k w y = k y w) (w y : E3) :
    qmqKR ℓ k w y = qmqKR ℓ k y w := by
  have h1 := qmqKernel_eq_ofRealKR ℓ k w y
  have h2 := qmqKernel_eq_ofRealKR ℓ k y w
  have h3 : qmqKernel ℓ k w y = qmqKernel ℓ k y w := qmqKernel_symm ℓ hk w y
  rw [h1, h2] at h3
  exact_mod_cast h3

/-! ## The two-variable box projection on `acube ℓ × acube ℓ` -/

/-- `P₁ f a b = ℓ⁻³∫_{a'∈acube} f a' b`. -/
noncomputable def boxP1 (ℓ : ℝ) (f : E3 → E3 → ℝ) (a b : E3) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (∫ a' in Submission.BoseGases.acube ℓ, f a' b)

/-- `P₂ f a b = ℓ⁻³∫_{b'∈acube} f a b'`. -/
noncomputable def boxP2 (ℓ : ℝ) (f : E3 → E3 → ℝ) (a b : E3) : ℝ :=
  ((ℓ ^ 3)⁻¹ : ℝ) * (∫ b' in Submission.BoseGases.acube ℓ, f a b')

/-- `P₁P₂ f a b = ℓ⁻⁶∫_{a'}∫_{b'} f a' b'`. -/
noncomputable def boxP12 (ℓ : ℝ) (f : E3 → E3 → ℝ) (a b : E3) : ℝ :=
  (((ℓ ^ 3)⁻¹ : ℝ) ^ 2)
    * (∫ a' in Submission.BoseGases.acube ℓ,
        ∫ b' in Submission.BoseGases.acube ℓ, f a' b')

/-- **The two-variable box projection** `(1 − P₁)(1 − P₂) f`. -/
noncomputable def boxProj (ℓ : ℝ) (f : E3 → E3 → ℝ) : E3 → E3 → ℝ :=
  fun a b => f a b - boxP1 ℓ f a b - boxP2 ℓ f a b + boxP12 ℓ f a b

/-- `boxProj ℓ k` is the real `Q M Q` kernel `qmqKR ℓ k`. -/
theorem boxProj_eq_qmqKR (ℓ : ℝ) (k : E3 → E3 → ℝ) :
    boxProj ℓ k = qmqKR ℓ k := by
  funext a b
  rw [boxProj, boxP1, boxP2, boxP12, qmqKR]
  ring

end Work.BoseBoxFock
