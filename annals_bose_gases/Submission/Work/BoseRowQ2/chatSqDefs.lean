import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowQ2.maskTailDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.chatSqDefs` — the vocabulary of the `chatSq` row

The sharp mask row of FS l.3253 needs the `L² → L²` bound `ChatᵀChat ⪯ ‖χ‖²∞` for the matrix

    `Chat N k i = χ̂ (vec (K k − K i))`,   `K = labVec : Lab N → ℤ³`,

i.e. the quadratic form inequality `∑_k (∑_i b i · Chat N k i)² ≤ ‖χ‖²∞ ∑_i b i²`
(`Work.BoseRowQ2.chatSq_form_le`, with `‖χ‖²∞ ≤ 48/π`).

The proof is the *sampling isometry*: `Chat` samples the Fourier transform of the single vector
`χ · C`, where `C` is the trigonometric polynomial `∑_i b i · e^{i⟪vec (K i),·⟫}`.  The
converse direction (the norm of `C` on the unit cube is `∑ b i²`) is the lattice orthogonality
`∫_{unitCell} e^{i⟪vec n,x⟫} dx = δ_{n,0}` of `Work.BoseB4.integral_unitCell_cos_lattice`.

This module contains only the definitions and the elementary bookkeeping lemmas; it is
`sorry`-free and is safe to import from delegated-lemma modules.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The lattice momentum `2π · K i` of the label `i` (`K = labVec`). -/
noncomputable def CVec (N : ℕ) (i : Lab N) : E3 := Work.BoseB4.vec (labVec N i)

@[simp] theorem CVec_apply (N : ℕ) (i : Lab N) (j : Fin 3) :
    CVec N i j = 2 * Real.pi * (labVec N i j : ℝ) :=
  rfl

/-- `vec` is injective. -/
theorem vec_injective : Function.Injective (Work.BoseB4.vec : (Fin 3 → ℤ) → E3) := by
  intro a b h
  have h' := congrArg (fun v : E3 => WithLp.ofLp v) h
  simp only [Work.BoseB4.vec, WithLp.ofLp_toLp] at h'
  funext l
  have hl : 2 * Real.pi * (a l : ℝ) = 2 * Real.pi * (b l : ℝ) := congrFun h' l
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  exact_mod_cast mul_left_cancel₀ hπ hl

/-- `vec` is additive for the honest difference of the balanced representatives. -/
theorem vec_sub (a b : Fin 3 → ℤ) :
    Work.BoseB4.vec (a - b) = Work.BoseB4.vec a - Work.BoseB4.vec b := by
  ext j
  simp only [Work.BoseB4.vec, WithLp.ofLp_toLp, Pi.sub_apply, PiLp.sub_apply]
  push_cast
  ring

/-- The lattice momentum of the difference of two labels. -/
theorem CVec_sub (N : ℕ) (k i : Lab N) :
    CVec N k - CVec N i = Work.BoseB4.vec (labVec N k - labVec N i) := by
  rw [CVec, CVec, ← vec_sub]

/-- `CVec` is injective. -/
theorem CVec_injective (N : ℕ) : Function.Injective (CVec N) :=
  vec_injective.comp (Work.BoseFixR.labVec_injective N)

/-- `Chat N k i` is the `χ̂` of the momentum difference. -/
theorem Chat_eq_chiHat (N : ℕ) (k i : Lab N) :
    Chat N k i = chiHat (CVec N k - CVec N i) := by
  rw [Chat, CVec_sub]

/-- The defining integral form of `Chat`. -/
theorem chat_eq_integral (N : ℕ) (k i : Lab N) :
    Chat N k i
      = ∫ x : E3, Submission.BoseGases.chi x * Real.cos (inner ℝ (CVec N k - CVec N i) x) := by
  rw [Chat_eq_chiHat, chiHat]
  rfl

/-- The trigonometric polynomial attached to the vector `b`: the sum of the plane waves
`e^{i⟪2π K i, x⟫}` weighted by `b i`. -/
noncomputable def ChatC (N : ℕ) (b : Lab N → ℝ) : E3 → ℂ :=
  fun x => ∑ i : Lab N, (b i : ℂ) * Complex.exp (Complex.I * (inner ℝ (CVec N i) x : ℂ))

theorem ChatC_apply (N : ℕ) (b : Lab N → ℝ) (x : E3) :
    ChatC N b x
      = ∑ i : Lab N, (b i : ℂ) * Complex.exp (Complex.I * (inner ℝ (CVec N i) x : ℂ)) :=
  rfl

end Work.BoseRowQ2
