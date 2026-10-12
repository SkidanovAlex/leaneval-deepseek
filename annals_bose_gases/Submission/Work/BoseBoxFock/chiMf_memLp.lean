import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiMf_memLp`

The windowed mean-free part of an `L²` one-body state is again `L²`:

    `χ_ℓ · mf ℓ f ∈ L²(ℝ³)`,  `mf ℓ f = f − (ℓ³)⁻¹ ∫_{boxL ℓ} f`   (`ℓ > 0`, `f ∈ L²`),

where `χ_ℓ = Submission.BoseGases.chiScale ℓ` is the corpus bump `χ(x/ℓ)` and `boxL ℓ` is the
corpus box of `Work.BoseK15.corpusBox`.

`mf` is a *fixed affine modification* of `f`: the subtracted integral does not depend on `x`.
Hence

    `χ_ℓ · mf ℓ f = χ_ℓ · f − c · χ_ℓ`,   `c := (ℓ³)⁻¹ ∫_{boxL ℓ} f`   (definitionally),

a difference of two products whose `L²`-membership is immediate from two facts about the window:

* `χ_ℓ` is bounded by `chiSup` (`Submission.BoseGases.abs_chiScale_le_chiSup`), i.e. it lies in
  `L^∞`, and a bounded function multiplies `L²` into `L²` (`chiScale_memLp_mul`, via
  `MeasureTheory.MemLp.mul` with the Hölder triple `(⊤, 2, 2)`);
* `χ_ℓ` itself is continuous with compact support, hence `L²` (`chiScale_memLp_two`, via
  `Continuous.memLp_of_hasCompactSupport`).

No integrability of `f` on `boxL ℓ` is needed: `c` is a definite complex number in either case.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The complexified window `χ_ℓ` is bounded**, hence an `L^∞` function: the bound is
`chiSup = (∫χ²)^{-1/2}`. -/
theorem chiScale_memLp_top {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MemLp (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) ⊤
      (volume : Measure E3) := by
  have hcont : Continuous (fun x : E3 => Complex.ofReal (Submission.BoseGases.chiScale ℓ x)) :=
    Complex.continuous_ofReal.comp
      ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous)
  refine memLp_top_of_bound hcont.aestronglyMeasurable Submission.BoseGases.chiSup ?_
  filter_upwards with x
  simpa using Submission.BoseGases.abs_chiScale_le_chiSup ℓ x

/-- **The complexified window `χ_ℓ` is `L²`**: it is continuous with compact support
(`chiScale_hasCompactSupport`), and Lebesgue measure is finite on compacts. -/
theorem chiScale_memLp_two {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MemLp (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) 2
      (volume : Measure E3) := by
  have hcont : Continuous (fun x : E3 => Complex.ofReal (Submission.BoseGases.chiScale ℓ x)) :=
    Complex.continuous_ofReal.comp
      ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous)
  have hcs : HasCompactSupport (fun x : E3 => Complex.ofReal (Submission.BoseGases.chiScale ℓ x)) :=
    HasCompactSupport.comp_left (g := Complex.ofReal) (f := Submission.BoseGases.chiScale ℓ)
      (Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)) (by simp)
  exact hcont.memLp_of_hasCompactSupport hcs

/-- **Multiplication by the window preserves `L²`**: `χ_ℓ` is an `L^∞` multiplier, and
`MemLp.mul` with the Hölder triple `p = ⊤`, `q = r = 2` multiplies `L²` by `L^∞` into `L²`
(`⊤⁻¹ + 2⁻¹ = 2⁻¹`). -/
theorem chiScale_memLp_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3)) :
    MemLp (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * f x) 2
      (volume : Measure E3) :=
  (chiScale_memLp_top hℓ).mul hf

/-- **The windowed mean-free part of an `L²` state is `L²`.**

`mf` differs from `f` by the constant `c := (ℓ³)⁻¹∫_{boxL ℓ} f`, so
`χ_ℓ · mf ℓ f = χ_ℓ · f − c·χ_ℓ` pointwise; the first term is `L²` by `chiScale_memLp_mul` and the
second is a multiple of the `L²` function `χ_ℓ` (`chiScale_memLp_two`). -/
theorem chiMf_memLp {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    MeasureTheory.MemLp (fun x : EuclideanSpace ℝ (Fin 3) =>
      ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ f x) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- the `x`-independent constant `c` by which `mf` differs from `f`
  set c : ℂ := ((ℓ ^ 3)⁻¹ : ℝ) * ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f y with hcdef
  -- `χ_ℓ · f ∈ L²`
  have h1 : MemLp (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * f x) 2
      (volume : Measure E3) := chiScale_memLp_mul hℓ hf
  -- `c · χ_ℓ ∈ L²`
  have h2 : MemLp (fun x : E3 => c * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) 2
      (volume : Measure E3) := (chiScale_memLp_two hℓ).const_mul c
  have h3 : MemLp (fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * f x
      - c * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)) 2 (volume : Measure E3) := h1.sub h2
  -- and the pointwise identity `χ_ℓ · mf ℓ f = χ_ℓ · f − c · χ_ℓ`
  have hkey : ∀ x : E3, ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * mf ℓ f x
      = ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * f x
        - c * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) := by
    intro x
    simp only [Work.BoseBoxFock.mf, hcdef]
    ring
  exact h3.ae_eq (Filter.Eventually.of_forall (fun x => (hkey x).symm))

end Work.BoseBoxFock
