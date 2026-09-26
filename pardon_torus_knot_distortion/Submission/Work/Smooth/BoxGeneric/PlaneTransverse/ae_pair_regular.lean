import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine

namespace Work.Smooth.BoxGeneric.PlaneTransverse

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

/-!
# Almost every pair of face values is a regular value of the corresponding pair map

For a fixed pair `(i, ε)` of a face of Pardon's box, consider the map

`p ↦ (pullback ψ (y ↦ y (σ 2)) p, pullback ψ (faceLin c σ i ε) p)`

from the parameter plane to `ℝ × ℝ`.  The statement
`Work.Smooth.BoxGeneric.PlaneTransverse.ae_pair_regular` says that for almost every pair of values
`(u, v)` and **every** parameter `p` mapping to `(u, v)`, the differential of this map at `p` is
invertible — equivalently, that almost every pair of values is a regular value.

This is two-dimensional Sard's theorem for the pair map, which is `C²` (it is the pull-back of
`C^∞` functions along the parametrisation) and `2π`-periodic in each variable (the standard torus
parametrisation is).  It is therefore an immediate consequence of
`Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair`, the critical values
of a `C²` periodic self-map of the plane being Lebesgue-null.  The finitely many pairs
`(i, ε) ∈ Fin 3 × {±1}` are combined at the end.

(Note that the case `σ i = σ 2` needs no separate treatment: there the second component is an
affine function of the first, the derivative is never invertible, and the critical value set is the
image, which is contained in a line — in particular it is null, which is exactly what the Sard
input provides.)
-/

/-- The pull-back `pullback ψ g` is `2π`-periodic in the first variable, because the standard
torus parametrisation `torusMap` is. -/
private theorem pullback_add_two_pi_left (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    Work.Smooth.Morse.pullback ψ g (p.1 + 2 * Real.pi, p.2) =
      Work.Smooth.Morse.pullback ψ g p := by
  rw [Work.Smooth.Morse.pullback_apply, Work.Smooth.Morse.pullback_apply,
    Work.Core.torusMap_add_two_pi_left]

/-- The pull-back `pullback ψ g` is `2π`-periodic in the second variable. -/
private theorem pullback_add_two_pi_right (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    Work.Smooth.Morse.pullback ψ g (p.1, p.2 + 2 * Real.pi) =
      Work.Smooth.Morse.pullback ψ g p := by
  rw [Work.Smooth.Morse.pullback_apply, Work.Smooth.Morse.pullback_apply,
    Work.Core.torusMap_add_two_pi_right]

/-- **Sard for a single pair of faces.**  For almost every pair of values `(u, v)`, every parameter
`p` with `pullback ψ (y ↦ y (σ 2)) p = u` and `pullback ψ (faceLin c σ i ε) p = v` is a regular
point of the pair map, i.e. the product of the two differentials is invertible. -/
private lemma ae_pair_regular_single {ψ : Submission.Diffeo} (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) :
    ∀ᵐ uv ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      ∀ p : ℝ × ℝ,
        Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p = uv.1 →
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p = uv.2 →
        ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2))) p).prod
          (fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε))
            p)).IsInvertible := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2))) :=
    Work.Smooth.Morse.pullback_contDiff ψ (by fun_prop)
  have hB : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) :=
    Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i ε
  -- the pair map is `C²`
  have hGcd : ContDiff ℝ 2
      (fun p : ℝ × ℝ => (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p)) := by
    have := hA.prodMk hB
    exact this.of_le (WithTop.coe_le_coe.mpr le_top)
  -- and `2π`-periodic in each variable
  have hper1 : ∀ p : ℝ × ℝ,
      (fun p : ℝ × ℝ => (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p))
        (p.1 + 2 * Real.pi, p.2) =
      (fun p : ℝ × ℝ => (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p)) p := by
    intro p
    change (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) (p.1 + 2 * Real.pi, p.2),
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)
          (p.1 + 2 * Real.pi, p.2)) =
      (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p)
    rw [pullback_add_two_pi_left, pullback_add_two_pi_left]
  have hper2 : ∀ p : ℝ × ℝ,
      (fun p : ℝ × ℝ => (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p))
        (p.1, p.2 + 2 * Real.pi) =
      (fun p : ℝ × ℝ => (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p)) p := by
    intro p
    change (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) (p.1, p.2 + 2 * Real.pi),
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)
          (p.1, p.2 + 2 * Real.pi)) =
      (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p,
        Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p)
    rw [pullback_add_two_pi_right, pullback_add_two_pi_right]
  -- Sard: the critical values of the pair map are null
  have hnull := Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair
    hGcd hper1 hper2
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro uv huv
  -- `huv` says that `uv` *is* a critical value of the pair map
  push Not at huv
  obtain ⟨p, h1, h2, h3⟩ := huv
  refine ⟨p, ?_, ?_⟩
  · exact Prod.ext h1 h2
  · -- the differential of the pair map is the product of the two differentials
    rw [DifferentiableAt.fderiv_prodMk (hA.contDiffAt.differentiableAt (by simp))
      (hB.contDiffAt.differentiableAt (by simp))]
    exact h3

/-- **Almost every pair of face values is regular.**  For almost every pair `(u, v)` of real
numbers, and for every face `(i, ε)` of Pardon's box (`i : Fin 3`, `ε = ±1`), every parameter `p`
of the surface with `y (σ 2) = u` and `faceLin c σ i ε = v` is a regular point of the pair
`(y (σ 2), faceLin c σ i ε)`: the product of the two differentials is invertible. -/
theorem ae_pair_regular {ψ : Submission.Diffeo} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ uv ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
        ∀ p : ℝ × ℝ,
          Work.Smooth.Morse.pullback ψ (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => y (σ 2)) p = uv.1 →
          Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p = uv.2 →
          ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : LeanEval.KnotTheory.PardonDistortion.R3 => y (σ 2))) p).prod
            (fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p)).IsInvertible := by
  -- combine the three faces and the two signs: finitely many almost-everywhere statements
  refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
  filter_upwards [ae_pair_regular_single (ψ := ψ) c σ i 1,
    ae_pair_regular_single (ψ := ψ) c σ i (-1)] with uv hpos hneg ε hε
  rcases hε with h | h
  · rw [h]; exact hpos
  · rw [h]; exact hneg

end Work.Smooth.BoxGeneric.PlaneTransverse
