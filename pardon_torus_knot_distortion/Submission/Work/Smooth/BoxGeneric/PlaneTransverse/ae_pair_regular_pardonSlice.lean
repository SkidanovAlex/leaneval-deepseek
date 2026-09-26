import Mathlib
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_pair_regular

/-!
# Almost every pair `(u, s)` of the cutting plane and the box norm is jointly regular

`Work.Smooth.BoxGeneric.PlaneTransverse.ae_pair_regular` is stated for the *coordinate* level
`uv.1` of `y ↦ y (σ 2)`.  The cutting plane of Pardon's box is `{y | y (σ 2) = c (σ 2) + u}`, so
here is the same statement in terms of the parameter `u`: for almost every pair `(u, s)`, and for
every parameter `p` at which the plane level is `c (σ 2) + u` and the face level `faceLin c σ i ε`
is `s`, the pair of derivatives of `y ↦ y (σ 2)` and of `faceLin c σ i ε` (pulled back to the
parameter plane) is invertible.

This is the input by which the two `1`-parameter families of Pardon's sweep — the box spheres
`{boxNorm c σ · = s}` and the cutting planes — can be put in *joint* general position: the bad pairs
`(u, s)` form a null set of `ℝ²`.  (The statement for a single, fixed `s` is *not* a consequence:
the slice of a null subset of `ℝ²` need not be null.)
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory

namespace Work.Smooth.BoxGeneric.PlaneTransverse

/-- **Almost every pair `(u, s)` is a regular value of the pair
`(y ↦ y (σ 2), faceLin c σ i ε)`**, with `u` the parameter of the cutting plane
`{y | y (σ 2) = c (σ 2) + u}` of Pardon's box. -/
theorem ae_pair_regular_pardonSlice {ψ : Submission.Diffeo} (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ us ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) →
        ∀ p : ℝ × ℝ,
          Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p = c (σ 2) + us.1 →
          Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p = us.2 →
          ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2))) p).prod
            (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p)).IsInvertible := by
  have h := ae_pair_regular (ψ := ψ) c σ
  rw [MeasureTheory.ae_iff] at h ⊢
  have hset : {us : ℝ × ℝ | ¬ (∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
        Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p = c (σ 2) + us.1 →
        Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p = us.2 →
        ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2))) p).prod
          (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p)).IsInvertible)} =
      (fun x : ℝ × ℝ => (c (σ 2), 0) + x) ⁻¹'
        {uv : ℝ × ℝ | ¬ (∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
          Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2)) p = uv.1 →
          Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p = uv.2 →
          ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ 2))) p).prod
            (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p)).IsInvertible)} := by
    ext us
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Prod.fst_add, Prod.snd_add,
      zero_add, add_assoc]
  rw [hset, MeasureTheory.measure_preimage_add]
  exact h

end Work.Smooth.BoxGeneric.PlaneTransverse
