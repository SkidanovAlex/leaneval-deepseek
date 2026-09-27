import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BaryBase

/-!
# Joint continuity of the four BCG building blocks

`pfun`, `dpfun` (the Poisson kernel and its `x`-derivative) live on `E n × Sph n`, while
`gradB`, `hessB` (the Euclidean gradient and Hessian of the Busemann function) live on
`Sph n × E n`.  On these regions the common denominator `tpart x - ⟪x,ξ⟫` is positive
(`busemann_arg_pos`), which is exactly what is needed both for the real powers occurring in
`pfun`/`dpfun` and for the inverses occurring in `gradB`/`hessB`.  Continuity is then purely
symbolic: sums, products, scalar multiples, inverses, `Real.rpow` with a fixed exponent and
the (continuous, bilinear) `smulRight` operation.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real

noncomputable section

variable {n : ℕ}

/-- The Poisson denominator `tpart x - ⟪x,ξ⟫` on `E n × Sph n`. -/
def denomX (n : ℕ) (q : E n × Sph n) : ℝ := tpart q.1 - inner ℝ q.1 q.2

/-- The Busemann denominator `tpart y - ⟪y,ξ⟫` on `Sph n × E n`. -/
def denomY (n : ℕ) (q : Sph n × E n) : ℝ := tpart q.2 - inner ℝ q.2 q.1

lemma continuous_denomX (n : ℕ) : Continuous (denomX n) := by
  rw [show denomX n = fun q : E n × Sph n =>
      tpart (q.1 : E n) - inner ℝ (q.1 : E n) (q.2 : E n) from rfl]
  exact (continuous_tpart.comp continuous_fst).sub
    (continuous_fst.inner (continuous_subtype_val.comp continuous_snd))

lemma continuous_denomY (n : ℕ) : Continuous (denomY n) := by
  rw [show denomY n = fun q : Sph n × E n =>
      tpart (q.2 : E n) - inner ℝ (q.2 : E n) (q.1 : E n) from rfl]
  exact (continuous_tpart.comp continuous_snd).sub
    (continuous_snd.inner (continuous_subtype_val.comp continuous_fst))

lemma denomX_pos (n : ℕ) (q : E n × Sph n) : 0 < denomX n q :=
  busemann_arg_pos (q.2 : E n) q.2.property (q.1 : E n)

lemma denomY_pos (n : ℕ) (q : Sph n × E n) : 0 < denomY n q :=
  busemann_arg_pos (q.1 : E n) q.1.property (q.2 : E n)

lemma continuous_pfun (n : ℕ) :
    Continuous (fun q : E n × Sph n => pfun n q.1 q.2) := by
  rw [show (fun q : E n × Sph n => pfun n q.1 q.2)
      = fun q : E n × Sph n => (denomX n q) ^ (-((n : ℝ) - 1)) from rfl]
  exact Continuous.rpow_const (continuous_denomX n) (fun q => Or.inl (ne_of_gt (denomX_pos n q)))

/-- `y ↦ (innerSL ℝ y).smulRight y` is continuous (it is the bilinear `smulRightL` composed
with the diagonal map). -/
lemma continuous_innerSL_smulRight (n : ℕ) :
    Continuous (fun y : E n => (innerSL ℝ y).smulRight y) := by
  have h1 : Continuous (fun y : E n => innerSL ℝ y) := (innerSL ℝ).continuous
  have h2 : Continuous (fun p : (E n →L[ℝ] ℝ) × E n => p.1.smulRight p.2) :=
    (ContinuousLinearMap.smulRightL ℝ (E n) (E n)).continuous₂
  exact h2.comp (h1.prodMk continuous_id)

lemma continuous_dpfun (n : ℕ) :
    Continuous (fun q : E n × Sph n => dpfun n q.1 q.2) := by
  rw [show (fun q : E n × Sph n => dpfun n q.1 q.2)
      = fun q : E n × Sph n =>
          (-((n : ℝ) - 1) * (denomX n q) ^ (-((n : ℝ) - 1) - 1)) •
            ((tpart (q.1 : E n))⁻¹ • innerSL ℝ (q.1 : E n) - innerSL ℝ (q.2 : E n)) from rfl]
  have hs : Continuous (fun q : E n × Sph n =>
      -((n : ℝ) - 1) * (denomX n q) ^ (-((n : ℝ) - 1) - 1)) :=
    continuous_const.mul (Continuous.rpow_const (continuous_denomX n)
      (fun q => Or.inl (ne_of_gt (denomX_pos n q))))
  have hv : Continuous (fun q : E n × Sph n =>
      (tpart (q.1 : E n))⁻¹ • innerSL ℝ (q.1 : E n) - innerSL ℝ (q.2 : E n)) := by
    refine Continuous.sub ?_ ?_
    · exact ((continuous_tpart.comp continuous_fst).inv₀
        (fun q => (tpart_pos (q.1 : E n)).ne')).smul ((innerSL ℝ).continuous.comp continuous_fst)
    · exact (innerSL ℝ).continuous.comp (continuous_subtype_val.comp continuous_snd)
  exact hs.smul hv

lemma continuous_gradB (n : ℕ) :
    Continuous (fun q : Sph n × E n => gradB n q.1 q.2) := by
  rw [show (fun q : Sph n × E n => gradB n q.1 q.2)
      = fun q : Sph n × E n =>
          (denomY n q)⁻¹ • ((tpart (q.2 : E n))⁻¹ • (q.2 : E n) - (q.1 : E n)) from rfl]
  have hs : Continuous (fun q : Sph n × E n => (denomY n q)⁻¹) :=
    (continuous_denomY n).inv₀ (fun q => (denomY_pos n q).ne')
  have hv : Continuous (fun q : Sph n × E n =>
      (tpart (q.2 : E n))⁻¹ • (q.2 : E n) - (q.1 : E n)) := by
    refine Continuous.sub ?_ ?_
    · exact ((continuous_tpart.comp continuous_snd).inv₀
        (fun q => (tpart_pos (q.2 : E n)).ne')).smul continuous_snd
    · exact continuous_subtype_val.comp continuous_fst
  exact hs.smul hv

lemma continuous_hessB (n : ℕ) :
    Continuous (fun q : Sph n × E n => hessB n q.1 q.2) := by
  rw [show (fun q : Sph n × E n => hessB n q.1 q.2)
      = fun q : Sph n × E n =>
          (denomY n q)⁻¹ •
              ((tpart (q.2 : E n))⁻¹ • (1 : E n →L[ℝ] E n) -
                ((tpart (q.2 : E n)) ^ 3)⁻¹ • (innerSL ℝ (q.2 : E n)).smulRight (q.2 : E n)) -
            (innerSL ℝ (gradB n (q.1 : E n) (q.2 : E n))).smulRight
              (gradB n (q.1 : E n) (q.2 : E n)) from rfl]
  have hs : Continuous (fun q : Sph n × E n => (denomY n q)⁻¹) :=
    (continuous_denomY n).inv₀ (fun q => (denomY_pos n q).ne')
  have hinner : Continuous (fun q : Sph n × E n =>
      (tpart (q.2 : E n))⁻¹ • (1 : E n →L[ℝ] E n) -
        ((tpart (q.2 : E n)) ^ 3)⁻¹ • (innerSL ℝ (q.2 : E n)).smulRight (q.2 : E n)) := by
    refine Continuous.sub ?_ ?_
    · exact ((continuous_tpart.comp continuous_snd).inv₀
        (fun q => (tpart_pos (q.2 : E n)).ne')).smul
        (continuous_const : Continuous (fun _ : Sph n × E n => (1 : E n →L[ℝ] E n)))
    · exact (((continuous_tpart.comp continuous_snd).pow 3).inv₀
        (fun q => pow_ne_zero 3 (tpart_pos (q.2 : E n)).ne')).smul
        ((continuous_innerSL_smulRight n).comp continuous_snd)
  have hlast : Continuous (fun q : Sph n × E n =>
      (innerSL ℝ (gradB n (q.1 : E n) (q.2 : E n))).smulRight
        (gradB n (q.1 : E n) (q.2 : E n))) :=
    (continuous_innerSL_smulRight n).comp (continuous_gradB n)
  exact (hs.smul hinner).sub hlast

/-- The four explicit building blocks of the BCG natural-map computanda (`pfun`, `dpfun`,
`gradB`, `hessB`) are jointly continuous on the region where they are meant to be evaluated:
the Poisson kernel and its `x`-derivative on `E n × Sph n`, the Euclidean gradient and Hessian
of the Busemann function on `Sph n × E n`. -/
theorem BCGBlocksContinuous (n : ℕ) :
    Continuous (fun q : Submission.Mostow.E n × Submission.Mostow.Sph n =>
        Work.Mostow.pfun n q.1 q.2) ∧
    Continuous (fun q : Submission.Mostow.E n × Submission.Mostow.Sph n =>
        Work.Mostow.dpfun n q.1 q.2) ∧
    Continuous (fun q : Submission.Mostow.Sph n × Submission.Mostow.E n =>
        Work.Mostow.gradB n q.1 q.2) ∧
    Continuous (fun q : Submission.Mostow.Sph n × Submission.Mostow.E n =>
        Work.Mostow.hessB n q.1 q.2) :=
  ⟨continuous_pfun n, continuous_dpfun n, continuous_gradB n, continuous_hessB n⟩

end

end Work.Mostow
