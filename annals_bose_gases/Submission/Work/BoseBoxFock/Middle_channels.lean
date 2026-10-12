import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.Middle_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_channels` — the four channel summands of `Middle`

`PotCubicExpansion.summand_four_split` expands the summand of the cubic row's middle kernel
`Middle` into four channels `(a) − (b) − (c) + (d)` (times `((√ℓ³)⁻¹)³`).  This module *names* the
four channels (`chsA` … `chsD`, with the `x`/`y`/`u` slot variables in the order of
`summand_four_split`) and the four weighted double sums (`ChA` … `ChD`), so that the channel
evaluations can be stated and consumed compactly.  The definitions are verbatim transcriptions of
the four terms of `summand_four_split`, so the identification is `rfl`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- Channel `(a)` of `summand_four_split`. -/
def chsA (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) (s k : Lab N) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
    * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))

/-- Channel `(b)` of `summand_four_split`. -/
def chsB (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) (s k : Lab N) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) y : ℂ)))
    * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) y : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
    * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)

/-- Channel `(c)` of `summand_four_split`. -/
def chsC (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) (s k : Lab N) : ℂ :=
  ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) u : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) u : ℝ) : ℂ))

/-- Channel `(d)` of `summand_four_split`. -/
def chsD (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) (s k : Lab N) : ℂ :=
  ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N (s - k)) : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ))
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
    * (((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) u)

/-- The weighted `(a)`-channel double sum. -/
def ChA (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsA v h fc fu μ N y x u s k

/-- The weighted `(b)`-channel double sum. -/
def ChB (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsB v h fc fu μ N y x u s k

/-- The weighted `(c)`-channel double sum. -/
def ChC (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsC v h fc fu μ N y x u s k

/-- The weighted `(d)`-channel double sum. -/
def ChD (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (y x u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsD v h fc fu μ N y x u s k

end Work.BoseBoxFock
