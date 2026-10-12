import ChallengeDeps
import Submission.Work.BoseBoxFock.PotCubicPins
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pcfFrameDefs` — the frame vocabulary of the cubic (`Q̃₃`) dictionary

The dictionary `PotCubicFree` compares the *mode* sum of the cubic row with the *position* word
`q3lowWord`.  Its whole analytic content is carried by three lattice sums ("frames"), which this
module names so that the assembly can be phrased in terms of them
(design: `FINDING_PotCubicFree_exists.md`, §4.2bis):

* `Kfr` — the `k`-frame `Σ_{k∈excited} Ŵ₁(k)e^{i⟨k,z⟩}`: evaluated by
  `Work.BoseBoxFock.W1_latticeSum_eq` (`= ℓ³Σ_d uvSmear(z+ℓd) − Ŵ₁(0)`);
* `Ksfr` — the `s`-frame `Σ_{s∈excited} f_L(s)e^{i⟨s,z⟩}`: evaluated by
  `Work.BoseBoxFock.fL_latticeSum_eq_complex` (the periodised multiplier kernel of
  `f(√−Δ/κ)`);
* `Kχfr` — the `χ̂`-weighted `k`-frame `Σ_{k∈excited} Ŵ₁(k)χ̂(ℓk)e^{i⟨k,z⟩}`: evaluated by
  `Work.BoseBoxFock.W1_chatChi_latticeSum_eq`;

and `Middle` is the *middle kernel* of the cubic row, i.e. the sum which the four-channel split
(`Work.BoseBoxFock.summand_four_split`, PROVED) expands channel by channel into products of these
three frames (see `FINDING…` §4.2bis).

Everything here is `sorry`-free (definitions only).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseBox

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The honest `Ŵ₁`-weight of the cubic row: the `W1` field of `KzEnvHon`, i.e.
`ζ_Λ(kmom)Ŵ₁(kmom)` at `Λ = uvRad (sideAt μ (a v)) N`. -/
def W1h (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (k : Lab N) : ℝ :=
  uvCut fu (uvRad (sideAt μ (BoseGases.a v)) N) (kmomLab (ellH v μ) N k)
    * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (sideAt μ (BoseGases.a v)))
        (kmomLab (ellH v μ) N k)

/-- The honest low-momentum weight `f_L(kmom)` of the cubic row, at FS's `K_L√(μa) = (d²ℓ)⁻¹`
(`Work.BoseFixB3.kapAt`). -/
def fLh (v : Ω → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (s : Lab N) : ℝ :=
  fc.f (‖kmomLab (ellH v μ) N s‖
    / (((paramsAt μ (BoseGases.a v)).d ^ 2 * sideAt μ (BoseGases.a v))⁻¹))

/-- The honest `χ̂(ℓk)` used by the `qVec`-correction channels. -/
def hatChih (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) : ℝ :=
  Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k)

/-- The **`k`-frame**: `Σ_{k∈excited}Ŵ₁(k)e^{i⟨kmom k,z⟩}` (`W1_latticeSum_eq`). -/
def Kfr (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (z : Ω) : ℂ :=
  ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((W1h v h μ fu N k : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))

/-- The **`s`-frame**: `Σ_{s∈excited}f_L(s)e^{i⟨kmom s,z⟩}` (`fL_latticeSum_eq_complex`). -/
def Ksfr (v : Ω → ℝ) (fc : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (z : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s : ℝ) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) z : ℂ))

/-- The **`χ̂`-weighted `k`-frame**: `Σ_{k∈excited}Ŵ₁(k)χ̂(ℓk)e^{i⟨kmom k,z⟩}`
(`W1_chatChi_latticeSum_eq`). -/
def Kχfr (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ)
    (z : Ω) : ℂ :=
  ∑ k ∈ Work.BoseB7.excited (Lab N),
    (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
      * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))

/-- The **middle kernel** of the cubic row: the `(s,k)`-sum which the four-channel split expands.
Its arguments are the point `x` of the second slot, and the two replacement variables `y` (first
slot) and `u` (second slot). -/
def Middle (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    (N : ℕ) (x y u : Ω) : ℂ :=
  ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
    ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
      * star (pinQ v μ N (s - k) y) * pinTheta v μ N s x * star (pinQ v μ N k u)

end Work.BoseBoxFock
