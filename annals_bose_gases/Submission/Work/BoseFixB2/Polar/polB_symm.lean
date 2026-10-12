import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.polB_symm`

FS §6's polarised box word `polB` (`𝒜_{ij}`'s numerator) is **symmetric**:

    `polB v h μ n Φ Ψ = polB v h μ n Ψ Φ`.

Since by definition `4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)`, and `Φ+Ψ` and
`Ψ+Φ` are the same function, this is exactly the **evenness** of the box word

    `wordB v h μ n (fun x => -(Φ x)) = wordB v h μ n Φ`,

used on the state `Ψ−Φ` (`Φ−Ψ = −(Ψ−Φ)`).  `wordB` is a quadratic form: the
box-restricted form `boxFormB` is the sum of the slot kinetic words (`fsT`
applied to the slot fibres) and of `(Φ x)²·potWordU x`, and every one of those
is a sum of squares of linear functionals of the state, hence even.

The proof below expands this into elementary pointwise identities of the four
kinetic pieces (`neuWord`, `gapWord`, `momWord`, `mainWord`); no integrability,
smoothness or positivity hypothesis is needed — every step is either a
pointwise identity of integrands or the unconditional `integral_neg`, and the
single `sInf` (`neuFrac`) is handled by the observation that the trial
functional flips the sign of the trial and the trial class (globally smooth,
compactly supported) is closed under negation.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

namespace PolB

/-! ## 1. Auxiliary facts about the box, the mean and the Fourier transform -/

/-- Negation preserves compact support. -/
lemma hasCompactSupport_neg_fun {f : ℝ³ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => -(f z)) :=
  hf.comp_left (g := fun x : ℝ => -x) (by simp)

/-- The case `−` of `fderiv` at the level of the evaluation on a vector. -/
lemma fderiv_neg_apply (g : ℝ³ → ℝ) (z v : ℝ³) :
    fderiv ℝ (fun y => -(g y)) z v = -(fderiv ℝ g z v) := by
  have h : fderiv ℝ (-g) z = -fderiv ℝ g z := fderiv_neg
  have h2 : (fun y => -(g y)) = (-g : ℝ³ → ℝ) := rfl
  rw [h2, h]
  rfl

/-- The `p`-convention Fourier transform is odd in its argument. -/
lemma kinFT_neg (u : ℝ³ → ℂ) (p : ℝ³) :
    Submission.BoseGases.kinFT (fun y => -(u y)) p = -Submission.BoseGases.kinFT u p := by
  simp only [Submission.BoseGases.kinFT, mul_neg, integral_neg]

/-! ## 2. The box mean, `Qfree` and the one-body kinetic pieces -/

/-- The moving-box mean is odd in the state. -/
lemma bsMean_neg (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsMean ℓ u (fun z => -(ψ z)) = -Work.BSKinetic.bsMean ℓ u ψ := by
  simp only [Work.BSKinetic.bsMean, integral_neg]
  ring

/-- The moving-box mean-free projection is odd in the state (pointwise form). -/
lemma bsQ_neg (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    Work.BSKinetic.bsQ ℓ u (fun z => -(ψ z)) x = -(Work.BSKinetic.bsQ ℓ u ψ x) := by
  simp only [Work.BSKinetic.bsQ, bsMean_neg]
  ring

/-- `Qfree` is odd in the state (pointwise form). -/
lemma Qfree_neg (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) (x : ℝ³) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => -(ψ z)) x = -(Work.BoseKinLoc.Qfree ℓ u ψ x) :=
  bsQ_neg ℓ u ψ x

/-- `Qfree` is odd in the state (function form). -/
lemma Qfree_neg_fun (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => -(ψ z)) = fun x => -(Work.BoseKinLoc.Qfree ℓ u ψ x) :=
  funext fun x => Qfree_neg ℓ u ψ x

/-- The one-body big-box kinetic word `bsOneBody` is odd in the state. -/
lemma bsOneBody_neg (ℓ : ℝ) (F : ℝ → ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BSKinetic.bsOneBody ℓ F u (fun z => -(ψ z)) = Work.BSKinetic.bsOneBody ℓ F u ψ := by
  simp only [Work.BSKinetic.bsOneBody, bsQ_neg, Complex.ofReal_neg, mul_neg, kinFT_neg, norm_neg]

/-- The bare large-momentum form is odd in the state. -/
lemma momForm_neg (ℓ d : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.momForm ℓ d u (fun z => -(ψ z)) = Work.BoseKinLoc.momForm ℓ d u ψ := by
  simp only [Work.BoseKinLoc.momForm, Qfree_neg, Complex.ofReal_neg, mul_neg, kinFT_neg, norm_neg]

/-- The bare box gap `⟨Q_uψ, Q_uψ⟩` is odd in the state. -/
lemma gapBare_neg (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.gapBare ℓ u (fun z => -(ψ z)) = Work.BoseKinLoc.gapBare ℓ u ψ := by
  simp only [Work.BoseKinLoc.gapBare, Qfree_neg, neg_sq]

/-! ## 3. The four kinetic pieces of `fsT` -/

/-- `neuFrac` is invariant under `φ ↦ −φ`.

The trial functional `T(φ,g) = ∫_Λ φ² − 2a²∫_Λ φg + a²(‖∇g‖² + a²‖g‖²)`
is quadratic in `(φ,g)` in the sense `T(−φ,g) = T(φ,−g)`, and the trial class
(globally smooth, compactly supported) is stable under `g ↦ −g`.  The identity
`T(−φ,g) = T(φ,−g)` is a pointwise identity of the four integrals: the first
and the last only involve squares, the cross term flips sign via `neg_mul`,
and the gradient term flips via `fderiv_neg`. -/
lemma neuFrac_neg (ℓ a2 : ℝ) (u : ℝ³) (φ : ℝ³ → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => -(φ z)) = Work.BoseKinLoc.neuFrac ℓ a2 u φ := by
  simp only [Work.BoseKinLoc.neuFrac]
  congr 1
  ext c
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, hg, hgs, hc⟩
    refine ⟨fun z => -(g z), hg.neg, hasCompactSupport_neg_fun hgs, ?_⟩
    rw [hc]
    simp only [neg_sq, neg_mul, mul_neg, neg_neg, integral_neg, fderiv_neg_apply]
  · rintro ⟨g, hg, hgs, hc⟩
    refine ⟨fun z => -(g z), hg.neg, hasCompactSupport_neg_fun hgs, ?_⟩
    rw [hc]
    simp only [neg_sq, neg_mul, mul_neg, neg_neg, integral_neg, fderiv_neg_apply]

lemma neuWord_neg (ℓ d εT : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.neuWord ℓ d εT u (fun z => -(ψ z)) = Work.BoseKinLoc.neuWord ℓ d εT u ψ := by
  simp only [Work.BoseKinLoc.neuWord, Qfree_neg_fun, neuFrac_neg]

lemma gapWord_neg (ℓ b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.gapWord ℓ b u (fun z => -(ψ z)) = Work.BoseKinLoc.gapWord ℓ b u ψ := by
  simp only [Work.BoseKinLoc.gapWord, gapBare_neg]

lemma momWord_neg (ℓ d εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.momWord ℓ d εT b u (fun z => -(ψ z)) = Work.BoseKinLoc.momWord ℓ d εT b u ψ := by
  simp only [Work.BoseKinLoc.momWord, momForm_neg]

lemma mainWord_neg (ℓ d s εT : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => -(ψ z)) = Work.BoseKinLoc.mainWord ℓ d s εT u ψ := by
  simp only [Work.BoseKinLoc.mainWord, bsOneBody_neg]

/-- FS `eq:DefT`'s localised kinetic word `𝒯_u` is odd in the state. -/
lemma fsT_neg (ℓ d s εT b : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => -(ψ z)) = Work.BoseKinLoc.fsT ℓ d s εT b u ψ := by
  simp only [Work.BoseKinLoc.fsT, neuWord_neg, gapWord_neg, momWord_neg, mainWord_neg]

/-! ## 4. The slot fibres and the box-restricted form -/

/-- The slot-`i` fibre of the negated state is the negated fibre. -/
lemma fibre_neg (N : ℕ) (i : Fin N) (Φ : X N → ℝ) (x : X N) :
    Work.BoseKinLoc.fibre N i (fun y => -(Φ y)) x
      = fun z => -(Work.BoseKinLoc.fibre N i Φ x z) := by
  funext z
  simp only [Work.BoseKinLoc.fibre]

/-- The box-restricted kinetic word is odd in the state. -/
lemma kinFormB_neg (N : ℕ) (ℓ d s εT b : ℝ) (Φ : X N → ℝ) :
    Work.BoseKinLoc.kinFormB N ℓ d s εT b (fun x => -(Φ x))
      = Work.BoseKinLoc.kinFormB N ℓ d s εT b Φ := by
  simp only [Work.BoseKinLoc.kinFormB, fibre_neg, fsT_neg]

/-- The box-restricted form `boxFormB` is odd in the state. -/
lemma boxFormB_neg (N : ℕ) (v g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (Φ : X N → ℝ) :
    Work.BoseKinLoc.boxFormB N v g ℓ μ d s εT b (fun x => -(Φ x))
      = Work.BoseKinLoc.boxFormB N v g ℓ μ d s εT b Φ := by
  simp only [Work.BoseKinLoc.boxFormB, kinFormB_neg, neg_sq]

/-- FS `eq:Def_HB2`'s box word `wordB` is odd in the state. -/
theorem wordB_neg (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    Work.BoseBoxFix.wordB v h μ n (fun x => -(Φ x)) = Work.BoseBoxFix.wordB v h μ n Φ := by
  simp only [Work.BoseBoxFix.wordB, boxFormB_neg]

end PolB

/-! ## 5. Symmetry of the polarised word -/

/-- **FS §6's polarised box word is symmetric.** -/
theorem polB_symm {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) : Work.BoseFixB2.polB v h μ n Φ Ψ = Work.BoseFixB2.polB v h μ n Ψ Φ := by
  -- `wordB` is even, applied to `Ψ−Φ`, where `Φ−Ψ = −(Ψ−Φ)`
  have key : Work.BoseBoxFix.wordB v h μ n (fun x => Φ x - Ψ x)
      = Work.BoseBoxFix.wordB v h μ n (fun x => Ψ x - Φ x) := by
    have he : (fun x => Φ x - Ψ x) = (fun x => -(Ψ x - Φ x)) := by
      funext x; ring
    rw [he]
    exact PolB.wordB_neg v h μ n (fun x => Ψ x - Φ x)
  -- and the sum `Φ+Ψ` is the sum `Ψ+Φ`
  have hcomm : Work.BoseBoxFix.wordB v h μ n (fun x => Φ x + Ψ x)
      = Work.BoseBoxFix.wordB v h μ n (fun x => Ψ x + Φ x) := by
    congr 1
    funext x
    ring
  simp only [Work.BoseFixB2.polB]
  rw [key, hcomm]

end Work.BoseFixB2.Polar
