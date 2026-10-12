import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiChiImages_pairing_boxSmooth
import Submission.Work.BoseBoxFock.imagesMirrorPeel
import Submission.Work.BoseBoxFock.imgFibre2_boxSmooth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesWordAux` — the two peel+pairing helpers of `imagesWordLe`

The pair terms of the two words `q1WordK ℓ (imgKernel ℓ W) Φ` and `q4WordK ℓ (imgKernel ℓ W) Φ`
are bound by the corpus's PROVED images-pairing tail `chiChiImages_pairing_boxSmooth`, which
consumes a `BoxSmooth` test function and its `pairEnergy` only (never a supremum of `W`).  The two
lemmas here package the whole route — the peel identity (`imgFibre_peel` for the `q1` word, the
mirror `imgFibre2_peel` for the `q4` word), the complexification, and the pairing bound — into the
single inequality that the assembly of `imagesWordLe` consumes:

    `|∫_{abox} (aP ℓ p.1 F₁)·G·imgKernel ℓ W (x p.1)(x p.2)|
        ≤ Cimg·(R/ℓ)^6·√(∫coulInt W)·√(ℓ³·pairEnergy ℓ (imgFibreC ℓ p F₁ G))`

(and the same with `aP ℓ p.2`/`imgFibre₂C`).

`Cimg = imagesCimg := Classical.choose (chiChiImages_pairing_boxSmooth 6)`, a **fixed** real,
independent of `ℓ`, `R`, `W` (its `∃C` sits *before* `ℓ`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fixed pairing constant of the images tail, extracted at `K = 6`. -/
noncomputable def imagesCimg : ℝ := Classical.choose (chiChiImages_pairing_boxSmooth 6)

theorem imagesCimg_nonneg : 0 ≤ imagesCimg :=
  (Classical.choose_spec (chiChiImages_pairing_boxSmooth 6)).1

/-- The images-pairing tail at `K = 6`, with the constant exposed. -/
theorem imagesCimg_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ / 4)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x : E3, 0 ≤ W x)
    (hWs : ∀ x : E3, R ≤ ‖x‖ → W x = 0) (hWJint : MeasureTheory.Integrable (coulInt W))
    {G : E3 → E3 → ℂ} (hG : BoxSmooth ℓ G) :
    ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y * G w y‖
      ≤ imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W z)
        * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ G) :=
  (Classical.choose_spec (chiChiImages_pairing_boxSmooth 6)).2 hℓ hR hRℓ hWi hW0 hWs hWJint hG

/-- The complexified box-squared pairing of `imgKernel ℓ W` against `imgFibreC` is the cast of the
real pairing, hence its norm is the absolute value of the real pairing. -/
theorem imgPairing_norm_eq {n : ℕ} (ℓ : ℝ) {p : Fin n × Fin n}
    (F₁ G : Submission.BoseGases.X n → ℝ) {W : E3 → ℝ} :
    ‖∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v‖
      = |∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v| := by
  have hinner : ∀ u : E3,
      (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v)
        = ((∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v : ℝ) : ℂ) := by
    intro u
    have h1 : (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v)
        = ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            ((imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [chiChiImages_eq_imgKernel, imgFibreC, Complex.ofReal_mul]
    rw [h1]
    exact integral_ofReal
  have houter : (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v)
      = ((∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v : ℝ) : ℂ) := by
    have heq : (fun u : E3 => ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v)
        = fun u => ((∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v : ℝ) : ℂ) :=
      funext hinner
    rw [heq]
    exact integral_ofReal
  rw [houter, Complex.norm_real, Real.norm_eq_abs]

/-- **The `q1`-pair images bound**: the `p.1`-slot peel pairs the pair term with `imgFibreC`, and
the images tail bounds that pairing. -/
theorem imgPairLe {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ / 4)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x : E3, 0 ≤ W x)
    (hWs : ∀ x : E3, R ≤ ‖x‖ → W x = 0) (hWJint : MeasureTheory.Integrable (coulInt W))
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    |∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.1 F₁ x * G x * imgKernel ℓ W (x p.1) (x p.2)|
      ≤ imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibreC ℓ p F₁ G)) := by
  rw [imgFibre_peel (n := n) (ℓ := ℓ) (R := R) (p := p) hℓ hp hWi hR.le (by linarith) hWs
    hF₁.continuous hG.continuous]
  calc |∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        imgKernel ℓ W u v * imgFibre ℓ p F₁ G u v|
      = ‖∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibreC ℓ p F₁ G u v‖ :=
        (imgPairing_norm_eq ℓ F₁ G).symm
    _ ≤ imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibreC ℓ p F₁ G)) :=
        imagesCimg_le hℓ hR hRℓ hWi hW0 hWs hWJint (imgFibre_boxSmooth hℓ hF₁ hG)

/-- **The `q4`-pair images bound** (the mirror peel). -/
theorem imgPairLe2 {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hRℓ : R ≤ ℓ / 4)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {W : E3 → ℝ} (hWi : MeasureTheory.Integrable W) (hW0 : ∀ᵐ x : E3, 0 ≤ W x)
    (hWs : ∀ x : E3, R ≤ ‖x‖ → W x = 0) (hWJint : MeasureTheory.Integrable (coulInt W))
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    |∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.2 F₁ x * G x * imgKernel ℓ W (x p.1) (x p.2)|
      ≤ imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p F₁ G)) := by
  rw [imgFibre2_peel (n := n) (ℓ := ℓ) (R := R) (p := p) hℓ hp hWi hR.le (by linarith) hWs
    hF₁.continuous hG.continuous]
  have hnorm : ‖∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v‖
      = |∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v| := by
    have hinner : ∀ u : E3,
        (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v)
          = ((∫ v in Work.BoseK15.corpusBox.boxL ℓ,
              imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ) := by
      intro u
      have h1 : (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v)
          = ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
              ((imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        simp only [chiChiImages_eq_imgKernel, imgFibre₂C, Complex.ofReal_mul]
      rw [h1]
      exact integral_ofReal
    have houter : (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v)
        = ((∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ) := by
      have heq : (fun u : E3 => ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v)
          = fun u => ((∫ v in Work.BoseK15.corpusBox.boxL ℓ,
              imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v : ℝ) : ℂ) :=
        funext hinner
      rw [heq]
      exact integral_ofReal
    rw [houter, Complex.norm_real, Real.norm_eq_abs]
  calc |∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
        imgKernel ℓ W u v * imgFibre₂ ℓ p F₁ G u v|
      = ‖∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) u v * imgFibre₂C ℓ p F₁ G u v‖ :=
        hnorm.symm
    _ ≤ imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p F₁ G)) :=
        imagesCimg_le hℓ hR hRℓ hWi hW0 hWs hWJint (imgFibre2_boxSmooth hℓ hF₁ hG)

end Work.BoseBoxFock
