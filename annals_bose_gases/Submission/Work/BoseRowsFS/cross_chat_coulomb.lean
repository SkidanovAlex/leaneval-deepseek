import Mathlib.Analysis.Fourier.Notation
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.CoulBilin.X2_add
import Submission.Work.BoseRowsFS.CoulBilin.X2_comm
import Submission.Work.BoseRowsFS.CoulBilin.chat_add
import Submission.Work.BoseRowsFS.CoulBilin.diag_chat_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

namespace Work.BoseRowsFS

open MeasureTheory ENNReal
open scoped Real FourierTransform ENNReal

local notation "R3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## The `chat`-convention Coulomb double `∫⁻` and the two momentum integrands

`X2 f g` is the Coulomb double `∫⁻` of the pair `(f,g)` (the cross term when `f ≠ g`, the
Newtonian energy when `f = g`); `diagInt h` and `crossInt h k` are the momentum-space
integrands `ĥ(k)²/(2‖k‖²)` and `ĥ(k)k̂(k)/(2‖k‖²)`.  The whole proof of
`Work.BoseRowsFS.cross_chat_coulomb` is performed in terms of these three definitions. -/

/-- The Coulomb double `∫⁻` in its two slots. -/
def X2 (f g : R3 → ℝ) : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * g y / ‖x - y‖)

/-- The diagonal momentum integrand `Ŵ(k)²/(2‖k‖²)`. -/
def diagInt (h : R3 → ℝ) : R3 → ℝ := fun p => Work.BoseFixR.chat h p ^ 2 / (2 * ‖p‖ ^ 2)

/-- The cross momentum integrand `Ŵ(k)Û(k)/(2‖k‖²)`. -/
def crossInt (h k : R3 → ℝ) : R3 → ℝ :=
  fun p => Work.BoseFixR.chat h p * Work.BoseFixR.chat k p / (2 * ‖p‖ ^ 2)

/-- **`X2` only sees the a.e. classes of its slots.** -/
lemma x2_congr_ae {f f' g g' : R3 → ℝ} (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    X2 f g = X2 f' g' := by
  apply lintegral_congr_ae
  filter_upwards [hf] with x hx
  apply lintegral_congr_ae
  filter_upwards [hg] with y hy
  rw [hx, hy]

/-! ## Interface with the four delegated Coulomb-bilinear facts

(`Work.BoseRowsFS.CoulBilin.X2_add`, `...X2_comm`, `...diag_chat_integrable`, `...chat_add`;
the statements below are those of the delegated lemmas read through the definitions `X2`,
`diagInt`.) -/

lemma X2_add' {f g : R3 → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    X2 (f + g) (f + g) = X2 f f + X2 f g + X2 g f + X2 g g :=
  CoulBilin.X2_add hf hg hf0 hg0

lemma X2_comm' {f g : R3 → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    X2 f g = X2 g f :=
  CoulBilin.X2_comm hf hg

lemma diagInt_integrable {W : R3 → ℝ} (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x)
    (hWe : ∀ x, W (-x) = W x) (hfin : X2 W W ≠ ⊤) :
    MeasureTheory.Integrable (diagInt W) :=
  CoulBilin.diag_chat_integrable hW hW0 hWe hfin

lemma chat_add' {W U : R3 → ℝ} (hW : MeasureTheory.Integrable W) (hU : MeasureTheory.Integrable U)
    (k : R3) :
    Work.BoseFixR.chat (W + U) k = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k :=
  CoulBilin.chat_add hW hU k

/-- **Cross-term Fourier–Coulomb (Newtonian energy) identity in the `chat` convention.**

For real, a.e. nonnegative, EVEN, integrable `W, U` on `ℝ³`, with the three Coulomb double
`∫⁻`-integrals finite,

  `(2π)⁻³ ∫ k, Ŵ(k)·Û(k)/(2‖k‖²) dk = (8π)⁻¹ · (∬ W(x)U(y)/‖x−y‖).toReal`,

where `Ŵ = Work.BoseFixR.chat W = Re(kinFT W) = 𝓕W((2π)⁻¹·)` (the last since `W` is even).

The DIAGONAL case (`U = W`) is already in the workspace
(`Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal`, and the `∫⁻` engine
`Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq` with normalisation
`∫⁻‖𝓕W‖²/‖p‖² = 2π²·∬WW/‖x−y‖`).  This is the cross (polarized) companion — the only
missing input for `Work.BoseRowsFS.mass_identity` at `W = W1fun v h ℓ`, `U = g0 v h`,
whose x-side is the proved `Work.BoseFixR.lintegral_W1_g0_eq`
(`∬W₁(x)g₀(y)/‖x−y‖ = 8π·∫W₁ω`).

The three finiteness hypotheses are what makes the `ℝ≥0∞` subtraction legitimate; they are
NOT vacuous (see `Work.BoseRowsFS.W1_g0_finite` for the intended instance).

Suggested route: replace `W` (resp. `U`) by the pointwise nonnegative even a.e.-equal
representative `max W 0` (`Work.BoseB7AK.C3Q.chat_congr_ae` shows `chat` and the double
`∫⁻`'s are unchanged); apply `lintegral_chat_sq_div_eq` to `W`, `U`, `W+U`
(`chat (W+U) = chat W + chat U` pointwise, by linearity of `kinFT`); use the `ℝ≥0∞`
additivity `I2(W+U) = I2 W + 2·X + I2 U` (`ofReal` splits since all four products are
nonnegative a.e.; Tonelli for the swap) plus finiteness of the summands and
`ENNReal.toReal_add`; comparing the resulting real identities gives
`∫ k, chat W k·chat U k/‖k‖² = 2π²·X.toReal`, whence `(2π)⁻³·(1/2)·2π² = 1/(8π)`. -/
theorem cross_chat_coulomb {W U : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hU : MeasureTheory.Integrable U)
    (hWnn : ∀ᵐ x, 0 ≤ W x) (hUnn : ∀ᵐ x, 0 ≤ U x)
    (hWe : ∀ x, W (-x) = W x) (hUe : ∀ x, U (-x) = U x)
    (hP : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤)
    (hR : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (U x * U y / ‖x - y‖)) ≠ ⊤)
    (hX : (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W x * U y / ‖x - y‖)) ≠ ⊤) :
    ((2 * Real.pi) ^ 3)⁻¹
        * (∫ k : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.chat W k * Work.BoseFixR.chat U k / (2 * ‖k‖ ^ 2))
      = (1 / (8 * Real.pi))
        * (∫⁻ x : EuclideanSpace ℝ (Fin 3), ∫⁻ y : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (W x * U y / ‖x - y‖)).toReal := by
  show ((2 * Real.pi) ^ 3)⁻¹
        * (∫ k : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.chat W k * Work.BoseFixR.chat U k / (2 * ‖k‖ ^ 2))
      = (1 / (8 * Real.pi)) * (X2 W U).toReal
  have hP' : X2 W W ≠ ⊤ := hP
  have hR' : X2 U U ≠ ⊤ := hR
  have hX' : X2 W U ≠ ⊤ := hX
  -- pointwise nonnegative, even representatives of the a.e. classes of `W`, `U`
  set f : R3 → ℝ := fun x => max (W x) 0 with hfdef
  set g : R3 → ℝ := fun x => max (U x) 0 with hgdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => by rw [hfdef]; exact le_max_right _ _
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hgdef]; exact le_max_right _ _
  have hfe : ∀ x, f (-x) = f x := fun x => by rw [hfdef]; simp only [hWe x]
  have hge : ∀ x, g (-x) = g x := fun x => by rw [hgdef]; simp only [hUe x]
  have haef : f =ᵐ[volume] W := hWnn.mono (fun x hx => by rw [hfdef]; exact max_eq_left hx)
  have haeg : g =ᵐ[volume] U := hUnn.mono (fun x hx => by rw [hgdef]; exact max_eq_left hx)
  have hfI : MeasureTheory.Integrable f := hW.congr haef.symm
  have hgI : MeasureTheory.Integrable g := hU.congr haeg.symm
  have hPf : X2 f f ≠ ⊤ := by rw [x2_congr_ae haef haef]; exact hP'
  have hPg : X2 g g ≠ ⊤ := by rw [x2_congr_ae haeg haeg]; exact hR'
  have hXfg : X2 f g ≠ ⊤ := by rw [x2_congr_ae haef haeg]; exact hX'
  -- the sum `f + g`
  have hfgI : MeasureTheory.Integrable (f + g) := hfI.add hgI
  have hfg0 : ∀ x, 0 ≤ (f + g) x := fun x => add_nonneg (hf0 x) (hg0 x)
  have hfge : ∀ x, (f + g) (-x) = (f + g) x := fun x => by
    simp only [Pi.add_apply, hfe x, hge x]
  have hsym : X2 g f = X2 f g := X2_comm' hgI.aestronglyMeasurable hfI.aestronglyMeasurable
  have hPfg : X2 (f + g) (f + g) ≠ ⊤ := by
    rw [X2_add' hfI.aestronglyMeasurable hgI.aestronglyMeasurable hf0 hg0, hsym]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hPf, hXfg⟩, hXfg⟩, hPg⟩
  -- integrability of the three diagonal momentum integrands
  have hIf : MeasureTheory.Integrable (diagInt f) := diagInt_integrable hfI hf0 hfe hPf
  have hIg : MeasureTheory.Integrable (diagInt g) := diagInt_integrable hgI hg0 hge hPg
  have hIfg : MeasureTheory.Integrable (diagInt (f + g)) :=
    diagInt_integrable hfgI hfg0 hfge hPfg
  -- the three diagonal Fourier–Coulomb identities
  have hdiagF : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, diagInt f p)
      = (1 / (8 * Real.pi)) * (X2 f f).toReal :=
    Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hfI (Filter.Eventually.of_forall hf0) hfe
  have hdiagG : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, diagInt g p)
      = (1 / (8 * Real.pi)) * (X2 g g).toReal :=
    Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hgI (Filter.Eventually.of_forall hg0) hge
  have hdiagFG : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, diagInt (f + g) p)
      = (1 / (8 * Real.pi)) * (X2 (f + g) (f + g)).toReal :=
    Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal hfgI (Filter.Eventually.of_forall hfg0) hfge
  -- the pointwise polarization identity `(x+y)² - x² - y² = 2xy`, `x = Ŵ(p)`, `y = Û(p)`
  have hpt : ∀ p : R3,
      diagInt (f + g) p - (diagInt f p + diagInt g p) = 2 * crossInt f g p := by
    intro p
    have hc : Work.BoseFixR.chat (f + g) p = Work.BoseFixR.chat f p + Work.BoseFixR.chat g p :=
      chat_add' hfI hgI p
    simp only [diagInt, crossInt, hc]
    by_cases hp : ‖p‖ = 0
    · simp [hp]
    · have h2d : 2 * ‖p‖ ^ 2 ≠ 0 := by
        have hp' : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg p) (Ne.symm hp)
        positivity
      field_simp
      ring
  -- the real integrals split by `integral_sub` / `integral_add`
  have hsplit : (∫ p : R3, diagInt (f + g) p)
        - ((∫ p : R3, diagInt f p) + (∫ p : R3, diagInt g p))
      = 2 * (∫ p : R3, crossInt f g p) := by
    have hφ : MeasureTheory.Integrable (fun p : R3 => diagInt f p + diagInt g p) := hIf.add hIg
    calc (∫ p : R3, diagInt (f + g) p)
          - ((∫ p : R3, diagInt f p) + (∫ p : R3, diagInt g p))
        = (∫ p : R3, diagInt (f + g) p)
          - (∫ p : R3, (diagInt f p + diagInt g p)) := by
          rw [integral_add hIf hIg]
      _ = (∫ p : R3, (diagInt (f + g) p - (diagInt f p + diagInt g p))) :=
          (integral_sub hIfg hφ).symm
      _ = (∫ p : R3, 2 * crossInt f g p) := by
          rw [show (fun p : R3 => diagInt (f + g) p - (diagInt f p + diagInt g p))
                = (fun p : R3 => 2 * crossInt f g p) from funext hpt]
      _ = 2 * (∫ p : R3, crossInt f g p) := integral_const_mul 2 (crossInt f g)
  -- the `toReal` expansion of the Coulomb double of `f + g`
  have hPfg_v : (X2 (f + g) (f + g)).toReal
      = (X2 f f).toReal + 2 * (X2 f g).toReal + (X2 g g).toReal := by
    have hb1 : X2 f f + X2 f g ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hPf, hXfg⟩
    have hb2 : X2 f f + X2 f g + X2 f g ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hb1, hXfg⟩
    rw [X2_add' hfI.aestronglyMeasurable hgI.aestronglyMeasurable hf0 hg0, hsym,
      ENNReal.toReal_add hb2 hPg, ENNReal.toReal_add hb1 hXfg, ENNReal.toReal_add hPf hXfg]
    ring
  -- multiply the split identity by `(2π)⁻³` and use the three diagonal identities
  have h2c : 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, crossInt f g p))
      = (1 / (8 * Real.pi))
        * ((X2 (f + g) (f + g)).toReal - ((X2 f f).toReal + (X2 g g).toReal)) := by
    have hA : 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, crossInt f g p))
        = ((2 * Real.pi) ^ 3)⁻¹ * (2 * (∫ p : R3, crossInt f g p)) := by ring
    rw [hA, ← hsplit, mul_sub, mul_add, hdiagFG, hdiagF, hdiagG]
    ring
  have h3 : (X2 (f + g) (f + g)).toReal - ((X2 f f).toReal + (X2 g g).toReal)
      = 2 * (X2 f g).toReal := by
    rw [hPfg_v]
    ring
  have hfin2 : 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, crossInt f g p))
      = 2 * ((1 / (8 * Real.pi)) * (X2 f g).toReal) := by
    rw [h2c, h3]
    ring
  have hmain : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : R3, crossInt f g p)
      = (1 / (8 * Real.pi)) * (X2 f g).toReal := by
    linarith
  -- transport back from the representatives to `W`, `U`
  have hfun : (fun k : R3 => Work.BoseFixR.chat W k * Work.BoseFixR.chat U k / (2 * ‖k‖ ^ 2))
      = fun k : R3 => Work.BoseFixR.chat f k * Work.BoseFixR.chat g k / (2 * ‖k‖ ^ 2) := by
    funext k
    rw [← Work.BoseB7AK.C3Q.chat_congr_ae haef k, ← Work.BoseB7AK.C3Q.chat_congr_ae haeg k]
  rw [hfun, ← x2_congr_ae haef haeg]
  exact hmain

end

end Work.BoseRowsFS
