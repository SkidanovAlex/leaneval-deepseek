import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.MomBilDefs
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.momForm_polar_diff` — `momBil` polarises `momForm`

The large-momentum word of FS `eq:DefT`'s third term,

`momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹<‖p‖}·‖kinFT (θ_u·Q_uψ) p‖²`,

is a **quadratic form** in the one-body state `ψ`.  Hence its polarisation is the bilinear
form `momBil` recorded in `MomBilDefs`:

`momForm ℓ d 0 (f+g) − momForm ℓ d 0 (f−g) = 4·momBil ℓ d f g`.

## Proof

`momForm ℓ d u ψ` is definitionally the `p`-integral of the bounded cut-off
`momProj ℓ d ≥ 0` times the squared modulus of `kinFT (boxState ℓ u ψ)`, the `p`-convention
Fourier transform of the localised mean-free state `boxState ℓ u ψ = ↑(θ_u·Q_uψ)`
(`Kinetic.momForm_eq_boxState`).  Three ingredients assemble the identity:

* `Q_u = Qfree ℓ u` is **linear** in the state (`FsTAux.Qfree_add`/`Qfree_sub`), so
  `boxState ℓ 0 (f±g) = boxState ℓ 0 f ± boxState ℓ 0 g` pointwise and, `kinFT` being linear
  on integrable states (`FsTAux.kinFT_add`/`kinFT_sub`), the Fourier transforms split;
* pointwise the polarisation identity in `ℂ`,
  `‖x+y‖² − ‖x−y‖² = 4·inner ℝ x y` (`norm_add_sq_real`/`norm_sub_sq_real`);
* the `p`-integrands are integrable: `boxState ℓ 0 ψ ∈ L¹ ∩ L²` for smooth `ψ`
  (`Kinetic.boxState_memLp`), Plancherel (`Kinetic.kinFT_sq_of_memLp`) makes
  `‖kinFT (boxState ℓ 0 ψ)‖²` integrable, and `momProj ≤ 1` preserves integrability
  (`FsTAux.integrable_momProj_boxState`), so `∫ (F − G) = ∫F − ∫G`.

No integrability of the *cross* term `momProj·inner` is needed: the scalar `4` factors out of
the Bochner integral unconditionally (`MeasureTheory.integral_const_mul`).
-/

noncomputable section

open MeasureTheory Filter

local notation "boxS" => Work.BoseKinLoc.Kinetic.boxState
local notation "kFT" => Submission.BoseGases.kinFT
local notation "mP" => Work.BoseKinLoc.momProj

namespace Work.BoseFixB2.DvApriori

set_option maxHeartbeats 1000000

/-- The polarisation identity for complex numbers, `ℂ` being a real inner product space:
`‖x+y‖² − ‖x−y‖² = 4·⟪x,y⟫_ℝ`. -/
private lemma norm_sq_add_sub_cplx (x y : ℂ) :
    ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 = 4 * inner ℝ x y := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

theorem momForm_polar_diff {ℓ d : ℝ} (hℓ : 0 < ℓ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BoseKinLoc.momForm ℓ d 0 (fun z => f z + g z)
      - Work.BoseKinLoc.momForm ℓ d 0 (fun z => f z - g z)
      = 4 * Work.BoseFixB2.DvApriori.momBil ℓ d f g := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  -- ## 1. the localised box states split
  have hsplit_add : boxS ℓ 0 (fun z => f z + g z)
      = fun z => boxS ℓ 0 f z + boxS ℓ 0 g z := by
    funext z
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [show Work.BoseKinLoc.Qfree ℓ 0 (fun z => f z + g z) z
        = Work.BoseKinLoc.Qfree ℓ 0 f z + Work.BoseKinLoc.Qfree ℓ 0 g z from
      congrFun (Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ 0 hfc hgc) z]
    push_cast
    ring
  have hsplit_sub : boxS ℓ 0 (fun z => f z - g z)
      = fun z => boxS ℓ 0 f z - boxS ℓ 0 g z := by
    funext z
    simp only [Work.BoseKinLoc.Kinetic.boxState]
    rw [show Work.BoseKinLoc.Qfree ℓ 0 (fun z => f z - g z) z
        = Work.BoseKinLoc.Qfree ℓ 0 f z - Work.BoseKinLoc.Qfree ℓ 0 g z from
      congrFun (Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ 0 hfc hgc) z]
    push_cast
    ring
  -- ## 2. the two box states are integrable
  have hIntf : Integrable (boxS ℓ 0 f) := by
    obtain ⟨h1, -⟩ := Work.BoseKinLoc.Kinetic.boxState_memLp hℓ
      (0 : EuclideanSpace ℝ (Fin 3)) hf
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  have hIntg : Integrable (boxS ℓ 0 g) := by
    obtain ⟨h1, -⟩ := Work.BoseKinLoc.Kinetic.boxState_memLp hℓ
      (0 : EuclideanSpace ℝ (Fin 3)) hg
    exact MeasureTheory.memLp_one_iff_integrable.mp h1
  -- ## 3. the Fourier transforms split
  have hKadd : ∀ p : EuclideanSpace ℝ (Fin 3),
      kFT (boxS ℓ 0 (fun z => f z + g z)) p
        = kFT (boxS ℓ 0 f) p + kFT (boxS ℓ 0 g) p := by
    intro p
    rw [hsplit_add]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_add hIntf hIntg p
  have hKsub : ∀ p : EuclideanSpace ℝ (Fin 3),
      kFT (boxS ℓ 0 (fun z => f z - g z)) p
        = kFT (boxS ℓ 0 f) p - kFT (boxS ℓ 0 g) p := by
    intro p
    rw [hsplit_sub]
    exact Work.BoseFixB2.Polar.FsTAux.kinFT_sub hIntf hIntg p
  -- ## 4. the two `momForm` `p`-integrands are integrable
  have hintp := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ
    (0 : EuclideanSpace ℝ (Fin 3)) (hf.add hg)
  have hintm := Work.BoseFixB2.Polar.FsTAux.integrable_momProj_boxState (d := d) hℓ
    (0 : EuclideanSpace ℝ (Fin 3)) (hf.sub hg)
  -- ## 5. the polarisation identity at the level of the `p`-integral
  have key : (∫ p : EuclideanSpace ℝ (Fin 3),
        mP ℓ d p * ‖kFT (boxS ℓ 0 (fun z => f z + g z)) p‖ ^ 2)
      - (∫ p : EuclideanSpace ℝ (Fin 3),
        mP ℓ d p * ‖kFT (boxS ℓ 0 (fun z => f z - g z)) p‖ ^ 2)
      = 4 * (∫ p : EuclideanSpace ℝ (Fin 3),
          mP ℓ d p * inner ℝ (kFT (boxS ℓ 0 f) p) (kFT (boxS ℓ 0 g) p)) := by
    rw [← MeasureTheory.integral_sub hintp hintm,
      ← MeasureTheory.integral_const_mul (4 : ℝ) (fun p : EuclideanSpace ℝ (Fin 3) =>
        mP ℓ d p * inner ℝ (kFT (boxS ℓ 0 f) p) (kFT (boxS ℓ 0 g) p))]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hKadd p, hKsub p]
    have hpol := norm_sq_add_sub_cplx (kFT (boxS ℓ 0 f) p) (kFT (boxS ℓ 0 g) p)
    linear_combination (norm := ring) (mP ℓ d p) * hpol
  -- ## 6. assemble
  rw [Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d 0 (fun z => f z + g z),
    Work.BoseKinLoc.Kinetic.momForm_eq_boxState ℓ d 0 (fun z => f z - g z)]
  unfold Work.BoseFixB2.DvApriori.momBil
  linear_combination (norm := ring) ((2 * Real.pi) ^ 3)⁻¹ * key

end Work.BoseFixB2.DvApriori
