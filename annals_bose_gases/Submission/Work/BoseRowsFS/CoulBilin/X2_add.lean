import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseRowsFS.CoulBilin

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Bilinear expansion of the Coulomb double `∫⁻` (additivity in the diagonal slot).**

For measurable, pointwise nonnegative `f g : ℝ³ → ℝ`, with
`X2 u v := ∫⁻ x, ∫⁻ y, ofReal (u x * v y / ‖x−y‖)`,

  `X2 (f+g) (f+g) = X2 f f + X2 f g + X2 g f + X2 g g`.

The pointwise content is `(f x + g x)(f y + g y)/‖x−y‖ = f x f y/d + f x g y/d + g x f y/d + g x g y/d`
with all four summands `≥ 0`, so `ENNReal.ofReal` splits; the four `∫⁻`'s separate by
`lintegral_add_left'` (the summands are a.e.-measurable because `f`, `g` are).  The two cross
terms are kept apart (they coincide by the companion lemma `X2_comm`). -/
theorem X2_add {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f) (hg : MeasureTheory.AEStronglyMeasurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x + g x) * (f y + g y) / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖))
        + (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * g y / ‖x - y‖))
        + (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * f y / ‖x - y‖))
        + (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖)) := by
  -- a.e.-measurability of `f`, `g`
  have hf' : AEMeasurable f volume := hf.aemeasurable
  have hg' : AEMeasurable g volume := hg.aemeasurable
  -- a.e.-measurability of the pieces on the product space
  have hf1 : AEMeasurable (fun z : E3 × E3 => f z.1) volume := hf'.comp_fst
  have hf2 : AEMeasurable (fun z : E3 × E3 => f z.2) volume := hf'.comp_snd
  have hg1 : AEMeasurable (fun z : E3 × E3 => g z.1) volume := hg'.comp_fst
  have hg2 : AEMeasurable (fun z : E3 × E3 => g z.2) volume := hg'.comp_snd
  have hnorm : AEMeasurable (fun z : E3 × E3 => ‖z.1 - z.2‖) volume :=
    ((measurable_fst.sub measurable_snd).norm).aemeasurable
  -- a.e.-measurability of the five integrands
  have hF : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal ((f z.1 + g z.1) * (f z.2 + g z.2) / ‖z.1 - z.2‖))
      volume :=
    (((hf1.add hg1).mul (hf2.add hg2)).div hnorm).ennreal_ofReal
  have hA : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖))
      volume :=
    ((hf1.mul hf2).div hnorm).ennreal_ofReal
  have hB : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖))
      volume :=
    ((hf1.mul hg2).div hnorm).ennreal_ofReal
  have hC : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal (g z.1 * f z.2 / ‖z.1 - z.2‖))
      volume :=
    ((hg1.mul hf2).div hnorm).ennreal_ofReal
  have hD : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal (g z.1 * g z.2 / ‖z.1 - z.2‖))
      volume :=
    ((hg1.mul hg2).div hnorm).ennreal_ofReal
  -- the pointwise algebraic expansion, split through `ENNReal.ofReal_add`
  have hpt : ∀ z : E3 × E3,
      ENNReal.ofReal ((f z.1 + g z.1) * (f z.2 + g z.2) / ‖z.1 - z.2‖)
        = ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖)
          + ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖)
          + ENNReal.ofReal (g z.1 * f z.2 / ‖z.1 - z.2‖)
          + ENNReal.ofReal (g z.1 * g z.2 / ‖z.1 - z.2‖) := by
    intro z
    have hn : (0 : ℝ) ≤ ‖z.1 - z.2‖ := norm_nonneg _
    have ha : 0 ≤ f z.1 * f z.2 / ‖z.1 - z.2‖ :=
      div_nonneg (mul_nonneg (hf0 z.1) (hf0 z.2)) hn
    have hb : 0 ≤ f z.1 * g z.2 / ‖z.1 - z.2‖ :=
      div_nonneg (mul_nonneg (hf0 z.1) (hg0 z.2)) hn
    have hc : 0 ≤ g z.1 * f z.2 / ‖z.1 - z.2‖ :=
      div_nonneg (mul_nonneg (hg0 z.1) (hf0 z.2)) hn
    have hd : 0 ≤ g z.1 * g z.2 / ‖z.1 - z.2‖ :=
      div_nonneg (mul_nonneg (hg0 z.1) (hg0 z.2)) hn
    have halg : (f z.1 + g z.1) * (f z.2 + g z.2) / ‖z.1 - z.2‖
        = ((f z.1 * f z.2 / ‖z.1 - z.2‖ + f z.1 * g z.2 / ‖z.1 - z.2‖)
          + g z.1 * f z.2 / ‖z.1 - z.2‖) + g z.1 * g z.2 / ‖z.1 - z.2‖ := by
      ring
    rw [halg, ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) hc) hd,
      ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb]
  -- Tonelli: the four iterated integrals as integrals over the product space
  have hL : (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f x + g x) * (f y + g y) / ‖x - y‖))
      = ∫⁻ z : E3 × E3,
          ENNReal.ofReal ((f z.1 + g z.1) * (f z.2 + g z.2) / ‖z.1 - z.2‖) :=
    (lintegral_prod (μ := volume) (ν := volume)
      (fun z : E3 × E3 => ENNReal.ofReal
        ((f z.1 + g z.1) * (f z.2 + g z.2) / ‖z.1 - z.2‖)) hF).symm
  have hE1 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖))
      = ∫⁻ z : E3 × E3, ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖) :=
    (lintegral_prod (μ := volume) (ν := volume)
      (fun z : E3 × E3 => ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖)) hA).symm
  have hE2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * g y / ‖x - y‖))
      = ∫⁻ z : E3 × E3, ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖) :=
    (lintegral_prod (μ := volume) (ν := volume)
      (fun z : E3 × E3 => ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖)) hB).symm
  have hE3 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * f y / ‖x - y‖))
      = ∫⁻ z : E3 × E3, ENNReal.ofReal (g z.1 * f z.2 / ‖z.1 - z.2‖) :=
    (lintegral_prod (μ := volume) (ν := volume)
      (fun z : E3 × E3 => ENNReal.ofReal (g z.1 * f z.2 / ‖z.1 - z.2‖)) hC).symm
  have hE4 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g x * g y / ‖x - y‖))
      = ∫⁻ z : E3 × E3, ENNReal.ofReal (g z.1 * g z.2 / ‖z.1 - z.2‖) :=
    (lintegral_prod (μ := volume) (ν := volume)
      (fun z : E3 × E3 => ENNReal.ofReal (g z.1 * g z.2 / ‖z.1 - z.2‖)) hD).symm
  rw [hL, hE1, hE2, hE3, hE4, lintegral_congr hpt,
    lintegral_add_left' (show AEMeasurable (fun z : E3 × E3 =>
      ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖)
        + ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖)
        + ENNReal.ofReal (g z.1 * f z.2 / ‖z.1 - z.2‖)) volume from (hA.add hB).add hC),
    lintegral_add_left' (show AEMeasurable (fun z : E3 × E3 =>
      ENNReal.ofReal (f z.1 * f z.2 / ‖z.1 - z.2‖)
        + ENNReal.ofReal (f z.1 * g z.2 / ‖z.1 - z.2‖)) volume from hA.add hB),
    lintegral_add_left' hA]

end Work.BoseRowsFS.CoulBilin
