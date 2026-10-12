import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.coulomb_pair_integrable`

**The pair (Coulomb) integrability created by the Fourier–Coulomb identity.**  For a real kernel
`W` on `ℝ³` (`ℝ³ = EuclideanSpace ℝ (Fin 3)`) which is

* `L¹` (`MeasureTheory.Integrable W`),
* nonnegative almost everywhere,
* even (`W (-x) = W x`),

and whose `p`-convention Fourier transform `Ŵ = Work.BoseFixR.chat W` has finite Coulomb energy
in momentum space, `∫ ‖Ŵ(p)²/(2‖p‖²)‖ < ∞` (`hint`), the position-space pair kernel

  `(x,y) ↦ W x · W y / ‖x − y‖`

is integrable on the product measure `volume × volume`.

This is the *forward* direction of the classical Newtonian-energy identity

  `∫⁻ p, ofReal (Ŵ(p)²/‖p‖²) = ofReal (2π²) · ∫⁻ x, ∫⁻ y, ofReal (W x · W y/‖x − y‖)`

(`Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq`, proved in the corpus for pointwise nonnegative
even integrable `W`): finiteness of the left-hand side forces `≠ ⊤` of the right-hand side, which
is exactly `∫⁻ z ∂(volume×volume), ofReal ‖W z.1 · W z.2/‖z.1 − z.2‖‖ < ⊤`, i.e. integrability.

## Route

* `lintegral_coulomb_congr_ae` — the position-space double `∫⁻` depends on the kernel only through
  its a.e. class (the two slots are peeled off by `lintegral_congr_ae`).
* `lintegral_chat_sq_div_eq_ae` — the `∫⁻` Fourier–Coulomb identity for an **a.e.** nonnegative
  even integrable `W` (the corpus lemma is applied to the pointwise nonnegative representative
  `max W 0`, and `Work.BoseB7AK.C3Q.chat_congr_ae` pushes the identity back to `W`).
* `hint` gives `∫⁻ p, ofReal (Ŵ(p)²/(2‖p‖²)) < ⊤` via `hasFiniteIntegral_iff_ofReal`; un-halving
  the denominator (`ofReal (a/2)`, monotonicity of the `∫⁻`) gives the same with `‖p‖²`, and
  `ENNReal.mul_lt_top_iff` extracts the finiteness of the position-space double `∫⁻`.
* Tonelli (`MeasureTheory.lintegral_prod`) turns the double `∫⁻` of the pointwise nonnegative
  representative into the product-measure `∫⁻`, `hasFiniteIntegral_iff_ofReal` into
  `HasFiniteIntegral`, and `Integrable.congr` transfers back to `W` along the a.e. equality
  `max W 0 =ᵐ W` (pushed through both coordinates of the product).

The statement is *not* symmetric in its hypotheses: the `1/2` in `hint` keeps the constant
`2π²` of the corpus identity, and all a.e. hypotheses enter only through the representative
`max W 0` — `W` itself need not be nonnegative pointwise.

## Use by the caller

The skeleton `Submission.Work.BoseRowsFS.honest_lattice_W1sq_le_uniform` carries its own
`Work.BoseRowsFS.coulomb_pair_integrable` (with a `sorry`) in the *same* namespace: that
placeholder must be **deleted** and this module imported instead, otherwise the two declarations
clash.  The two helpers here (`lintegral_coulomb_congr_ae`, `lintegral_chat_sq_div_eq_ae`) are
reusable on their own: the second is the `∫⁻` Fourier–Coulomb identity for a merely
a.e. nonnegative even `L¹` kernel.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseRowsFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The position-space Coulomb double `∫⁻` only sees the a.e. class of the kernel.**
If `U =ᵐ V` then `∫⁻ x, ∫⁻ y, ofReal (U x * U y / ‖x − y‖)` is unchanged: for a.e. `x` the
`y`-slice agrees a.e., and then the outer `∫⁻` agrees by the a.e. equality of the two slices. -/
lemma lintegral_coulomb_congr_ae {U V : E3 → ℝ} (h : U =ᵐ[volume] V) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (U x * U y / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V y / ‖x - y‖)) := by
  calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (U x * U y / ‖x - y‖))
      = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (U x * V y / ‖x - y‖)) := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards with x
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [h] with y hy
        rw [hy]
    _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (V x * V y / ‖x - y‖)) := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [h] with x hx
        rw [hx]

/-- **The `∫⁻` Fourier–Coulomb (Newtonian energy) identity with only a.e. nonnegativity.**

`Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq` requires `0 ≤ W` *pointwise*.  Replacing `W` by the
pointwise nonnegative representative `W⁺ = max W 0` (even, integrable, a.e. equal to `W`) and
using that both `chat` (`Work.BoseB7AK.C3Q.chat_congr_ae`) and the position-space double `∫⁻`
(`lintegral_coulomb_congr_ae` above) see only the a.e. class removes that hypothesis. -/
lemma lintegral_chat_sq_div_eq_ae {W : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x) :
    (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal (2 * Real.pi ^ 2)
        * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
  set Wp : E3 → ℝ := fun x => max (W x) 0 with hWp
  have hWp0 : ∀ x, 0 ≤ Wp x := fun x => by rw [hWp]; exact le_max_right _ _
  have hWpe : ∀ x, Wp (-x) = Wp x := fun x => by rw [hWp]; simp only [hWe x]
  have hae : Wp =ᵐ[volume] W :=
    hW0.mono (fun x hx => by rw [hWp]; exact max_eq_left hx)
  have hWpI : MeasureTheory.Integrable Wp := hW.congr hae.symm
  calc (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2))
      = (∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat Wp p) ^ 2 / ‖p‖ ^ 2)) := by
        apply MeasureTheory.lintegral_congr
        intro p
        rw [Work.BoseB7AK.C3Q.chat_congr_ae hae p]
    _ = ENNReal.ofReal (2 * Real.pi ^ 2)
          * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖) :=
        Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq hWpI hWp0 hWpe
    _ = ENNReal.ofReal (2 * Real.pi ^ 2)
          * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
        rw [lintegral_coulomb_congr_ae hae]

theorem coulomb_pair_integrable {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x)
    (hint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W p.1 * W p.2 / ‖p.1 - p.2‖) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  -- ## 1. `hint` turns into finiteness of the momentum-space `∫⁻`
  have hnn : 0 ≤ᵐ[volume] (fun p : E3 => Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2)) :=
    Filter.Eventually.of_forall (fun p => div_nonneg (sq_nonneg _) (by positivity))
  have hfin_half :
      (∫⁻ p, ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2))) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal hnn).mp hint.2
  -- ## 2. the same with the denominator `‖p‖ ^ 2` (the `1/2` is pulled out)
  have hfin_mom : (∫⁻ p, ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / ‖p‖ ^ 2)) < ⊤ := by
    have hpt : ∀ p : E3, ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / ‖p‖ ^ 2)
        = ENNReal.ofReal 2
          * ENNReal.ofReal (Work.BoseFixR.chat W p ^ 2 / (2 * ‖p‖ ^ 2)) := by
      intro p
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rcases eq_or_ne (‖p‖ ^ 2) 0 with h | h
      · rw [h]; simp
      · field_simp
    rw [MeasureTheory.lintegral_congr hpt,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_half
  -- ## 3. the Coulomb identity converts this into finiteness of the x-space double `∫⁻`
  have hYfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖)) < ⊤ := by
    have h := hfin_mom
    rw [lintegral_chat_sq_div_eq_ae hW hW0 hWe] at h
    rcases ENNReal.mul_lt_top_iff.mp h with ⟨-, hb⟩ | ha0 | hb0
    · exact hb
    · exact absurd ha0 (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
    · rw [hb0]; exact ENNReal.zero_lt_top
  -- ## 4. the pointwise nonnegative representative `W⁺ = max W 0`
  set Wp : E3 → ℝ := fun x => max (W x) 0 with hWp
  have hWp0 : ∀ x, 0 ≤ Wp x := fun x => by rw [hWp]; exact le_max_right _ _
  have hae : Wp =ᵐ[volume] W := hW0.mono (fun x hx => by rw [hWp]; exact max_eq_left hx)
  have hWpI : MeasureTheory.Integrable Wp := hW.congr hae.symm
  have hYpfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖)) < ⊤ := by
    rw [lintegral_coulomb_congr_ae hae]; exact hYfin
  -- ## 5. Tonelli: the product-measure `∫⁻` of the pair kernel `W⁺ W⁺/‖·−·‖` is finite
  have hWpm : AEMeasurable Wp volume := hWpI.1.aemeasurable
  have hAEM' : AEMeasurable
      (fun z : E3 × E3 => Wp z.1 * Wp z.2 / ‖z.1 - z.2‖) (volume.prod volume) :=
    ((hWpm.comp_fst).mul (hWpm.comp_snd)).div
      (((measurable_fst.sub measurable_snd).norm).aemeasurable)
  have hAEM : AEMeasurable
      (fun z : E3 × E3 => ENNReal.ofReal (Wp z.1 * Wp z.2 / ‖z.1 - z.2‖))
      (volume.prod volume) := hAEM'.ennreal_ofReal
  have hprod1 : (∫⁻ z : E3 × E3, ENNReal.ofReal (Wp z.1 * Wp z.2 / ‖z.1 - z.2‖)
        ∂(volume.prod volume))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Wp x * Wp y / ‖x - y‖) :=
    MeasureTheory.lintegral_prod _ hAEM
  have hprod_lt : (∫⁻ z : E3 × E3, ENNReal.ofReal (Wp z.1 * Wp z.2 / ‖z.1 - z.2‖)
        ∂(volume.prod volume)) < ⊤ := hprod1 ▸ hYpfin
  have hHFp : MeasureTheory.HasFiniteIntegral
      (fun z : E3 × E3 => Wp z.1 * Wp z.2 / ‖z.1 - z.2‖) (volume.prod volume) :=
    (MeasureTheory.hasFiniteIntegral_iff_ofReal (f := fun z : E3 × E3 =>
        Wp z.1 * Wp z.2 / ‖z.1 - z.2‖) (μ := volume.prod volume)
      (Filter.Eventually.of_forall (fun z =>
        div_nonneg (mul_nonneg (hWp0 z.1) (hWp0 z.2)) (norm_nonneg _)))).mpr hprod_lt
  have hfp_int : MeasureTheory.Integrable
      (fun z : E3 × E3 => Wp z.1 * Wp z.2 / ‖z.1 - z.2‖) (volume.prod volume) :=
    ⟨hAEM'.aestronglyMeasurable, hHFp⟩
  -- ## 6. transfer to `W` itself along the a.e. equality `max W 0 =ᵐ W`
  have hpae : (fun z : E3 × E3 => Wp z.1 * Wp z.2 / ‖z.1 - z.2‖)
      =ᵐ[volume.prod volume] (fun z : E3 × E3 => W z.1 * W z.2 / ‖z.1 - z.2‖) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hW0,
      Measure.quasiMeasurePreserving_snd.ae hW0] with z hz1 hz2
    rw [show Wp z.1 = W z.1 from by rw [hWp]; exact max_eq_left hz1,
      show Wp z.2 = W z.2 from by rw [hWp]; exact max_eq_left hz2]
  exact hfp_int.congr hpae

end Work.BoseRowsFS
