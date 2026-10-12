import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.pairKernel_latFin9_lintegral_lt_top`

**The Coulomb pair kernel with the finite lattice window `latFin9` is `lintegral`-finite.**

Let `W : ℝ³ → ℝ` be integrable, nonnegative a.e., with **finite Coulomb self-energy**

    hpot :  ∀ᵐ x, ∫⁻ y, ofReal (W y * ‖x - y‖⁻¹) ≤ ofReal C       (a.e. `x`).

Then the double `lintegral` of `W ⊗ W` against the *finite* sum of translation invariant
Coulomb kernels

    q ↦ ∑_{p ∈ latFin9} ‖q.1 - q.2 - lat ℓ p‖⁻¹

is finite:

    ∫⁻ q, ofReal (W q.1 * W q.2 * ∑_{p ∈ latFin9} ‖q.1 - q.2 - lat ℓ p‖⁻¹) < ⊤.

The proof is the standard "one Coulomb potential per lattice translation" argument:

* the finite sum is distributed over the `ofReal` (`ofReal` commutes with finite sums of
  nonnegative terms) and `lintegral_finsetSum'` splits the integral into the finitely many
  terms indexed by `p ∈ latFin9`;
* each single term is evaluated by Tonelli (`lintegral_prod_symm`) in the first coordinate;
  the a.e. hypothesis `hpot`, transported to the shifted point `x + lat ℓ p` by the
  translation invariance of Lebesgue measure (`measurePreserving_add_right`), bounds the
  inner integral by `ofReal C`;
* the remaining integral `∫⁻ y, ofReal (W y) * ofReal C = ofReal C * ofReal (∫ y, W y)`
  is finite (`ofReal` of a real number is never `⊤`).

Nothing here uses the positivity of `ℓ` or of `C`; the hypotheses are kept because that is
how the requester states it.  In particular **no** domination of `1/latDistL` by the window
sum is used: the statement is a pure finiteness statement about the finite sum of Coulomb
kernels.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixR.FarLat

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- **One Coulomb term.**  For any shift `c`, if the a.e. Coulomb-potential bound holds at
the point `y + c`, then the `lintegral` of `W ⊗ W` against the single translation invariant
kernel `‖· - · - c‖⁻¹` is at most `ofReal C * ofReal (∫ W)`.

Proof: rewrite `W q.1 * W q.2 * ‖q.1 - (q.2 + c)‖⁻¹` as
`ofReal (W q.1) * ofReal (W q.2 * ‖…)` (on the a.e. set where `W ≥ 0`), apply Tonelli to
integrate over the first coordinate first, pull the constant `ofReal (W y)` out of the inner
integral, use the hypothesis at `y + c`, and finally identify
`∫⁻ y, ofReal (W y) = ofReal (∫ y, W y)`. -/
private lemma pairTerm_le {C : ℝ} {W : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W) {c : E3}
    (hc : ∀ᵐ y : E3,
      (∫⁻ x : E3, ENNReal.ofReal (W x * ‖x - (y + c)‖⁻¹)) ≤ ENNReal.ofReal C) :
    (∫⁻ q : E3 × E3, ENNReal.ofReal (W q.1 * W q.2 * ‖q.1 - (q.2 + c)‖⁻¹))
      ≤ ENNReal.ofReal C * ENNReal.ofReal (∫ y : E3, W y) := by
  classical
  have hm1 : AEMeasurable (fun q : E3 × E3 => W q.1) volume :=
    hW.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hm2 : AEMeasurable (fun q : E3 × E3 => W q.2) volume :=
    hW.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmk : Measurable (fun q : E3 × E3 => (‖q.1 - (q.2 + c)‖)⁻¹) :=
    ((measurable_fst.sub (measurable_snd.add_const c))).norm.inv
  have hnn1 : ∀ᵐ q : E3 × E3, 0 ≤ W q.1 :=
    Measure.quasiMeasurePreserving_fst.ae hWnn
  -- Split the product `ofReal (W q.1 * W q.2 * r)` on the a.e. set `0 ≤ W q.1`.
  have hsplit : (fun q : E3 × E3 => ENNReal.ofReal (W q.1 * W q.2 * ‖q.1 - (q.2 + c)‖⁻¹))
      =ᵐ[volume] (fun q : E3 × E3 =>
        ENNReal.ofReal (W q.1) * ENNReal.ofReal (W q.2 * ‖q.1 - (q.2 + c)‖⁻¹)) := by
    filter_upwards [hnn1] with q hq
    rw [mul_assoc, ENNReal.ofReal_mul hq]
  rw [lintegral_congr_ae hsplit]
  -- Tonelli, integrating the *first* coordinate first.
  have hton :
      (∫⁻ q : E3 × E3, ENNReal.ofReal (W q.1) * ENNReal.ofReal (W q.2 * ‖q.1 - (q.2 + c)‖⁻¹))
        = ∫⁻ y : E3, ∫⁻ x : E3,
            ENNReal.ofReal (W x) * ENNReal.ofReal (W y * ‖x - (y + c)‖⁻¹) := by
    rw [show (volume : Measure (E3 × E3)) = volume.prod volume from rfl]
    exact lintegral_prod_symm
      (f := fun z : E3 × E3 =>
        ENNReal.ofReal (W z.1) * ENNReal.ofReal (W z.2 * ‖z.1 - (z.2 + c)‖⁻¹))
      (hm1.ennreal_ofReal.mul ((hm2.mul hmk.aemeasurable).ennreal_ofReal))
  rw [hton]
  -- The inner integral, for a.e. `y`.
  have hinner : ∀ᵐ y : E3,
      (∫⁻ x : E3, ENNReal.ofReal (W x) * ENNReal.ofReal (W y * ‖x - (y + c)‖⁻¹))
        ≤ ENNReal.ofReal (W y) * ENNReal.ofReal C := by
    filter_upwards [hWnn, hc] with y hy hyc
    have hmx : AEMeasurable
        (fun x : E3 => ENNReal.ofReal (W x) * ENNReal.ofReal (‖x - (y + c)‖⁻¹)) volume :=
      (hW.aemeasurable.ennreal_ofReal).mul
        ((((measurable_id.sub (measurable_const (a := y + c)))).norm.inv).ennreal_ofReal).aemeasurable
    have hstep1 : (fun x : E3 => ENNReal.ofReal (W x) * ENNReal.ofReal (W y * ‖x - (y + c)‖⁻¹))
        = fun x : E3 => ENNReal.ofReal (W y) *
            (ENNReal.ofReal (W x) * ENNReal.ofReal (‖x - (y + c)‖⁻¹)) := by
      funext x
      rw [ENNReal.ofReal_mul hy, mul_left_comm]
    rw [hstep1, lintegral_const_mul'' _ hmx]
    have hstep2 : (∫⁻ x : E3, ENNReal.ofReal (W x) * ENNReal.ofReal (‖x - (y + c)‖⁻¹))
        = ∫⁻ x : E3, ENNReal.ofReal (W x * ‖x - (y + c)‖⁻¹) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hWnn] with x hx
      exact (ENNReal.ofReal_mul hx).symm
    rw [hstep2]
    exact mul_le_mul_right hyc _
  refine le_trans (lintegral_mono_ae hinner) ?_
  have hfin : (∫⁻ y : E3, ENNReal.ofReal (W y) * ENNReal.ofReal C)
      = ENNReal.ofReal C * ENNReal.ofReal (∫ y : E3, W y) := by
    rw [lintegral_mul_const'' (ENNReal.ofReal C) (hW.aemeasurable.ennreal_ofReal),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hW hWnn]
    exact mul_comm _ _
  exact le_of_eq hfin

-- imports used below: Submission.Work.BoseFixR.FarLatDefs
theorem pairKernel_latFin9_lintegral_lt_top {ℓ C : ℝ} (hℓ : 0 < ℓ) (hC : 0 ≤ C)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hpot : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
      (∫⁻ y : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W y * ‖x - y‖⁻¹)) ≤ ENNReal.ofReal C) :
    (∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W q.1 * W q.2
          * (∑ p ∈ Work.BoseFixR.latFin9, (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))) < ⊤ := by
  classical
  have hm1 : AEMeasurable (fun q : E3 × E3 => W q.1) volume :=
    hW.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hm2 : AEMeasurable (fun q : E3 × E3 => W q.2) volume :=
    hW.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  -- Distribute the finite sum over `ofReal`.
  have hexp : (fun q : E3 × E3 => ENNReal.ofReal (W q.1 * W q.2
        * (∑ p ∈ Work.BoseFixR.latFin9, (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹)))
      = fun q : E3 × E3 => ∑ p ∈ Work.BoseFixR.latFin9,
          ENNReal.ofReal (W q.1 * W q.2 * (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹) := by
    funext q
    have hnn : ∀ p ∈ Work.BoseFixR.latFin9,
        (0 : ℝ) ≤ (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹ :=
      fun p _ => inv_nonneg.mpr (norm_nonneg _)
    rw [ENNReal.ofReal_mul' (Finset.sum_nonneg hnn), ENNReal.ofReal_sum_of_nonneg hnn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    exact (ENNReal.ofReal_mul' (hnn p hp)).symm
  have hmeasp : ∀ p ∈ Work.BoseFixR.latFin9,
      AEMeasurable (fun q : E3 × E3 =>
        ENNReal.ofReal (W q.1 * W q.2 * (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹)) volume := by
    intro p _
    refine ((hm1.mul hm2).mul (((measurable_fst.sub measurable_snd).sub
      (measurable_const (a := Work.BoseFixR.lat ℓ p))).norm.inv).aemeasurable).ennreal_ofReal
  -- Each single lattice translation is bounded by the a.e. Coulomb bound.
  have hterm : ∀ p ∈ Work.BoseFixR.latFin9,
      (∫⁻ q : E3 × E3,
          ENNReal.ofReal (W q.1 * W q.2 * (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))
        ≤ ENNReal.ofReal C * ENNReal.ofReal (∫ y : E3, W y) := by
    intro p _
    -- Transport `hpot` to the shifted point `y + lat ℓ p`.
    have hshift : ∀ᵐ y : E3,
        (∫⁻ x : E3, ENNReal.ofReal (W x * ‖x - (y + Work.BoseFixR.lat ℓ p)‖⁻¹))
          ≤ ENNReal.ofReal C := by
      refine ae_of_ae_map
        (p := fun z : E3 => (∫⁻ x : E3, ENNReal.ofReal (W x * ‖x - z‖⁻¹)) ≤ ENNReal.ofReal C)
        (μ := (volume : Measure E3))
        (f := fun y : E3 => y + Work.BoseFixR.lat ℓ p)
        (measurable_add_const _).aemeasurable ?_
      rw [(measurePreserving_add_right volume (Work.BoseFixR.lat ℓ p)).map_eq]
      filter_upwards [hpot] with a ha
      rw [show (∫⁻ x : E3, ENNReal.ofReal (W x * ‖x - a‖⁻¹))
          = ∫⁻ y : E3, ENNReal.ofReal (W y * ‖a - y‖⁻¹) from by
        refine lintegral_congr (fun x => ?_)
        rw [norm_sub_rev]]
      exact ha
    calc (∫⁻ q : E3 × E3,
            ENNReal.ofReal (W q.1 * W q.2 * (‖q.1 - q.2 - Work.BoseFixR.lat ℓ p‖)⁻¹))
        = ∫⁻ q : E3 × E3, ENNReal.ofReal (W q.1 * W q.2
            * ‖q.1 - (q.2 + Work.BoseFixR.lat ℓ p)‖⁻¹) := by
          refine lintegral_congr (fun q => ?_)
          rw [sub_sub]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (∫ y : E3, W y) := pairTerm_le hW hWnn hshift
  rw [hexp, lintegral_finsetSum' _ hmeasp]
  refine ENNReal.sum_lt_top.mpr (fun p hp => ?_)
  exact lt_of_le_of_lt (hterm p hp)
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top))

end Work.BoseFixR.FarLat
