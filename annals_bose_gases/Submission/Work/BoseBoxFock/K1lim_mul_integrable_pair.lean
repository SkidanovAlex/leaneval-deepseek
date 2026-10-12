import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_mul_integrable
import Submission.Work.BoseBoxFock.K1lim_mul_integrable_slot
import Submission.Work.BoseBoxFock.PairGc21Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_mul_integrable_pair`

The limit pair kernel `K1lim ℓ W` (`pinQLimDefs`) read at **two** configuration slots
`x p.1`, `x p.2` of an `n`-particle configuration `x : Xn n`, against a bounded,
a.e. strongly measurable kernel `F` supported in the `n`-particle box `boxPow n ℓ`:

    `x ↦ K1lim ℓ W (x p.1) (x p.2) * F x`  is `L¹` on `Xn n = (ℝ³)ⁿ`

with the weight `W` only assumed **integrable**.

## Route

*Measurability.*  The uncurried kernel is a.e. strongly measurable for an integrable weight
(`aesm_uncurry_K1lim_of_integrable`), and it is invariant under an a.e. change of the weight
(`K1lim_ae_congr'`).  The pull-back along `x ↦ (x p.1, x p.2)` is handled by the
`QuasiMeasurePreserving` of that map (`quasiMeasurePreserving_eval_pair_fst` below), which is
obtained from the measure preserving equivalence
`insEquiv p hp : ((ℝ³ × ℝ³) × Fib) ≃ᵐ Xn n` of `PairGc21Aux`: the pair-evaluation map is
`Prod.fst ∘ insEquiv.symm`, a composition of the (quasi-measure-preserving) projection of a
product with a measure preserving equivalence.

*Finiteness.*  `F` is bounded by `C` and supported in `boxPow n ℓ`, so

    `∫⁻ x, ‖K1lim ℓ W (x p.1) (x p.2) · F x‖ₑ ≤ ofReal (max C 0)
        · ∫⁻ x, 1_{boxPow n ℓ}(x) · ‖K1lim ℓ W (x p.1) (x p.2)‖ₑ`,

and the box-restricted integral of the kernel is finite (`lintegral_boxPow_K1lim_lt_top` below):
rewriting `boxPow n ℓ = abox n ℓ` and using the change of variables of `PairGc21Aux`
(`lintegral_abox_eq_lintegral_triBox`), the integral over the `n`-particle box becomes an integral
over the **triple box** `(boxL ℓ × boxL ℓ) × boxPiSet ℓ`, whose Fubini expansion
(`lintegral_pair_box_eq` below) is the *pair box* integral
`∫⁻ q, 1_{boxL} q.1 · 1_{boxL} q.2 · ‖K1lim ℓ W q.1 q.2‖ₑ` times the finite volume of the
remaining-coordinates box.  The weight is then replaced by a measurable representative, so that
the already proved `K1lim_pair_box_lt_top` applies.

(Every ingredient is proved here or in the imported modules; the proof does not use
`lintegral_boxPow_eval_pair`.)
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "bxL" => Work.BoseK15.corpusBox.boxL

set_option maxHeartbeats 4000000

/-! ## Auxiliary lemmas -/

/-- `boxPow` is the corpus box `abox` (for positive side). -/
lemma boxPow_eq_abox' (N : ℕ) {l : ℝ} (hl : 0 < l) :
    Work.MB.boxPow N l = Submission.BoseGases.abox N l := by
  rw [Work.MB.boxPow, Submission.BoseGases.abox_eq_pi_acube]
  exact Set.pi_congr rfl fun i _ => corpusBox_boxL_eq_acube hl

/-- The indicator of a product set applied to a pair `q` is the product of the two indicators. -/
lemma prod_indicator_eq (S T : Set E3) (f : E3 → E3 → ENNReal) (q : E3 × E3) :
    (S ×ˢ T).indicator (fun q => f q.1 q.2) q
      = S.indicator (fun _ => (1 : ENNReal)) q.1 * T.indicator (fun _ => (1 : ENNReal)) q.2
          * f q.1 q.2 := by
  by_cases h1 : q.1 ∈ S <;> by_cases h2 : q.2 ∈ T <;>
    simp [Set.mem_prod, h1, h2]

/-- Pulling a constant out of a set integral (the `≠ ⊤` hypothesis avoids any measurability
assumption). -/
lemma setLIntegral_mul_const_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → ENNReal) {c : ENNReal} (hc : c ≠ ⊤) :
    (∫⁻ a in s, f a * c ∂μ) = (∫⁻ a in s, f a ∂μ) * c := by
  have hf : ∀ a, s.indicator (fun a => f a * c) a = s.indicator f a * c := by
    intro a
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]
  calc (∫⁻ a in s, f a * c ∂μ) = ∫⁻ a, s.indicator (fun a => f a * c) a ∂μ :=
        (lintegral_indicator hs _).symm
    _ = ∫⁻ a, s.indicator f a * c ∂μ := lintegral_congr hf
    _ = (∫⁻ a, s.indicator f a ∂μ) * c := lintegral_mul_const' c _ hc
    _ = (∫⁻ a in s, f a ∂μ) * c := by rw [lintegral_indicator hs f]

/-- **Fubini for an integrand which only sees the two kernel slots.**  The `ℝ≥0∞`-integral over the
`n`-particle box of a function of the two coordinates `p.1`, `p.2` is the volume of the box of the
remaining coordinates times the integral over the two-particle box. -/
lemma lintegral_pair_box_eq {N : ℕ} {l : ℝ} (hl : 0 < l) (p : Fin N × Fin N) (hp : p.1 ≠ p.2)
    {h : E3 → E3 → ENNReal} (hh : Measurable (Function.uncurry h)) :
    (∫⁻ x in Submission.BoseGases.abox N l, h (x p.1) (x p.2))
      = MeasureTheory.volume (boxPiSet {k : Fin N // k ≠ p.1 ∧ k ≠ p.2} l)
        * ∫⁻ q : E3 × E3, (bxL l).indicator (fun _ => 1) q.1
            * (bxL l).indicator (fun _ => 1) q.2 * h q.1 q.2 := by
  set ι : Type := {k : Fin N // k ≠ p.1 ∧ k ≠ p.2} with hιdef
  have hL : MeasurableSet (bxL l) := Work.BoseB4.BoxData.boxL_measurableSet _ l
  have hFmeas : Measurable (fun z : (E3 × E3) × (ι → E3) => h z.1.1 z.1.2) :=
    hh.comp (by fun_prop)
  have hvolne : MeasureTheory.volume (boxPiSet ι l) ≠ ⊤ :=
    (isCompact_boxPiSet (ι := ι) hl).measure_lt_top.ne
  have key : (∫⁻ z in triBox l p, h z.1.1 z.1.2)
      = MeasureTheory.volume (boxPiSet ι l) * ∫⁻ q : E3 × E3, (bxL l).indicator (fun _ => 1) q.1
            * (bxL l).indicator (fun _ => 1) q.2 * h q.1 q.2 := by
    have h1 : (∫⁻ z in triBox l p, h z.1.1 z.1.2)
        = ∫⁻ z in ((bxL l ×ˢ bxL l) ×ˢ boxPiSet ι l), h z.1.1 z.1.2
            ∂((volume : Measure (E3 × E3)).prod (volume : Measure (ι → E3))) := rfl
    rw [h1, MeasureTheory.setLIntegral_prod (μ := (volume : Measure (E3 × E3)))
      (ν := (volume : Measure (ι → E3)))
      (s := bxL l ×ˢ bxL l) (t := boxPiSet ι l)
      (f := fun z => h z.1.1 z.1.2)
      ((hFmeas.aemeasurable.mono_measure Measure.restrict_le_self))]
    rw [show (∫⁻ q in bxL l ×ˢ bxL l, ∫⁻ r in boxPiSet ι l, h q.1 q.2)
        = ∫⁻ q in bxL l ×ˢ bxL l, (h q.1 q.2 * MeasureTheory.volume (boxPiSet ι l)) from
      setLIntegral_congr_fun (hL.prod hL) (fun q _ => setLIntegral_const _ _)]
    rw [setLIntegral_mul_const_eq (hL.prod hL) (fun q : E3 × E3 => h q.1 q.2) hvolne]
    rw [mul_comm]
    congr 1
    rw [← lintegral_indicator (s := bxL l ×ˢ bxL l) (f := fun q : E3 × E3 => h q.1 q.2)
      (hL.prod hL)]
    exact lintegral_congr (fun q => prod_indicator_eq (bxL l) (bxL l) h q)
  calc (∫⁻ x in Submission.BoseGases.abox N l, h (x p.1) (x p.2))
      = ∫⁻ z in triBox l p, h z.1.1 z.1.2 := by
        rw [lintegral_abox_eq_lintegral_triBox hl p hp]
        exact setLIntegral_congr_fun (triBox_measurableSet l p) (fun z _ => by
          simp only [insertCoord2_apply_self, insertCoord2_apply_other hp])
    _ = _ := key

/-- **The pair-evaluation map is quasi-measure-preserving** (it is the projection of the triple
space composed with the measure preserving insertion equivalence `insEquiv`). -/
lemma quasiMeasurePreserving_eval_pair_fst {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    Measure.QuasiMeasurePreserving (fun x : Xn n => (x p.1, x p.2))
      (volume : Measure (Xn n)) (volume : Measure (E3 × E3)) := by
  set ι : Type := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} with hιdef
  have hqmp1 : Measure.QuasiMeasurePreserving (fun z : (E3 × E3) × (ι → E3) => z.1)
      (volume : Measure ((E3 × E3) × (ι → E3))) (volume : Measure (E3 × E3)) :=
    Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (E3 × E3)))
      (ν := (volume : Measure (ι → E3)))
  have hqmp2 : Measure.QuasiMeasurePreserving (insEquiv p hp).symm
      (volume : Measure (Xn n)) (volume : Measure ((E3 × E3) × (ι → E3))) :=
    (insEquiv_measurePreserving p hp).symm.quasiMeasurePreserving
  have hqmp3 := hqmp1.comp hqmp2
  have hpt : ∀ x : Xn n, ((insEquiv p hp).symm x).1 = (x p.1, x p.2) := by
    intro x
    obtain ⟨a, b, x', hz⟩ : ∃ (a b : E3) (x' : ι → E3),
        (insEquiv p hp).symm x = ((a, b), x') := ⟨_, _, _, rfl⟩
    rw [hz]
    have h := (insEquiv p hp).apply_symm_apply x
    rw [hz, insEquiv_apply] at h
    refine Prod.ext ?_ ?_
    · rw [← congrFun h p.1, insertCoord2_apply_self]
    · rw [← congrFun h p.2, insertCoord2_apply_other hp]
  have hg : Measurable (fun x : Xn n => (x p.1, x p.2)) :=
    (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  exact hqmp3.congr hg (Filter.EventuallyEq.of_eq (funext hpt))

/-- The pulled-back kernel is measurable for a measurable weight. -/
lemma measurable_K1lim_pair {n : ℕ} {l : ℝ} {U : E3 → ℝ} (hU : Measurable U)
    (p : Fin n × Fin n) :
    Measurable (fun x : Xn n => K1lim l U (x p.1) (x p.2)) := by
  have hg : Measurable (fun x : Xn n => (x p.1, x p.2)) :=
    (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  exact Measurable.comp (f := fun x : Xn n => (x p.1, x p.2))
    (measurable_uncurry_K1lim (ℓ := l) hU) hg

/-- The pulled-back kernel is a.e. strongly measurable for an integrable weight. -/
lemma aestronglyMeasurable_K1lim_pair {n : ℕ} {l : ℝ} {W : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    AEStronglyMeasurable (fun x : Xn n => K1lim l W (x p.1) (x p.2)) volume := by
  let U : E3 → ℝ := AEStronglyMeasurable.mk W hW.aestronglyMeasurable
  have hUm : Measurable U := (hW.aestronglyMeasurable.stronglyMeasurable_mk).measurable
  have hWU : W =ᵐ[volume] U := hW.aestronglyMeasurable.ae_eq_mk
  have hae : (fun x : Xn n => K1lim l W (x p.1) (x p.2))
      =ᵐ[volume] (fun x : Xn n => K1lim l U (x p.1) (x p.2)) :=
    (quasiMeasurePreserving_eval_pair_fst p hp).ae_eq (K1lim_ae_congr' (ℓ := l) hWU)
  exact (measurable_K1lim_pair hUm p).aestronglyMeasurable.congr hae.symm

/-- **Finiteness of the box-restricted kernel integral.**  For an integrable weight `W` the
`ℝ≥0∞`-integral of `‖K1lim ℓ W (· p.1) (· p.2)‖ₑ` over the `n`-particle box is finite. -/
lemma lintegral_boxPow_K1lim_lt_top {n : ℕ} {l : ℝ} (hl : 0 < l) {W : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    (∫⁻ x : Xn n, (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
      * ‖K1lim l W (x p.1) (x p.2)‖ₑ) < ⊤ := by
  let U : E3 → ℝ := AEStronglyMeasurable.mk W hW.aestronglyMeasurable
  have hUm : Measurable U := (hW.aestronglyMeasurable.stronglyMeasurable_mk).measurable
  have hWU : W =ᵐ[volume] U := hW.aestronglyMeasurable.ae_eq_mk
  have hUfin : ∫⁻ z : E3, ‖(U z : ℂ)‖ₑ < ⊤ := by
    have h1 : ∫⁻ z : E3, ‖(U z : ℂ)‖ₑ = ∫⁻ z : E3, ‖(W z : ℂ)‖ₑ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hWU] with z hz
      simp only [hz]
    have h2 : ∫⁻ z : E3, ‖(W z : ℂ)‖ₑ = ∫⁻ z : E3, ‖(W z : ℝ)‖ₑ := by
      refine lintegral_congr fun z => ?_
      rw [← ofReal_norm, ← ofReal_norm, errBdd_norm_ofReal, Real.norm_eq_abs]
    rw [h1, h2]
    exact hW.hasFiniteIntegral
  have hae : (fun x : Xn n => K1lim l W (x p.1) (x p.2))
      =ᵐ[volume] (fun x : Xn n => K1lim l U (x p.1) (x p.2)) :=
    (quasiMeasurePreserving_eval_pair_fst p hp).ae_eq (K1lim_ae_congr' (ℓ := l) hWU)
  have hhU : Measurable (Function.uncurry (fun a b : E3 => ‖K1lim l U a b‖ₑ)) := by
    have hfun : Function.uncurry (fun a b : E3 => ‖K1lim l U a b‖ₑ)
        = fun q : E3 × E3 => ENNReal.ofReal ‖K1lim l U q.1 q.2‖ := by
      funext q; exact (ofReal_norm (K1lim l U q.1 q.2)).symm
    rw [hfun]
    exact ENNReal.measurable_ofReal.comp ((measurable_uncurry_K1lim (ℓ := l) hUm).norm)
  have h1 : (∫⁻ x : Xn n, (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
      * ‖K1lim l W (x p.1) (x p.2)‖ₑ)
      = ∫⁻ x : Xn n, (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
          * ‖K1lim l U (x p.1) (x p.2)‖ₑ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hx]
  have h2 : (∫⁻ x : Xn n, (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
      * ‖K1lim l U (x p.1) (x p.2)‖ₑ)
      = ∫⁻ x in Submission.BoseGases.abox n l, ‖K1lim l U (x p.1) (x p.2)‖ₑ := by
    rw [boxPow_eq_abox' n hl]
    rw [← lintegral_indicator (s := Submission.BoseGases.abox n l)
      (f := fun x : Xn n => ‖K1lim l U (x p.1) (x p.2)‖ₑ)
      (Submission.BoseGases.abox_measurable n l)]
    exact lintegral_congr (fun x => by
      by_cases hx : x ∈ Submission.BoseGases.abox n l
      · rw [Set.indicator_of_mem hx, one_mul, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, zero_mul, Set.indicator_of_notMem hx])
  rw [h1, h2, lintegral_pair_box_eq hl p hp hhU]
  exact ENNReal.mul_lt_top
    (isCompact_boxPiSet (ι := {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) hl).measure_lt_top
    (K1lim_pair_box_lt_top hl hUm hUfin)

/-! ## The target -/

theorem K1lim_mul_integrable_pair {n : ℕ} {l : ℝ} (hl : 0 < l) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    {F : Work.BoseDict.Xn n → ℂ}
    (hFm : MeasureTheory.AEStronglyMeasurable F MeasureTheory.volume)
    (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFs : Function.support F ⊆ Work.MB.boxPow n l) :
    MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn n => Work.BoseBoxFock.K1lim l W (x p.1) (x p.2) * F x)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)) := by
  refine ⟨(aestronglyMeasurable_K1lim_pair hWi p hp).mul hFm, ?_⟩
  obtain ⟨C, hC⟩ := hFb
  have hbnd : ∀ x : Work.BoseDict.Xn n,
      ‖K1lim l W (x p.1) (x p.2) * F x‖ₑ
      ≤ ENNReal.ofReal (max C 0) * ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
          * ‖K1lim l W (x p.1) (x p.2)‖ₑ) := by
    intro x
    rw [enorm_mul]
    have hFbd : ‖F x‖ₑ ≤ ENNReal.ofReal (max C 0)
        * (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x := by
      by_cases hx : x ∈ Work.MB.boxPow n l
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_trans (hC x) (le_max_left C 0))
      · rw [show F x = 0 from by
            by_contra hne; exact hx (hFs (Function.mem_support.mpr hne)), enorm_zero]
        simp
    calc ‖K1lim l W (x p.1) (x p.2)‖ₑ * ‖F x‖ₑ
        ≤ ‖K1lim l W (x p.1) (x p.2)‖ₑ * (ENNReal.ofReal (max C 0)
            * (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x) :=
          mul_le_mul_of_nonneg_left hFbd (by simp)
      _ = ENNReal.ofReal (max C 0) * ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
            * ‖K1lim l W (x p.1) (x p.2)‖ₑ) := by ring
  calc ∫⁻ x : Work.BoseDict.Xn n, ‖K1lim l W (x p.1) (x p.2) * F x‖ₑ
      ≤ ∫⁻ x : Work.BoseDict.Xn n, ENNReal.ofReal (max C 0) *
          ((Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
            * ‖K1lim l W (x p.1) (x p.2)‖ₑ) := lintegral_mono hbnd
    _ = ENNReal.ofReal (max C 0) * ∫⁻ x : Work.BoseDict.Xn n,
          (Work.MB.boxPow n l).indicator (fun _ => (1 : ENNReal)) x
            * ‖K1lim l W (x p.1) (x p.2)‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_boxPow_K1lim_lt_top hl hWi p hp)

end Work.BoseBoxFock
