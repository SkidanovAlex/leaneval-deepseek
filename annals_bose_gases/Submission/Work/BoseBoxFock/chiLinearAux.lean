import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.chiRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiLinearAux` — the measurable-bounded slot toolbox

The χ-row slot forms of `Submission/Work/BoseBoxFock/chiRowDefs.lean` (`pairSlot`, `chiA`,
`muLine`) are linear in the *weight* `w : ℝ³ → ℝ`.  The weights that occur in the χ-row
assembly are of the form `χ_Λ² − 1 − Re(chiTail)`: bounded and measurable, but **not**
continuous.  The corpus's slot toolbox (`Submission/Q0Sector.lean`, `Submission/Q0Value.lean`)
only bounds/measures `aP ℓ i F` for *continuous* `F`, and provides self-adjointness only for
continuous test functions.  This module supplies the missing measurable-bounded variants,
which is exactly what the integral linearity needs (a.e. integrability witnesses for
`integral_sub`).

Contents:

* `aP_abs_le_of_boundOn` — a slot mean of a measurable function bounded by `M` **on the box**
  is bounded by `M` on the box (the corpus's `aP_abs_le` needs `Continuous`);
* `aP_aestronglyMeasurable_of_measurable` — the slot mean of a measurable function is a.e.
  strongly measurable on the box (the corpus's `aP_aestronglyMeasurable` needs `Continuous`);
* `integrableOn_update_of_bounded` — integrability of the peeled fibre `y ↦ F (update x i y)`
  over the cube;
* `aP_sub_at`, `aP_sub`, `aP_sub_of_boundOn` — additivity of `aP ℓ i` in its argument, in the
  local (box) form used inside integrals;
* `integrableOn_cont_slot_bounded` — the product `A x * u (x i) * B x` of two continuous
  factors and a bounded measurable slot factor `u` is integrable on the centred box;
* `aQ_cont`, `aQ_pair_cont` — continuity of the `Q`-slot factors.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **`aP` does not increase a bound that holds on the box.**  If `F` is measurable and
`|F z| ≤ M` for `z` in the `N`-particle centred box, then the same bound holds for the slot
mean `aP ℓ i F` on the box.  (The corpus's `aP_abs_le` assumes `F` continuous.) -/
lemma aP_abs_le_of_boundOn {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {F : X N → ℝ}
    (hFm : Measurable F) {M : ℝ} (hFb : ∀ z ∈ abox N ℓ, |F z| ≤ M) :
    ∀ x ∈ abox N ℓ, |aP ℓ i F x| ≤ M := by
  intro x hx
  have hbdd : ∀ᵐ y ∂(volume.restrict (acube ℓ)), |F (Function.update x i y)| ≤ M := by
    rw [ae_restrict_iff' (acube_measurable ℓ)]
    exact ae_of_all volume (fun y hy => hFb _ (update_mem_abox i hx hy))
  have hint : IntegrableOn (fun y : Sp => F (Function.update x i y)) (acube ℓ) volume := by
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_ M ?_
    · exact ((hFm.comp (measurable_update x)).aestronglyMeasurable).restrict
    · filter_upwards [hbdd] with y hy
      rwa [Real.norm_eq_abs]
  have habs : |(∫ y in acube ℓ, F (Function.update x i y))| ≤ M * ℓ ^ 3 := by
    calc |(∫ y in acube ℓ, F (Function.update x i y))|
        ≤ ∫ y in acube ℓ, |F (Function.update x i y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y in acube ℓ, M := by
            refine integral_mono_ae hint.abs ?_ ?_
            · exact (integrableOn_const (μ := volume) (s := acube ℓ) (C := M)
                (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp))
            · filter_upwards [hbdd] with y hy
              exact hy
      _ = M * ℓ ^ 3 := Submission.BoseGases.integral_const_acube ℓ hℓ M
  have hpos : 0 ≤ (1 : ℝ) / ℓ ^ 3 := by positivity
  unfold aP
  rw [abs_mul, abs_of_nonneg hpos]
  calc (1 / ℓ ^ 3) * |∫ y in acube ℓ, F (Function.update x i y)|
      ≤ (1 / ℓ ^ 3) * (M * ℓ ^ 3) := mul_le_mul_of_nonneg_left habs hpos
    _ = M := by field_simp

/-- **A slot mean of a measurable function is a.e. strongly measurable on the box.**  (The
corpus's `aP_aestronglyMeasurable` assumes `F` continuous; the proof only uses the
measurability of the peeled fibre, hence works for measurable `F`.) -/
lemma aP_aestronglyMeasurable_of_measurable {N : ℕ} {ℓ : ℝ} (i : Fin N)
    {F : X N → ℝ} (hFm : Measurable F) :
    AEStronglyMeasurable (aP ℓ i F) (volume.restrict (abox N ℓ)) := by
  have hfc : AEStronglyMeasurable
      (fun p : X N × Sp => F (Function.update p.1 i p.2))
      ((volume : Measure (X N)).prod ((volume : Measure Sp).restrict (acube ℓ))) :=
    (hFm.comp (by fun_prop : Measurable
      (fun p : X N × Sp => Function.update p.1 i p.2))).aestronglyMeasurable
  haveI : SigmaFinite ((volume : Measure Sp).restrict (acube ℓ)) := by infer_instance
  have hf : AEStronglyMeasurable
      (fun x : X N => ∫ y : Sp, F (Function.update x i y)
        ∂((volume : Measure Sp).restrict (acube ℓ))) (volume : Measure (X N)) :=
    hfc.integral_prod_right'
  change AEStronglyMeasurable (fun x : X N => (1 / ℓ ^ 3) *
    (∫ y : Sp in acube ℓ, F (Function.update x i y))) (volume.restrict (abox N ℓ))
  exact (hf.const_mul (1 / ℓ ^ 3)).restrict

/-- **The peeled fibre is integrable.**  If `F` is measurable and bounded by `M` on the box,
then for every box point `x` the fibre `y ↦ F (Function.update x i y)` is integrable over the
centred cube. -/
lemma integrableOn_update_of_bounded {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {F : X N → ℝ}
    (hFm : Measurable F) {M : ℝ} (hFb : ∀ z ∈ abox N ℓ, |F z| ≤ M) {x : X N}
    (hx : x ∈ abox N ℓ) :
    IntegrableOn (fun y : Sp => F (Function.update x i y)) (acube ℓ) volume := by
  refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) ?_ M ?_
  · exact ((hFm.comp (measurable_update x)).aestronglyMeasurable).restrict
  · rw [ae_restrict_iff' (acube_measurable ℓ)]
    exact ae_of_all volume (fun y hy => by
      rw [Real.norm_eq_abs]
      exact hFb _ (update_mem_abox i hx hy))

/-- **Local additivity of the slot mean.**  At a single configuration `x`, the slot mean is
additive as soon as the two peeled fibres are integrable over the cube. -/
lemma aP_sub_at {N : ℕ} {ℓ : ℝ} (i : Fin N) {F G : X N → ℝ} (x : X N)
    (hF : IntegrableOn (fun y : Sp => F (Function.update x i y)) (acube ℓ) volume)
    (hG : IntegrableOn (fun y : Sp => G (Function.update x i y)) (acube ℓ) volume) :
    aP ℓ i (fun y => F y - G y) x = aP ℓ i F x - aP ℓ i G x := by
  have h1 : (∫ y in acube ℓ, (fun y' : X N => F y' - G y') (Function.update x i y))
      = ∫ y in acube ℓ, (F (Function.update x i y) - G (Function.update x i y)) := rfl
  simp only [aP]
  rw [h1, integral_sub hF hG]
  ring

/-- Additivity of the slot mean, global in `x`. -/
lemma aP_sub {N : ℕ} {ℓ : ℝ} (i : Fin N) {F G : X N → ℝ}
    (hF : ∀ x, IntegrableOn (fun y : Sp => F (Function.update x i y)) (acube ℓ) volume)
    (hG : ∀ x, IntegrableOn (fun y : Sp => G (Function.update x i y)) (acube ℓ) volume)
    (x : X N) : aP ℓ i (fun y => F y - G y) x = aP ℓ i F x - aP ℓ i G x :=
  aP_sub_at i x (hF x) (hG x)

/-- **Additivity of the slot mean, measurable-bounded form** (the case that occurs in the
χ-row): both functions only need to be measurable, with a bound *on the box*. -/
lemma aP_sub_of_boundOn {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {F G : X N → ℝ}
    (hFm : Measurable F) (hGm : Measurable G) {M M' : ℝ}
    (hFb : ∀ z ∈ abox N ℓ, |F z| ≤ M) (hGb : ∀ z ∈ abox N ℓ, |G z| ≤ M') {x : X N}
    (hx : x ∈ abox N ℓ) :
    aP ℓ i (fun y => F y - G y) x = aP ℓ i F x - aP ℓ i G x :=
  aP_sub_at i x (integrableOn_update_of_bounded hℓ i hFm hFb hx)
    (integrableOn_update_of_bounded hℓ i hGm hGb hx)

/-- **Slot-weighted products are integrable on the box.**  The product of two continuous
factors with a bounded measurable slot factor `u (x i)` is integrable over the centred box. -/
lemma integrableOn_cont_slot_bounded {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {A B : X n → ℝ} (hAc : Continuous A) (hBc : Continuous B)
    {u : Sp → ℝ} (hum : Measurable u) {K : ℝ} (huK : ∀ z, |u z| ≤ K) :
    IntegrableOn (fun x : X n => A x * u (x i) * B x) (abox n ℓ) volume := by
  have hAB : IntegrableOn (fun x : X n => A x * B x) (abox n ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (hAc.mul hBc)
  have hu : AEStronglyMeasurable (fun x : X n => u (x i))
      ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    (hum.comp (measurable_pi_apply i)).aestronglyMeasurable
  have hbdd : ∀ᵐ x ∂((volume : Measure (X n)).restrict (abox n ℓ)), ‖u (x i)‖ ≤ K :=
    ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact huK (x i))
  have h := hAB.mul_bdd hu hbdd
  refine h.congr ?_
  exact Filter.EventuallyEq.of_eq (funext (fun x => by ring))

/-- A uniform bound for the slot mean `aP ℓ j Φ` on the box, for continuous `Φ`. -/
lemma exists_bound_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ abox N ℓ, |aP ℓ j Φ z| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ)
    (f := aP ℓ j Φ) (aP_continuous hℓ j hΦc).continuousOn
  refine ⟨C, ?_, fun z hz => ?_⟩
  · exact le_trans (norm_nonneg _) (hC (0 : X N) (zero_mem_abox hℓ.le))
  · simpa [Real.norm_eq_abs] using hC z hz

/-- Continuity of the `Q`-slot factor `Q_i Φ = Φ − P_i Φ`. -/
lemma aQ_cont {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) : Continuous (aQ ℓ i Φ) := by
  have h : aQ ℓ i Φ = fun x : X n => Φ x - aP ℓ i Φ x := rfl
  rw [h]
  exact hΦc.sub (aP_continuous hℓ i hΦc)

/-- Continuity of `Q_i (P_j Φ)`. -/
lemma aQ_pair_cont {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) : Continuous (aQ ℓ i (fun y : X n => aP ℓ j Φ y)) := by
  have h : aQ ℓ i (fun y : X n => aP ℓ j Φ y)
      = fun x : X n => aP ℓ j Φ x - aP ℓ i (fun y : X n => aP ℓ j Φ y) x := rfl
  rw [h]
  exact (aP_continuous hℓ j hΦc).sub (aP_continuous hℓ i (aP_continuous hℓ j hΦc))

end Work.BoseBoxFock
