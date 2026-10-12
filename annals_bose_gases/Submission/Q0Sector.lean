import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.CentreBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — sector projections Pᵢ, Qᵢ on the *centred* box Λ(ℓ)

The Fournais--Solovej box analysis (potsplit Q0..Q4, `lem:potsplit` /
`lem:QDecompSimpler` of `final_v2.tex`) is carried out on the centred box
`acube ℓ = [−ℓ/2,ℓ/2]³` (which contains `supp χ_ℓ ⊆ ball 0 (ℓ/2)`, see
`CentreBox.ball_subset_acube`).  The condensate on `acube ℓ` is the constant
function, so the projection onto it is the *mean over the centred box*:

    (PᵢΦ)(x) := (1/ℓ³)·∫_{y ∈ acube ℓ} Φ (update x i y),      Qᵢ := 1 − Pᵢ

(as FS `def:projections` with `θ = 1_{Λ(ℓ)}`).  This module is the centred
mirror of `SectorProj.sectP/sectQ` (which lives on the positive cube) and
provides:

  * the acube/abox integrability toolbox (`aP_abs_le`,
    `aP_aestronglyMeasurable`, `aP_integrableOn`, peels `abox_peel_mp`,
    `abox_integral_peel`, compactness facts, constant-over-cube integrals);
  * the structural constancy lemmas (`PᵢΦ` is constant in slot `i`,
    `PᵢPⱼΦ` is constant in slots `i,j`) — the algebraic heart of the
    Q0-sector value identities;
  * the projection algebra (idempotency, self-adjointness over the box,
    orthogonality of `Pᵢ` and `Qᵢ`, mass preservation).

All lemmas mirror their `SectorProj`/`Potential` counterparts verbatim with
`acube ℓ`/`abox N ℓ` in place of `cube L`/`box N L`; the measure identities
come from `CentreBox` (`restrict_abox_eq_pi`,
`measurePreserving_coordSplitFinAcube`, `acube_volume`).  State hypotheses:
Φ, Ψ smooth or continuous on all of `X N` (functions are total), `0 < ℓ`.

## Route notes (for the child)

* Copy the corresponding `SectorProj` proofs (`sectP_abs_le`,
  `sectP_aestronglyMeasurable`, `sectP_integrableOn`, `box_peel_mp`,
  `box_integral_peel`, `sectP_idem`, `sectP_sym`, `sectQ_ortho`,
  `sectP_integral_eq`) replacing `cube L` ↦ `acube ℓ`, `box N L` ↦
  `abox N ℓ`, `volume_cube`/`real_volume_cube`/`integral_const_cube` ↦ the
  acube versions (use `CentreBox.acube_volume` + `ENNReal.toReal_ofReal`),
  `update_mem_box` ↦ `update_mem_abox`, and the peel map facts from
  `CentreBox.measurePreserving_coordSplitFinAcube`/`restrict_abox_eq_pi`.
* `aP_const_in_coord`: both sides reduce to `(1/ℓ³)·∫_y Φ (update x i y)`
  (double update collapses).
* `aP_pair_const_in_coord`: peel through two updates; if `i ≠ j` the two
  slots are updated independently and both integrals factor out.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real
open scoped NNReal

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The projection onto functions constant in particle `i` (the condensate
mean over the centred box `acube ℓ`). -/
noncomputable def aP (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ :=
  (1 / ℓ ^ 3) * ∫ y in acube ℓ, Φ (Function.update x i y)

/-- The complement projection `Qᵢ := 1 − Pᵢ`. -/
noncomputable def aQ (ℓ : ℝ) {N : ℕ} (i : Fin N) (Φ : X N → ℝ) (x : X N) : ℝ :=
  Φ x - aP ℓ i Φ x

/-! ## Norm helpers for the centred boxes -/

/-- In a finite-dimensional Euclidean space, coordinate bounds imply the norm
bound `‖y‖ ≤ sqrt 3 · L`. -/
lemma eucl_norm_le_of_abs_coord_le {L : ℝ} (hL : 0 ≤ L) {y : ℝ³}
    (hy : ∀ m : Fin 3, |y m| ≤ L) : ‖y‖ ≤ Real.sqrt 3 * L := by
  have hb : 0 ≤ Real.sqrt 3 * L := mul_nonneg (Real.sqrt_nonneg 3) hL
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ m : Fin 3, (y m) ^ 2 ≤ ∑ m : Fin 3, L ^ 2 := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        calc
          (y m) ^ 2 = |y m| ^ 2 := by rw [sq_abs]
          _ ≤ L ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hy m) 2
      _ = 3 * L ^ 2 := by norm_num
      _ = (Real.sqrt 3 * L) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  · exact hb

/-- A point of the N-particle centred box has norm at most `sqrt 3 · ℓ/2`. -/
lemma norm_le_of_mem_abox {N : ℕ} {ℓ : ℝ} {x : X N} (hℓ : 0 ≤ ℓ) (hx : x ∈ abox N ℓ) :
    ‖x‖ ≤ Real.sqrt 3 * (ℓ / 2) := by
  rw [Pi.norm_def]
  have hhalf : 0 ≤ ℓ / 2 := by nlinarith
  have hc0 : 0 ≤ Real.sqrt 3 * (ℓ / 2) := mul_nonneg (Real.sqrt_nonneg 3) hhalf
  let c : ℝ≥0 := ⟨Real.sqrt 3 * (ℓ / 2), hc0⟩
  have hc : (c : ℝ) = Real.sqrt 3 * (ℓ / 2) := rfl
  rw [← hc]
  exact_mod_cast (Finset.sup_le_iff.mpr (fun i hi => by
    have hxi : x i ∈ acube ℓ := hx i
    rw [mem_acube_iff] at hxi
    exact eucl_norm_le_of_abs_coord_le hhalf (fun m : Fin 3 => by
      have hm : (x i) m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hxi m
      have h1 : -(ℓ / 2) ≤ (x i) m := by nlinarith [hm.1]
      exact abs_le.mpr ⟨h1, hm.2⟩)))

/-- The zero configuration lies in the centred box for `0 ≤ ℓ`. -/
lemma zero_mem_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : (0 : X N) ∈ abox N ℓ := by
  intro i
  rw [mem_acube_iff]
  intro m
  have h1 : (-ℓ / 2 : ℝ) ≤ (0 : ℝ) := by nlinarith
  have h2 : (0 : ℝ) ≤ ℓ / 2 := by nlinarith
  exact ⟨h1, h2⟩

/-! ## Geometry: closed/bounded/compact centred boxes -/

/-- The centred cube is closed. -/
lemma acube_isClosed (ℓ : ℝ) : IsClosed (acube ℓ) := by
  rw [show acube ℓ = ⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' (Set.Icc (-ℓ / 2) (ℓ / 2)) by
    ext y
    simp [acube]]
  exact isClosed_iInter (fun m => IsClosed.preimage (by fun_prop : Continuous fun y : ℝ³ => y m) isClosed_Icc)


/-- The centred cube is bounded for `0 ≤ ℓ`. -/
lemma acube_isBounded (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : Bornology.IsBounded (acube ℓ) := by
  rw [Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ³))]
  refine ⟨Real.sqrt 3 * (ℓ / 2), ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  have hhalf : 0 ≤ ℓ / 2 := by nlinarith
  have hyb : ‖y‖ ≤ Real.sqrt 3 * (ℓ / 2) := eucl_norm_le_of_abs_coord_le hhalf (fun m => by
    rw [mem_acube_iff] at hy
    have hm : y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy m
    have h1 : -(ℓ / 2) ≤ y m := by nlinarith [hm.1]
    exact abs_le.mpr ⟨h1, hm.2⟩)
  simpa [dist_eq_norm] using hyb


/-- The centred cube is compact for `0 < ℓ`. -/
lemma acube_compact {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (acube ℓ) := by
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨acube_isClosed ℓ, acube_isBounded ℓ hℓ.le⟩


/-- The N-particle centred box is closed. -/
lemma abox_isClosed (N : ℕ) (ℓ : ℝ) : IsClosed (abox N ℓ) := by
  rw [show abox N ℓ = ⋂ i : Fin N, (fun x : X N => x i) ⁻¹' (acube ℓ) by
    ext x
    simp [abox]]
  exact isClosed_iInter (fun i => IsClosed.preimage (by fun_prop : Continuous fun x : X N => x i) (acube_isClosed ℓ))


/-- The N-particle centred box is bounded for `0 ≤ ℓ`. -/
lemma abox_isBounded (N : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : Bornology.IsBounded (abox N ℓ) := by
  rw [Metric.isBounded_iff_subset_closedBall (c := (0 : X N))]
  refine ⟨Real.sqrt 3 * (ℓ / 2), ?_⟩
  intro x hx
  rw [Metric.mem_closedBall]
  have hxle := norm_le_of_mem_abox hℓ hx
  simpa [dist_eq_norm] using hxle

/-- The N-particle centred box is compact for `0 < ℓ`. -/
lemma abox_compact (N : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (abox N ℓ) := by
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨abox_isClosed N ℓ, abox_isBounded N ℓ hℓ.le⟩


/-- Real measure of the centred cube: `ℓ³`. -/
lemma real_volume_acube (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ((volume : Measure ℝ³).restrict (acube ℓ)).real Set.univ = ℓ ^ 3 := by
  rw [MeasureTheory.measureReal_def]
  rw [Measure.restrict_apply_univ, acube_volume ℓ hℓ]
  exact ENNReal.toReal_ofReal (pow_nonneg hℓ 3)


/-- Integral of a constant over the centred cube. -/
lemma integral_const_acube (ℓ : ℝ) (hℓ : 0 < ℓ) (c : ℝ) :
    (∫ y : ℝ³ in acube ℓ, c) = c * ℓ ^ 3 := by
  have h1 : (∫ y : ℝ³ in acube ℓ, c) = (((volume : Measure ℝ³).restrict (acube ℓ)).real Set.univ) • c := by
    simpa using (MeasureTheory.integral_const (μ := (volume : Measure ℝ³).restrict (acube ℓ)) (c := c))
  rw [h1, real_volume_acube ℓ hℓ.le]
  ring


/-! ## Integrability of the mean over the centred box -/

/-- A continuous function is integrable over the centred cube. -/
lemma integrableOn_acube_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ³ → ℝ}
    (hF : Continuous F) : IntegrableOn F (acube ℓ) volume := by
  exact ContinuousOn.integrableOn_compact (acube_compact hℓ) hF.continuousOn


/-- A continuous function on the whole space is integrable over the N-box. -/
lemma integrableOn_abox_of_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {F : X N → ℝ}
    (hF : Continuous F) : IntegrableOn F (abox N ℓ) volume := by
  exact ContinuousOn.integrableOn_compact (abox_compact N hℓ) hF.continuousOn


/-- Updating coordinate `i` to a centred-cube point keeps a box point in the
centred box. -/
lemma update_mem_abox {N : ℕ} {ℓ : ℝ} {x : X N} (i : Fin N) {z : ℝ³}
    (hx : x ∈ abox N ℓ) (hz : z ∈ acube ℓ) : Function.update x i z ∈ abox N ℓ := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hz
  · simpa [hj] using (hx j)


/-- `|PᵢΦ x|` is bounded by a bound of `|Φ|` on the centred box. -/
lemma aP_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) :
    ∀ x ∈ abox N ℓ, |aP ℓ i Φ x| ≤ B := by
  intro x hx
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  have hInt1 : Integrable (fun y : ℝ³ => |Φ (Function.update x i y)|) μ' := by
    exact integrableOn_acube_of_continuous hℓ (by
      have hc : Continuous (fun y : ℝ³ => Φ (Function.update x i y)) := by
        exact hΦc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y))
      exact hc.norm)
  have hInt2 : Integrable (fun _ : ℝ³ => B) μ' := by
    exact (integrableOn_const (μ := volume) (s := acube ℓ) (C := B)
      (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp))
  have hmono : (∫ y : ℝ³, |Φ (Function.update x i y)| ∂μ') ≤ (∫ y : ℝ³, B ∂μ') := by
    refine integral_mono_ae hInt1 hInt2 ?_
    change ∀ᵐ y ∂μ', |Φ (Function.update x i y)| ≤ B
    rw [ae_restrict_iff' (acube_measurable ℓ)]
    exact ae_of_all volume (by
      intro y hy
      exact hΦB (Function.update x i y) (update_mem_abox i hx hy))
  have hIntB : (∫ y : ℝ³, B ∂μ') = B * ℓ ^ 3 := by
    rw [MeasureTheory.integral_const]
    rw [real_volume_acube ℓ hℓ.le]
    simp
    ring
  have hmain : |(1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x i y))| ≤ B := by
    have hnon : 0 ≤ 1 / ℓ ^ 3 := by positivity
    calc
      |(1 / ℓ ^ 3) * (∫ y : ℝ³, Φ (Function.update x i y) ∂μ')|
          = (1 / ℓ ^ 3) * |(∫ y : ℝ³, Φ (Function.update x i y) ∂μ')| := by
            rw [abs_mul, abs_of_nonneg hnon]
      _ ≤ (1 / ℓ ^ 3) * (∫ y : ℝ³, |Φ (Function.update x i y)| ∂μ') := by
            exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs
              (f := fun y : ℝ³ => Φ (Function.update x i y)) (μ := μ')) hnon
      _ ≤ (1 / ℓ ^ 3) * (∫ y : ℝ³, B ∂μ') := by
            exact mul_le_mul_of_nonneg_left hmono hnon
      _ ≤ B := by
            rw [hIntB]
            field_simp [ne_of_gt hℓ]
            exact le_rfl
  change |aP ℓ i Φ x| ≤ B
  unfold aP
  simpa using hmain


/-- `aP ℓ i Φ` is (strongly) measurable in `x` on the centred box. -/
lemma aP_aestronglyMeasurable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : AEStronglyMeasurable (aP ℓ i Φ) (volume.restrict (abox N ℓ)) := by
  have hf : AEStronglyMeasurable (fun x : X N => ∫ y : ℝ³, Φ (Function.update x i y)
      ∂((volume : Measure ℝ³).restrict (acube ℓ))) (volume : Measure (X N)) := by
    have hfc : AEStronglyMeasurable (fun p : X N × ℝ³ => Φ (Function.update p.1 i p.2))
        ((volume : Measure (X N)).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
      exact (hΦc.comp (by fun_prop : Continuous (fun p : X N × ℝ³ => Function.update p.1 i p.2))).aestronglyMeasurable
    haveI : SigmaFinite ((volume : Measure ℝ³).restrict (acube ℓ)) := by
      infer_instance
    exact hfc.integral_prod_right'
  change AEStronglyMeasurable (fun x : X N => (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, Φ (Function.update x i y)))
      (volume.restrict (abox N ℓ))
  exact (hf.const_mul (1 / ℓ ^ 3)).restrict


/-- `aP ℓ i Φ` is integrable over the centred box. -/
lemma aP_integrableOn {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (aP ℓ i Φ) (abox N ℓ) volume := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := by
    have hb := hC (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  refine IntegrableOn.of_bound ?hs ?hf C ?hb
  · exact (abox_compact N hℓ).measure_lt_top
  · exact aP_aestronglyMeasurable hℓ i hΦc
  · change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), ‖aP ℓ i Φ x‖ ≤ C
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all volume (by
      intro x hx
      have hle := aP_abs_le hℓ i hΦc hC0 (by intro y hy; simpa [Real.norm_eq_abs] using hC y hy) x hx
      simpa using hle)


/-- The square of `QᵢΦ` is integrable over the centred box (for smooth Φ). -/
lemma integrableOn_sq_aQ {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (fun x : X N => (aQ ℓ i Φ x) ^ 2) (abox N ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  have hbndP : ∀ x ∈ abox N ℓ, |aP ℓ i Φ x| ≤ B :=
    aP_abs_le hℓ i hΦc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy)
  have hbndΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ B := by
    intro x hx
    simpa [Real.norm_eq_abs] using hB x hx
  refine IntegrableOn.of_bound ?hs ?hf ((2 * B) ^ 2) ?hb
  · exact (abox_compact N hℓ).measure_lt_top
  · have hq : AEStronglyMeasurable (aQ ℓ i Φ) (volume.restrict (abox N ℓ)) := by
      change AEStronglyMeasurable (fun x : X N => Φ x - aP ℓ i Φ x) (volume.restrict (abox N ℓ))
      exact (hΦc.aestronglyMeasurable.restrict (s := abox N ℓ)).sub
        (aP_aestronglyMeasurable hℓ i hΦc)
    exact hq.pow 2
  · change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), ‖(aQ ℓ i Φ x) ^ 2‖ ≤ (2 * B) ^ 2
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all volume (by
      intro x hx
      have h1 : |Φ x| ≤ B := hbndΦ x hx
      have h2 : |aP ℓ i Φ x| ≤ B := hbndP x hx
      have hq : |aQ ℓ i Φ x| ≤ 2 * B := by
        unfold aQ
        have htri : |Φ x - aP ℓ i Φ x| ≤ |Φ x| + |aP ℓ i Φ x| := by
          simpa using (norm_sub_le (Φ x) (aP ℓ i Φ x))
        nlinarith
      calc
        ‖(aQ ℓ i Φ x) ^ 2‖ = (aQ ℓ i Φ x) ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        _ = |aQ ℓ i Φ x| ^ 2 := by rw [sq_abs]
        _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hq 2)


/-! ## The peel of the centred box isolating one coordinate -/

/-- The measure-preserving peel of the centred N-box isolating particle `i`
(restricted-measure form). -/
lemma abox_peel_mp (n : ℕ) (ℓ : ℝ) (i : Fin (n + 1)) :
    MeasurePreserving (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ))
      (((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  have h1 := measurePreserving_coordSplitFinAcube (n := n) ℓ i
  simpa [restrict_abox_eq_pi] using h1


/-- Real integral peel of the centred box. -/
lemma abox_integral_peel {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) (F : X (n + 1) → ℝ)
    (hF : IntegrableOn F (abox (n + 1) ℓ) volume) :
    (∫ x in abox (n + 1) ℓ, F x) =
      ∫ r : X n, (∫ y : ℝ³ in acube ℓ, F (kcInsN n i (y, r)))
        ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  let ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n ℓ)
  have hmp2 : MeasurePreserving (⇑(kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ³) i))
      (abox_peel_mp (n := n) ℓ i)
    simpa [kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : (ℝ³ × X n) => F (kcInsN n i p)) (μ'.prod ν) := by
    change Integrable (fun p : kcE3 × X n => F (kcInsN n i p)) (μ'.prod ν)
    exact (hmp2.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  calc
    (∫ x in abox (n + 1) ℓ, F x) = ∫ x : X (n + 1), F x ∂((volume : Measure (X (n+1))).restrict (abox (n + 1) ℓ)) := by rfl
    _ = ∫ p : ℝ³ × X n, F (kcInsN n i p) ∂(μ'.prod ν) := by
      simpa [μ', ν] using (hmp2.integral_comp' F).symm
    _ = ∫ r : X n, (∫ y : ℝ³, F (kcInsN n i (y, r)) ∂μ') ∂ν := by
      exact MeasureTheory.integral_prod_symm (f := fun p : ℝ³ × X n => F (kcInsN n i p)) hpeel
    _ = ∫ r : X n, (∫ y : ℝ³ in acube ℓ, F (kcInsN n i (y, r))) ∂ν := by rfl


/-! ## Structural constancy of the means -/

/-- `PᵢΦ` does not depend on the value of the `i`-th coordinate. -/
lemma aP_const_in_coord {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) (x : X N) (z : ℝ³) :
    aP ℓ i Φ (Function.update x i z) = aP ℓ i Φ x := by
  have hupd : ∀ y : ℝ³, Function.update (Function.update x i z) i y = Function.update x i y := by
    intro y
    ext k
    by_cases hk : k = i <;> simp [hk]
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact congrArg Φ (hupd y)


/-- `PᵢPⱼΦ` does not depend on the value of the `i`-th coordinate (for `i ≠ j`
the same proof works without the hypothesis; kept for clarity). -/
lemma aP_pair_const_in_i {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) (z : ℝ³) :
    aP ℓ i (aP ℓ j Φ) (Function.update x i z) = aP ℓ i (aP ℓ j Φ) x := by
  have hupd : ∀ y : ℝ³, Function.update (Function.update x i z) i y = Function.update x i y := by
    intro y
    ext k
    by_cases hk : k = i <;> simp [hk]
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  exact congrArg (aP ℓ j Φ) (hupd y)


/-- `PᵢPⱼΦ` does not depend on the value of the `j`-th coordinate. -/
lemma aP_pair_const_in_j {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (x : X N) (z : ℝ³) :
    aP ℓ i (aP ℓ j Φ) (Function.update x j z) = aP ℓ i (aP ℓ j Φ) x := by
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  ext k
  by_cases hkj : k = j
  · subst k
    simp
  · by_cases hki : k = i
    · subst k
      simp [hkj]
    · simp [hkj, hki]


/-! ## Projection algebra over the centred box -/

/-- Idempotency of `Pᵢ`: `Pᵢ(PᵢΦ) = PᵢΦ` pointwise. -/
lemma aP_idem {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) (x : X N) :
    aP ℓ i (aP ℓ i Φ) x = aP ℓ i Φ x := by
  have hinv : ∀ y : ℝ³, aP ℓ i Φ (Function.update x i y) = aP ℓ i Φ x := by
    intro y
    exact aP_const_in_coord hℓ i hΦc x y
  calc
    aP ℓ i (aP ℓ i Φ) x = (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, aP ℓ i Φ x) := by
      unfold aP
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      exact hinv y
    _ = aP ℓ i Φ x := by
      rw [integral_const_acube ℓ hℓ]
      field_simp [ne_of_gt hℓ]


/-! ## Projection-algebra toolbox for the centred box -/

/-- `Pᵢ` of an inserted configuration equals the centred-cube mean of the fibre. -/
lemma aP_kcInsN {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (y : ℝ³) (r : X n) :
    aP ℓ i Φ (kcInsN n i (y, r)) =
      (1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r))) := by
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  exact update_kcInsN i y z r

/-- Cauchy--Schwarz on the centred cube: `(∫ f)² ≤ ℓ³·∫ f²` for a continuous `f`. -/
lemma cs_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {f : ℝ³ → ℝ} (hf : Continuous f) :
    (∫ y in acube ℓ, f y) ^ 2 ≤ ℓ ^ 3 * (∫ y in acube ℓ, (f y) ^ 2) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  have hfin : IsFiniteMeasure μ' := by
    refine ⟨?set⟩
    rw [Measure.restrict_apply_univ]
    exact acube_lt_top ℓ hℓ.le
  letI : IsFiniteMeasure μ' := hfin
  have hm : AEStronglyMeasurable f μ' := hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := (acube_compact hℓ).exists_bound_of_continuousOn (s := acube ℓ) (f := f) hf.continuousOn
  have hb : ∀ᵐ y ∂μ', |f y| ≤ C := by
    rw [ae_restrict_iff' (acube_measurable ℓ)]
    exact ae_of_all volume (fun y hy => by
      have hb' := hC y hy
      simpa [Real.norm_eq_abs] using hb')
  have hcs := cs_finite_measure (μ := μ') (f := f) hm hb
  have hvol : μ'.real Set.univ = ℓ ^ 3 := by
    dsimp [μ']
    exact real_volume_acube ℓ hℓ.le
  rw [hvol] at hcs
  simpa [μ'] using hcs

/-- fibre Cauchy--Schwarz on the centred cube: the square of the fibre mean is
at most the fibre mean square. -/
lemma fibre_cs_acube {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦ : Continuous Φ) (r : X n) :
    (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 ≤
      ℓ ^ 3 * (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2) := by
  have hT : Continuous (fun y : ℝ³ => kcInsN n i (y, r)) := by
    rw [show (fun y : ℝ³ => kcInsN n i (y, r)) = fun y : ℝ³ => Function.update (kcInsN n i (0, r)) i y by
      funext y
      exact kcInsN_update_zero i y r]
    fun_prop
  exact cs_acube hℓ (hf := hΦ.comp hT)

/-- square of `aP ℓ i Φ` is integrable over the centred box -/
lemma integrableOn_sq_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : IntegrableOn (fun x : X N => (aP ℓ i Φ x) ^ 2) (abox N ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Φ (0 : X N))) hb
  refine IntegrableOn.of_bound ?hs ?hf (B ^ 2) ?hbnd
  · exact (abox_compact N hℓ).measure_lt_top
  · exact (aP_aestronglyMeasurable hℓ i hΦc).pow 2
  · change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), ‖(aP ℓ i Φ x) ^ 2‖ ≤ B ^ 2
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all volume (by
      intro x hx
      have hle : |aP ℓ i Φ x| ≤ B :=
        aP_abs_le hℓ i hΦc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy) x hx
      calc
        ‖(aP ℓ i Φ x) ^ 2‖ = (aP ℓ i Φ x) ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        _ = |aP ℓ i Φ x| ^ 2 := by rw [sq_abs]
        _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2)

/-- `aP ℓ i Ψ` multiplied by a continuous function is integrable over the centred box -/
lemma integrableOn_mul_aP {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    IntegrableOn (fun x : X N => Φ x * aP ℓ i Ψ x) (abox N ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := Ψ) hΨc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : X N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (Ψ (0 : X N))) hb
  have hf : AEStronglyMeasurable (fun x : X N => Φ x * aP ℓ i Ψ x)
      (volume.restrict (abox N ℓ)) := by
    exact ((hΦc.aestronglyMeasurable.restrict (s := abox N ℓ)).mul
      (aP_aestronglyMeasurable hℓ i hΨc))
  have hg : Integrable (fun x : X N => |Φ x| * B) (volume.restrict (abox N ℓ)) := by
    have hΦabs : Integrable (fun x : X N => |Φ x|) (volume.restrict (abox N ℓ)) :=
      integrableOn_abox_of_continuous hℓ hΦc.norm
    exact hΦabs.mul_const B
  refine Integrable.mono' hg hf ?_
  change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), ‖Φ x * aP ℓ i Ψ x‖ ≤ |Φ x| * B
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  exact ae_of_all volume (by
    intro x hx
    have hbndP : |aP ℓ i Ψ x| ≤ B :=
      aP_abs_le hℓ i hΨc hB0 (by intro y hy; simpa [Real.norm_eq_abs] using hB y hy) x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hbndP (abs_nonneg _))

/-- peeled form of the squared projection on the centred box -/
lemma peel_sq_aP {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) =
      ∫ r : X n, (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
        ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
  have hP := abox_integral_peel (i := i)
    (F := fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2) (integrableOn_sq_aP hℓ i hΦc)
  have hpoint : ∀ r : X n,
      (∫ y in acube ℓ, (aP ℓ i Φ (kcInsN n i (y, r))) ^ 2)
        = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 := by
    intro r
    calc
      (∫ y in acube ℓ, (aP ℓ i Φ (kcInsN n i (y, r))) ^ 2)
          = ∫ y in acube ℓ, ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with y
            rw [aP_kcInsN (ℓ := ℓ) (i := i) (Φ := Φ) y r]
      _ = ℓ ^ 3 * ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) ^ 2 := by
            rw [integral_const_acube ℓ hℓ]
            ring
      _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 := by
            field_simp [ne_of_gt hℓ]
  calc
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
        = ∫ r : X n, (∫ y in acube ℓ, (aP ℓ i Φ (kcInsN n i (y, r))) ^ 2)
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hP
    _ = ∫ r : X n, (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
          apply integral_congr_ae
          filter_upwards with r
          exact hpoint r

/-- peeled form of `⟨Φ, PᵢΦ⟩` on the centred box -/
lemma Phi_mul_aP_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox (n + 1) ℓ, Φ x * aP ℓ i Φ x) =
      ∫ r : X n, (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
        ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
  have hP := abox_integral_peel (i := i)
    (F := fun x : X (n + 1) => Φ x * aP ℓ i Φ x)
    (integrableOn_mul_aP hℓ i hΦc hΦc)
  have hpoint : ∀ r : X n,
      (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
        = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 := by
    intro r
    calc
      (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
          = ∫ y in acube ℓ, Φ (kcInsN n i (y, r)) *
              ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) := by
            apply integral_congr_ae
            filter_upwards with y
            exact congrArg (fun t : ℝ => Φ (kcInsN n i (y, r)) * t)
              (aP_kcInsN (ℓ := ℓ) (i := i) (Φ := Φ) y r)
      _ = (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) *
              ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) := by
            rw [MeasureTheory.integral_mul_const]
      _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 := by
            ring
  calc
    (∫ x in abox (n + 1) ℓ, Φ x * aP ℓ i Φ x)
        = ∫ r : X n, (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hP
    _ = ∫ r : X n, (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
          apply integral_congr_ae
          filter_upwards with r
          exact hpoint r

/-- Self-adjointness of `Pᵢ` over the centred box. -/
lemma aP_sym_box {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, (aP ℓ i Φ x) * Ψ x) = ∫ x in abox N ℓ, Φ x * (aP ℓ i Ψ x) := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hP1 := abox_integral_peel (i := i)
        (F := fun x : X (n + 1) => Ψ x * aP ℓ i Φ x) (integrableOn_mul_aP hℓ i hΨc hΦc)
      have hP2 := abox_integral_peel (i := i)
        (F := fun x : X (n + 1) => Φ x * aP ℓ i Ψ x) (integrableOn_mul_aP hℓ i hΦc hΨc)
      have hpoint : ∀ r : X n,
          (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
            = (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r))) := by
        intro r
        let A : ℝ := ∫ z in acube ℓ, Φ (kcInsN n i (z, r))
        let B : ℝ := ∫ y in acube ℓ, Ψ (kcInsN n i (y, r))
        have h1 : (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
            = (1 / ℓ ^ 3) * A * B := by
          calc
            (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
                = ∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) *
                    ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) := by
                  apply integral_congr_ae
                  filter_upwards with y
                  congr 1
                  exact aP_kcInsN (ℓ := ℓ) (i := i) (Φ := Φ) y r
            _ = (∫ y in acube ℓ, Ψ (kcInsN n i (y, r))) *
                    ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r)))) := by
                  rw [MeasureTheory.integral_mul_const]
            _ = (1 / ℓ ^ 3) * A * B := by
                  rw [show (∫ y in acube ℓ, Ψ (kcInsN n i (y, r))) = B by rfl,
                      show (∫ z in acube ℓ, Φ (kcInsN n i (z, r))) = A by rfl]
                  ring
        have h2 : (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)))
            = (1 / ℓ ^ 3) * A * B := by
          calc
            (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)))
                = ∫ y in acube ℓ, Φ (kcInsN n i (y, r)) *
                    ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Ψ (kcInsN n i (z, r)))) := by
                  apply integral_congr_ae
                  filter_upwards with y
                  congr 1
                  exact aP_kcInsN (ℓ := ℓ) (i := i) (Φ := Ψ) y r
            _ = (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) *
                    ((1 / ℓ ^ 3) * (∫ z in acube ℓ, Ψ (kcInsN n i (z, r)))) := by
                  rw [MeasureTheory.integral_mul_const]
            _ = (1 / ℓ ^ 3) * A * B := by
                  rw [show (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) = A by rfl,
                      show (∫ z in acube ℓ, Ψ (kcInsN n i (z, r))) = B by rfl]
                  ring
        exact h1.trans h2.symm
      calc
        (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) * Ψ x)
            = ∫ x in abox (n + 1) ℓ, Ψ x * (aP ℓ i Φ x) := by
              apply integral_congr_ae
              filter_upwards with x
              rw [mul_comm]
        _ = ∫ r : X n, (∫ y in acube ℓ, Ψ (kcInsN n i (y, r)) * aP ℓ i Φ (kcInsN n i (y, r)))
              ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hP1
        _ = ∫ r : X n, (∫ y in acube ℓ, Φ (kcInsN n i (y, r)) * aP ℓ i Ψ (kcInsN n i (y, r)))
              ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
              apply integral_congr_ae
              filter_upwards with r
              exact hpoint r
        _ = (∫ x in abox (n + 1) ℓ, Φ x * (aP ℓ i Ψ x)) := hP2.symm


/-- The mean square equals the square of the mean plus the square of the
complement (`⟨PᵢΦ, QᵢΦ⟩ = 0`-orthogonality in integral form). -/
lemma aQ_ortho_box {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x)) = 0 := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hInt1 : IntegrableOn (fun x : X (n + 1) => aP ℓ i Φ x * Φ x) (abox (n + 1) ℓ) volume := by
        have hEq : (fun x : X (n + 1) => aP ℓ i Φ x * Φ x) = fun x : X (n + 1) => Φ x * aP ℓ i Φ x := by
          funext x
          rw [mul_comm]
        rw [hEq]
        exact integrableOn_mul_aP hℓ i hΦc hΦc
      have hInt2 : IntegrableOn (fun x : X (n + 1) => (aP ℓ i Φ x) ^ 2) (abox (n + 1) ℓ) volume :=
        integrableOn_sq_aP hℓ i hΦc
      have hpeel1 := peel_sq_aP hℓ i hΦc
      have hpeel2 := Phi_mul_aP_integral hℓ i hΦc
      have hmain : (∫ x in abox (n + 1) ℓ, aP ℓ i Φ x * Φ x)
          = (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
        calc
          (∫ x in abox (n + 1) ℓ, aP ℓ i Φ x * Φ x)
              = ∫ x in abox (n + 1) ℓ, Φ x * aP ℓ i Φ x := by
                apply integral_congr_ae
                filter_upwards with x
                rw [mul_comm]
          _ = (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
                rw [hpeel1, hpeel2]
      calc
        (∫ x in abox (n + 1) ℓ, aP ℓ i Φ x * aQ ℓ i Φ x)
            = ∫ x in abox (n + 1) ℓ, aP ℓ i Φ x * Φ x - (aP ℓ i Φ x) ^ 2 := by
              apply integral_congr_ae
              filter_upwards with x
              unfold aQ
              ring
        _ = (∫ x in abox (n + 1) ℓ, aP ℓ i Φ x * Φ x) -
              (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
              exact integral_sub (μ := (volume : Measure (X (n + 1))).restrict (abox (n + 1) ℓ)) hInt1 hInt2
        _ = 0 := by rw [hmain]; ring


/-- `Pᵢ` preserves the total mass on the centred box. -/
lemma aP_integral_eq_box {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, aP ℓ i Φ x) = ∫ x in abox N ℓ, Φ x := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      have hΦint : IntegrableOn Φ (abox (n + 1) ℓ) volume :=
        integrableOn_abox_of_continuous hℓ hΦc
      have hPl := abox_integral_peel (i := i)
        (F := fun x : X (n + 1) => aP ℓ i Φ x) (aP_integrableOn hℓ i hΦc)
      have hPR := abox_integral_peel (i := i) (F := Φ) hΦint
      calc
        (∫ x in abox (n + 1) ℓ, aP ℓ i Φ x)
            = ∫ r : X n, (∫ y : ℝ³ in acube ℓ, aP ℓ i Φ (kcInsN n i (y, r)))
                ∂((volume : Measure (X n)).restrict (abox n ℓ)) := hPl
        _ = ∫ r : X n, (∫ z : ℝ³ in acube ℓ, Φ (kcInsN n i (z, r)))
                ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
              apply integral_congr_ae
              filter_upwards with r
              have h1 : (∫ y : ℝ³ in acube ℓ, aP ℓ i Φ (kcInsN n i (y, r)))
                  = ∫ y : ℝ³ in acube ℓ, (1 / ℓ ^ 3) * (∫ z in acube ℓ, Φ (kcInsN n i (z, r))) := by
                apply integral_congr_ae
                filter_upwards with y
                exact aP_kcInsN i y r
              rw [h1]
              rw [integral_const_acube ℓ hℓ]
              field_simp [ne_of_gt hℓ]
        _ = (∫ x in abox (n + 1) ℓ, Φ x) := hPR.symm


/-- Contraction of the mean: `‖PᵢΦ‖² ≤ ‖Φ‖²` on the centred box. -/
lemma aP_sq_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) ≤ ∫ x in abox N ℓ, (Φ x) ^ 2 := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn (s := abox (n + 1) ℓ) (f := Φ)
        hΦc.continuousOn
      have hB0 : 0 ≤ B := by
        have hb := hB (0 : X (n + 1)) (zero_mem_abox hℓ.le)
        exact le_trans (norm_nonneg (Φ (0 : X (n + 1)))) hb
      have hswap : Continuous (fun p : X n × ℝ³ => (p.2, p.1)) := by fun_prop
      let F1 : X n → ℝ := fun r => (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
      let F2 : X n → ℝ := fun r => ∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2
      have hg2aem : AEStronglyMeasurable F2 (volume : Measure (X n)) := by
        have hf : AEStronglyMeasurable (fun p : X n × ℝ³ => (Φ (kcInsN n i (p.2, p.1))) ^ 2)
            ((volume : Measure (X n)).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
          exact ((hΦc.comp ((kcInsN_cont i).comp hswap)).pow 2).aestronglyMeasurable
        haveI : SigmaFinite ((volume : Measure ℝ³).restrict (acube ℓ)) := by infer_instance
        exact (hf.integral_prod_right' : AEStronglyMeasurable (fun r : X n =>
          ∫ y : ℝ³, (Φ (kcInsN n i (y, r))) ^ 2 ∂(volume.restrict (acube ℓ))) (volume : Measure (X n)))
      have hF2_aem : AEStronglyMeasurable F2 (volume.restrict (abox n ℓ)) := by
        change AEStronglyMeasurable (fun r : X n => ∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2)
          (volume.restrict (abox n ℓ))
        exact hg2aem.restrict
      have hF2_bnd : ∀ᵐ r ∂(volume.restrict (abox n ℓ)), ‖F2 r‖ ≤ B ^ 2 * ℓ ^ 3 := by
        change ∀ᵐ r ∂(volume.restrict (abox n ℓ)),
            ‖∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2‖ ≤ B ^ 2 * ℓ ^ 3
        rw [ae_restrict_iff' (IsClosed.measurableSet (abox_isClosed n ℓ))]
        exact ae_of_all volume (by
          intro r hr
          have hbnd : ∀ᵐ y ∂(volume.restrict (acube ℓ)), (Φ (kcInsN n i (y, r))) ^ 2 ≤ B ^ 2 := by
            rw [ae_restrict_iff' (acube_measurable ℓ)]
            exact ae_of_all volume (by
              intro y hy
              have hb' := hB (kcInsN n i (y, r)) (by
                intro j
                by_cases hj : j = i
                · subst j
                  rw [kc_insN_apply_same]
                  exact hy
                · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
                  rw [kc_insN_apply_succ]
                  exact hr j')
              have hb2 : |Φ (kcInsN n i (y, r))| ≤ B := by simpa [Real.norm_eq_abs] using hb'
              calc
                (Φ (kcInsN n i (y, r))) ^ 2 = |Φ (kcInsN n i (y, r))| ^ 2 := by rw [sq_abs]
                _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb2 2)
          have hIntY : Integrable (fun y : ℝ³ => (Φ (kcInsN n i (y, r))) ^ 2)
              (volume.restrict (acube ℓ)) := by
            have hc : Continuous (fun y : ℝ³ => (Φ (kcInsN n i (y, r))) ^ 2) := by
              exact ((hΦc.comp ((kcInsN_cont i).comp
                (by fun_prop : Continuous (fun y : ℝ³ => (y, r))))).pow 2)
            exact integrableOn_acube_of_continuous hℓ hc
          have hIntC : Integrable (fun _ : ℝ³ => B ^ 2) (volume.restrict (acube ℓ)) :=
            integrableOn_const (s := acube ℓ) (C := B ^ 2) (hs := ne_of_lt (acube_lt_top ℓ hℓ.le)) (hC := by simp)
          have hle1 : (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2) ≤ (∫ y in acube ℓ, B ^ 2) := by
            exact integral_mono_ae hIntY hIntC hbnd
          have hineq : (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2) ≤ B ^ 2 * ℓ ^ 3 := by
            calc
              (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2) ≤ (∫ y in acube ℓ, B ^ 2) := hle1
              _ = B ^ 2 * ℓ ^ 3 := by rw [integral_const_acube ℓ hℓ]
          have habs : ‖∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2‖
              = ∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg]
            exact integral_nonneg (fun _ => sq_nonneg _)
          rw [habs]
          exact hineq)
      have hg2_int : Integrable F2 (volume.restrict (abox n ℓ)) := by
        exact IntegrableOn.of_bound (s := abox n ℓ) (f := F2) (C := B ^ 2 * ℓ ^ 3)
          (hs := (abox_compact n hℓ).measure_lt_top) (hf := hF2_aem) (hfC := hF2_bnd)
      have hpt : ∀ r : X n, F1 r ≤ F2 r := by
        intro r
        have hcs := fibre_cs_acube hℓ i hΦc r
        have hmul : (1 / ℓ ^ 3) * ℓ ^ 3 = 1 := by field_simp [ne_of_gt hℓ]
        calc
          F1 r = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2 := by rfl
          _ ≤ (1 / ℓ ^ 3) * (ℓ ^ 3 * (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2)) := by
                exact mul_le_mul_of_nonneg_left hcs (by positivity)
          _ = ∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2 := by
                rw [← mul_assoc, hmul, one_mul]
          _ = F2 r := by rfl
      have hF1_aem : AEStronglyMeasurable F1 (volume.restrict (abox n ℓ)) := by
        change AEStronglyMeasurable (fun r : X n => (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2)
          (volume.restrict (abox n ℓ))
        have hA : AEStronglyMeasurable (fun r : X n => ∫ y in acube ℓ, Φ (kcInsN n i (y, r)))
            (volume : Measure (X n)) := by
          have hf : AEStronglyMeasurable (fun p : X n × ℝ³ => Φ (kcInsN n i (p.2, p.1)))
              ((volume : Measure (X n)).prod ((volume : Measure ℝ³).restrict (acube ℓ))) := by
            exact (hΦc.comp ((kcInsN_cont i).comp hswap)).aestronglyMeasurable
          haveI : SigmaFinite ((volume : Measure ℝ³).restrict (acube ℓ)) := by infer_instance
          exact (hf.integral_prod_right' : AEStronglyMeasurable (fun r : X n =>
            ∫ y : ℝ³, Φ (kcInsN n i (y, r)) ∂(volume.restrict (acube ℓ))) (volume : Measure (X n)))
        exact ((hA.restrict).pow 2).const_mul (1 / ℓ ^ 3)
      have hF1_bnd : ∀ᵐ r ∂(volume.restrict (abox n ℓ)), ‖F1 r‖ ≤ F2 r := by
        filter_upwards with r
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hpt r
        · positivity
      have hg1_int : Integrable F1 (volume.restrict (abox n ℓ)) :=
        Integrable.mono' hg2_int hF1_aem hF1_bnd
      have hP := peel_sq_aP hℓ i hΦc
      have hPR := abox_integral_peel (i := i)
        (F := fun x : X (n + 1) => (Φ x) ^ 2) (integrableOn_abox_of_continuous hℓ (hΦc.pow 2))
      calc
        (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2)
            = ∫ r : X n, (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (kcInsN n i (y, r))) ^ 2
                ∂(volume.restrict (abox n ℓ)) := hP
        _ ≤ ∫ r : X n, (∫ y in acube ℓ, (Φ (kcInsN n i (y, r))) ^ 2)
                ∂(volume.restrict (abox n ℓ)) := by
              refine integral_mono_ae (μ := (volume : Measure (X n)).restrict (abox n ℓ)) hg1_int hg2_int ?_
              filter_upwards with r
              exact hpt r
        _ = (∫ x in abox (n + 1) ℓ, (Φ x) ^ 2) := hPR.symm



/-- A continuous function of two centred-cube variables is integrable for the
product of the two restricted measures. -/
lemma integrableOn_prod_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ³ × ℝ³ → ℝ}
    (hg : Continuous g) :
    Integrable g ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ))) := by
  have hprod : (volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ)) =
      (volume.prod volume).restrict ((acube ℓ) ×ˢ (acube ℓ)) := by
    simpa using (Measure.prod_restrict (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
      (s := acube ℓ) (t := acube ℓ))
  rw [hprod]
  exact ContinuousOn.integrableOn_compact (IsCompact.prod (acube_compact hℓ) (acube_compact hℓ))
    hg.continuousOn

/-- `PᵢPⱼ = PⱼPᵢ` (commutation), pointwise. -/
lemma aP_comm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) (x : X N) :
    aP ℓ i (aP ℓ j Φ) x = aP ℓ j (aP ℓ i Φ) x := by
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      by_cases hij : i = j
      · subst j
        rfl
      · let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
        let G : ℝ³ → ℝ³ → ℝ := fun y z => Φ (Function.update (Function.update x i y) j z)
        have hGsymm : ∀ y z : ℝ³,
            G y z = Φ (Function.update (Function.update x j z) i y) := by
          intro y z
          dsimp [G]
          congr 1
          rw [show Function.update (Function.update x i y) j z =
                Function.update (Function.update x j z) i y by
            exact Function.update_comm hij y z x]
        have hGc : Continuous (fun p : ℝ³ × ℝ³ => G p.1 p.2) := by
          dsimp [G]
          fun_prop
        have hGint : Integrable (fun p : ℝ³ × ℝ³ => G p.1 p.2) (μ'.prod μ') := by
          dsimp [μ']
          exact integrableOn_prod_acube hℓ hGc
        have hswap : (∫ y : ℝ³, (∫ z : ℝ³, G y z ∂μ') ∂μ') =
            (∫ z : ℝ³, (∫ y : ℝ³, G y z ∂μ') ∂μ') := by
          exact integral_integral_swap (μ := μ') (ν := μ') (f := G) hGint
        have hL : aP ℓ i (aP ℓ j Φ) x
            = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ y : ℝ³, (∫ z : ℝ³, G y z ∂μ') ∂μ') := by
          calc
            aP ℓ i (aP ℓ j Φ) x
                = (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ,
                    (1 / ℓ ^ 3) * (∫ z : ℝ³ in acube ℓ, Φ (Function.update (Function.update x i y) j z))) := by
                  rfl
            _ = (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, (1 / ℓ ^ 3) * (∫ z : ℝ³ in acube ℓ, G y z)) := by
                  rfl
            _ = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, (∫ z : ℝ³ in acube ℓ, G y z)) := by
                  rw [MeasureTheory.integral_const_mul]
                  ring
            _ = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ y : ℝ³, (∫ z : ℝ³, G y z ∂μ') ∂μ') := by
                  rfl
        have hR : aP ℓ j (aP ℓ i Φ) x
            = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ z : ℝ³, (∫ y : ℝ³, G y z ∂μ') ∂μ') := by
          calc
            aP ℓ j (aP ℓ i Φ) x
                = (1 / ℓ ^ 3) * (∫ z : ℝ³ in acube ℓ,
                    (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, Φ (Function.update (Function.update x j z) i y))) := by
                  rfl
            _ = (1 / ℓ ^ 3) * (∫ z : ℝ³ in acube ℓ, (1 / ℓ ^ 3) * (∫ y : ℝ³ in acube ℓ, G y z)) := by
                  congr 1
                  apply integral_congr_ae
                  filter_upwards with z
                  congr 1
                  apply integral_congr_ae
                  filter_upwards with y
                  exact (hGsymm y z).symm
            _ = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ z : ℝ³ in acube ℓ, (∫ y : ℝ³ in acube ℓ, G y z)) := by
                  rw [MeasureTheory.integral_const_mul]
                  ring
            _ = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ z : ℝ³, (∫ y : ℝ³, G y z ∂μ') ∂μ') := by
                  rfl
        calc
          aP ℓ i (aP ℓ j Φ) x
              = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ y : ℝ³, (∫ z : ℝ³, G y z ∂μ') ∂μ') := hL
          _ = (1 / ℓ ^ 3) * (1 / ℓ ^ 3) * (∫ z : ℝ³, (∫ y : ℝ³, G y z ∂μ') ∂μ') := by
                rw [hswap]
          _ = aP ℓ j (aP ℓ i Φ) x := hR.symm


end BoseGases

end Submission
