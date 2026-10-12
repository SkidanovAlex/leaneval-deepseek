import Mathlib
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3FibreQ_int`

The integrability of the one-slot fibre pairing

    `x ↦ conj (Ψ x) * (w (x j) * ∫ u, conj (w u) * Ξ (x[j ↦ u]))`

for `Ψ, Ξ ∈ L²(X_n)` and `w` bounded, compactly supported and a.e.-strongly measurable.

The ingredients are

* `qmp_update_slice` — the slice map `(x, u) ↦ x[j ↦ u]` is quasi-measure-preserving for
  Lebesgue measure (the preimage of a null set is null).  This makes the joint integrands
  a.e.-strongly measurable, and it gives the a.e.-measurability of the `u`-sections;
* `lintegral_indicator_update` — the fibre identity
  `∫⁻ x, 1_K(x j) * (∫⁻ u, ‖Ξ (x[j ↦ u])‖ₑ ^ 2) = volume K * ∫⁻ x, ‖Ξ x‖ₑ ^ 2`
  (Tonelli + the coordinate-peel substitution `lintegral_fibre_one`; the `j`-th coordinate of the
  slice does not survive, so the `K`-indicator collapses to the factor `volume K`);
* `enorm_integral_conj_mul_sq_le` — Cauchy–Schwarz for the Bochner integral in `enorm` form,
  which bounds `‖∫ u, conj (w u) Ξ (x[j ↦ u])‖ₑ ^ 2` by the product of the two `L²` masses.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1.  The slice map is quasi-measure-preserving -/

/-- **The slice map is quasi-measure-preserving.**  Overwriting the `i`-th coordinate of a
configuration is quasi-measure-preserving for Lebesgue measure: the preimage of a null set is
null.  The proof factors the slice map through the measure-preserving splitting
`MeasurableEquiv.piFinSuccAbove`, which turns it into the projection `((a,b),z) ↦ (z,b)`. -/
theorem qmp_update_volume (m : ℕ) (i : Fin (m + 1)) :
    Measure.QuasiMeasurePreserving
      (fun p : (Fin (m + 1) → E3) × E3 => Function.update p.1 i p.2)
      ((volume : Measure (Fin (m + 1) → E3)).prod (volume : Measure E3))
      (volume : Measure (Fin (m + 1) → E3)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => E3) i
  have hS : Measure.QuasiMeasurePreserving
      (fun p : (E3 × (Fin m → E3)) × E3 => (p.2, p.1.2)) volume volume :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).quasiMeasurePreserving.comp
      (QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
        (Measure.QuasiMeasurePreserving.id volume))
  have hT : (fun p : (Fin (m + 1) → E3) × E3 => Function.update p.1 i p.2)
      = e.symm ∘ (fun p : (E3 × (Fin m → E3)) × E3 => (p.2, p.1.2)) ∘ Prod.map e id := by
    funext p
    obtain ⟨x, z⟩ := p
    simp only [Function.comp_apply, Prod.map, id_eq]
    have h1 : e (Function.update x i z) = (z, i.removeNth x) := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        ← Fin.insertNth_removeNth, Fin.insertNth_apply_same, Fin.removeNth_insertNth]
    have h2 : (e x).2 = i.removeNth x := by
      rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
    rw [← e.symm_apply_apply (Function.update x i z), h1, h2]
  rw [hT]
  exact (he.symm.quasiMeasurePreserving).comp
    (hS.comp ((MeasurePreserving.prod he (MeasurePreserving.id volume)).quasiMeasurePreserving))

/-- The slice map is quasi-measure-preserving at every particle number. -/
theorem qmp_update_slice {n : ℕ} (j : Fin n) :
    Measure.QuasiMeasurePreserving (fun p : (Fin n → E3) × E3 => Function.update p.1 j p.2)
      ((volume : Measure (Fin n → E3)).prod (volume : Measure E3))
      (volume : Measure (Fin n → E3)) := by
  match n, j with
  | m + 1, j => exact qmp_update_volume m j

/-! ## 2.  The coordinate insertion -/

/-- Overwriting the `j`-th coordinate of an inserted configuration re-inserts the new value. -/
lemma update_fibreIns {n : ℕ} (j : Fin n) (v u : E3) (x' : {k : Fin n // k ≠ j} → E3) :
    Function.update (fibreIns j v x') j u = fibreIns j u x' := by
  funext k
  by_cases h : k = j
  · subst h
    rw [Function.update_self, fibreIns_apply_self]
  · rw [Function.update_of_ne h]
    simp only [fibreIns]
    rw [dif_neg h, dif_neg h]

/-! ## 3.  The fibre identity for the `K`-indicator -/

/-- **The fibre identity.**  For a measurable `K ⊆ E3` of finite measure and `Ξ` a.e.-strongly
measurable,

    `∫⁻ x, 1_K(x j) * (∫⁻ u, ‖Ξ (x[j ↦ u])‖ₑ ^ 2) = volume K * ∫⁻ x, ‖Ξ x‖ₑ ^ 2`.

The `u`-integral does not depend on the `j`-th coordinate of `x`, so the `K`-indicator contributes
exactly `volume K`; the remaining double integral over `(u, x')` is the full `L²` mass of `Ξ`, by
the measure-preserving character of the insertion `(u, x') ↦ x'[j ↦ u]`. -/
theorem lintegral_indicator_update {n : ℕ} (j : Fin n) {K : Set E3} (hK : MeasurableSet K)
    (hKfin : (volume : Measure E3) K ≠ ⊤)
    {Ξ : Xn n → ℂ} (hΞ : AEStronglyMeasurable Ξ (volume : Measure (Xn n))) :
    ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
        * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)
      = (volume K) * ∫⁻ x, ‖Ξ x‖ₑ ^ 2 := by
  classical
  have hind : Measurable (fun y : E3 => K.indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    measurable_const.indicator hK
  have hindj : Measurable (fun x : Xn n => K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)) :=
    hind.comp (measurable_pi_apply j)
  -- joint a.e.-strong measurability of the slice
  have hjoint : AEStronglyMeasurable (fun p : Xn n × E3 => Ξ (Function.update p.1 j p.2))
      ((volume : Measure (Xn n)).prod (volume : Measure E3)) :=
    hΞ.comp_quasiMeasurePreserving (qmp_update_slice j)
  have hAj : AEMeasurable
      (fun p : Xn n × E3 => K.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 j)
        * ‖Ξ (Function.update p.1 j p.2)‖ₑ ^ 2)
      ((volume : Measure (Xn n)).prod (volume : Measure E3)) := by
    have h2 : AEMeasurable (fun p : Xn n × E3 => ‖Ξ (Function.update p.1 j p.2)‖ₑ ^ 2)
        ((volume : Measure (Xn n)).prod (volume : Measure E3)) := by
      have h3 := hjoint.enorm
      have h4 := h3.mul h3
      exact h4.congr (Filter.Eventually.of_forall fun p => by simp [pow_two, Pi.mul_apply])
    exact ((hindj.comp measurable_fst).aemeasurable).mul h2
  -- the left-hand side as a double integral, and Tonelli
  have hstep1 : ∀ x : Xn n, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
        * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)
      = ∫⁻ u : E3, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2 := by
    intro x
    refine (lintegral_const_mul' (K.indicator (fun _ => (1 : ℝ≥0∞)) (x j))
      (fun u : E3 => ‖Ξ (Function.update x j u)‖ₑ ^ 2) ?_).symm
    by_cases hx : x j ∈ K <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hswap : (∫⁻ x : Xn n, ∫⁻ u : E3, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
        * ‖Ξ (Function.update x j u)‖ₑ ^ 2)
      = ∫⁻ u : E3, ∫⁻ x : Xn n, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2 :=
    lintegral_lintegral_swap hAj
  -- the inner integral, for a.e. `u`
  have hsec : ∀ᵐ u ∂(volume : Measure E3), AEMeasurable
      (fun x : Xn n => K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
        * ‖Ξ (Function.update x j u)‖ₑ ^ 2) (volume : Measure (Xn n)) := by
    filter_upwards [hjoint.prodMk_right] with u hu
    have h3 : AEMeasurable (fun x : Xn n => ‖Ξ (Function.update x j u)‖ₑ ^ 2)
        (volume : Measure (Xn n)) := by
      have h4 := hu.enorm
      have h5 := h4.mul h4
      exact h5.congr (Filter.Eventually.of_forall fun p => by simp [pow_two, Pi.mul_apply])
    exact hindj.aemeasurable.mul h3
  have hinner : ∀ᵐ u ∂(volume : Measure E3),
      (∫⁻ x : Xn n, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2)
        = (volume K) * ∫⁻ x' : {k : Fin n // k ≠ j} → E3,
            ‖Ξ (fibreIns j u x')‖ₑ ^ 2 := by
    filter_upwards [hsec] with u hu
    calc ∫⁻ x : Xn n, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2
        = ∫⁻ v : E3, ∫⁻ x' : {k : Fin n // k ≠ j} → E3,
            K.indicator (fun _ => (1 : ℝ≥0∞)) (fibreIns j v x' j)
              * ‖Ξ (Function.update (fibreIns j v x') j u)‖ₑ ^ 2 :=
          lintegral_fibre_one j hu
      _ = ∫⁻ v : E3, K.indicator (fun _ => (1 : ℝ≥0∞)) v
            * (∫⁻ x' : {k : Fin n // k ≠ j} → E3, ‖Ξ (fibreIns j u x')‖ₑ ^ 2) :=
          lintegral_congr fun v => by
            rw [show (fun x' : {k : Fin n // k ≠ j} → E3 =>
                  K.indicator (fun _ => (1 : ℝ≥0∞)) (fibreIns j v x' j)
                    * ‖Ξ (Function.update (fibreIns j v x') j u)‖ₑ ^ 2)
                = fun x' : {k : Fin n // k ≠ j} → E3 =>
                    K.indicator (fun _ => (1 : ℝ≥0∞)) v * ‖Ξ (fibreIns j u x')‖ₑ ^ 2 from
              funext fun x' => by rw [fibreIns_apply_self, update_fibreIns]]
            rw [lintegral_const_mul' _ _
              (by
                by_cases hv : v ∈ K <;>
                  simp [Set.indicator_of_mem, Set.indicator_of_notMem, hv])]
      _ = (volume K) * ∫⁻ x' : {k : Fin n // k ≠ j} → E3,
            ‖Ξ (fibreIns j u x')‖ₑ ^ 2 := by
          rw [lintegral_mul_const _ hind, lintegral_indicator_const hK (1 : ℝ≥0∞), one_mul]
  -- the `L²` mass of `‖Ξ‖ₑ ^ 2`, in the `u`-outer order
  have hΞ2 : AEMeasurable (fun y : Xn n => ‖Ξ y‖ₑ ^ 2) (volume : Measure (Xn n)) := by
    have h3 := hΞ.enorm
    have h4 := h3.mul h3
    exact h4.congr (Filter.Eventually.of_forall fun p => by simp [pow_two, Pi.mul_apply])
  calc ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
        * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)
      = ∫⁻ x : Xn n, ∫⁻ u : E3, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2 := lintegral_congr hstep1
    _ = ∫⁻ u : E3, ∫⁻ x : Xn n, K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
          * ‖Ξ (Function.update x j u)‖ₑ ^ 2 := hswap
    _ = ∫⁻ u : E3, (volume K) * ∫⁻ x' : {k : Fin n // k ≠ j} → E3,
          ‖Ξ (fibreIns j u x')‖ₑ ^ 2 := lintegral_congr_ae hinner
    _ = (volume K) * ∫⁻ u : E3, ∫⁻ x' : {k : Fin n // k ≠ j} → E3,
          ‖Ξ (fibreIns j u x')‖ₑ ^ 2 :=
        lintegral_const_mul' (volume K)
          (fun u : E3 => ∫⁻ x' : {k : Fin n // k ≠ j} → E3, ‖Ξ (fibreIns j u x')‖ₑ ^ 2) hKfin
    _ = (volume K) * ∫⁻ x, ‖Ξ x‖ₑ ^ 2 := by
        rw [← lintegral_fibre_one j hΞ2]

/-! ## 4.  The `L²` bound for the fibre operator -/

/-- **The one-slot fibre operator is bounded on `L²`.**  For `Ξ ∈ L²` and a bounded, compactly
supported, a.e.-strongly measurable `w`, the function
`x ↦ w (x j) * ∫ u, conj (w u) Ξ (x[j ↦ u])` is square-integrable. -/
theorem memLp_fibreUpdate {n : ℕ} (j : Fin n) {Ξ : Xn n → ℂ}
    (hΞ : MemLp Ξ 2 (volume : Measure (Xn n)))
    {w : E3 → ℂ} (hwc : AEStronglyMeasurable w (volume : Measure E3))
    (hwb : ∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) (hwcs : HasCompactSupport w) :
    MemLp (fun x : Xn n => w (x j) * ∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u))
      2 (volume : Measure (Xn n)) := by
  classical
  obtain ⟨C, hC⟩ := hwb
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := le_max_right C 0
  have hCz : ∀ z : E3, ‖w z‖ ≤ C' := fun z => le_trans (hC z) (le_max_left C 0)
  set K : Set E3 := tsupport w with hKdef
  have hKc : IsCompact K := hwcs.isCompact
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : (volume : Measure E3) K < ⊤ := hKc.measure_lt_top
  have hKne : (volume : Measure E3) K ≠ ⊤ := hKfin.ne
  have hw0 : ∀ z : E3, z ∉ K → w z = 0 := by
    intro z hz
    by_contra h
    exact hz (subset_tsupport w (show z ∈ Function.support w from h))
  have hind : Measurable (fun y : E3 => K.indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    measurable_const.indicator hKm
  have hindj : Measurable (fun x : Xn n => K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)) :=
    hind.comp (measurable_pi_apply j)
  -- the pointwise support bound
  have hsupp : ∀ z : E3, ‖w z‖ₑ ≤ ENNReal.ofReal C' * K.indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, mul_one, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hCz z)
    · rw [Set.indicator_of_notMem hz, mul_zero, hw0 z hz]
      simp
  -- joint a.e.-strong measurability
  have hjointΞ : AEStronglyMeasurable (fun p : Xn n × E3 => Ξ (Function.update p.1 j p.2))
      ((volume : Measure (Xn n)).prod (volume : Measure E3)) :=
    hΞ.aestronglyMeasurable.comp_quasiMeasurePreserving (qmp_update_slice j)
  have hjoint : AEStronglyMeasurable
      (fun p : Xn n × E3 => (starRingEnd ℂ) (w p.2) * Ξ (Function.update p.1 j p.2))
      ((volume : Measure (Xn n)).prod (volume : Measure E3)) :=
    ((hwc.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Xn n)))
        (ν := (volume : Measure E3)))).star).mul hjointΞ
  -- Cauchy–Schwarz for the inner integral, a.e. in `x`
  have hCS : ∀ᵐ x ∂(volume : Measure (Xn n)),
      ‖∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2
        ≤ (∫⁻ u : E3, ‖w u‖ₑ ^ 2) * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2) := by
    filter_upwards [hjointΞ.prodMk_left] with x hx
    exact enorm_integral_conj_mul_sq_le hwc.aemeasurable hx.aemeasurable
  -- the pointwise bound
  have hpt : ∀ᵐ x ∂(volume : Measure (Xn n)),
      ‖w (x j) * ∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2
        ≤ ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
            * (K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
                * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) := by
    filter_upwards [hCS] with x hx
    have h1 : K.indicator (fun _ => (1 : ℝ≥0∞)) (x j) ^ 2
        = K.indicator (fun _ => (1 : ℝ≥0∞)) (x j) := by
      by_cases h : x j ∈ K <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc ‖w (x j) * ∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2
        = ‖w (x j)‖ₑ ^ 2
            * ‖∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2 := by
          rw [enorm_mul, mul_pow]
      _ ≤ (ENNReal.ofReal C' * K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)) ^ 2
            * ((∫⁻ u : E3, ‖w u‖ₑ ^ 2)
                * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) :=
          mul_le_mul' (pow_le_pow_left' (hsupp (x j)) 2) hx
      _ = ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
            * (K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
                * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) := by
          rw [mul_pow, h1]
          ring
  -- the a.e.-measurability of the `x`-dependent factor
  have hG : AEMeasurable (fun x : Xn n => K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
      * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) (volume : Measure (Xn n)) := by
    have h2 : AEMeasurable (fun x : Xn n => ∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)
        (volume : Measure (Xn n)) := by
      have h3 : AEMeasurable (fun p : Xn n × E3 => ‖Ξ (Function.update p.1 j p.2)‖ₑ ^ 2)
          ((volume : Measure (Xn n)).prod (volume : Measure E3)) := by
        have h4 := hjointΞ.enorm
        have h5 := h4.mul h4
        exact h5.congr (Filter.Eventually.of_forall fun p => by simp [pow_two, Pi.mul_apply])
      exact h3.lintegral_prod_right'
    exact hindj.aemeasurable.mul h2
  -- integrability of the kernel's `L²` mass
  have hwfin : ∫⁻ u : E3, ‖w u‖ₑ ^ 2 < ⊤ := by
    have hle : ∫⁻ u : E3, ‖w u‖ₑ ^ 2
        ≤ ENNReal.ofReal C' ^ 2 * (volume : Measure E3) K := by
      calc ∫⁻ u : E3, ‖w u‖ₑ ^ 2
          ≤ ∫⁻ u : E3, (ENNReal.ofReal C' * K.indicator (fun _ => (1 : ℝ≥0∞)) u) ^ 2 :=
            lintegral_mono fun u => pow_le_pow_left' (hsupp u) 2
        _ = ∫⁻ u : E3, ENNReal.ofReal C' ^ 2 * K.indicator (fun _ => (1 : ℝ≥0∞)) u := by
            refine lintegral_congr fun u => ?_
            rw [mul_pow]
            by_cases h : u ∈ K <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
        _ = ENNReal.ofReal C' ^ 2 * ∫⁻ u : E3, K.indicator (fun _ => (1 : ℝ≥0∞)) u :=
            lintegral_const_mul' _ _
              (by
                rw [pow_two]
                exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        _ = ENNReal.ofReal C' ^ 2 * (volume : Measure E3) K := by
            rw [lintegral_indicator_const hKm (1 : ℝ≥0∞), one_mul]
    exact lt_of_le_of_lt hle (by
      rw [pow_two]
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hKfin)
  -- the `L²` mass of `Ξ`
  have hΞfin : ∫⁻ x : Xn n, ‖Ξ x‖ₑ ^ 2 < ⊤ := by
    have h := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
      two_ne_zero ENNReal.ofNat_ne_top hΞ.eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h
  -- the `L²` bound
  have hbound : ∫⁻ x : Xn n, ‖w (x j) * ∫ u : E3,
        (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2
      ≤ ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
          * ((volume K) * ∫⁻ x : Xn n, ‖Ξ x‖ₑ ^ 2) :=
    calc ∫⁻ x : Xn n, ‖w (x j) * ∫ u : E3,
            (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)‖ₑ ^ 2
        ≤ ∫⁻ x : Xn n, ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
            * (K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
                * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
            * ∫⁻ x : Xn n, (K.indicator (fun _ => (1 : ℝ≥0∞)) (x j)
                * (∫⁻ u : E3, ‖Ξ (Function.update x j u)‖ₑ ^ 2)) :=
          lintegral_const_mul'' _ hG
      _ = ENNReal.ofReal C' ^ 2 * (∫⁻ u : E3, ‖w u‖ₑ ^ 2)
            * ((volume K) * ∫⁻ x : Xn n, ‖Ξ x‖ₑ ^ 2) := by
          rw [lintegral_indicator_update j hKm hKne hΞ.aestronglyMeasurable]
  have hmeasF : AEStronglyMeasurable (fun x : Xn n => w (x j) * ∫ u : E3,
      (starRingEnd ℂ) (w u) * Ξ (Function.update x j u)) volume := ((hwc.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (μ := fun _ : Fin n => (volume : Measure E3)) j)).mul
        hjoint.integral_prod_right')
  rw [memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2)
    two_ne_zero ENNReal.ofNat_ne_top hmeasF]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top
      (by rw [pow_two]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      hwfin)
    (ENNReal.mul_lt_top hKfin hΞfin))

/-! ## 5.  The target -/

theorem PB3FibreQ_int {n : ℕ} (j : Fin n) {Ψ Ξ : Work.BoseDict.Xn n → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ 2 (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)))
    (hΞ : MeasureTheory.MemLp Ξ 2 (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)))
    {w : EuclideanSpace ℝ (Fin 3) → ℂ} (hwc : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (hwb : ∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) (hwcs : HasCompactSupport w) :
    MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn n => (starRingEnd ℂ) (Ψ x)
        * (w (x j) * (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
            * Ξ (Function.update x j u))))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)) := by
  have hconj : MemLp (fun x : Xn n => (starRingEnd ℂ) (Ψ x)) 2 (volume : Measure (Xn n)) := by
    have h' : (star Ψ) = fun x : Xn n => (starRingEnd ℂ) (Ψ x) := by
      funext x
      rw [Pi.star_apply, starRingEnd_apply]
    have hΨ_star := hΨ.star
    rw [h'] at hΨ_star
    exact hΨ_star
  have hW := memLp_fibreUpdate j hΞ hwc hwb hwcs
  exact (MemLp.integrable_mul hconj hW).congr
    (Filter.Eventually.of_forall fun x => rfl)

end Work.BoseBoxFock
