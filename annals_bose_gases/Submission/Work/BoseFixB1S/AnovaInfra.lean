import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.AnovaInfra` — the product-measure (Fubini) infrastructure for the ANOVA bound

The target `Work.BoseFixB1S.anovaLeCnPlusB1Fix` reduces, after the identification of the fibre
measure `volume.restrict (Set.univ.pi A)` with the product measure `Measure.pi (fun _ => ν)`
(`ν = volume.restrict A`, `restrict_pi_pi` + `volume_pi`), to the **ANOVA / Efron–Stein
inequality on a product measure**:

    Var_π(f) ≤ Σ_i ∫ (f x − E_i f x)² ∂π,

with `π = Measure.pi (fun _ : Fin N => ν)` and `E_i f x = (ν univ).toReal⁻¹ ∫ z, f (update x i z) ∂ν`.

This module supplies the Fubini/peel primitives that the ANOVA proof consumes:

* `pi_peel` — integrating out one coordinate of the product measure multiplies the integral of a
  function by the total mass of that coordinate: the `Measure.pi` "tower property"
  `∫_π E_i G = ∫_π G` in the unnormalised form.  (Proven by `MeasurePreserving piFinSuccAbove`,
  Fubini and `Fin.insertNth` manipulations; the proof follows the scratch development
  `Scratch/anova/dev1.lean` of the previous session of this project.)
* `aestronglyMeasurable_pi_coordMean` — the coordinate mean of an a.e. strongly measurable
  function is a.e. strongly measurable.
* `ae_aestronglyMeasurable_pi_slice` — for a.e. configuration `x`, the slice `z ↦ f (update x i z)`
  is a.e. strongly measurable.  This is what makes the Bochner integrals in the ANOVA statement
  the true conditional means (and not the `integral_undef` value `0`).
* `integral_sq_pi_coordMean_le` — the coordinate mean is an `L²`-contraction
  (`∫_π (E_i u)² ≤ ∫_π u²`), the normalised Cauchy–Schwarz/Jensen bound on the fibre.

These are the only measure-theoretic inputs of the ANOVA step; the combinatorial telescoping is
proved separately (`Work.BoseFixB1S.piAnovaLeCoordMeans`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

variable {α : Type*} [MeasurableSpace α]

/-- **One-coordinate peel.**  Integrating out one coordinate of a product measure multiplies the
integral of a function by the total mass of that coordinate's measure.  This is the (unnormalised)
tower property of the coordinate mean `E_j G x = ∫ z, G (update x j z) ∂ν`. -/
theorem pi_peel (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    {k : ℕ} (j : Fin (k + 1)) {G : (Fin (k + 1) → α) → ℝ}
    (hG : Integrable G (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  have he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j := rfl
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod (Measure.pi (fun _ : Fin k => ν)))
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hK : Integrable (fun p : α × (Fin k → α) => G (e.symm p))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    (hmp'.integrable_comp_emb hemb (g := G)).mpr hG
  have hE : ((e.symm : α × (Fin k → α) → (Fin (k + 1) → α)))
      = fun f => Fin.insertNth j f.1 f.2 := by
    rw [he]
    funext f mm
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hpoint : ∀ (p : α × (Fin k → α)) (z : α),
      Function.update (e.symm p) j z = e.symm (z, p.2) := by
    rintro ⟨a, y⟩ z
    rw [hE]
    exact Fin.update_insertNth (α := fun _ : Fin (k + 1) => α) j a z y
  have h1 : (∫ x, (∫ z, G (Function.update x j z) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ p : α × (Fin k → α), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    have h := hmp'.integral_comp hemb (fun x => ∫ z, G (Function.update x j z) ∂ν)
    rw [← h]
    simp only [hpoint]
  have hKw : Integrable (fun w : Fin k → α => ∫ z, G (e.symm (z, w)) ∂ν)
      (Measure.pi (fun _ : Fin k => ν)) := hK.integral_prod_right
  have hT : Integrable (fun p : α × (Fin k → α) => ∫ z, G (e.symm (z, p.2)) ∂ν)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    simpa using hKw.comp_snd ν
  have h2 : (∫ p : α × (Fin k → α), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))))
      = (ν Set.univ).toReal * ∫ p : α × (Fin k → α), G (e.symm p)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    rw [integral_prod_symm _ hT]
    have hc : ∀ w : Fin k → α, (∫ _a : α, (∫ z, G (e.symm (z, w)) ∂ν) ∂ν)
        = (ν Set.univ).toReal * (∫ z, G (e.symm (z, w)) ∂ν) := by
      intro w
      rw [integral_const, Measure.real_def, smul_eq_mul]
    simp only [hc]
    rw [integral_const_mul, ← integral_prod_symm _ hK]
  calc
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ p : α × (Fin k → α), (∫ z, G (e.symm (z, p.2)) ∂ν)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h1
    _ = (ν Set.univ).toReal * ∫ p : α × (Fin k → α), G (e.symm p)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h2
    _ = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [hmp'.integral_comp hemb G]

/-- The pointwise relation between the peeled coordinates and `Function.update`: for the
measurable equivalence `piFinSuccAbove` in the coordinate `j`, updating the `j`-th coordinate of
`e.symm p` is the same as inserting the new value and keeping the remaining coordinates `p.2`. -/
theorem piFinSuccAbove_update {k : ℕ} (j : Fin (k + 1)) (p : α × (Fin k → α)) (z : α) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j).symm p) j z
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j).symm (z, p.2) := by
  have hE : (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j).symm :
        α × (Fin k → α) → (Fin (k + 1) → α)))
      = fun f => Fin.insertNth j f.1 f.2 := by
    funext f mm
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [hE]
  exact Fin.update_insertNth (α := fun _ : Fin (k + 1) => α) j p.1 z p.2

/-- For a.e. configuration `x`, the slice `z ↦ f (Function.update x j z)` of an a.e. strongly
measurable function on the product measure is a.e. strongly measurable.  This is what makes the
coordinate means of `f` the true conditional expectations (rather than the `integral_undef`
value `0`). -/
theorem ae_aestronglyMeasurable_pi_slice (ν : Measure α) [SigmaFinite ν]
    {k : ℕ} (j : Fin (k + 1)) {f : (Fin (k + 1) → α) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      AEStronglyMeasurable (fun z => f (Function.update x j z)) ν := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν)) (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hf' : AEStronglyMeasurable (fun p : α × (Fin k → α) => f (e.symm p)) (ν.prod ρ) :=
    (hmp'.aestronglyMeasurable_comp_iff hemb).mpr hf
  have hslice : ∀ᵐ r ∂ρ, AEStronglyMeasurable (fun z => f (e.symm (z, r))) ν :=
    AEStronglyMeasurable.prodMk_right hf'
  have hq : Measure.QuasiMeasurePreserving (fun x : Fin (k + 1) → α => (e x).2)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) ρ :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).comp
      (MeasurePreserving.quasiMeasurePreserving hmp)
  filter_upwards [hq.tendsto_ae.eventually hslice] with x hx
  have hfun : (fun z => f (Function.update x j z)) = fun z => f (e.symm (z, (e x).2)) := by
    funext z
    rw [← piFinSuccAbove_update (α := α) j (e x) z, MeasurableEquiv.symm_apply_apply]
  rw [hfun]
  exact hx

/-- The coordinate mean of an a.e. strongly measurable function is a.e. strongly measurable. -/
theorem aestronglyMeasurable_pi_coordMean (ν : Measure α) [SigmaFinite ν]
    {k : ℕ} (j : Fin (k + 1)) {f : (Fin (k + 1) → α) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    AEStronglyMeasurable (fun x => ∫ z, f (Function.update x j z) ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν)) (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hf' : AEStronglyMeasurable (fun p : α × (Fin k → α) => f (e.symm p)) (ν.prod ρ) :=
    (hmp'.aestronglyMeasurable_comp_iff hemb).mpr hf
  have hswap : AEStronglyMeasurable (fun q : (Fin k → α) × α => f (e.symm (q.2, q.1)))
      (ρ.prod ν) := AEStronglyMeasurable.prod_swap hf'
  have hleft : AEStronglyMeasurable (fun r : Fin k → α => ∫ z, f (e.symm (z, r)) ∂ν) ρ :=
    AEStronglyMeasurable.integral_prod_right' hswap
  have hq : Measure.QuasiMeasurePreserving (fun x : Fin (k + 1) → α => (e x).2)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) ρ :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).comp
      (MeasurePreserving.quasiMeasurePreserving hmp)
  have hcomp := AEStronglyMeasurable.comp_quasiMeasurePreserving hleft hq
  refine hcomp.congr ?_
  filter_upwards with x
  refine integral_congr_ae ?_
  filter_upwards with z
  rw [← piFinSuccAbove_update (α := α) j (e x) z, MeasurableEquiv.symm_apply_apply]



/-! ## The `L²`-contraction of the coordinate mean

The coordinate mean `E_j u x = (ν univ).toReal⁻¹ ∫ z, u (update x j z) ∂ν` is an `L²`-contraction.
The proof avoids the (false) pointwise Cauchy–Schwarz route: it splits on the integrability of
`(E_j u)²`, uses the (unconditional) self-adjointness/tower identity
`∫ (E_j u)² = ∫ u · E_j u` — which follows from `pi_peel` applied to `u · E_j u` together with the
*unconditional* identity `∫ z, f z * c ∂ν = (∫ z, f z ∂ν) * c` (`integral_mul_const`) — and then
the integral Cauchy–Schwarz (`integral_mul_norm_le_Lp_mul_Lq`). -/

/-- **The `L²`-contraction of the coordinate mean.** -/
theorem integral_sq_pi_coordMean_le (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {u : (Fin (k + 1) → α) → ℝ}
    (hum : AEStronglyMeasurable u (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hu2 : Integrable (fun x => (u x) ^ 2) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∫ x, ((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      ≤ ∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  set V : ℝ := (ν Set.univ).toReal with hVdef
  have hVpos : 0 < V := hν
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hMaesm : AEStronglyMeasurable
      (fun x : Fin (k + 1) → α => (1 / V) * ∫ z, u (Function.update x j z) ∂ν)
      (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
    (aestronglyMeasurable_pi_coordMean ν j hum).const_mul (1 / V)
  by_cases hM2 : Integrable
      (fun x : Fin (k + 1) → α => ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2)
      (Measure.pi (fun _ : Fin (k + 1) => ν))
  · -- the non-degenerate case: `(E_j u)²` is integrable
    -- integrability of the product `u · (E_j u)`
    have huM : Integrable
        (fun x : Fin (k + 1) → α => u x * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν))
        (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      refine Integrable.mono' (g := fun x : Fin (k + 1) → α =>
        ((u x) ^ 2 + ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2) / 2)
        ((hu2.add hM2).div_const 2) (hum.mul hMaesm) ?_
      filter_upwards with x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h := sq_nonneg (|u x| - |((1 / V) * ∫ z, u (Function.update x j z) ∂ν)|)
      rw [sub_sq, sq_abs, sq_abs] at h
      nlinarith [h]
    -- the peel
    have hpeel := pi_peel ν j huM
    -- the pointwise evaluation of the peeled integrand
    have hpoint : ∀ x : Fin (k + 1) → α,
        (∫ z, u (Function.update x j z)
            * ((1 / V) * ∫ z', u (Function.update (Function.update x j z) j z') ∂ν) ∂ν)
          = V * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2 := by
      intro x
      have hfun : (fun z => u (Function.update x j z)
            * ((1 / V) * ∫ z', u (Function.update (Function.update x j z) j z') ∂ν))
          = fun z => u (Function.update x j z)
            * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) := by
        funext z
        congr 1
        congr 1
        apply integral_congr_ae
        filter_upwards with z'
        rw [Function.update_idem]
      rw [hfun, integral_mul_const]
      field_simp
    have h1 : (∫ x, (∫ z, u (Function.update x j z)
            * ((1 / V) * ∫ z', u (Function.update (Function.update x j z) j z') ∂ν) ∂ν)
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ x, V * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    have h2 : (∫ x, V * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = V * ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := integral_const_mul _ _
    -- the tower identity `∫ (E_j u)² = ∫ u · E_j u`
    have htower : ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
        = ∫ x, u x * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν)
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
      have h := hpeel
      rw [h1, h2] at h
      exact mul_left_cancel₀ hVne h
    -- integral Cauchy–Schwarz
    have hMemU : MemLp u (2 : ℝ≥0∞) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      (memLp_two_iff_integrable_sq hum).mpr hu2
    have hMemM : MemLp (fun x : Fin (k + 1) → α => (1 / V) * ∫ z, u (Function.update x j z) ∂ν)
        (2 : ℝ≥0∞) (Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      (memLp_two_iff_integrable_sq hMaesm).mpr hM2
    rw [← ENNReal.ofReal_ofNat 2] at hMemU hMemM
    have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := Measure.pi (fun _ : Fin (k + 1) => ν))
      (f := u) (g := fun x : Fin (k + 1) → α => (1 / V) * ∫ z, u (Function.update x j z) ∂ν)
      Real.HolderConjugate.two_two hMemU hMemM
    have hcs_calc : ∫ x, u x * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν)
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
        ≤ Real.sqrt (∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
          * Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
              ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) := by
      calc ∫ x, u x * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν)
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
          ≤ ∫ x, ‖u x * ((1 / V) * ∫ z, u (Function.update x j z) ∂ν)‖
              ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
            integral_mono_ae huM huM.norm (Filter.Eventually.of_forall (fun x => le_abs_self _))
        _ = ∫ x, ‖u x‖ * ‖(1 / V) * ∫ z, u (Function.update x j z) ∂ν‖
              ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [norm_mul]
        _ ≤ (∫ x, ‖u x‖ ^ (2 : ℝ) ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) ^ (1 / (2 : ℝ))
              * (∫ x, ‖(1 / V) * ∫ z, u (Function.update x j z) ∂ν‖ ^ (2 : ℝ)
                  ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) ^ (1 / (2 : ℝ)) := hholder
        _ = Real.sqrt (∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
              * Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
                  ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) := by
            congr 1
            · rw [Real.sqrt_eq_rpow]
              congr 1
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
            · rw [Real.sqrt_eq_rpow]
              congr 1
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    have hcs : ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
        ≤ Real.sqrt (∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
          * Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
              ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) := htower.trans_le hcs_calc
    -- arithmetic: `a ≤ √b · √a` gives `a ≤ b`
    have ha0 : 0 ≤ ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := integral_nonneg (fun x => sq_nonneg _)
    have hb0 : 0 ≤ ∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) :=
      integral_nonneg (fun x => sq_nonneg _)
    have hsq : Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        ≤ Real.sqrt (∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) := by
      rcases eq_or_lt_of_le ha0 with h0 | h0
      · rw [← h0, Real.sqrt_zero]
        exact Real.sqrt_nonneg _
      · have hsa : 0 < Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν))) := Real.sqrt_pos.mpr h0
        refine le_of_mul_le_mul_right ?_ hsa
        rw [← sq, Real.sq_sqrt ha0]
        exact hcs
    calc ∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
        = (Real.sqrt (∫ x, ((1 / V) * ∫ z, u (Function.update x j z) ∂ν) ^ 2
            ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))) ^ 2 := (Real.sq_sqrt ha0).symm
      _ ≤ (Real.sqrt (∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
      _ = ∫ x, (u x) ^ 2 ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := Real.sq_sqrt hb0
  · -- the degenerate case: the left-hand side is `0` by `integral_undef`
    rw [integral_undef hM2]
    exact integral_nonneg (fun x => sq_nonneg (u x))

end Work.BoseFixB1S
