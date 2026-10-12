import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1S.PiCoordMeanL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.PiAnovaAux` — the conditional-expectation calculus for the ANOVA bound

Helper lemmas for the ANOVA/Efron–Stein inequality on a product measure
(`Submission/Work/BoseFixB1S/piAnovaLeCoordMeans.lean`).  Writing
`E_j u x = (ν univ).toReal⁻¹ ∫ z, u (update x j z) ∂ν` for the coordinate mean, this module
provides:

* `ae_integrable_pi_slice` — a.e. integrability of the slices of an integrable function;
* `pi_tower_left` / `pi_tower_right` — the tower (self-adjointness) identities
  `∫ u w = ∫ u (E_j w)` for `u` independent of coordinate `j`, and `∫ u w = ∫ (E_j u) w` for `w`
  independent of coordinate `j` (both from the Bochner peel `pi_peel` and the *unconditional*
  identity `∫ z, f z * c ∂ν = (∫ z, f z ∂ν) * c`);
* `pi_coordMean_idem` — `E_j w = w` for `w` independent of coordinate `j`;
* `pi_coordMean_sub_ae` — a.e. linearity of `E_j`;
* the coordinate bookkeeping around the peel `MeasurableEquiv.piFinSuccAbove`
  (`piFinSuccAbove_symm_update`, `piFinSuccAbove_lift`), i.e. the fact that a function independent
  of the peeled coordinate is the lift of its restriction to the remaining coordinates;
* `lintegral_pi_lift` / `integral_pi_lift` — the transport of (lin)integrals of lifted functions.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

variable {α : Type*} [MeasurableSpace α]

/-- **A.e. integrability of the slices** of an integrable function on the product measure. -/
theorem ae_integrable_pi_slice (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    {k : ℕ} (j : Fin (k + 1)) {f : (Fin (k + 1) → α) → ℝ}
    (hf : Integrable f (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin (k + 1) => ν)),
      Integrable (fun z => f (Function.update x j z)) ν := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  let π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν)
  have hmp : MeasurePreserving e π (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod ρ) π := MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hG : Integrable (fun p : α × (Fin k → α) => f (e.symm p)) (ν.prod ρ) :=
    (hmp'.integrable_comp_emb hemb).mpr hf
  have hslice : ∀ᵐ r ∂ρ, Integrable (fun z => f (e.symm (z, r))) ν := hG.prod_left_ae
  have hq : Measure.QuasiMeasurePreserving (fun x : Fin (k + 1) → α => (e x).2) π ρ :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ρ)).comp
      (MeasurePreserving.quasiMeasurePreserving hmp)
  filter_upwards [hq.tendsto_ae.eventually hslice] with x hx
  have hfun : (fun z => f (e.symm (z, (e x).2))) = fun z => f (Function.update x j z) := by
    funext z
    have h1 : Function.update x j z = e.symm (z, (e x).2) := by
      have h2 : Function.update (e.symm (e x)) j z = e.symm (z, (e x).2) :=
        piFinSuccAbove_update j (e x) z
      rwa [MeasurableEquiv.symm_apply_apply e x] at h2
    rw [h1]
  rwa [hfun] at hx

/-- **The tower identity, right form**: `∫ u w = ∫ (E_j u)·w` for `w` independent of coordinate
`j`. -/
theorem pi_tower_right (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {u w : (Fin (k + 1) → α) → ℝ}
    (hw : ∀ x z, w (Function.update x j z) = w x)
    (hint : Integrable (fun x => u x * w x) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∫ x, u x * w x ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, ((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) * w x
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  have hVne : (ν Set.univ).toReal ≠ 0 := ne_of_gt hν
  have hpeel := pi_peel ν j hint
  have hpoint : ∀ x : Fin (k + 1) → α,
      ∫ z, u (Function.update x j z) * w (Function.update x j z) ∂ν
        = (ν Set.univ).toReal
          * (((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) * w x) := by
    intro x
    have hfun : (fun z => u (Function.update x j z) * w (Function.update x j z))
        = fun z => u (Function.update x j z) * w x := by
      funext z
      rw [hw x z]
    rw [hfun, integral_mul_const]
    field_simp
  have h1 : ∫ x, (∫ z, u (Function.update x j z) * w (Function.update x j z) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, (ν Set.univ).toReal
          * (((1 / (ν Set.univ).toReal) * ∫ z, u (Function.update x j z) ∂ν) * w x)
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint x
  rw [h1, integral_const_mul] at hpeel
  exact (mul_left_cancel₀ hVne hpeel).symm

/-- **The tower identity, left form**: `∫ u w = ∫ u·(E_j w)` for `u` independent of coordinate
`j`. -/
theorem pi_tower_left (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {u w : (Fin (k + 1) → α) → ℝ}
    (hu : ∀ x z, u (Function.update x j z) = u x)
    (hint : Integrable (fun x => u x * w x) (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    ∫ x, u x * w x ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, u x * ((1 / (ν Set.univ).toReal) * ∫ z, w (Function.update x j z) ∂ν)
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  have hVne : (ν Set.univ).toReal ≠ 0 := ne_of_gt hν
  have hpeel := pi_peel ν j hint
  have hpoint : ∀ x : Fin (k + 1) → α,
      ∫ z, u (Function.update x j z) * w (Function.update x j z) ∂ν
        = (ν Set.univ).toReal
          * (u x * ((1 / (ν Set.univ).toReal) * ∫ z, w (Function.update x j z) ∂ν)) := by
    intro x
    have hfun : (fun z => u (Function.update x j z) * w (Function.update x j z))
        = fun z => u x * w (Function.update x j z) := by
      funext z
      rw [hu x z]
    rw [hfun, integral_const_mul]
    field_simp
  have h1 : ∫ x, (∫ z, u (Function.update x j z) * w (Function.update x j z) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, (ν Set.univ).toReal
          * (u x * ((1 / (ν Set.univ).toReal) * ∫ z, w (Function.update x j z) ∂ν))
          ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
    apply integral_congr_ae
    filter_upwards with x
    exact hpoint x
  rw [h1, integral_const_mul] at hpeel
  exact (mul_left_cancel₀ hVne hpeel).symm

/-- **Idempotence**: the coordinate mean of a function independent of coordinate `j` is the
function itself (pointwise). -/
theorem pi_coordMean_idem (ν : Measure α) [IsFiniteMeasure ν] (hν : 0 < (ν Set.univ).toReal)
    {k : ℕ} (j : Fin (k + 1)) {w : (Fin (k + 1) → α) → ℝ}
    (hw : ∀ x z, w (Function.update x j z) = w x) (x : Fin (k + 1) → α) :
    (1 / (ν Set.univ).toReal) * ∫ z, w (Function.update x j z) ∂ν = w x := by
  have hVne : (ν Set.univ).toReal ≠ 0 := ne_of_gt hν
  have hfun : (fun z => w (Function.update x j z)) = fun _ => w x := funext (fun z => hw x z)
  rw [hfun, integral_const, Measure.real_def, smul_eq_mul]
  field_simp

/-- **A.e. linearity** of the coordinate mean. -/
theorem pi_coordMean_sub_ae (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν]
    {k : ℕ} (j : Fin (k + 1)) {u w : (Fin (k + 1) → α) → ℝ}
    (hu : Integrable u (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hw : Integrable w (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (fun x => (1 / (ν Set.univ).toReal) * ∫ z, (u - w) (Function.update x j z) ∂ν)
      =ᵐ[Measure.pi (fun _ : Fin (k + 1) => ν)]
      fun x => (1 / (ν Set.univ).toReal) * (∫ z, u (Function.update x j z) ∂ν)
        - (1 / (ν Set.univ).toReal) * (∫ z, w (Function.update x j z) ∂ν) := by
  filter_upwards [ae_integrable_pi_slice ν j hu, ae_integrable_pi_slice ν j hw] with x hu' hw'
  have hfun : (fun z => (u - w) (Function.update x j z))
      = fun z => u (Function.update x j z) - w (Function.update x j z) := by
    funext z
    rw [Pi.sub_apply]
  rw [hfun, integral_sub hu' hw']
  ring

/-- The `piFinSuccAbove` parametrisation: replacing the peeled coordinate of `e.symm p` is the
same as replacing the peeled coordinate of the pair. -/
theorem piFinSuccAbove_symm_update {m : ℕ} (j : Fin (m + 1)) (p : α × (Fin m → α)) (a : α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j).symm (a, p.2)
      = Function.update
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j).symm p) j a := by
  have key : ∀ q : α × (Fin m → α),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j).symm q
        = Fin.insertNth (α := fun _ : Fin (m + 1) => α) j q.1 q.2 := by
    intro q
    funext kk
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [key (a, p.2), key p]
  funext k
  by_cases hk : k = j
  · subst hk
    simp [Function.update_apply, Fin.insertNth_apply_same]
  · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hk
    rw [Function.update_apply, if_neg (Fin.succAbove_ne j m'), Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]

/-- **Lifting**: a function on the product which is independent of the peeled coordinate is the
lift of its restriction to the remaining coordinates. -/
theorem piFinSuccAbove_lift {m : ℕ} (j : Fin (m + 1)) (z₀ : α)
    {H : (Fin (m + 1) → α) → ℝ} {g : (Fin m → α) → ℝ}
    (hg : ∀ r, g r = H ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j).symm (z₀, r)))
    (hH : ∀ x z, H (Function.update x j z) = H x) :
    ∀ x, H x = g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j) x).2 := by
  intro x
  have h1 : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j).symm
        (z₀, ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j) x).2)
      = Function.update x j z₀ := by
    rw [piFinSuccAbove_symm_update]
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hg ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) j) x).2, h1, hH]

/-- **Transport of `lintegral`s of lifted functions.** -/
theorem lintegral_pi_lift (ν : Measure α) [SigmaFinite ν] {k : ℕ} (j : Fin (k + 1))
    {Φ : (Fin k → α) → ℝ≥0∞} (hΦ : AEMeasurable Φ (Measure.pi (fun _ : Fin k => ν))) :
    ∫⁻ x, Φ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j) x).2
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = (ν Set.univ) * ∫⁻ r, Φ r ∂(Measure.pi (fun _ : Fin k => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  let π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν)
  have hmp : MeasurePreserving e π (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hmap : Measure.map (Prod.snd ∘ e) π = (ν Set.univ) • ρ := by
    rw [← Measure.map_map measurable_snd (MeasurableEquiv.measurable e), hmp.map_eq,
      Measure.map_snd_prod]
  calc ∫⁻ x, Φ ((e x).2) ∂π
      = ∫⁻ r, Φ r ∂(Measure.map (Prod.snd ∘ e) π) :=
        (lintegral_map' (by rw [hmap]; exact hΦ.smul_measure (ν Set.univ))
          (measurable_snd.comp (MeasurableEquiv.measurable e)).aemeasurable).symm
    _ = ∫⁻ r, Φ r ∂((ν Set.univ) • ρ) := by rw [hmap]
    _ = (ν Set.univ) * ∫⁻ r, Φ r ∂ρ := by
        rw [lintegral_smul_measure (ν Set.univ) Φ, smul_eq_mul]

/-- The basic `apply` lemmas for the peel parametrisation. -/
theorem piFinSuccAbove_symm_apply_same {m : ℕ} (i : Fin (m + 1)) (a : α) (r : Fin m → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, r) i = a := by
  have key : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, r)
      = Fin.insertNth (α := fun _ : Fin (m + 1) => α) i a r := by
    funext kk
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [key, Fin.insertNth_apply_same]

theorem piFinSuccAbove_symm_apply_succAbove {m : ℕ} (i : Fin (m + 1)) (a : α) (r : Fin m → α)
    (j : Fin m) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, r) (i.succAbove j)
      = r j := by
  have key : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, r)
      = Fin.insertNth (α := fun _ : Fin (m + 1) => α) i a r := by
    funext kk
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  rw [key, Fin.insertNth_apply_succAbove]

/-- At a *non-inserted* slot, updating the insertion is the insertion of the updated rest
tuple. -/
theorem piFinSuccAbove_symm_update_succAbove {m : ℕ} (i : Fin (m + 1)) (a : α) (r : Fin m → α)
    (j : Fin m) (z : α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, Function.update r j z)
      = Function.update
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (a, r))
          (i.succAbove j) z := by
  funext k
  by_cases hk : k = i
  · rw [hk]
    simp only [Function.update_apply, if_neg (Ne.symm (Fin.succAbove_ne i j)),
      piFinSuccAbove_symm_apply_same]
  · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hk
    by_cases hj : j' = j
    · subst hj
      simp only [Function.update_apply, if_pos rfl, piFinSuccAbove_symm_apply_succAbove]
    · simp only [Function.update_apply, if_neg (fun h => hj (Fin.succAbove_right_injective h)),
        if_neg (fun h => hj (Fin.succAbove_right_injective h)),
        piFinSuccAbove_symm_apply_succAbove, if_neg hj]

/-- The coordinate mean of a function independent of the slot `j` is again independent of the
slot `j` (pointwise). -/
theorem pi_coordMean_indep (ν : Measure α) {k : ℕ} (j k' : Fin (k + 1)) (hjk : k' ≠ j)
    {K : (Fin (k + 1) → α) → ℝ} (hK : ∀ x z, K (Function.update x j z) = K x) :
    ∀ x z, (fun y => (1 / (ν Set.univ).toReal) * ∫ z', K (Function.update y k' z') ∂ν)
        (Function.update x j z)
      = (fun y => (1 / (ν Set.univ).toReal) * ∫ z', K (Function.update y k' z') ∂ν) x := by
  intro x z
  show (1 / (ν Set.univ).toReal) * ∫ z', K (Function.update (Function.update x j z) k' z') ∂ν
    = (1 / (ν Set.univ).toReal) * ∫ z', K (Function.update x k' z') ∂ν
  congr 1
  apply integral_congr_ae
  filter_upwards with z'
  rw [Function.update_comm (Ne.symm hjk) z z' x, hK]

/-- The slot mean in the big space of the lift of `g` is the lift of the slot mean of `g`. -/
theorem pi_lift_coordMean (ν : Measure α) {m : ℕ} (i : Fin (m + 1)) (z₀ : α)
    {K : (Fin (m + 1) → α) → ℝ} {g : (Fin m → α) → ℝ}
    (hg : ∀ r, g r = K ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm (z₀, r)))
    (hK : ∀ x z, K (Function.update x i z) = K x) (j : Fin m) (x : Fin (m + 1) → α) :
    (1 / (ν Set.univ).toReal) * ∫ z, K (Function.update x (i.succAbove j) z) ∂ν
      = (1 / (ν Set.univ).toReal)
        * ∫ z, g (Function.update
            (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i) x).2) j z) ∂ν := by
  have hlift := piFinSuccAbove_lift i z₀ hg hK
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have h1 : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i)
        (Function.update x (i.succAbove j) z)).2
      = Function.update (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i) x).2) j z := by
    have h2 : Function.update x (i.succAbove j) z
        = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i).symm
            (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i) x).1,
              Function.update (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => α) i) x).2) j z) := by
      rw [piFinSuccAbove_symm_update_succAbove, MeasurableEquiv.symm_apply_apply]
    rw [h2, MeasurableEquiv.apply_symm_apply]
  rw [hlift (Function.update x (i.succAbove j) z), h1]

/-- **Transport of integrals of lifted functions.** -/
theorem integral_pi_lift (ν : Measure α) [SigmaFinite ν] [IsFiniteMeasure ν] {k : ℕ}
    (j : Fin (k + 1)) (z₀ : α) {K : (Fin (k + 1) → α) → ℝ} {g : (Fin k → α) → ℝ}
    (hg : ∀ r, g r = K ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j).symm (z₀, r)))
    (hK : ∀ x z, K (Function.update x j z) = K x) {Ψ : ℝ → ℝ}
    (hint : Integrable (fun x => Ψ (K x)) (Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hprod : Integrable (fun p : α × (Fin k → α) => Ψ (g p.2))
      (ν.prod (Measure.pi (fun _ : Fin k => ν)))) :
    ∫ x, Ψ (K x) ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = (ν Set.univ).toReal * ∫ r, Ψ (g r) ∂(Measure.pi (fun _ : Fin k => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) j
  let ρ : Measure (Fin k → α) := Measure.pi (fun _ : Fin k => ν)
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν)) (ν.prod ρ) :=
    measurePreserving_piFinSuccAbove (μ := fun _ : Fin (k + 1) => ν) j
  have hlift := piFinSuccAbove_lift j z₀ hg hK
  have h1 : (fun x => Ψ (K x))
      =ᵐ[Measure.pi (fun _ : Fin (k + 1) => ν)] fun x => Ψ (g ((e x).2)) :=
    Filter.Eventually.of_forall (fun x => by simp only [hlift x]; rfl)
  calc ∫ x, Ψ (K x) ∂(Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, Ψ (g ((e x).2)) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := integral_congr_ae h1
    _ = ∫ p : α × (Fin k → α), Ψ (g p.2) ∂(ν.prod ρ) :=
        hmp.integral_comp' (fun p : α × (Fin k → α) => Ψ (g p.2))
    _ = ∫ z : α, ∫ r, Ψ (g r) ∂ρ ∂ν :=
        MeasureTheory.integral_prod (f := fun p : α × (Fin k → α) => Ψ (g p.2)) hprod
    _ = (∫ r, Ψ (g r) ∂ρ) * (ν Set.univ).toReal := by
        rw [integral_const, Measure.real_def, smul_eq_mul, mul_comm]
    _ = (ν Set.univ).toReal * ∫ r, Ψ (g r) ∂(Measure.pi (fun _ : Fin k => ν)) := by
        rw [mul_comm]

end Work.BoseFixB1S
