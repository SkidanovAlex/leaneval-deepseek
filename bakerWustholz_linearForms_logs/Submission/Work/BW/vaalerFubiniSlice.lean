import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Work.BW

theorem vaalerFubiniSlice {n : ℕ} (U : Set (Fin (n+1) → ℝ)) (j : Fin (n+1))
    (hU : MeasurableSet U) (φ : ℝ → ℝ) (hφ : Measurable φ) (hφint : MeasureTheory.Integrable φ)
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_int : ∀ i, MeasureTheory.Integrable (h i))
    (hprod : MeasureTheory.Integrable (fun u : Fin (n+1) → ℝ => φ (u j) * ∏ i, h i (u (j.succAbove i)))) :
    ∫ u in U, φ (u j) * ∏ i, h i (u (j.succAbove i))
      = ∫ t, φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := by
  let e : (Fin (n+1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  let F : ℝ × (Fin n → ℝ) → ℝ := fun p => φ p.1 * ∏ i, h i (p.2 i)
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  have hFcomp : (fun u : Fin (n+1) → ℝ => F (e u))
      = (fun u => φ (u j) * ∏ i, h i (u (j.succAbove i))) := by
    funext u
    simp [F, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      Fin.removeNth_apply]
  have hFint : Integrable F := by
    refine (he.integrable_comp_emb e.measurableEmbedding (g := F)).mp ?_
    rw [show (F ∘ e) = (fun u : Fin (n+1) → ℝ => φ (u j) * ∏ i, h i (u (j.succAbove i)))
      from hFcomp]
    exact hprod
  set S : Set (ℝ × (Fin n → ℝ)) := {p | Fin.insertNth j p.1 p.2 ∈ U} with hSdef
  have hS : e '' U = S := by
    rw [hSdef]
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 : Fin.insertNth j ((e u).1) ((e u).2) = u := by
        funext k
        simp [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
      change Fin.insertNth j ((e u).1) ((e u).2) ∈ U
      rw [h1]; exact hu
    · intro hp
      refine ⟨Fin.insertNth j p.1 p.2, hp, ?_⟩
      have h2 : Fin.insertNth j p.1 p.2 = e.symm p := by
        ext k
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
      rw [h2]; simp
  have hSmeas : MeasurableSet S := hS ▸ (e.measurableEmbedding.measurableSet_image.mpr hU)
  have hSint : Integrable (Set.indicator S F) := hFint.indicator hSmeas
  have hinner : ∀ t : ℝ, ∫ x, Set.indicator S F (t, x)
      = φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := by
    intro t
    have hslice_meas : MeasurableSet {x : Fin n → ℝ | Fin.insertNth j t x ∈ U} :=
      hU.preimage (continuous_const.finInsertNth j continuous_id).measurable
    have h1 : (fun x : Fin n → ℝ => Set.indicator S F (t, x))
        = (fun x => φ t * Set.indicator {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}
            (fun y => ∏ i, h i (y i)) x) := by
      funext x
      have hx : (t, x) ∈ S ↔ x ∈ {x : Fin n → ℝ | Fin.insertNth j t x ∈ U} := by
        rw [hSdef]; simp
      by_cases hc : x ∈ {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (hx.mpr hc)]
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun hh => hc (hx.mp hh))]
        simp
    rw [h1, integral_const_mul, integral_indicator hslice_meas]
  have hFub : ∫ p in S, F p
      = ∫ t, φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := by
    rw [← integral_indicator hSmeas]
    rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume from rfl]
    rw [integral_prod (fun p : ℝ × (Fin n → ℝ) => Set.indicator S F p) hSint]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hinner
  calc ∫ u in U, φ (u j) * ∏ i, h i (u (j.succAbove i))
      = ∫ u in U, F (e u) := by rw [hFcomp]
      _ = ∫ p in e '' U, F p :=
            (MeasurePreserving.setIntegral_image_emb he e.measurableEmbedding F U).symm
      _ = ∫ p in S, F p := by rw [hS]
      _ = ∫ t, φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := hFub

end Work.BW
