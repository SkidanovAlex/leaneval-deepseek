import Mathlib
import Submission.Work.BW.vaalerFubiniSlice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Work.BW

theorem sliceFubiniIntegrable {n : ℕ} (U : Set (Fin (n+1) → ℝ)) (j : Fin (n+1))
    (hU : MeasurableSet U) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hφ_int : MeasureTheory.Integrable φ)
    (h : Fin n → ℝ → ℝ) (hh_meas : ∀ i, Measurable (h i))
    (hh_int : ∀ i, MeasureTheory.Integrable (h i)) :
    MeasureTheory.Integrable (fun t : ℝ => φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i)) ∧
    (∫ u in U, φ (u j) * ∏ i, h i (u (j.succAbove i)))
      = ∫ t, φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := by
  classical
  -- The measure-preserving equivalence splitting off the `j`-th coordinate.
  let e : (Fin (n+1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  -- The integrand transported to the product space.
  let F : ℝ × (Fin n → ℝ) → ℝ := fun p => φ p.1 * ∏ i, h i (p.2 i)
  have hGint : Integrable (fun y : Fin n → ℝ => ∏ i, h i (y i)) :=
    Integrable.fintype_prod (fun i => hh_int i)
  have hFint : Integrable F := hφ_int.mul_prod hGint
  have hFcomp : (fun u : Fin (n+1) → ℝ => F (e u))
      = (fun u => φ (u j) * ∏ i, h i (u (j.succAbove i))) := by
    funext u
    simp [F, e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      Fin.removeNth_apply]
  -- Integrability of the full integrand on `Fin (n+1) → ℝ`.
  have hprod : Integrable (fun u : Fin (n+1) → ℝ => φ (u j) * ∏ i, h i (u (j.succAbove i))) := by
    rw [← hFcomp]
    exact (he.integrable_comp_emb e.measurableEmbedding (g := F)).mpr hFint
  -- The slice set in the product coordinates.
  set S : Set (ℝ × (Fin n → ℝ)) := {p | Fin.insertNth j p.1 p.2 ∈ U} with hSdef
  have hSmeas : MeasurableSet S :=
    hU.preimage (continuous_fst.finInsertNth j continuous_snd).measurable
  have hSint : Integrable (S.indicator F) := hFint.indicator hSmeas
  -- Pointwise description of the `t`-slice of the indicator.
  have hinner : ∀ t : ℝ, ∫ x, S.indicator F (t, x)
      = φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i) := by
    intro t
    have hslice_meas : MeasurableSet {x : Fin n → ℝ | Fin.insertNth j t x ∈ U} :=
      hU.preimage (continuous_const.finInsertNth j continuous_id).measurable
    have h1 : (fun x : Fin n → ℝ => S.indicator F (t, x))
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
  -- Integrability of the sliced function, from Fubini applied to the indicator.
  have hB : Integrable (fun t : ℝ =>
      φ t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, h i (y i)) :=
    hSint.integral_prod_left |>.congr (Filter.Eventually.of_forall hinner)
  exact ⟨hB, vaalerFubiniSlice U j hU φ hφ_meas hφ_int h hh_meas hh_int hprod⟩

end Work.BW
