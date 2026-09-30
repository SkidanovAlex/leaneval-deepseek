import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set

namespace Work.BW

/-- Fubini/slicing identity for a product of coordinate functions, sliced along an
arbitrary coordinate `j : Fin (n+1)`.

The change of variables is the measure-preserving equivalence
`Fin.insertNthEquiv` / `MeasurableEquiv.piFinSuccAbove`, which identifies
`Fin (n+1) → ℝ` with `ℝ × (Fin n → ℝ)` by splitting off the coordinate `j`.
The product `∏ k, g k (u k)` factors as `g j (u j) * ∏ i, g (j.succAbove i) (u (j.succAbove i))`
(`Fin.prod_univ_succAbove`), whose integrability follows from
`Integrable.fintype_prod`; then Tonelli/Fubini on the product measure gives the
iterated integral over the slice `t ↦ {x | Fin.insertNth j t x ∈ U}`. -/
theorem vaalerFubiniSliceG {n : ℕ} (U : Set (Fin (n+1) → ℝ)) (j : Fin (n+1))
    (hU : MeasurableSet U) (g : Fin (n+1) → ℝ → ℝ) (hg_meas : ∀ k, Measurable (g k))
    (hg_int : ∀ k, MeasureTheory.Integrable (g k)) :
    ∫ u in U, ∏ k, g k (u k)
      = ∫ t, g j t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, g (j.succAbove i) (y i) := by
  classical
  let e : (Fin (n+1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  let F : ℝ × (Fin n → ℝ) → ℝ := fun p => g j p.1 * ∏ i, g (j.succAbove i) (p.2 i)
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j
  -- The inverse of `e` inserts the `j`-th coordinate back.
  have he_symm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth j p.1 p.2 := by
    intro p
    funext k
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  -- The full product factors through the slice coordinates.
  have hFcomp : (fun u : Fin (n+1) → ℝ => F (e u)) = (fun u => ∏ k, g k (u k)) := by
    funext u
    change g j (u j) * ∏ i, g (j.succAbove i) (u (j.succAbove i)) = ∏ k, g k (u k)
    rw [Fin.prod_univ_succAbove (fun k => g k (u k)) j]
  have hprod : Integrable (fun u : Fin (n+1) → ℝ => ∏ k, g k (u k)) :=
    Integrable.fintype_prod (μ := fun _ : Fin (n+1) => (volume : Measure ℝ)) (f := g)
      (fun k => hg_int k)
  have hcomp : (F ∘ e) = (fun u : Fin (n+1) → ℝ => ∏ k, g k (u k)) := by
    funext u; exact congrFun hFcomp u
  have hFint : Integrable F :=
    (he.integrable_comp_emb e.measurableEmbedding).mp (hcomp.symm ▸ hprod)
  -- The slice set in the product coordinates.
  set S : Set (ℝ × (Fin n → ℝ)) := {p | Fin.insertNth j p.1 p.2 ∈ U} with hSdef
  have hS : e '' U = S := by
    rw [hSdef]
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      have h1 : Fin.insertNth j ((e u).1) ((e u).2) = u := by
        rw [← he_symm (e u)]
        exact MeasurableEquiv.symm_apply_apply e u
      change Fin.insertNth j (e u).1 (e u).2 ∈ U
      rw [h1]; exact hu
    · intro hp
      refine ⟨Fin.insertNth j p.1 p.2, hp, ?_⟩
      rw [← he_symm p]
      exact MeasurableEquiv.apply_symm_apply e p
  have hSmeas : MeasurableSet S := by
    rw [← hS]
    exact e.measurableEmbedding.measurableSet_image.mpr hU
  have hSint : Integrable (S.indicator F) := hFint.indicator hSmeas
  -- Pointwise description of the `t`-slice of the indicator.
  have hinner : ∀ t : ℝ, ∫ x, S.indicator F (t, x)
      = g j t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, g (j.succAbove i) (y i) := by
    intro t
    have hslice_meas : MeasurableSet {x : Fin n → ℝ | Fin.insertNth j t x ∈ U} :=
      hU.preimage (continuous_const.finInsertNth j continuous_id).measurable
    have h1 : (fun x : Fin n → ℝ => S.indicator F (t, x))
        = (fun x => g j t * ({x : Fin n → ℝ | Fin.insertNth j t x ∈ U}.indicator
            (fun y => ∏ i, g (j.succAbove i) (y i)) x)) := by
      funext x
      have hx : (t, x) ∈ S ↔ x ∈ {x : Fin n → ℝ | Fin.insertNth j t x ∈ U} := by
        rw [hSdef]; simp
      by_cases hc : x ∈ {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}
      · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (hx.mpr hc)]
      · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun hh => hc (hx.mp hh))]
        simp
    rw [h1, integral_const_mul, integral_indicator hslice_meas]
  have hFub : ∫ p in S, F p
      = ∫ t, g j t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, g (j.succAbove i) (y i) := by
    rw [← integral_indicator hSmeas]
    rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = volume.prod volume from rfl]
    rw [integral_prod (fun p : ℝ × (Fin n → ℝ) => S.indicator F p) hSint]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hinner
  calc ∫ u in U, ∏ k, g k (u k)
      = ∫ u in U, F (e u) := by rw [hFcomp]
      _ = ∫ p in e '' U, F p := (he.setIntegral_image_emb e.measurableEmbedding F U).symm
      _ = ∫ p in S, F p := by rw [hS]
      _ = ∫ t, g j t * ∫ y in {x : Fin n → ℝ | Fin.insertNth j t x ∈ U}, ∏ i, g (j.succAbove i) (y i) := hFub

end Work.BW
