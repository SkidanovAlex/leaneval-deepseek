import Mathlib
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.CoreStep.projTop_image_nhds_of_himm
import Submission.Work.CoreStep.himm_of_finrank

namespace Work.WilE7.CoreStep

theorem attainment_open {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (hj : T.j = m)
    (hrank : ∀ z ∈ T.X.set, Module.finrank ℝ
      ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
        ((Work.WilE7.CoreStep.projTopLin n m).comp
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1))))) = n + 1)
    (C : Set (Fin n → ℝ)) (ℓ : (Fin n → ℝ) → ℝ) (hℓ : ContinuousOn ℓ C)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ C)
    (hx₀' : ∃ z ∈ T.X.set, Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z)
      = Fin.snoc x₀ (ℓ x₀)) :
    ∃ U ∈ nhds x₀, ∀ x ∈ C ∩ U, ∃ z ∈ T.X.set,
      Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt z) = Fin.snoc x (ℓ x) := by
  classical
  -- Choose a point `z₀` of the stratum projecting to `(x₀, ℓ x₀)`.
  obtain ⟨z₀, hz₀mem, hz₀proj⟩ := hx₀'
  -- At `z₀` the maximal-rank hypothesis gives injectivity of `π_{n+1}` on the tangent space, ...
  have himm₀ := Work.CoreStep.himm_of_finrank T hT hj hz₀mem (hrank z₀ hz₀mem)
  -- ... so that `projTop (absSet T)` is a neighbourhood of `projTop (absPt z₀) = (x₀, ℓ x₀)`.
  obtain ⟨V, _hV, hVimg⟩ := Work.CoreStep.projTop_image_nhds_of_himm T hT hj hz₀mem himm₀
  have hWmem : (projTop n m '' (Work.WilE7.MainDesign.absSet T ∩ V))
      ∈ nhds (Fin.snoc x₀ (ℓ x₀) : Fin (n + 1) → ℝ) := by
    rw [← hz₀proj]; exact hVimg
  -- The graph map `x ↦ (x, ℓ x)` is continuous on `C` (where `ℓ` is continuous), hence it maps
  -- `C`-nearby points `x` into that neighbourhood.
  have hgcont : Continuous
      (fun y : C => (Fin.snoc (y : Fin n → ℝ) (ℓ (y : Fin n → ℝ)) : Fin (n + 1) → ℝ)) := by
    refine Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ) ?_ ?_
    · exact continuous_subtype_val
    · exact hℓ.comp_continuous continuous_subtype_val (fun y => y.2)
  have hpre : (fun y : C =>
        (Fin.snoc (y : Fin n → ℝ) (ℓ (y : Fin n → ℝ)) : Fin (n + 1) → ℝ)) ⁻¹'
      (projTop n m '' (Work.WilE7.MainDesign.absSet T ∩ V)) ∈ nhds (⟨x₀, hx₀⟩ : C) :=
    hgcont.continuousAt.preimage_mem_nhds (by simpa using hWmem)
  rw [nhds_subtype] at hpre
  obtain ⟨U, hU, hUsub⟩ := Filter.mem_comap.mp hpre
  refine ⟨U, hU, ?_⟩
  intro x hx
  obtain ⟨hxC, hxU⟩ := hx
  have hgxW : (Fin.snoc x (ℓ x) : Fin (n + 1) → ℝ) ∈
      projTop n m '' (Work.WilE7.MainDesign.absSet T ∩ V) := by
    simpa using hUsub (a := ⟨x, hxC⟩) hxU
  -- Lift the point of the image back into the stratum `T`.
  obtain ⟨w, hwmem, hwproj⟩ := hgxW
  refine ⟨Work.WilE7.DimAPI.absPtInv (n + (m + 1)) w,
    (Work.CoreStep.mem_absSet_iff T w).mp hwmem.1, ?_⟩
  rw [Work.WilE7.DimAPI.absPt_absPtInv]
  exact hwproj

end Work.WilE7.CoreStep
