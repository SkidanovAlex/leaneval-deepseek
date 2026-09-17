import Mathlib.MeasureTheory.Constructions.Pi

namespace Commons.MeasureTheory.Pi

theorem pi_map_restrict_fin {X : Type*} [MeasurableSpace X] {K k : ℕ} (hk : k ≤ K)
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν] :
    (MeasureTheory.Measure.pi (fun _ : Fin K => ν)).map
        (fun x : Fin K → X => fun j : Fin k => x (Fin.castLE hk j)) =
      MeasureTheory.Measure.pi (fun _ : Fin k => ν) := by
  classical
  refine (MeasureTheory.Measure.pi_eq (μ := fun _ : Fin k => ν) (fun s hs => ?_)).symm
  let f : Fin K → Set X := fun i => if h : (i : ℕ) < k then s ⟨i.val, h⟩ else Set.univ
  have hf : ∀ j : Fin k, f (Fin.castLE hk j) = s j := by
    intro j
    have h : ((Fin.castLE hk j : Fin K) : ℕ) < k := by rw [Fin.val_castLE]; exact j.isLt
    simp only [f, dif_pos h]
    congr 1
  have hpre : (fun x : Fin K → X => fun j : Fin k => x (Fin.castLE hk j)) ⁻¹' (Set.univ.pi s)
      = Set.pi (↑(Finset.univ.image (Fin.castLE hk)) : Set (Fin K)) f := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi]
    constructor
    · rintro hx i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi)
      simpa [hf j] using hx j
    · intro hx j
      have h2 : x (Fin.castLE hk j) ∈ f (Fin.castLE hk j) :=
        hx (Fin.castLE hk j)
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
      rwa [hf j] at h2
  rw [MeasureTheory.Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs), hpre,
    MeasureTheory.Measure.pi_pi_finset]
  rw [Finset.prod_image (Set.injOn_of_injective (Fin.castLE_injective hk))]
  exact Finset.prod_congr rfl fun j _ => by rw [hf j]

end Commons.MeasureTheory.Pi