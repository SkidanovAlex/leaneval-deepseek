import Mathlib
import Submission.Work.DSG4a.Present

namespace Work.DSG4a

open TensorProduct

/-- Pairing a vector against a standard basis vector recovers its coordinate. -/
lemma dot_pi_single {A : Type*} [CommRing A] {m : ℕ} (w : Fin m → A) (j : Fin m) :
    dot w (Pi.single j (1 : A)) = w j := by
  simp only [dot]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem mem_splitIdeal_presentMk {A : Type*} [CommRing A] {m n : ℕ} (D : Fin m → Fin n → A)
    (e : Fin m → A) (x : A) :
    x ∈ Work.DSG4a.splitIdeal A (Work.DSG4a.presentMk D e) ↔
      ∃ w ∈ Work.DSG4a.solSet D, Work.DSG4a.dot w e = x := by
  constructor
  · intro hx
    obtain ⟨σ, hσ⟩ := mem_splitIdeal.mp hx
    refine ⟨coord (σ ∘ₗ presentMk D), ?_, ?_⟩
    · rw [mem_solSet]
      intro j
      calc ∑ i, D i j * coord (σ ∘ₗ presentMk D) i
          = dot (transMap D (coord (σ ∘ₗ presentMk D))) (Pi.single j (1 : A)) := by
            rw [dot_pi_single, transMap_apply]
        _ = dot (coord (σ ∘ₗ presentMk D)) (matMap D (Pi.single j (1 : A))) :=
            dot_transMap_matMap D _ _
        _ = (σ ∘ₗ presentMk D) (matMap D (Pi.single j (1 : A))) := by
            rw [apply_eq_dot_coord]
        _ = 0 := by
            rw [LinearMap.comp_apply]
            have hz : presentMk D (matMap D (Pi.single j (1 : A))) = 0 := by
              rw [presentMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
              exact ⟨Pi.single j (1 : A), rfl⟩
            rw [hz, map_zero]
    · rw [← apply_eq_dot_coord, LinearMap.comp_apply]
      exact hσ
  · rintro ⟨w, hw, hwe⟩
    refine mem_splitIdeal.mpr ⟨Submodule.liftQ (LinearMap.range (matMap D)) (ofCoord w) ?_, ?_⟩
    · intro z hz
      rw [LinearMap.mem_ker]
      obtain ⟨z', rfl⟩ := LinearMap.mem_range.mp hz
      rw [ofCoord_apply, ← dot_transMap_matMap]
      have hw0 : transMap D w = 0 := LinearMap.mem_ker.mp hw
      rw [hw0, dot_zero_left]
    · simp only [presentMk, Submodule.mkQ_apply, Submodule.liftQ_apply, ofCoord_apply, hwe]

end Work.DSG4a
