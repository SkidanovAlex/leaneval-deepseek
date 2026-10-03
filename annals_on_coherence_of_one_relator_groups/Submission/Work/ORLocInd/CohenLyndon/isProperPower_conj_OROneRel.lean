import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.ORLocInd.CohenLyndon

universe u

theorem isProperPower_conj_OROneRel {α : Type u} (r g : FreeGroup α) :
    Work.OROneRel.IsProperPower (g * r * g⁻¹) ↔ Work.OROneRel.IsProperPower r := by
  constructor
  · rintro ⟨u, k, hk, h⟩
    refine ⟨g⁻¹ * u * g, k, hk, ?_⟩
    have h2 : (g⁻¹ * u * g) ^ k = g⁻¹ * u ^ k * g := by
      simpa [inv_inv] using (conj_pow (a := g⁻¹) (b := u) (i := k))
    rw [h2, ← h]
    group
  · rintro ⟨u, k, hk, h⟩
    exact ⟨g * u * g⁻¹, k, hk, by rw [h, conj_pow]⟩

end Work.ORLocInd.CohenLyndon
