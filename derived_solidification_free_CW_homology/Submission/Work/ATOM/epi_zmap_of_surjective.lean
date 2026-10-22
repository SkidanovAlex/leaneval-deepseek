import Mathlib
import Submission.Work.ATOM.zdesc

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed in
theorem epi_zmap_of_surjective {T' T : LightProfinite.{0}} (π : T' ⟶ T)
    (hπ : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom π)) :
    Epi (Work.ATOM.zmap π) := by
  refine ⟨fun {Z} u v huv => ?_⟩
  have hφ : Work.ATOM.zmap (pullback.fst π π) ≫ (Work.ATOM.zmap π ≫ u)
      = Work.ATOM.zmap (pullback.snd π π) ≫ (Work.ATOM.zmap π ≫ u) := by
    simp only [← Category.assoc, ← Functor.map_comp, pullback.condition]
  obtain ⟨ψ, -, huniq⟩ := zdesc π hπ (φ := Work.ATOM.zmap π ≫ u) hφ
  have hu : u = ψ := huniq u rfl
  have hv : v = ψ := huniq v (by rw [huv])
  rw [hu, hv]

end Work.ATOM
