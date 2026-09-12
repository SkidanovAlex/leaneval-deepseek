import Mathlib.GroupTheory.Index

namespace Commons.GroupTheory

theorem finiteIndex_comap_equiv {G D : Type} [AddCommGroup G] [AddCommGroup D]
    (σ : G ≃+ D) (L : AddSubgroup D) (hL : L.FiniteIndex) :
    (AddSubgroup.comap σ.toAddMonoidHom L).FiniteIndex := by
  rw [AddSubgroup.finiteIndex_iff]
  rw [AddSubgroup.index_comap_of_surjective]
  · exact hL.index_ne_zero
  · exact σ.surjective

end Commons.GroupTheory