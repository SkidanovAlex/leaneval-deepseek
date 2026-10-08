import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.ConjSub

/-- **The normalizer of a conjugate subgroup.**  `N_G(K^g) = (N_G K)^g`, where
`K^g = Work.GW2.conjSub g K = g K g⁻¹`.  This is the `MulAut.conj` case of
`Subgroup.map_equiv_normalizer_eq`. -/
theorem normalizer_conjSub {G : Type} [Group G] (g : G) (K : Subgroup G) :
    Subgroup.normalizer ((Work.GW2.conjSub g K : Subgroup G) : Set G) =
      Work.GW2.conjSub g (Subgroup.normalizer (K : Set G)) := by
  -- `conjSub g K = K.map (MulAut.conj g).toMonoidHom`, so this is exactly the
  -- `MulAut.conj g` instance of `Subgroup.map_equiv_normalizer_eq`, read backwards.
  exact (Subgroup.map_equiv_normalizer_eq K (MulAut.conj g)).symm

end Work.CORE4.ConjSub
