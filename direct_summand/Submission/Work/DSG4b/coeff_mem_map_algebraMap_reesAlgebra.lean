import Mathlib

namespace Work.DSG4b

theorem coeff_mem_map_algebraMap_reesAlgebra {A : Type*} [CommRing A] {I : Ideal A}
    {a : reesAlgebra I} (ha : a ∈ Ideal.map (algebraMap A (reesAlgebra I)) I) (n : ℕ) :
    (a : Polynomial A).coeff n ∈ I ^ (n + 1) :=
  (mem_map_algebraMap_reesAlgebra_iff a).mp ha n

end Work.DSG4b
