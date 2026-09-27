import Mathlib

namespace Work.Drive

theorem sup_inf_eq_top_of_triple_bot
    (W A B : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hAB : A ⊔ B = ⊤) (htri : W ⊓ A ⊓ B = ⊥)
    (hW : Module.finrank ℝ W = 2) (hA : Module.finrank ℝ A = 2)
    (hB : Module.finrank ℝ B = 2) :
    W ⊔ (A ⊓ B) = ⊤ := by
  -- the ambient space is 3-dimensional
  have hAmb : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    rw [finrank_euclideanSpace]; norm_num
  -- dim (A ⊔ B) = dim (⊤) = 3
  have hABfin : Module.finrank ℝ ↥(A ⊔ B) = 3 := by
    rw [hAB, finrank_top]; exact hAmb
  -- the dimension formula on A, B gives dim (A ⊓ B) = 2 + 2 - 3 = 1
  have hAB1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hInfAB : Module.finrank ℝ ↥(A ⊓ B) = 1 := by
    rw [hABfin, hA, hB] at hAB1; omega
  -- W ⊓ (A ⊓ B) = (W ⊓ A) ⊓ B = ⊥
  have htri' : W ⊓ (A ⊓ B) = ⊥ := by
    simpa only [inf_assoc] using htri
  -- the dimension formula on W, A ⊓ B gives dim (W ⊔ (A ⊓ B)) = 2 + 1 - 0 = 3
  have hSup := Submodule.finrank_sup_add_finrank_inf_eq W (A ⊓ B)
  have hSup2 : Module.finrank ℝ ↥(W ⊔ (A ⊓ B)) = 3 := by
    rw [htri', finrank_bot, hInfAB, hW] at hSup
    omega
  -- a subspace of the same finite dimension as the ambient space is everything
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hSup2, hAmb]

end Work.Drive
