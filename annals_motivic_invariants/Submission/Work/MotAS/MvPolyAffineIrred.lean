import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

theorem MvPolyAffineIrred (L : Type) [Field L] (a b : L) :
    Irreducible (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 + MvPolynomial.C b :
      MvPolynomial (Fin 2) L) := by
  have h10 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro h
    rcases (Finsupp.single_eq_single_iff (1 : Fin 2) (0 : Fin 2) (1 : ℕ) (1 : ℕ)).mp h with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 (by decide)
    · exact absurd h1 one_ne_zero
  have h20 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro h
    exact one_ne_zero (Finsupp.single_eq_zero.mp h.symm)
  have hcoeff : (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 + MvPolynomial.C b :
      MvPolynomial (Fin 2) L).coeff (Finsupp.single (0 : Fin 2) 1) = 1 := by
    simp [MvPolynomial.coeff_X, h10, h20]
  refine MvPolynomial.irreducible_of_totalDegree_eq_one ?_ ?_
  · apply le_antisymm
    · calc (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 + MvPolynomial.C b :
              MvPolynomial (Fin 2) L).totalDegree
          ≤ max (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 :
                  MvPolynomial (Fin 2) L).totalDegree
                (MvPolynomial.C b : MvPolynomial (Fin 2) L).totalDegree :=
              MvPolynomial.totalDegree_add _ _
        _ ≤ 1 := by
            refine max_le ?_ ?_
            · calc (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 :
                      MvPolynomial (Fin 2) L).totalDegree
                  ≤ max (MvPolynomial.X 0 : MvPolynomial (Fin 2) L).totalDegree
                        (MvPolynomial.C a * MvPolynomial.X 1 : MvPolynomial (Fin 2) L).totalDegree :=
                    MvPolynomial.totalDegree_add _ _
              _ ≤ 1 := by
                  refine max_le ?_ ?_
                  · calc (MvPolynomial.X 0 : MvPolynomial (Fin 2) L).totalDegree = 1 :=
                        MvPolynomial.totalDegree_X 0
                      _ ≤ 1 := by omega
                  · calc (MvPolynomial.C a * MvPolynomial.X 1 :
                            MvPolynomial (Fin 2) L).totalDegree
                        ≤ (MvPolynomial.C a : MvPolynomial (Fin 2) L).totalDegree +
                          (MvPolynomial.X 1 : MvPolynomial (Fin 2) L).totalDegree :=
                          MvPolynomial.totalDegree_mul _ _
                      _ ≤ 1 := by
                          rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
            · calc (MvPolynomial.C b : MvPolynomial (Fin 2) L).totalDegree = 0 :=
                  MvPolynomial.totalDegree_C b
                _ ≤ 1 := by omega
    · have hmem : Finsupp.single (0 : Fin 2) 1 ∈
          (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1 + MvPolynomial.C b :
            MvPolynomial (Fin 2) L).support := by
        rw [MvPolynomial.mem_support_iff, hcoeff]
        exact one_ne_zero
      have h1 : (Finsupp.single (0 : Fin 2) 1).sum (fun _ (e : ℕ) => e) = 1 :=
        Finsupp.sum_single_index rfl
      have h2 := MvPolynomial.le_totalDegree hmem
      exact (le_of_eq h1.symm).trans h2
  · intro x hx
    refine isUnit_of_dvd_one ?_
    rw [← hcoeff]
    exact hx (Finsupp.single (0 : Fin 2) 1)

end Work.MotAS
