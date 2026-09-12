import Mathlib.Analysis.Polynomial.Norm

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

theorem finite_int_polys_bounded_supNorm (n : ℕ) (B : ℝ) :
    {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
      (P.map (Int.castRingHom ℝ)).supNorm ≤ B}.Finite := by
  classical
  let F : Finset ℤ := Finset.Icc (⌈(-B : ℝ)⌉ : ℤ) (⌊(B : ℝ)⌋ : ℤ)
  let A : Set (Polynomial ℤ) :=
    {P | P.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖((P.coeff (i : ℕ)) : ℝ)‖ ≤ B}
  have hmemF (c : ℤ) (hc : ‖(c : ℝ)‖ ≤ B) : c ∈ F := by
    dsimp [F]
    rw [Finset.mem_Icc]
    rw [Real.norm_eq_abs] at hc
    have hb := (abs_le.mp hc)
    exact ⟨Int.ceil_le.mpr hb.1, Int.le_floor.mpr hb.2⟩
  have hsubset : {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
      (P.map (Int.castRingHom ℝ)).supNorm ≤ B} ⊆ A := by
    intro P hP
    rcases hP with ⟨hne, hdeg, hsup⟩
    refine ⟨hdeg, ?_⟩
    intro i
    let Q : Polynomial ℝ := P.map (Int.castRingHom ℝ)
    have hQi : Q.coeff (i : ℕ) = ((P.coeff (i : ℕ) : ℤ) : ℝ) := by
      dsimp [Q]
      rw [Polynomial.coeff_map]
      rfl
    have hb : ‖Q.coeff (i : ℕ)‖ ≤ B := le_trans (Q.le_supNorm (i : ℕ)) hsup
    rwa [hQi] at hb
  have hA : A.Finite := by
    let π : Polynomial ℤ → Fin (n + 1) → ℤ := fun P i => P.coeff (i : ℕ)
    let T : Set (Fin (n + 1) → ℤ) := {v | ∀ i : Fin (n + 1), v i ∈ (F : Set ℤ)}
    have hT : T.Finite := by
      dsimp [T]
      exact Set.Finite.pi' (fun _ : Fin (n + 1) => F.finite_toSet)
    have him : π '' A ⊆ T := by
      intro v hv
      rcases hv with ⟨P, hP, rfl⟩
      rcases hP with ⟨hdeg, hcoeff⟩
      intro i
      change P.coeff (i : ℕ) ∈ (F : Set ℤ)
      exact hmemF (P.coeff (i : ℕ)) (hcoeff i)
    have hinj : Set.InjOn π A := by
      intro P hP Q hQ hpq
      rcases hP with ⟨hdegP, _⟩
      rcases hQ with ⟨hdegQ, _⟩
      refine (ext_iff_natDegree_le hdegP hdegQ).2 ?_
      intro i hi
      have hcon := congr_fun hpq ⟨i, Nat.lt_succ_of_le hi⟩
      simpa [π] using hcon
    exact (hT.subset him).of_finite_image hinj
  exact hA.subset hsubset

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree