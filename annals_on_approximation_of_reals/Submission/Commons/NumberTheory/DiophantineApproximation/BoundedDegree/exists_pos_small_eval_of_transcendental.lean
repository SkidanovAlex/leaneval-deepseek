import Mathlib.Analysis.Polynomial.Norm
import Mathlib.RingTheory.Algebraic.Defs

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open Polynomial

/-- For an integer polynomial `P`, evaluating at `ξ : ℝ` the real-coefficient polynomial
`P.map (Int.castRingHom ℝ)` agrees with the ℚ-algebra evaluation of the ℚ-coefficient
polynomial `P.map (Int.castRingHom ℚ)`. -/
private lemma aeval_eq_eval_of_int (ξ : ℝ) (P : Polynomial ℤ) :
    (Polynomial.aeval (R := ℚ) (x := ξ) (P.map (Int.castRingHom ℚ))) =
    Polynomial.eval ξ (P.map (Int.castRingHom ℝ)) := by
  calc
    Polynomial.aeval ξ (P.map (Int.castRingHom ℚ))
        = Polynomial.eval ξ ((P.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)) := by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    _ = Polynomial.eval ξ (P.map (Int.castRingHom ℝ)) := by
          congr 1
          rw [Polynomial.map_map]
          congr

/-- If `ξ` is transcendental over `ℚ`, then a nonzero integer polynomial does not vanish at
`ξ` (after mapping its coefficients into `ℝ`). -/
private lemma int_poly_eval_ne_zero_of_transcendental (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (P : Polynomial ℤ) (hP : P ≠ 0) :
    Polynomial.eval ξ (P.map (Int.castRingHom ℝ)) ≠ 0 := by
  intro hzero
  have hQne : P.map (Int.castRingHom ℚ) ≠ 0 := by
    intro hQ
    apply hP
    have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℚ)) :=
      Polynomial.map_injective (Int.castRingHom ℚ) (by
        intro a b hab
        exact Int.cast_injective hab)
    exact hinj (by simp [hQ])
  have hξ' : ∀ p : Polynomial ℚ, Polynomial.aeval ξ p = 0 → p = 0 := transcendental_iff.mp hξ
  have hQzero : Polynomial.aeval ξ (P.map (Int.castRingHom ℚ)) = 0 := by
    rw [aeval_eq_eval_of_int]
    exact hzero
  exact hQne (hξ' (P.map (Int.castRingHom ℚ)) hQzero)

/-- There are only finitely many nonzero integer polynomials of degree at most `n` whose
coefficients (viewed in `ℝ`) have sup norm at most `B`. -/
private lemma finite_int_polys_bounded_supNorm (n : ℕ) (B : ℝ) :
    {P : Polynomial ℤ | P ≠ 0 ∧ P.natDegree ≤ n ∧
      (P.map (Int.castRingHom ℝ)).supNorm ≤ B}.Finite := by
  classical
  let U : Set ℤ := {c : ℤ | |(c : ℝ)| ≤ B}
  have hU : U.Finite := by
    let B0 : ℝ := max B 0
    let N : ℤ := Int.ceil B0
    have hUsub : U ⊆ Set.Icc (-N) N := by
      intro c hc
      rw [Set.mem_Icc]
      have hB_le_B0 : B ≤ B0 := le_max_left B 0
      have hB0_le_N : B0 ≤ (N : ℝ) := by
        dsimp [N]
        exact Int.le_ceil B0
      have h1 : |(c : ℝ)| ≤ (N : ℝ) := le_trans (le_trans hc hB_le_B0) hB0_le_N
      have hcge : -N ≤ c := by
        exact Int.cast_le.mp (by simpa using (abs_le.mp h1).1)
      have hcle : c ≤ N := by
        exact Int.cast_le.mp (abs_le.mp h1).2
      exact ⟨hcge, hcle⟩
    exact (Set.finite_Icc (-N) N).subset hUsub
  let A : Set (Polynomial ℤ) := {P : Polynomial ℤ | P.natDegree ≤ n ∧ ∀ i : ℕ, P.coeff i ∈ U}
  have hA : A.Finite := by
    let π : Polynomial ℤ → Fin (n + 1) → ℤ := fun P i => P.coeff i.1
    have himg : π '' A ⊆ Set.pi Set.univ (fun _ : Fin (n + 1) => U) := by
      rintro v ⟨P, hP, rfl⟩ i hi
      exact hP.2 i.1
    have hinj : Set.InjOn π A := by
      intro P hP Q hQ hπ
      apply (Polynomial.ext_iff_natDegree_le hP.1 hQ.1).2
      intro i hi
      have hc : π P ⟨i, Nat.lt_succ_of_le hi⟩ = π Q ⟨i, Nat.lt_succ_of_le hi⟩ :=
        congrFun hπ ⟨i, Nat.lt_succ_of_le hi⟩
      simpa [π] using hc
    exact ((Set.Finite.pi (fun _ : Fin (n + 1) => hU)).subset himg).of_finite_image hinj
  refine hA.subset ?_
  intro P hP
  rcases hP with ⟨hPne, hdeg, hsup⟩
  refine ⟨hdeg, ?_⟩
  intro i
  change |((P.coeff i : ℤ) : ℝ)| ≤ B
  simpa [Polynomial.coeff_map] using
    (le_trans (Polynomial.le_supNorm (P.map (Int.castRingHom ℝ)) i) hsup)

/-- A transcendental real number cannot be approximated too well by values of nonzero
integer polynomials of bounded degree and bounded coefficients: there is a uniform positive
lower bound for the distance from the values of such polynomials to zero. -/
theorem exists_pos_small_eval_of_transcendental (n : ℕ) (B : ℝ) (ξ : ℝ)
    (hξ : Transcendental ℚ ξ) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∀ P : Polynomial ℤ, P ≠ 0 → P.natDegree ≤ n →
        (P.map (Int.castRingHom ℝ)).supNorm ≤ B →
          m ≤ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ := by
  classical
  let S : Set (Polynomial ℤ) := {P | P ≠ 0 ∧ P.natDegree ≤ n ∧
      (P.map (Int.castRingHom ℝ)).supNorm ≤ B}
  have hSfin : S.Finite := by
    simpa [S] using finite_int_polys_bounded_supNorm n B
  let T : Finset (Polynomial ℤ) := hSfin.toFinset
  by_cases hTempty : T = ∅
  · use 1
    constructor; norm_num
    constructor; norm_num
    intro P hPne hdeg hsup
    exfalso
    have hmem : P ∈ S := ⟨hPne, hdeg, hsup⟩
    have hPT : P ∈ T := (hSfin.mem_toFinset).mpr hmem
    simp [T, hTempty] at hPT
  · have hTne : T.Nonempty := (Finset.nonempty_iff_ne_empty).mpr hTempty
    let U : Finset ℝ := T.image (fun P => ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖)
    have hUne : U.Nonempty := by
      rcases hTne with ⟨P0, hP0⟩
      refine ⟨‖Polynomial.eval ξ (P0.map (Int.castRingHom ℝ))‖, ?_⟩
      exact Finset.mem_image.mpr ⟨P0, hP0, rfl⟩
    let a : ℝ := U.min' hUne
    refine ⟨min a 1, ?_, ?_, ?_⟩
    · have hapos : 0 < a := by
        have haU : a ∈ U := U.min'_mem hUne
        rcases Finset.mem_image.mp haU with ⟨P, hPT, hPf⟩
        have hPne : P ≠ 0 := (hSfin.mem_toFinset.mp hPT).1
        have hne : Polynomial.eval ξ (P.map (Int.castRingHom ℝ)) ≠ 0 :=
          int_poly_eval_ne_zero_of_transcendental ξ hξ P hPne
        rw [← hPf]
        exact norm_pos_iff.mpr hne
      exact lt_min hapos zero_lt_one
    · exact min_le_right a 1
    · intro P hPne hdeg hsup
      have hmem : P ∈ S := ⟨hPne, hdeg, hsup⟩
      have hPT : P ∈ T := (hSfin.mem_toFinset).mpr hmem
      have hfU : ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ ∈ U :=
        Finset.mem_image.mpr ⟨P, hPT, rfl⟩
      have hale : a ≤ ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ := by
        simpa [a] using (U.min'_le ‖Polynomial.eval ξ (P.map (Int.castRingHom ℝ))‖ hfU)
      exact le_trans (min_le_left a 1) hale

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree