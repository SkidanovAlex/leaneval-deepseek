import Mathlib

/-!
# Gregory–Newton cube lemma (value non-zero on an integer cube)

A nonzero complex multivariate polynomial of total degree `≤ d` has a nonzero
value at some point of the integer cube `{0,…,d}^r`.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Submission.CubeLemma

lemma univariate_value {d : ℕ} (q : Polynomial ℂ) (hq : q ≠ 0) (hd : q.natDegree ≤ d) :
    ∃ y : ℕ, y ≤ d ∧ q.eval (y : ℂ) ≠ 0 := by
  by_contra h
  have hzero : ∀ y : ℕ, y ≤ d → q.eval (y : ℂ) = 0 := by
    intro y hy
    by_contra hyz
    exact h ⟨y, hy, hyz⟩
  let Z : Finset ℂ := (Finset.range (d + 1)).image fun y : ℕ => (y : ℂ)
  have hZcard : Z.card = d + 1 := by
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range (d + 1)
    · intro a ha b hb hab
      exact Nat.cast_injective hab
  have hroot : ∀ z ∈ Z, z ∈ q.roots := by
    intro z hz
    rw [Polynomial.mem_roots hq]
    rw [Polynomial.IsRoot.def]
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact hzero y (Nat.le_of_lt_succ (Finset.mem_range.mp hy))
  have hsub : Z.val ⊆ q.roots := by
    intro z hz
    exact hroot z (by simpa using hz)
  have hcard : Z.card ≤ q.natDegree := Polynomial.card_le_degree_of_subset_roots hsub
  omega

theorem cube_value {r d : ℕ} (P : MvPolynomial (Fin r) ℂ) (hP : P ≠ 0)
    (hdeg : P.totalDegree ≤ d) :
    ∃ v : Fin r → ℕ, (∀ i, v i ≤ d) ∧
      MvPolynomial.eval (fun i : Fin r => (v i : ℂ)) P ≠ 0 := by
  induction r with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · have hc0 : P.coeff 0 ≠ 0 := by
          intro hc
          apply hP
          have hEq : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
          rw [hEq, hc]
          simp
        have hEq : P = MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
        rw [hEq]
        simpa using hc0
  | succ n ih =>
      let p : Polynomial (MvPolynomial (Fin n) ℂ) := MvPolynomial.finSuccEquiv ℂ n P
      have hp0 : p ≠ 0 := by
        intro hp
        apply hP
        have hz : (MvPolynomial.finSuccEquiv ℂ n) P = (MvPolynomial.finSuccEquiv ℂ n) 0 := by
          simpa [p] using hp
        exact (MvPolynomial.finSuccEquiv ℂ n).injective hz
      let e := p.natDegree
      have hpe : p.coeff e ≠ 0 := by
        simpa [e, Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hp0)
      let c : MvPolynomial (Fin n) ℂ := p.coeff e
      have hc0 : c ≠ 0 := by simpa [c] using hpe
      have hadd : c.totalDegree + e ≤ P.totalDegree := by
        exact MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le (R := ℂ) (f := P) (i := e)
          (by simpa [c, p] using hpe)
      have hcdeg : c.totalDegree ≤ d := by
        exact le_trans (le_trans (Nat.le_add_right _ _) hadd) hdeg
      have hedeg : e ≤ d := by
        exact le_trans (le_trans (Nat.le_add_left e c.totalDegree) hadd) hdeg
      rcases ih c hc0 hcdeg with ⟨wfun, hw, hcval⟩
      let s : Fin n → ℂ := fun k => (wfun k : ℂ)
      let q : Polynomial ℂ := Polynomial.map (MvPolynomial.eval s) p
      have hq_e : q.coeff e ≠ 0 := by
        dsimp [q]
        rw [Polynomial.coeff_map]
        simpa [c, s] using hcval
      have hq0 : q ≠ 0 := by
        intro hzero
        exact hq_e (by simp [hzero])
      have hqdeg : q.natDegree ≤ d := by
        calc
          q.natDegree ≤ p.natDegree := by
            dsimp [q]
            exact Polynomial.natDegree_map_le (f := MvPolynomial.eval s) (p := p)
          _ = e := rfl
          _ ≤ d := hedeg
      rcases univariate_value q hq0 hqdeg with ⟨y, hy_le, hyval⟩
      let t : Fin (n + 1) → ℂ :=
        Fin.cons (α := fun _ : Fin (n + 1) => ℂ) (y : ℂ) s
      have heval : MvPolynomial.eval t P = q.eval (y : ℂ) := by
        dsimp [q, s, p, t]
        exact MvPolynomial.eval_eq_eval_mv_eval' (fun k : Fin n => (wfun k : ℂ)) (y : ℂ) P
      have hmain : MvPolynomial.eval t P ≠ 0 := by
        rw [heval]
        exact hyval
      let v : Fin (n + 1) → ℕ :=
        Fin.cons (α := fun _ : Fin (n + 1) => ℕ) y wfun
      refine ⟨v, ?_, ?_⟩
      · rw [Fin.forall_iff_succ]
        constructor
        · simpa [v] using hy_le
        · intro k
          simpa [v] using hw k
      · have hfun : (fun i : Fin (n + 1) => ((v i : ℕ) : ℂ)) = t := by
          funext i
          refine Fin.cases (motive := fun j =>
              ((v j : ℕ) : ℂ) = t j) ?_ ?_ i
          · simp [v, t]
          · intro k
            simp [v, t, s]
        rw [hfun]
        exact hmain

end Submission.CubeLemma
