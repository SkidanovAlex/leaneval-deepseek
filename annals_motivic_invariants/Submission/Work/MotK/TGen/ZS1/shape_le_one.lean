import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZS1

open MvPolynomial

/-- Classification of a `Finsupp` on `Fin 2` whose total degree (sum of the
component multiplicities) is at most `1`: it is either `0`, the monomial giving
the first variable, or the monomial giving the second variable. -/
private lemma fin2_classify (d : Fin 2 →₀ ℕ) (h : d.sum (fun _ e => e) ≤ 1) :
    d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
  have hs : d.sum (fun _ e => e) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype]
    · exact Fin.sum_univ_two _
    · intro i; rfl
  have hd : d = Finsupp.single (0 : Fin 2) (d 0) + Finsupp.single 1 (d 1) := by
    ext i; fin_cases i <;> simp
  have h01 : d 0 + d 1 ≤ 1 := by rw [← hs]; exact h
  rcases (by omega : d 0 = 0 ∨ d 0 = 1) with h0 | h0 <;>
    rcases (by omega : d 1 = 0 ∨ d 1 = 1) with h1 | h1
  · left; rw [hd, h0, h1]; simp
  · right; right; rw [hd, h0, h1]; simp
  · right; left; rw [hd, h0, h1]; simp
  · exfalso; omega

private lemma sum_single_one (i : Fin 2) :
    (Finsupp.single i (1 : ℕ)).sum (fun _ e => e) = 1 := by
  rw [Finsupp.sum_single_index]; rfl

private lemma sum_zero_fin2 : (0 : Fin 2 →₀ ℕ).sum (fun _ e => e) = 0 := by simp

theorem shape_le_one {L : Type} [Field L] (p : MvPolynomial (Fin 2) L)
    (h : p.totalDegree ≤ 1) :
    ∃ a b c : L, p = MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c := by
  classical
  refine ⟨p.coeff (Finsupp.single (0 : Fin 2) 1), p.coeff (Finsupp.single (1 : Fin 2) 1),
    p.coeff 0, ?_⟩
  have hX0 : MvPolynomial.C (p.coeff (Finsupp.single (0 : Fin 2) 1)) * MvPolynomial.X (0 : Fin 2)
      = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) 1)
          (p.coeff (Finsupp.single (0 : Fin 2) 1)) := by
    simpa using (MvPolynomial.C_mul_X_pow_eq_monomial (s := (0 : Fin 2))
      (a := p.coeff (Finsupp.single (0 : Fin 2) 1)) (n := 1))
  have hX1 : MvPolynomial.C (p.coeff (Finsupp.single (1 : Fin 2) 1)) * MvPolynomial.X (1 : Fin 2)
      = MvPolynomial.monomial (Finsupp.single (1 : Fin 2) 1)
          (p.coeff (Finsupp.single (1 : Fin 2) 1)) := by
    simpa using (MvPolynomial.C_mul_X_pow_eq_monomial (s := (1 : Fin 2))
      (a := p.coeff (Finsupp.single (1 : Fin 2) 1)) (n := 1))
  have hA : (Finsupp.single (1 : Fin 2) (1 : ℕ) : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro hh
    rw [Finsupp.single_left_inj (show (1 : ℕ) ≠ 0 by norm_num)] at hh
    exact absurd hh (by decide)
  have hA' : (Finsupp.single (0 : Fin 2) (1 : ℕ) : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
    fun hh => hA hh.symm
  have hB : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 :=
    (Finsupp.single_ne_zero.mpr (by norm_num)).symm
  have hC : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
    (Finsupp.single_ne_zero.mpr (by norm_num)).symm
  rw [hX0, hX1]
  ext d
  simp only [AddMonoidAlgebra.coeff_add, coeff_monomial, coeff_C]
  by_cases hsum : d.sum (fun _ e => e) ≤ 1
  · rcases fin2_classify d hsum with hd | hd | hd <;> subst hd <;> simp [hA, hA', hB, hC]
  · have hd : 1 < d.sum (fun _ e => e) := not_le.mp hsum
    have hpc : p.coeff d = 0 := by
      apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
      exact lt_of_le_of_lt h hd
    rw [hpc]
    have hne0 : (0 : Fin 2 →₀ ℕ) ≠ d := by
      intro he; rw [← he, sum_zero_fin2] at hd; omega
    have hne1 : (Finsupp.single (0 : Fin 2) 1) ≠ d := by
      intro he; rw [← he, sum_single_one] at hd; omega
    have hne2 : (Finsupp.single (1 : Fin 2) 1) ≠ d := by
      intro he; rw [← he, sum_single_one] at hd; omega
    simp [hne0, hne1, hne2]

end Work.MotK.TGen.ZS1
