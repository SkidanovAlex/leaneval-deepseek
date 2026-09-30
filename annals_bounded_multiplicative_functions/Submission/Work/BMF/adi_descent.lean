import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_defs
import Submission.Work.BMF.adi_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The degree descent of the ADI argument

State, invariant and one step of the descent that peels off `(T_j/2π)·Tay_j + μ_j t^j` from a
polynomial `P₀` satisfying the approximate dilation invariance
`P₀(a·) - P₀(b·) = E + G` with `|E| ≤ A` and `G` integer valued on the lattice `(1/Qm)ℤ`.
-/

namespace Work.BMF

open Polynomial Finset

/-- Parameters of a one-sided ADI descent. -/
structure ADIPar where
  k : ℕ
  C₀ : ℝ
  a : ℕ
  b : ℕ
  x : ℝ
  L : ℝ
  Qm : ℕ
  N : ℝ
  P₀ : ℝ[X]

/-- Standing hypotheses of the one-sided descent. -/
def ADIHyp (p : ADIPar) : Prop :=
  1 ≤ p.C₀ ∧ p.P₀.natDegree ≤ p.k ∧ 2 ≤ p.L ∧ 100 * p.C₀ ^ 4 ≤ p.N ∧
  1 ≤ p.Qm ∧ 0 < p.x ∧ p.N * p.L ≤ p.C₀ * p.x ∧ p.x ≤ p.C₀ * (p.N * p.L) ∧
  1 ≤ p.b ∧ p.b < p.a ∧
  (p.a : ℝ) ≤ p.C₀ * p.N * ((p.a : ℝ) - (p.b : ℝ)) ∧
  p.N * ((p.a : ℝ) - (p.b : ℝ)) ≤ p.C₀ * p.a

/-- A state of the descent: current polynomial `P`, error split `E + G`, sup bound `A`, and the
already extracted coefficients `T_m`, `μ_m`. -/
structure DSt where
  j : ℕ
  P : ℝ[X]
  E : ℝ[X]
  G : ℝ[X]
  A : ℝ
  T : ℕ → ℝ
  mu : ℕ → ℝ

/-- The invariant of the descent at level `s.j`. -/
def DInv (p : ADIPar) (s : DSt) : Prop :=
  s.j ≤ p.k ∧
  s.P.natDegree ≤ s.j ∧ s.E.natDegree ≤ s.j ∧ s.G.natDegree ≤ s.j ∧
  dil (p.a : ℝ) s.P - dil (p.b : ℝ) s.P = s.E + s.G ∧
  (∀ t ∈ Set.Icc (p.x / (p.a : ℝ)) ((p.x + p.L) / (p.a : ℝ)), |s.E.eval t| ≤ s.A) ∧
  0 ≤ s.A ∧ s.A ≤ Alev p.k p.C₀ s.j ∧
  IntegralOn (1 / (p.Qm : ℝ)) (C (((Dfac p.k s.j : ℕ) : ℝ)) * s.G) ∧
  (p.P₀ = s.P + ∑ m ∈ Finset.Icc (s.j + 1) p.k,
      (C (s.T m / (2 * Real.pi)) * Tay m p.x + C (s.mu m) * X ^ m)) ∧
  (∀ m ∈ Finset.Icc (s.j + 1) p.k, |s.T m| ≤ CTc p.k p.C₀ * p.N ^ (m + 1)) ∧
  (∀ m ∈ Finset.Icc (s.j + 1) p.k, ∃ z : ℤ,
      s.mu m = z * (p.Qm : ℝ) ^ m /
        (((Dfac p.k m : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) * (((qj p.a p.b m : ℕ) : ℝ))))

/-- The new `T` coefficient extracted at level `s.j`. -/
noncomputable def Tval (p : ADIPar) (s : DSt) : ℝ :=
  2 * Real.pi * (s.j : ℝ) * (-1) ^ (s.j - 1) * p.x ^ (s.j) *
    (s.E.coeff s.j / (((qj p.a p.b s.j : ℕ) : ℝ)))

/-- The new lattice coefficient extracted at level `s.j`. -/
noncomputable def muval (p : ADIPar) (s : DSt) : ℝ :=
  s.G.coeff s.j / (((qj p.a p.b s.j : ℕ) : ℝ))

/-- The integer used to cancel the constant `(T/2π) log (a/b)` in the error term. -/
noncomputable def nval (p : ADIPar) (s : DSt) : ℤ :=
  ⌊(Tval p s / (2 * Real.pi)) * Real.log ((p.a : ℝ) / (p.b : ℝ)) + 1 / 2⌋

/-- One step of the descent: from level `s.j` to level `s.j - 1`. -/
noncomputable def dstep (p : ADIPar) (s : DSt) : DSt where
  j := s.j - 1
  P := s.P - C (Tval p s / (2 * Real.pi)) * Tay s.j p.x - C (muval p s) * X ^ s.j
  E := s.E - C (Tval p s / (2 * Real.pi)) *
      (dil (p.a : ℝ) (Tay s.j p.x) - dil (p.b : ℝ) (Tay s.j p.x)) + C (nval p s : ℝ)
  G := s.G - C (s.G.coeff s.j) * X ^ s.j - C (nval p s : ℝ)
  A := s.A * (1 + Dgrow p.k p.C₀) + 1
  T := Function.update s.T s.j (Tval p s)
  mu := Function.update s.mu s.j (muval p s)

theorem dstep_j (p : ADIPar) (s : DSt) : (dstep p s).j = s.j - 1 := rfl

theorem dstep_P (p : ADIPar) (s : DSt) :
    (dstep p s).P =
      s.P - C (Tval p s / (2 * Real.pi)) * Tay s.j p.x - C (muval p s) * X ^ s.j := rfl

theorem dstep_E (p : ADIPar) (s : DSt) :
    (dstep p s).E = s.E - C (Tval p s / (2 * Real.pi)) *
      (dil (p.a : ℝ) (Tay s.j p.x) - dil (p.b : ℝ) (Tay s.j p.x)) + C (nval p s : ℝ) := rfl

theorem dstep_G (p : ADIPar) (s : DSt) :
    (dstep p s).G = s.G - C (s.G.coeff s.j) * X ^ s.j - C (nval p s : ℝ) := rfl

theorem dstep_A (p : ADIPar) (s : DSt) :
    (dstep p s).A = s.A * (1 + Dgrow p.k p.C₀) + 1 := rfl

theorem dstep_T (p : ADIPar) (s : DSt) :
    (dstep p s).T = Function.update s.T s.j (Tval p s) := rfl

theorem dstep_mu (p : ADIPar) (s : DSt) :
    (dstep p s).mu = Function.update s.mu s.j (muval p s) := rfl

end Work.BMF
