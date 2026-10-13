import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE7.pad_eval
import Submission.Work.WilE9G.Lagrange.eaD_pad
import Submission.Work.WilE9G.Lagrange.lagPoint_apply

namespace Work.WilE9G.Lagrange

open WilkiesDesign WilkiesDesign.E

/-!
# Evaluating the equations of the Lagrange stratum

This file proves `lagEqs_eval`: evaluating the polynomials `lagH`, `lagL`, `lagN` of the Lagrange
construction at the point `lagPoint z mu mu0` gives exactly the intended numbers, namely

* `lagH a` evaluates to `h_a(z)`,
* `lagL l` evaluates to the homogeneous Lagrange combination
  `μ₀(∂_l Φ(z) + Φ(z) c_l) - ∑_a μ_a ∂_l h_a(z)`,
* `lagN` evaluates to `∑_a μ_a² + μ₀² - 1`.

The proof is the bookkeeping of the coordinate conventions: the pads evaluate through
`takeZ` (`Work.WilE7.pad_eval`), and `takeZ` of `lagPoint` is `z` while the multiplier coordinates
of `lagPoint` are `μ` and `μ₀`.
-/

/-! ## Reading off the coordinates of `lagPoint` -/

/-- Truncating `lagPoint z mu mu0` to the base-and-fibre coordinates returns `z`. -/
theorem lagEval_takeZ_lagPoint {n m j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ)
    (mu0 : ℝ) (hk : n + (1 + m) ≤ n + (1 + (m + j + 1))) :
    Work.WilE7.takeZ hk (Work.WilE9G.lagPoint z mu mu0) = z := by
  funext i
  simp [Work.WilE7.takeZ, Work.WilE9G.lagPoint, Fin.append, Fin.addCases]

/-- The coordinate of `lagPoint z mu mu0` at `muIdx n m a` is `mu a`. -/
theorem lagEval_lagPoint_muIdx {n m j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ)
    (mu0 : ℝ) (a : Fin j) :
    Work.WilE9G.lagPoint z mu mu0 (Work.WilE9G.Lagrange.muIdx n m a) = mu a := by
  rw [Work.WilE9G.lagPoint]
  rw [show finCongr (by omega : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1))
      (Work.WilE9G.Lagrange.muIdx n m a)
      = Fin.natAdd (n + (1 + m)) (Fin.castAdd 1 a) from rfl]
  rw [Fin.append_right, Fin.append_left]

/-- The coordinate of `lagPoint z mu mu0` at `mu0Idx n m j` is `mu0`. -/
theorem lagEval_lagPoint_mu0Idx {n m j : ℕ} (z : Fin (n + (1 + m)) → ℝ) (mu : Fin j → ℝ)
    (mu0 : ℝ) :
    Work.WilE9G.lagPoint z mu mu0 (Work.WilE9G.Lagrange.mu0Idx n m j) = mu0 := by
  rw [Work.WilE9G.lagPoint]
  rw [show finCongr (by omega : n + (1 + (m + j + 1)) = n + (1 + m) + (j + 1))
      (Work.WilE9G.Lagrange.mu0Idx n m j)
      = Fin.natAdd (n + (1 + m)) (Fin.last j) from rfl]
  rw [Fin.append_right]
  rw [show (Fin.last j : Fin (j + 1)) = Fin.natAdd j (0 : Fin 1) from rfl]
  rw [Fin.append_right]

/-! ## `eaEval` is a ring homomorphism -/

theorem lagEval_add {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (P + Q) x = eaEval c P x + eaEval c Q x := by simp [eaEval]

theorem lagEval_sub {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (P - Q) x = eaEval c P x - eaEval c Q x := by simp [eaEval]

theorem lagEval_mul {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (P * Q) x = eaEval c P x * eaEval c Q x := by simp [eaEval]

theorem lagEval_pow {k r : ℕ} (c : EAChain k r) (P : EAPoly k r) (N : ℕ) (x : Fin k → ℝ) :
    eaEval c (P ^ N) x = eaEval c P x ^ N := by simp [eaEval]

theorem lagEval_sum {k r : ℕ} {ι : Type*} (c : EAChain k r) (s : Finset ι) (f : ι → EAPoly k r)
    (x : Fin k → ℝ) :
    eaEval c (∑ i ∈ s, f i) x = ∑ i ∈ s, eaEval c (f i) x := by simp [eaEval]

theorem lagEval_one {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) :
    eaEval c (1 : EAPoly k r) x = 1 := by simp [eaEval]

theorem lagEval_C {k r : ℕ} (c : EAChain k r) (a : ℝ) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C a) x = a := by simp [eaEval]

/-! ## Evaluation of the padded chain at `lagPoint` -/

/-- A polynomial of `S`, padded to the ambient space of the Lagrange stratum, evaluates at
`lagPoint z mu mu0` to its value at `z` in the chain of `S`. -/
theorem lagEval_pad {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Q : EAPoly (n + (1 + m)) S.X.r) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ)
    (mu0 : ℝ) :
    eaEval (lagChain S) (Work.WilE7.EAPoly.pad (by omega) Q) (Work.WilE9G.lagPoint z mu mu0)
      = eaEval S.X.c Q z := by
  have h := (Work.WilE7.pad_eval (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) S.X.c).2.2
    Q (Work.WilE9G.lagPoint z mu mu0)
  rw [lagEval_takeZ_lagPoint] at h
  exact h

/-- The multiplier variable `μ₀` evaluates at `lagPoint z mu mu0` to `mu0`. -/
theorem lagEval_mu0Var {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    eaEval (lagChain S) (mu0Var S) (Work.WilE9G.lagPoint z mu mu0) = mu0 := by
  simp [mu0Var, eaEval, lagEval_lagPoint_mu0Idx]

/-- The multiplier variable `μ_a` evaluates at `lagPoint z mu mu0` to `mu a`. -/
theorem lagEval_muVar {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) (a : Fin S.j) :
    eaEval (lagChain S) (muVar S a) (Work.WilE9G.lagPoint z mu mu0) = mu a := by
  simp [muVar, eaEval, lagEval_lagPoint_muIdx]

/-! ## The main statement -/

theorem lagEqs_eval {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    (∀ a : Fin S.j,
        WilkiesDesign.E.eaEval (Work.WilE9G.Lagrange.lagChain S) (Work.WilE9G.Lagrange.lagH S a)
            (Work.WilE9G.lagPoint z mu mu0)
          = WilkiesDesign.E.eaEval S.X.c (S.h a) z) ∧
      (∀ l : Fin (1 + m),
        WilkiesDesign.E.eaEval (Work.WilE9G.Lagrange.lagChain S)
            (Work.WilE9G.Lagrange.lagL S Phi c l) (Work.WilE9G.lagPoint z mu mu0)
          = mu0 * (WilkiesDesign.E.eaEval S.X.c
                  (WilkiesDesign.E.eaD S.X.c (Fin.natAdd n l) Phi) z
                + WilkiesDesign.E.eaEval S.X.c Phi z * c l)
            - ∑ a : Fin S.j, mu a * WilkiesDesign.E.eaEval S.X.c
                (WilkiesDesign.E.eaD S.X.c (Fin.natAdd n l) (S.h a)) z) ∧
      (WilkiesDesign.E.eaEval (Work.WilE9G.Lagrange.lagChain S)
          (Work.WilE9G.Lagrange.lagN S) (Work.WilE9G.lagPoint z mu mu0)
        = (∑ a : Fin S.j, (mu a) ^ 2) + mu0 ^ 2 - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact lagEval_pad S (S.h a) z mu mu0
  · intro l
    simp only [lagL]
    simp only [lagEval_sum, lagEval_sub, lagEval_add, lagEval_mul, lagEval_C,
      lagEval_pad, lagEval_mu0Var, lagEval_muVar]
    ring
  · simp only [lagN]
    simp only [lagEval_sum, lagEval_sub, lagEval_add, lagEval_pow, lagEval_one,
      lagEval_mu0Var, lagEval_muVar]

end Work.WilE9G.Lagrange
