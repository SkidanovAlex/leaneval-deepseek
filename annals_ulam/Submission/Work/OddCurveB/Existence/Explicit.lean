import Mathlib
import Submission.Work.OddCurveB.Existence.Diag

/-!
# The odd Volterra data at the diagonal, in explicit closed form

The two rows of the Volterra system `(hah44)` that involve the perturbation are the two
components of `-G₂(s,s,z)`; on the diagonal `G₂(s,s,z) = π • K(s,s,z)`
(`Work.OddBridge.G2_self_eq_smul`).  At `σ = s` the Abel numerators and the denominator are the
*explicit polynomials*

`J₁(s,s,t) = (2n+1)!! (-(L ∂_sL))^{n+1}`, `J₂(s,s,t) = (2n-1)!! (-(L ∂_sL))^n ∂_sL`,
`Kden(s,s,t) = √((t + h' s) · 2 L)`,  `L = s t + h s`, `∂_sL = t + h' s`

(`Work.OddCurveB.Existence.J1_diag_eq`, `J2_diag_eq`, `Kden_diag_eq`).  Consequently
`𝐆(s,z)` depends on `h` **only through the two numbers `h s` and `h'(s)`** — there are no
iterated derivatives of `h` in the value of the system.  This module records that fact as

* `Kdiag1`, `Kdiag2`, `KvecDiag`, `GoddDiag` — the explicit functions;
* **`Godd_eq_GoddDiag`** — `Godd n h s z = GoddDiag n s (h s) (deriv h s) z`.

It is the structural input of every estimate on the perturbed data (`dist_Godd_le`,
`dist_fderiv_Godd_le`, the linearization `A s`): all of them become elementary analysis of an
explicit rational function of `(s, h s, h'(s), z)` on a compact box.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Existence

open Work.OddVolterra

noncomputable section

/-- The first diagonal Abel kernel, as an explicit function of the local data
`(s, h s, h' s, t)`. -/
def Kdiag1 (n : ℕ) (s hs hp t : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-((s * t + hs) * (t + hp))) ^ (n + 1)) /
    Real.sqrt ((t + hp) * (2 * (s * t + hs)))

/-- The second diagonal Abel kernel, as an explicit function of the local data. -/
def Kdiag2 (n : ℕ) (s hs hp t : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-((s * t + hs) * (t + hp))) ^ n * (t + hp)) /
    Real.sqrt ((t + hp) * (2 * (s * t + hs)))

/-- The two-component diagonal kernel `K(s,s,z,z')`, explicit. -/
def KvecDiag (n : ℕ) (s hs hp x y x' y' : ℝ) : Fin 2 → ℝ :=
  ![ - (Kdiag1 n s hs hp (-x) * x' + Kdiag1 n s hs hp y * y'),
     - (Kdiag2 n s hs hp (-x) * x' + Kdiag2 n s hs hp y * y')]

/-- The left-hand side `𝐆` of the paper's system at the diagonal, as a function of the local
data `(s, h s, h' s, z)`. -/
def GoddDiag (n : ℕ) (s hs hp : ℝ) (z : St) : St :=
  ![z 0, z 1, -(abelMass * KvecDiag n s hs hp (z 0) (z 1) (z 2) (z 3) 0),
     -(abelMass * KvecDiag n s hs hp (z 0) (z 1) (z 2) (z 3) 1)]

/-- The first diagonal kernel is the paper's `K₁` on the diagonal. -/
lemma K1_diag_eq (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K1 n h s s t = Kdiag1 n s (h s) (deriv h s) t := by
  unfold K1 Kdiag1
  rw [J1_diag_eq, Kden_diag_eq]
  simp only [Work.OddVolterra.line, Work.OddVolterra.lineSlope]

/-- The second diagonal kernel is the paper's `K₂` on the diagonal. -/
lemma K2_diag_eq (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K2 n h s s t = Kdiag2 n s (h s) (deriv h s) t := by
  unfold K2 Kdiag2
  rw [J2_diag_eq, Kden_diag_eq]
  simp only [Work.OddVolterra.line, Work.OddVolterra.lineSlope]

/-- The diagonal kernel vector `K(s,s,z,z')` in terms of the local data. -/
lemma Kvec_diag_eq (n : ℕ) (h : ℝ → ℝ) (s x y x' y' : ℝ) :
    Kvec n h s s x y x' y' = KvecDiag n s (h s) (deriv h s) x y x' y' := by
  funext i
  fin_cases i <;>
    simp only [Kvec, KvecDiag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      K1_diag_eq, K2_diag_eq]

/-- **The perturbed system depends on `h` only through `h s` and `h'(s)`.** -/
theorem Godd_eq_GoddDiag (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) :
    Godd n h s z = GoddDiag n s (h s) (deriv h s) z := by
  rw [Godd_eq_abelMass_smul, Kvec_diag_eq]
  rfl

/-- The base (`h ≡ 0`) case: `Godd n 0 s z` is the explicit function evaluated at `0, 0`. -/
lemma Godd_zero_eq (n : ℕ) (s : ℝ) (z : St) :
    Godd n 0 s z = GoddDiag n s 0 0 z := by
  have h : Godd n (0 : ℝ → ℝ) s z =
      GoddDiag n s ((0 : ℝ → ℝ) s) (deriv (0 : ℝ → ℝ) s) z :=
    Godd_eq_GoddDiag n (0 : ℝ → ℝ) s z
  simpa using h

end

end Work.OddCurveB.Existence
