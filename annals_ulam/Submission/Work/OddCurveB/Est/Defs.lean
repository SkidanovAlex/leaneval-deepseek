import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.Godd_zero_diag
import Submission.Work.OddVolterra.Existence.diag_K2_explicit
import Submission.Work.Geometry.Ulam.AbelBeta

/-!
# The diagonal linearization of the unperturbed odd Volterra map: local setup

At `h = 0` and `σ = s` the odd Volterra map `Godd n 0 s` is the explicit

`Godd n 0 s z = ![z 0, z 1,
   I (K₁(s,s,-z 0) z 2 + K₁(s,s,z 1) z 3),
   I (K₂(s,s,-z 0) z 2 + K₂(s,s,z 1) z 3)]`

with `I = ∫₀¹ dτ/√(τ(1-τ)) = π` the Abel weight mass and the diagonal kernels
`K₁(s,s,t) = C₁(s)|t|^{2n+1}`, `K₂(s,s,t) = C₂(s) t |t|^{2n-1}`.  Hence near the base state
`(p,p,q,q)` (`p = profileX s > 0`, `q = (profileX)' s`) the map is, on the region `z 0 > 0`,
`z 1 > 0`, the polynomial model `model n s`, whose derivative is the block-triangular map
with rows

`[1,0,0,0]`, `[0,1,0,0]`, `[α,α,a,a]`, `[γ,-γ,c,-c]`

(`α = pAA`, `a = pA`, `γ = pGG`, `c = pC`), whose `2×2` block `[[a,a],[c,-c]]` has determinant
`-2ac ≠ 0`; `Psi` below is its inverse.

This file only sets up the objects; the derivative computation, the two-sided inverse
identities, and the continuity/boundedness of `s ↦ Psi n s` on a compact slope interval
`[a,b] ⊂ (0,1]` are in the files that import it.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Est

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

/-- The coordinate projection `St → ℝ`, a continuous linear map. -/
abbrev Proj (i : Fin 4) : St →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i

/-- The Abel weight mass `∫₀¹ dτ/√(τ(1-τ)) = π`. -/
def abelMass : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹

lemma abelMass_eq_pi : abelMass = Real.pi := by
  have h : (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹)
      = fun τ : ℝ => 1 / Real.sqrt (τ * ((1 : ℝ) - τ)) := by
    funext τ; rw [one_div]
  rw [abelMass, h, Commons.Geometry.Ulam.integral_one_div_sqrt_tau_one_sub_tau_eq_pi]

lemma abelMass_pos : 0 < abelMass := by
  rw [abelMass_eq_pi]; exact Real.pi_pos

lemma abelMass_ne_zero : abelMass ≠ 0 := ne_of_gt abelMass_pos

/-- The `s`-dependent constant of `K₁(s,s,t) = dc1 n s · |t|^{2n+1}`. -/
def dc1 (n : ℕ) (s : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n + 1) : ℕ) : ℝ) * (-s) ^ (n + 1) / Real.sqrt (2 * s)

/-- The `s`-dependent constant of `K₂(s,s,t) = dc2 n s · t |t|^{2n-1}`. -/
def dc2 (n : ℕ) (s : ℝ) : ℝ :=
  ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) * (-s) ^ n / Real.sqrt (2 * s)

/-- The `(2,2)`, `(2,3)`, `(3,2)` entries of the diagonal linearization. -/
def pA (n : ℕ) (s : ℝ) : ℝ := abelMass * dc1 n s * (profileX s) ^ (2 * n + 1)

/-- The `(3,2)` entry (the `(3,3)` entry is its negative). -/
def pC (n : ℕ) (s : ℝ) : ℝ := -(abelMass * dc2 n s * (profileX s) ^ (2 * n))

/-- The `(2,0)` and `(2,1)` entries. -/
def pAA (n : ℕ) (s : ℝ) : ℝ :=
  abelMass * dc1 n s * (((2 * n + 1 : ℕ) : ℝ) * (profileX s) ^ (2 * n)) * deriv profileX s

/-- The `(3,0)` entry (the `(3,1)` entry is its negative). -/
def pGG (n : ℕ) (s : ℝ) : ℝ :=
  -(abelMass * (((2 * n : ℕ) : ℝ) * dc2 n s) * (profileX s) ^ (2 * n - 1)
    * deriv profileX s)

/-- The second row of the diagonal derivative. -/
def row2 (n : ℕ) (s : ℝ) : St →L[ℝ] ℝ :=
  pAA n s • Proj 0 + pAA n s • Proj 1 + pA n s • Proj 2 + pA n s • Proj 3

/-- The third row of the diagonal derivative. -/
def row3 (n : ℕ) (s : ℝ) : St →L[ℝ] ℝ :=
  pGG n s • Proj 0 - pGG n s • Proj 1 + pC n s • Proj 2 - pC n s • Proj 3

/-- The rows of the diagonal derivative, as a `Fin 4`-family. -/
def PhiRows (n : ℕ) (s : ℝ) : Fin 4 → St →L[ℝ] ℝ := ![Proj 0, Proj 1, row2 n s, row3 n s]

/-- The candidate for `fderiv ℝ (Godd n 0 s ·) (baseState s)`. -/
def Phi (n : ℕ) (s : ℝ) : St →L[ℝ] St := ContinuousLinearMap.pi (PhiRows n s)

/-- The scalar coefficient `u` of the inverse matrix. -/
def invU (n : ℕ) (s : ℝ) : ℝ := pAA n s / (2 * pA n s) + pGG n s / (2 * pC n s)

/-- The scalar coefficient `v` of the inverse matrix. -/
def invV (n : ℕ) (s : ℝ) : ℝ := pAA n s / (2 * pA n s) - pGG n s / (2 * pC n s)

/-- The second row of the candidate inverse. -/
def psiRow2 (n : ℕ) (s : ℝ) : St →L[ℝ] ℝ :=
  - (invU n s) • Proj 0 - (invV n s) • Proj 1 + (2 * pA n s)⁻¹ • Proj 2
    + (2 * pC n s)⁻¹ • Proj 3

/-- The third row of the candidate inverse. -/
def psiRow3 (n : ℕ) (s : ℝ) : St →L[ℝ] ℝ :=
  - (invV n s) • Proj 0 - (invU n s) • Proj 1 + (2 * pA n s)⁻¹ • Proj 2
    - (2 * pC n s)⁻¹ • Proj 3

/-- The rows of the candidate inverse. -/
def PsiRows (n : ℕ) (s : ℝ) : Fin 4 → St →L[ℝ] ℝ :=
  ![Proj 0, Proj 1, psiRow2 n s, psiRow3 n s]

/-- The candidate inverse of `Phi n s`. -/
def Psi (n : ℕ) (s : ℝ) : St →L[ℝ] St := ContinuousLinearMap.pi (PsiRows n s)

/-- The `(2,2)`-coordinate map of the polynomial model of `Godd n 0 s`. -/
def gm2 (n : ℕ) (s : ℝ) (z : St) : ℝ :=
  abelMass * (dc1 n s * (z 0) ^ (2 * n + 1) * z 2 + dc1 n s * (z 1) ^ (2 * n + 1) * z 3)

/-- The `(2,3)`-coordinate map of the polynomial model of `Godd n 0 s`. -/
def gm3 (n : ℕ) (s : ℝ) (z : St) : ℝ :=
  abelMass * (dc2 n s * (-((z 0) ^ (2 * n))) * z 2 + dc2 n s * ((z 1) ^ (2 * n)) * z 3)

/-- The polynomial model of `Godd n 0 s` near the base state: on `z 0 > 0`, `z 1 > 0` the
absolute values of the diagonal kernels are the powers `z 0^{2n+1}`, `z 1^{2n+1}`. -/
def model (n : ℕ) (s : ℝ) : St → St := fun z => ![z 0, z 1, gm2 n s z, gm3 n s z]

/-! ## The diagonal kernels in the model's shape -/

lemma K1_diag (n : ℕ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    K1 n (fun _ : ℝ => 0) s s t = dc1 n s * |t| ^ (2 * n + 1) := by
  rw [Work.OddVolterra.Existence.diag_K1_explicit n hs t]
  unfold dc1
  ring

lemma K2_diag (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    K2 n (fun _ : ℝ => 0) s s t = dc2 n s * (t * |t| ^ (2 * n - 1)) := by
  rw [Work.OddVolterra.Existence.diag_K2_explicit n hn hs t]
  unfold dc2
  ring

/-! ## Nonvanishing of the entries on positive slopes -/

lemma dc1_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : dc1 n s ≠ 0 := by
  unfold dc1
  exact div_ne_zero
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne')
      (pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hs))))
    (ne_of_gt (Real.sqrt_pos.2 (by linarith)))

lemma dc2_ne_zero {n : ℕ} {s : ℝ} (hs : 0 < s) : dc2 n s ≠ 0 := by
  unfold dc2
  exact div_ne_zero
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne')
      (pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hs))))
    (ne_of_gt (Real.sqrt_pos.2 (by linarith)))

lemma pA_ne_zero (n : ℕ) {s : ℝ} (hs : 0 < s) : pA n s ≠ 0 := by
  unfold pA
  exact mul_ne_zero (mul_ne_zero abelMass_ne_zero (dc1_ne_zero hs))
    (pow_ne_zero _ (ne_of_gt (profileX_pos s hs)))

lemma pC_ne_zero (n : ℕ) {s : ℝ} (hs : 0 < s) : pC n s ≠ 0 := by
  unfold pC
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero abelMass_ne_zero (dc2_ne_zero hs))
    (pow_ne_zero _ (ne_of_gt (profileX_pos s hs))))

end
end Work.OddCurveB.Est
