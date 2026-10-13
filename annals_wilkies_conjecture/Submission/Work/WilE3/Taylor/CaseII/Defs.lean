import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Grad.PolarDefs

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the vocabulary of the replacement route**
  (design `cbc/wilkies_e3_caseII.md`, §3, installed by AREA E3 SESSION 16 on the instruction of the
  project lead).

  The route replaces `ArcCrux` / `PolarLike` by placing every bad arc on a *square EA system whose
  pivot row is `Φ`* and whose other rows vanish along the arc, with a Jacobian that is not
  identically degenerate along it.  The PROVED Case A (`Work.WilE3.Taylor.CaseII.Gen.squareCount_goodLevel`)
  then gives `m ≤ a·K`, and `gradOrderLe` gives `n + a ≤ m` — so the arc crux is bypassed, and Case II
  is never entered.

  The system is built from the *perturbed squared gradient* `G·exp⟨v, x - y⟩`, `G = sqGrad c Φ`:

  * `pertMinor c Φ v i₀ i` — the `(i₀,i)` minor of `(∇Φ, ∇G + G•v)`;
  * `sphereP y δ2` — the sphere `∑ (xᵢ - yᵢ)² = δ2`;
  * `pertMinor3 c Φ v y i₀ j₀ l` — the `(i₀,j₀,l)` `3×3` minor of `(∇G + G•v, ∇Φ, x - y)`.

  `G·exp⟨v, x - y⟩` itself is **never** put into the EA class (that would need a new exponential
  `e^{⟨v,x⟩}`, hence a chain depending on `v`); only the Lagrange rows enter the count, and those are
  EA polynomials in the *same* chain `c`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- Perturbed gradient-polar minor: the `(i₀,i)` minor of `(∇Φ, ∇G + G•v)`, `G = sqGrad c Φ`.
`∇G + G•v ∝ ∇(G·exp⟨v,·⟩)`, so its vanishing for all `i` (with `∂_{i₀}Φ ≠ 0`) is the Lagrange
condition for minimising `G·exp⟨v, x - y⟩` on a level set of `Φ`. -/
def pertMinor (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ) (i₀ i : Fin k) : EAPoly k r :=
  eaD c i₀ Φ * (eaD c i (sqGrad c Φ) + MvPolynomial.C (v i) * sqGrad c Φ)
    - eaD c i Φ * (eaD c i₀ (sqGrad c Φ) + MvPolynomial.C (v i₀) * sqGrad c Φ)

/-- The sphere `∑ (xᵢ - yᵢ)² = δ2` as an EA polynomial. -/
def sphereP (y : Fin k → ℝ) (δ2 : ℝ) : EAPoly k r :=
  ∑ i : Fin k, (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i)) ^ 2 - MvPolynomial.C δ2

/-- Perturbed radial minor: the `(i₀, j₀, l)` `3×3` minor of the rows
`(∇G + G•v, ∇Φ, x - y)` (same expansion as `Grad.det3`). -/
def pertMinor3 (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (i₀ j₀ l : Fin k) :
    EAPoly k r :=
  let U : Fin k → EAPoly k r := fun i =>
    eaD c i (sqGrad c Φ) + MvPolynomial.C (v i) * sqGrad c Φ
  let W : Fin k → EAPoly k r := fun i => eaD c i Φ
  let T : Fin k → EAPoly k r := fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i)
  U i₀ * (W j₀ * T l - W l * T j₀) - U j₀ * (W i₀ * T l - W l * T i₀)
    + U l * (W i₀ * T j₀ - W j₀ * T i₀)

/-- Interior square system: pivot row `Φ`, other rows the perturbed polar minors. -/
def pertSys (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ) (i₀ : Fin k) :
    Fin k → EAPoly k r :=
  fun i => if i = i₀ then Φ else pertMinor c Φ v i₀ i

/-- Boundary square system: pivot row `Φ`, row `j₀` the fixed sphere, others the radial minors. -/
def sphSys (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (δ2 : ℝ) (i₀ j₀ : Fin k) :
    Fin k → EAPoly k r :=
  fun i => if i = i₀ then Φ else if i = j₀ then sphereP y δ2 else pertMinor3 c Φ v y i₀ j₀ i

/-- The square Jacobian determinant of a system `P` at `x`. -/
def sysDet (c : EAChain k r) (P : Fin k → EAPoly k r) (x : Fin k → ℝ) : ℝ :=
  (Matrix.of fun i j => eaEval c (eaD c j (P i)) x).det

end Work.WilE3.Taylor.CaseII
