import Mathlib
import Submission.Work.HP.Defs

/-!
# Shared auxiliary objects for node N08 (`Work.HP.moment_D`)

This file is a **sorry-free** library of definitions and elementary lemmas used by the
proof of `Work.HP.moment_D` (Browning--Le Boudec--Sawin, Lemma D / Lemma D44) and by the
lemmas delegated underneath it.

Recall (see `Submission/Work/HP/Defs.lean`):
* `NV d n a B = (1/2) # {x ∈ Xi d n B : f_a(x) = 0}`;
* `Dglob d n A B = ∑ᶠ a ∈ primSet d n A ⊤, (NV a B ^ 2 - NV a B)`;
* `Omega d n B = {(x,y) : x,y ∈ Xi d n B, x ≠ y, x ≠ -y}`;
* `Gam d n x y = Λ_{ν(x)} ⊓ Λ_{ν(y)}`;
* `muXY d n x y = 3 n² max(𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²)`;
* `mainTerm A B = 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP

variable (d n : ℕ)

/-- The per-pair primitive count, i.e. `𝓢*₀(Γ_{x,y}; B_{N}(A))`: the number of primitive
coefficient vectors of norm at most `A` that vanish at both `p.1` and `p.2`. -/
def pairS0 (A : ℝ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  (({a ∈ primSet d n A (fun _ => True) |
      formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} : Set (Mon d n → ℤ)).ncard : ℝ)

/-- The "small `μ`" part `Σ^{(1)}` of the second moment, doubled for `±a`. -/
def Sigma1 (A B : ℝ) : ℝ :=
  (1 / 4) * ∑ᶠ p ∈ {p ∈ Omega d n B | muXY n p.1 p.2 ≤ A}, pairS0 d n A p

/-- The "large `μ`" part `Σ^{(2)}` of the second moment, doubled for `±a`. -/
def Sigma2 (A B : ℝ) : ℝ :=
  (1 / 4) * ∑ᶠ p ∈ {p ∈ Omega d n B | ¬ (muXY n p.1 p.2 ≤ A)}, pairS0 d n A p

end Work.HP
