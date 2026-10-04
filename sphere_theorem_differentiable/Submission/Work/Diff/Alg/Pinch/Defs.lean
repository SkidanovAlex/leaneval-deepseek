import Mathlib
import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the Böhm–Wilking pinching-set construction

Vocabulary for `Work.Diff.Alg.pinching_set_exists` (Brendle–Schoen Prop. 17, via Böhm–Wilking).

Conventions match `Submission.Diff.Alg`:
* `R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`, so `R i j i j` is the sectional curvature of `eᵢ ∧ eⱼ`
  and `Q (Iso n) = 2(n-1) • Iso n` is the (unit) round sphere.
* `ric R i j = ∑ k, R k i k j` is the Ricci tensor (`scalAlg R = ∑ i, ric R i i`).
* `knProd` is the Kulkarni–Nomizu product, `ell a b` is the Böhm–Wilking linear transform
  `ℓ_{a,b}(R) = R + b·Ric₀(R) ∧ id + (a/n)·scal(R)·id ∧ id`
  (Brendle–Schoen §3, Böhm–Wilking Thm. 2 / Lemmas 3.4–3.5).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The identity `2`-tensor (Kronecker delta). -/
noncomputable def id2 (n : ℕ) : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0

/-- The Ricci tensor of a `4`-index array: `ric R i j = ∑ k, R k i k j`. -/
noncomputable def ric (R : Curv4 n) (i j : Fin n) : ℝ := ∑ k, R k i k j

/-- Traceless Ricci tensor. -/
noncomputable def ric0 (R : Curv4 n) (i j : Fin n) : ℝ :=
  ric R i j - (scalAlg R / (n : ℝ)) * id2 n i j

/-- Kulkarni–Nomizu product `(A ∧ B)ᵢⱼₖₗ = AᵢₖBⱼₗ − AᵢₗBⱼₖ − AⱼₖBᵢₗ + AⱼₗBᵢₖ`. -/
noncomputable def knProd (A B : Fin n → Fin n → ℝ) : Curv4 n :=
  fun i j k l => A i k * B j l - A i l * B j k - A j k * B i l + A j l * B i k

/-- The Böhm–Wilking linear transformation `ℓ_{a,b}`. -/
noncomputable def ell (a b : ℝ) (R : Curv4 n) : Curv4 n :=
  R + b • knProd (ric0 R) (id2 n) + (a / (n : ℝ) * scalAlg R) • knProd (id2 n) (id2 n)

/-- `Ric ≥ (p/n)·scal`, as a positive-semidefiniteness condition on the bilinear form `ric R`. -/
def RicPinch (p : ℝ) (R : Curv4 n) : Prop :=
  ∀ v : Fin n → ℝ,
    (p * scalAlg R / (n : ℝ)) * (∑ i, v i * v i) ≤ ∑ i, ∑ j, ric R i j * v i * v j

/-- The cone `D(p) = {R algebraic : PIC2(R)} ∩ {Ric ≥ p·scal/n}`. -/
def Dpic (p : ℝ) : Set (Curv4 n) :=
  {R | IsAlgCurv R ∧ InPIC2 R ∧ RicPinch p R}

/-- The Böhm–Wilking cone `ℓ_{a,b}(D(p))`. -/
def Ccone (a b p : ℝ) : Set (Curv4 n) := ell a b '' Dpic (n := n) p

end Work.Diff.Alg.Pinch
