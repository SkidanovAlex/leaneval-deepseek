import Mathlib
import Submission.Work.HomologyMV.LinAlg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the Mayer–Vietoris matrices and their integer certificates

**This file is generated** by `Submission/Work/HomologyMV/scripts/gen_mv_data.py` from
`rtdata/data/mv_certificate.json` (Ratcliffe–Tschantz data, verified exactly by the data
agent).  Do not edit by hand: rerun the script.

The matrices are the maps `φ_k : H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` of the Mayer–Vietoris sequence
of `M̂ = A ∪ B`, in the model bases

* source `H_k(A ∩ B) = ⊕_{v=1..5} H_k(T³_v)`, columns cusp-major: for `v = 1..5` the classes
  `(σ, λ₂, λ₃)` in degree `1`, `(σ∧λ₂, σ∧λ₃, λ₂∧λ₃)` in degree `2`, `[T³_v]` in degree `3`;
* target `H_k(A) ⊞ H_k(B)`, where `H_k(A)` comes first: `(ℤ, ℤ⁵, ℤ¹⁰, ℤ⁴)` in degrees
  `(0,1,2,3)` for `M̄` and `H_k(B) = ⊕_v H_k(T²_v)` has the `(y₂, y₃)` classes in degree `1`
  and `[T²_v]` in degree `2`.

In degree `0` the map is `e_v ↦ (1, -e_v)` (`H₀(A ∩ B) = ℤ⁵`, `H₀(A) ⊞ H₀(B) = ℤ ⊞ ℤ⁵`):
the sign/ordering convention is the one that makes the *following* certificates hold, which is
all the Mayer–Vietoris computation uses.  In degrees `≥ 4` the map is the zero map of zero
modules and is not stored here.

## Certificates

| name | meaning |
|---|---|
| `inv0Mat_mul_phi0Mat` | `φ₀` is injective (it has a left inverse) |
| `phi1Mat_mul_inv1Mat`, `inv1Mat_mul_phi1Mat` | `φ₁` is an isomorphism |
| `phi2Mat_mul_inv2Mat`, `inv2Mat_mul_phi2Mat` | `φ₂` is an isomorphism |
| `phi3Mat_mul_psi3Mat` | `φ₃` is surjective |
| `P3Mat_mul_Q3Mat`, `Q3Mat_mul_P3Mat` | `P3` is invertible |
| `phi3Mat_mul_P3Mat` | `φ₃ ∘ P3 = [1₄ \| 0]`, so `ker φ₃ ≅ ℤ` |

All checks are integer matrix identities decided in the kernel (`decide`), i.e. re-verified by
Lean rather than trusted from Python.
-/

namespace Work.HomologyMV

open Matrix

/-- `φ₀ : ℤ⁵ → ℤ⁶`, `e_v ↦ (1, -e_v)`: the degree-`0` Mayer–Vietoris map. -/
def phi0Mat : Matrix (Fin 6) (Fin 5) ℤ :=
  !![1, 1, 1, 1, 1; -1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, -1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, -1]
/-- A left inverse of `φ₀` (so `φ₀` is injective). -/
def inv0Mat : Matrix (Fin 5) (Fin 6) ℤ :=
  !![0, -1, 0, 0, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, -1, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, 0, 0, -1]
theorem inv0Mat_mul_phi0Mat : inv0Mat * phi0Mat = 1 := by decide

/-- A unimodular matrix putting `φ₀` in the normal form `[1₅ ; 0]`: `U0Mat * phi0Mat = inclMat 5`. -/
def U0Mat : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 0, 1, 1, 1, 1; 1, 1, 0, 1, 1, 1; 1, 1, 1, 0, 1, 1; 1, 1, 1, 1, 0, 1; 1, 1, 1, 1, 1, 0; 1, 1, 1, 1, 1, 1]
/-- The inverse of `U0Mat` over `ℤ`. -/
def V0Mat : Matrix (Fin 6) (Fin 6) ℤ :=
  !![1, 1, 1, 1, 1, -4; -1, 0, 0, 0, 0, 1; 0, -1, 0, 0, 0, 1; 0, 0, -1, 0, 0, 1; 0, 0, 0, -1, 0, 1; 0, 0, 0, 0, -1, 1]
theorem U0Mat_mul_V0Mat : U0Mat * V0Mat = 1 := by decide

theorem V0Mat_mul_U0Mat : V0Mat * U0Mat = 1 := by decide

theorem U0Mat_mul_phi0Mat : U0Mat * phi0Mat = inclMat 5 := by decide

/-- `φ₁ : ℤ¹⁵ → ℤ¹⁵`, the degree-`1` Mayer–Vietoris matrix (from `rtdata`; `det = -1`). -/
def phi1Mat : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
/-- The inverse of `φ₁Mat` over `ℤ`. -/
def inv1Mat : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
theorem phi1Mat_mul_inv1Mat : phi1Mat * inv1Mat = 1 := by decide

theorem inv1Mat_mul_phi1Mat : inv1Mat * phi1Mat = 1 := by decide

/-- `φ₂ : ℤ¹⁵ → ℤ¹⁵`, the degree-`2` Mayer–Vietoris matrix (from `rtdata`; `det = -1`). -/
def phi2Mat : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
/-- The inverse of `φ₂Mat` over `ℤ`. -/
def inv2Mat : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
theorem phi2Mat_mul_inv2Mat : phi2Mat * inv2Mat = 1 := by decide

theorem inv2Mat_mul_phi2Mat : inv2Mat * phi2Mat = 1 := by decide

/-- `φ₃ : ℤ⁵ → ℤ⁴`, the degree-`3` Mayer–Vietoris matrix (from `rtdata`; Smith normal form `(1,1,1,1)`). -/
def phi3Mat : Matrix (Fin 4) (Fin 5) ℤ :=
  !![-1, 0, 0, 0, -1; 0, 0, 1, 0, -1; 0, 1, 0, 0, 1; 0, 0, 0, -1, 1]
/-- A right inverse of `φ₃Mat`: this is the surjectivity certificate. -/
def psi3Mat : Matrix (Fin 5) (Fin 4) ℤ :=
  !![-1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 0, 0]
theorem phi3Mat_mul_psi3Mat : phi3Mat * psi3Mat = 1 := by decide

/-- A unimodular matrix bringing `φ₃Mat` to the normal form `[1₄ \| 0]`; its last column generates `ker φ₃`. -/
def P3Mat : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-1, 0, 0, 0, -1; 0, 0, 1, 0, -1; 0, 1, 0, 0, 1; 0, 0, 0, -1, 1; 0, 0, 0, 0, 1]
/-- The inverse of `P3Mat` over `ℤ`. -/
def Q3Mat : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-1, 0, 0, 0, -1; 0, 0, 1, 0, -1; 0, 1, 0, 0, 1; 0, 0, 0, -1, 1; 0, 0, 0, 0, 1]
theorem P3Mat_mul_Q3Mat : P3Mat * Q3Mat = 1 := by decide

theorem Q3Mat_mul_P3Mat : Q3Mat * P3Mat = 1 := by decide

/-- The normal form `[1₄ \| 0] : ℤ⁵ → ℤ⁴` of `φ₃`. -/
def projMat45 : Matrix (Fin 4) (Fin 5) ℤ := projMat 4

theorem phi3Mat_mul_P3Mat : phi3Mat * P3Mat = projMat45 := by decide

end Work.HomologyMV
