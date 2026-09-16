import Submission.ZagierHoffmanProof.ABPValue

/-!
# The final assembly of the ABP criterion

Combining the key identity (`finalP_spec`) with the value step (`final_value_step`): given a
polynomial row vector `h` with `E = ∑ᵢ hᵢ ψᵢ = 0` whose associated `P = finalP Φ.adjugate h M`
satisfies `P(θ) ϑ = 0` and `P(θ) ≠ 0`, we obtain a polynomial row vector `P'` with `P' ψ = 0` and
`P'(θ) = ρ`.
-/

set_option autoImplicit false
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {q : ℕ} [FrobPow K q]

/-- ★★★ **The final assembly of the ABP criterion.** -/
theorem criterion_final {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)}
    {ψ : Fin ℓ → PowerSeries K}
    (hfe : ψ = (frobTwistMat (q := q) 1 ((coeHom (K := K)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := q) 1 ψ))
    {θ : K} {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) K}
    (hind : LinearIndependent K (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i))
    {ρ : Fin ℓ → K} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    {h : Fin ℓ → Polynomial K} {M : ℕ}
    (hE : ∑ i, coeHom (K := K) (h i) * ψ i = 0)
    (haux : Matrix.vecMul (fun j => (finalP (q := q) Φ.adjugate h M j).eval θ) ϑ = 0)
    (hne : (fun j => (finalP (q := q) Φ.adjugate h M j).eval θ) ≠ 0) :
    ∃ P : Fin ℓ → Polynomial K,
      (∑ j, coeHom (K := K) (P j) * ψ j = 0) ∧ (∀ j, (P j).eval θ = ρ j) :=
  final_value_step hℓ hind hρ hρ0 (finalP_spec (q := q) (Matrix.adjugate_mul Φ) hfe hE) haux hne

end ZagierHoffmanPositiveChar
