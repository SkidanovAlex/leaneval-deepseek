import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# `Work.KT.Psi.kronAux` — infrastructure for the multiplicativity of `ψ²`

Definitions and elementary lemmas used by `Submission.Work.KT.Psi.psi2Cls_kron`.

The multiplicative formula `ψ²(p ⊗ q) = ψ²p · ψ²q` rests on the tensor decomposition
`(p⊗q) ⊗ (p⊗q) ≅ (p⊗p) ⊗ (q⊗q)` together with the identity

`(1 + ε σ_Aσ_B)/2 = ((1+σ_A)/2)((1+εσ_B)/2) + ((1-σ_A)/2)((1-εσ_B)/2)`

for commuting involutions `σ_A`, `σ_B`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The symmetric/antisymmetric projector `(1 + ε·S)/2` on square matrices. -/
def projE {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℂ) (S : Matrix ι ι A) : Matrix ι ι A :=
  algebraMap ℂ A (1 / 2) • (1 + algebraMap ℂ A ε • S)

/-- The "middle four" exchange `((a,a'),(b,b')) ↦ ((a,b),(a',b'))`. -/
def midPerm (M N : ℕ) :
    (Fin M × Fin N) × (Fin M × Fin N) ≃ (Fin M × Fin M) × (Fin N × Fin N) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv z := by rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv z := by rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

/-- The index equivalence `Fin (M*N) × Fin (M*N) ≃ (Fin M × Fin M) × (Fin N × Fin N)`. -/
def xiToOm (M N : ℕ) :
    Fin (M * N) × Fin (M * N) ≃ (Fin M × Fin M) × (Fin N × Fin N) :=
  (finProdFinEquiv.symm.prodCongr finProdFinEquiv.symm).trans (midPerm M N)

/-- The index equivalence `Ω ≃ Fin ((M*M)*(N*N))`. -/
def omToFin (M N : ℕ) :
    (Fin M × Fin M) × (Fin N × Fin N) ≃ Fin ((M * M) * (N * N)) :=
  (finProdFinEquiv.prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- The index equivalence `Ω ≃ Fin ((M*N)*(M*N))`. -/
def omToFinMN (M N : ℕ) :
    (Fin M × Fin M) × (Fin N × Fin N) ≃ Fin ((M * N) * (M * N)) :=
  (xiToOm M N).symm.trans finProdFinEquiv

end

end Work.KT.Psi
