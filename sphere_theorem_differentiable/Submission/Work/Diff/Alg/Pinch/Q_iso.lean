import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's reaction term on the round sphere: `Q (Iso n) = 2 (n − 1) • Iso n`

Under Ricci flow, in an Uhlenbeck frame, the curvature tensor evolves by `∂_t R = ΔR + Q(R)` with
Hamilton's reaction term
`Q(R)ᵢⱼₖₗ = ∑_{p q} (Rᵢⱼₚq Rₖₗₚq + 2 Rᵢₚₖq Rⱼₚₗq − 2 Rᵢₚₗq Rⱼₚₖq)`
(`Submission.Diff.Alg.Q`).  For the curvature tensor of the unit round sphere,
`Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ`, the reaction term is a scalar multiple of `Iso n`: it equals
`2 (n − 1) • Iso n`.  This fixed point of the ODE (up to scaling) pins down the sign and the
normalisation of `Q`, and is what makes the round sphere an invariant of the flow.

The proof is a purely algebraic index computation.  Writing `δ` for the Kronecker delta `id2 n`,
`Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ`, and `Q (Iso n)` splits into three double sums
(`∑ Rᵢⱼₚq Rₖₗₚq`, `2 ∑ Rᵢₚₖq Rⱼₚₗq`, `−2 ∑ Rᵢₚₗq Rⱼₚₖq`), each of which is evaluated by the
contraction identities of `Work.Diff.Alg.Pinch.Delta`:
`∑ Rᵢⱼₚq Rₖₗₚq = 2 (δᵢₖ δⱼₗ − δᵢₗ δⱼₖ)`,
`∑ Rᵢₚₖq Rⱼₚₗq = (n − 2) δᵢₖ δⱼₗ + δᵢⱼ δₖₗ`,
`∑ Rᵢₚₗq Rⱼₚₖq = (n − 2) δᵢₗ δⱼₖ + δᵢⱼ δₖₗ`.
The two `δᵢⱼ δₖₗ` terms cancel, leaving `2 (n − 1) (δᵢₖ δⱼₗ − δᵢₗ δⱼₖ)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- First piece of `Q (Iso n)`: `∑_{p,q} Rᵢⱼₚq Rₖₗₚq` for `R = Iso n`. -/
lemma sum_Iso_Iso (i j k l : Fin n) :
    (∑ p, ∑ q, (id2 n i p * id2 n j q - id2 n i q * id2 n j p)
        * (id2 n k p * id2 n l q - id2 n k q * id2 n l p))
      = 2 * (id2 n i k * id2 n j l) - 2 * (id2 n i l * id2 n j k) := by
  have hpt : ∀ p q : Fin n,
      (id2 n i p * id2 n j q - id2 n i q * id2 n j p)
          * (id2 n k p * id2 n l q - id2 n k q * id2 n l p)
        = (id2 n i p * id2 n k p) * (id2 n j q * id2 n l q)
          - (id2 n j p * id2 n k p) * (id2 n i q * id2 n l q)
          - (id2 n i p * id2 n l p) * (id2 n j q * id2 n k q)
          + (id2 n j p * id2 n l p) * (id2 n i q * id2 n k q) := by
    intro p q; ring
  rw [show (∑ p, ∑ q, (id2 n i p * id2 n j q - id2 n i q * id2 n j p)
          * (id2 n k p * id2 n l q - id2 n k q * id2 n l p))
        = ∑ p, ∑ q, ((id2 n i p * id2 n k p) * (id2 n j q * id2 n l q)
            - (id2 n j p * id2 n k p) * (id2 n i q * id2 n l q)
            - (id2 n i p * id2 n l p) * (id2 n j q * id2 n k q)
            + (id2 n j p * id2 n l p) * (id2 n i q * id2 n k q))
      from Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  rw [sum4]
  simp only [sum_sum_mul, sum_id2_row]
  ring

/-- Second piece of `Q (Iso n)`: `∑_{p,q} Rᵢₚₖq Rⱼₚₗq` for `R = Iso n`. -/
lemma sum_Iso_pp (i j k l : Fin n) :
    (∑ p, ∑ q, (id2 n i k * id2 n p q - id2 n i q * id2 n p k)
        * (id2 n j l * id2 n p q - id2 n j q * id2 n p l))
      = ((n : ℝ) - 2) * (id2 n i k * id2 n j l) + id2 n i j * id2 n k l := by
  have hpt : ∀ p q : Fin n,
      (id2 n i k * id2 n p q - id2 n i q * id2 n p k)
          * (id2 n j l * id2 n p q - id2 n j q * id2 n p l)
        = (id2 n i k * id2 n j l) * (id2 n p q * id2 n p q)
          - id2 n i k * (id2 n p q * id2 n p l * id2 n j q)
          - id2 n j l * (id2 n p q * id2 n p k * id2 n i q)
          + (id2 n p k * id2 n p l) * (id2 n i q * id2 n j q) := by
    intro p q; ring
  rw [show (∑ p, ∑ q, (id2 n i k * id2 n p q - id2 n i q * id2 n p k)
          * (id2 n j l * id2 n p q - id2 n j q * id2 n p l))
        = ∑ p, ∑ q, ((id2 n i k * id2 n j l) * (id2 n p q * id2 n p q)
            - id2 n i k * (id2 n p q * id2 n p l * id2 n j q)
            - id2 n j l * (id2 n p q * id2 n p k * id2 n i q)
            + (id2 n p k * id2 n p l) * (id2 n i q * id2 n j q))
      from Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  rw [sum4]
  simp only [pullconst2, sum_sum_mul]
  rw [sum_id2_sq, sum_id2_mixed l j, sum_id2_mixed k i, sum_id2_col k l, sum_id2_row i j]
  ring

/-- Third piece of `Q (Iso n)`: `∑_{p,q} Rᵢₚₗq Rⱼₚₖq` for `R = Iso n`. -/
lemma sum_Iso_cross (i j k l : Fin n) :
    (∑ p, ∑ q, (id2 n i l * id2 n p q - id2 n i q * id2 n p l)
        * (id2 n j k * id2 n p q - id2 n j q * id2 n p k))
      = ((n : ℝ) - 2) * (id2 n i l * id2 n j k) + id2 n i j * id2 n k l := by
  have h := sum_Iso_pp (n := n) i j l k
  rw [id2_symm l k] at h
  exact h

theorem Q_iso (n : ℕ) :
    Submission.Diff.Alg.Q (Submission.Diff.Alg.Iso n) =
      (2 * (n - 1)) • Submission.Diff.Alg.Iso n := by
  rcases n with - | m
  · funext i j k l
    exact i.elim0
  · have hcast : ((2 * (Nat.succ m - 1) : ℕ) : ℝ) = 2 * ((Nat.succ m : ℝ) - 1) := by
      push_cast; ring
    funext i j k l
    simp only [Q, Pi.smul_apply, nsmul_eq_mul, hcast, Iso_eq_id2]
    simp only [mul_assoc]
    rw [sum_lin]
    rw [sum_Iso_Iso i j k l, sum_Iso_pp i j k l, sum_Iso_cross i j k l]
    ring

end Work.Diff.Alg.Pinch
