import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.VarCoefAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-!
# `varLap A B` preserves smooth `1`-periodic functions

`varLap A B f = -(Σ_{a,b} A a b · ∂_a ∂_b f + Σ_a B a · ∂_a f)` is a finite sum of compositions
`M_{A a b} ∘ ∂_a ∘ ∂_b` (and `M_{B a} ∘ ∂_a`); each factor preserves smooth `1`-periodic functions
(`mulOp_isOrd`, `pdOp_isOrd`), hence so does the sum, its negative, and the whole operator.

Rather than re-deriving the closure of `SmoothPer` under sums/products/partial derivatives, we take
the shortcut through the order calculus of `VarCoef/OpOrder.lean` and `VarCoef/Assembly.lean`: the
`IsCommOrd` certificate of `varLapOp` against *any* operator `L` that commutes with multiplication
and with the partial derivatives (`Assembly.varLap_isCommOrd`) is available in particular for
`L = id`, and its `ord` component is an `IsOrd 2 C (varLapOp A B)`, whose `pres` field is exactly
`Preserves (varLapOp A B)`.

The only commutator inputs needed for the `L = id` instance are `[id, M_m] = 0` and `[id, ∂_a] = 0`,
which are the zero operator, of every order (`IsOrd.zero'`).
-/

theorem varLapOp_preserves {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    Work.Diff.STE.B3.VarCoef.Preserves (Work.Diff.STE.B3.VarCoef.varLapOp A B) := by
  -- `[id, M_m] = 0` and `[id, ∂_a] = 0`, both of every order
  have hIdmul : ∀ m : (ι → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) m → Work.Diff.STE.Periodic1 m →
      ∃ C : ℤ → ℝ, IsOrd (-1) C (commOp (id : Op ι) (mulOp m)) :=
    fun m _ _ => ⟨0, IsOrd.congr (IsOrd.zero' (-1))
      (fun f _ => by funext x; simp [commOp_apply])⟩
  have hIdpd : ∀ i : ι, ∃ C : ℤ → ℝ, IsOrd 0 C (commOp (id : Op ι) (pdOp i)) :=
    fun i => ⟨0, IsOrd.congr (IsOrd.zero' 0)
      (fun f _ => by funext x; simp [commOp_apply])⟩
  obtain ⟨C, Cl, h⟩ := varLap_isCommOrd (id : Op ι) linSP_id Preserves.id
    A B hA hAp hB hBp (fun m hm hmp => mulOp_isOrd m hm hmp) (fun i => pdOp_isOrd i) hIdmul hIdpd
  exact h.ord.pres

end Work.Diff.STE.B3.VarCoef
