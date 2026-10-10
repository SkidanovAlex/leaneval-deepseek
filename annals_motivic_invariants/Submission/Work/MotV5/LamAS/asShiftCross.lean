import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.Translation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cross relation for a Klein coordinate system with a shift law

Let `K_i := kleinCoord D M i` be the Klein linear forms of a Klein model `D` over an `𝕜`-algebra
`M`, and let `τ` be an `M`-algebra automorphism of the function field `M(E)` which acts on the
`K_i` by a *shift* with a common factor `lam`:

`τ (K_i) = lam * K_{i+1}`  for all `i : Fin 5`.

This file proves the **cross relation**

`(τ^k K_i) * K_{j+k} = (τ^k K_j) * K_{i+k}`  for all `k i j : Fin 5`

(`Work.MotV5.LamAS.asShiftCross`).  The content is purely formal: iterating the shift law gives
`τ^k (K_i) = c_k * K_{i+k}` with the *same* factor `c_k = ∏_{m<k} τ^m (lam)` for every `i`; the
common factor cancels in the cross relation.  In particular nonvanishing of `lam` is *not* needed
(the shift law forces `τ` to be injective and `c_k ≠ 0` when `lam ≠ 0`, but the cross relation
itself is a consequence of multiplicativity alone).

This is the function-level input of the twisted Galois law
`γ (κ_i(R)) = (μ γ) * κ_{i + d γ}(R)` used in `Work.MotV5.LamAS.asTwistPoint_coords`.
-/

namespace Work.MotV5.LamAS

/-- The shift `n ↦ n mod 5`, as an element of `Fin 5`.  (There is no `NatCast (Fin 5)` instance,
so we spell the wrapping shift out by hand.) -/
def shift5 (n : ℕ) : Fin 5 := ⟨n % 5, Nat.mod_lt n (by norm_num)⟩

lemma shift5_zero : shift5 0 = 0 := by
  ext; simp [shift5]

lemma shift5_succ (n : ℕ) : shift5 (n + 1) = shift5 n + 1 := by
  ext; simp only [shift5, Fin.val_add, Fin.val_one]; omega

lemma shift5_val (k : Fin 5) : shift5 (k : ℕ) = k := by
  ext; simp only [shift5]; exact Nat.mod_eq_of_lt k.isLt

/-- The shift is compatible with adding `1` in `Fin 5`: shifting by `n + 1` is shifting by `n`
after translating the index by `1`. -/
lemma add_shift5_succ (j : Fin 5) (n : ℕ) : j + shift5 (n + 1) = (j + 1) + shift5 n := by
  ext; simp only [shift5, Fin.val_add, Fin.val_one]; omega

theorem asShiftCross {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (M : Type) [Field M] [Algebra 𝕜 M]
    (τ : Work.MotC2.Func (D.E.baseChange M) ≃ₐ[M] Work.MotC2.Func (D.E.baseChange M))
    (lam : Work.MotC2.Func (D.E.baseChange M)) (hlam : lam ≠ 0)
    (hshift : ∀ i : Fin 5, τ (Work.MotV.kleinCoord D M i) = lam * Work.MotV.kleinCoord D M (i + 1)) :
    ∀ (k : Fin 5) (i j : Fin 5),
      (τ ^ (k : ℕ)) (Work.MotV.kleinCoord D M i) * Work.MotV.kleinCoord D M (j + k)
        = (τ ^ (k : ℕ)) (Work.MotV.kleinCoord D M j) * Work.MotV.kleinCoord D M (i + k) := by
  -- `hlam` is not needed: only multiplicativity of `τ` and the shift law enter.
  have _ := hlam
  -- Key step: `τ^n` rescales all coordinates by the *same* factor `c`.
  have key : ∀ n : ℕ, ∃ c : Work.MotC2.Func (D.E.baseChange M), ∀ i : Fin 5,
      (τ ^ n) (Work.MotV.kleinCoord D M i)
        = c * Work.MotV.kleinCoord D M (i + shift5 n) := by
    intro n
    induction n with
    | zero => exact ⟨1, fun i => by simp [shift5_zero]⟩
    | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨(τ ^ n) lam * c, fun i => ?_⟩
      rw [pow_succ, AlgEquiv.mul_apply, hshift i, map_mul, hc (i + 1), ← add_shift5_succ i n]
      first | refl_ring1 | ring
  intro k i j
  obtain ⟨c, hc⟩ := key (k : ℕ)
  rw [hc i, hc j, shift5_val k]
  ac_rfl

end Work.MotV5.LamAS
