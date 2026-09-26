import Mathlib
import Submission.Work.SGsep.symAux.defs

/-!
# The cocycle identity for `sgTau`

`sgTau k` is the translation cocycle `τ_k : P → ℝ³/ℤ³` of the space-group representative `k`,
tabulated on the (finite) point group `P = arithRep (sgArith k)`.  Its defining identity is
the factor-set relation

`τ(A B) = τ(A) + A · τ(B)   (mod ℤ³)`,

which is the statement that `τ` is a `1`-cocycle for the action of `P` on `ℝ³/ℤ³`.

The table-side (`zK`/`nK`) version of the identity is proved elsewhere; here we turn it into
the real-vector identity needed by the `sym` certificate soundness argument: whenever the
three values `τ(A)`, `τ(B)`, `τ(A B)` are given by the integer numerators `zK` over the common
denominator `nK k`, and the numerators satisfy the linear relation

`z (A B) = z A + A · z B + (nK k) • m`   (with `m` an integer vector),

then `τ(A B) = τ(A) + A · τ(B) + m'` for some integer vector `m'` — namely `m` itself, so that
the defect is an honest integer translation.

Two elementary bridges are used:

* `toRMat_mulVec_div`: multiplying the real vector `v / n` by the real image of an integer
  matrix `A` is the same as dividing the integer vector `A v` by `n` (this is *also* true for
  `n = 0`, where both sides are `0`, since Lean's field division is total);
* `int_cast_div_add`: `(a + b + n m)/n = a/n + b/n + m` for `n ≠ 0`, the arithmetic core of
  the cocycle identity.
-/

namespace Work.SGsep.symAux

open Work.SG Work.SGsep

/-- Multiplying the real vector `v / n` by the real image of an integer matrix `A` is the same
as dividing the image of `v` under `A` by `n`. -/
theorem toRMat_mulVec_div (A : IMat) (v : IVec) (n : ℕ) :
    (toRMat A).mulVec (fun c => (v c : ℝ) / (n : ℝ))
      = fun c => ((A.mulVec v c : ℤ) : ℝ) / (n : ℝ) := by
  have h1 : (fun c => (v c : ℝ) / (n : ℝ)) = (n : ℝ)⁻¹ • toRVec v := by
    funext c; simp [toRVec, div_eq_inv_mul]
  rw [h1, Matrix.mulVec_smul, mulVec_toRVec]
  funext c
  simp [toRVec, div_eq_inv_mul]

/-- Division by `n ≠ 0` of an integer denominator-cleared sum: the arithmetic core of the
cocycle identity. -/
theorem int_cast_div_add (a b m : ℤ) (n : ℕ) (hn : (n : ℝ) ≠ 0) :
    (((a + b + (n : ℤ) * m : ℤ)) : ℝ) / (n : ℝ)
      = (a : ℝ) / (n : ℝ) + (b : ℝ) / (n : ℝ) + (m : ℝ) := by
  push_cast
  field_simp

theorem sgTau_cocycle (k : Fin 230) (g i : ℕ)
    (hvalG : sgTau k (GK k g) = fun c => ((zK k (geni k g)).toFun c : ℝ) / (nK k : ℝ))
    (hvalI : sgTau k (eK k i) = fun c => ((zK k i).toFun c : ℝ) / (nK k : ℝ))
    (hvalGI : sgTau k (GK k g * eK k i) =
      fun c => ((zK k (mulg k g i)).toFun c : ℝ) / (nK k : ℝ))
    (hz : ∃ m : Fin 3 → ℤ, (zK k (mulg k g i)).toFun
      = (zK k (geni k g)).toFun + (GK k g).mulVec (zK k i).toFun + (nK k : ℤ) • m) :
    ∃ m' : IVec, sgTau k (GK k g * eK k i)
      = sgTau k (GK k g) + (toRMat (GK k g)).mulVec (sgTau k (eK k i)) + toRVec m' := by
  obtain ⟨m, hm⟩ := hz
  by_cases hn : nK k = 0
  · -- degenerate case: every term carries a factor `1/nK k = 0`
    refine ⟨0, ?_⟩
    simp only [hvalGI, hvalG, hvalI, hn, Nat.cast_zero]
    funext c
    simp [Matrix.mulVec, dotProduct]
  · -- the honest case: the defect of the table relation is the integer vector `m`
    refine ⟨m, ?_⟩
    have hn' : (nK k : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [hvalGI, hvalG, hvalI, toRMat_mulVec_div]
    funext c
    have hc : (zK k (mulg k g i)).toFun c
        = (zK k (geni k g)).toFun c + ((GK k g).mulVec (zK k i).toFun) c
          + (nK k : ℤ) * m c := by
      have h := congrFun hm c
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
    rw [hc]
    exact int_cast_div_add _ _ _ _ hn'

end Work.SGsep.symAux
