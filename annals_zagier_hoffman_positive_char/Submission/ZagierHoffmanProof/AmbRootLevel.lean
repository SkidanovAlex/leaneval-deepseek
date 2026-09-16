import Submission.ZagierHoffmanProof.ABPSiegel

/-!
# Roots of elements of a level `A_ν` inside the higher levels `A_{ν+M}`

`AmbRoot.lean` takes the `q^ν`-th root of an element of `A_0 = F_q[θ]`, realising it in `A_ν`.
The auxiliary-function chapter of the ABP criterion is level-uniform: if the input matrix `Θ` has
coefficients in `A_ν` (rather than in `A_0 = F_q[θ]`), all the roots that occur must be taken at
level `ν` as well.  This file provides these roots:

* `ambPreimageAt ν x hx` — a polynomial `p ∈ F[T]` with `p(θ_ν) = x` (`x ∈ A_ν`);
* `ambRootAt ν M x hx := (ambPreimageAt ν x hx)(θ_{ν+M})`, with

  ★ `(ambRootAt ν M x hx) ^ (q^M) = x`,   ★ `ambRootAt ν M x hx ∈ A_{ν+M}`,
  ★ `(v (ambRootAt ν M x hx)) ^ (q^M) = v x`.

The key input is `θ_{ν+M}^{q^M} = θ_ν`.

## Main results

* `ambThetaNu_pow_add` — `θ_{ν+M} ^ (q^M) = θ_ν`.
* `ambThetaNu_eval_pow_mul` — `(p(θ_ν)) ^ (q^j) = p(θ_ν ^ (q^j))`.
* `ambRootAt_pow`, `ambRootAt_mem`, `v_ambRootAt_pow`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- **`θ_{ν+M} ^ (q^M) = θ_ν`**. -/
lemma ambThetaNu_pow_add (ν M : ℕ) :
    (ambThetaNu F (ν + M)) ^ (Nat.card F ^ M) = ambThetaNu F ν := by
  have h := ambThetaNu_eq_pow F (show ν ≤ ν + M by omega)
  rw [Nat.add_sub_cancel_left] at h
  exact h.symm

/-- Raising a `θ_ν`-polynomial to the `q^j`-th power raises the evaluation point to the `q^j`-th
power. -/
lemma ambThetaNu_eval_pow_mul (j ν : ℕ) (p : Polynomial F) :
    (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ (Nat.card F ^ j)
      = p.eval₂ (algebraMap F (Ambient F)) ((ambThetaNu F ν) ^ (Nat.card F ^ j)) := by
  haveI : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  haveI : FrobPow (Ambient F) (Nat.card F ^ j) := FrobPow.pow (R := Ambient F) j
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, show i * Nat.card F ^ j = Nat.card F ^ j * i by ring, pow_mul]
  congr 1
  change (ambCoeff F (p.coeff i)) ^ (Nat.card F ^ j) = ambCoeff F (p.coeff i)
  exact ambCoeff_pow_pow F j (p.coeff i)

/-- A chosen `θ_ν`-preimage in `F[T]` of an element of `A_ν`. -/
noncomputable def ambPreimageAt (ν : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) : Polynomial F :=
  Classical.choose ((mem_ambA_iff F ν x).mp hx)

lemma ambPreimageAt_spec (ν : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) :
    (ambPreimageAt F ν x hx).eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x :=
  Classical.choose_spec ((mem_ambA_iff F ν x).mp hx)

/-- **The `q^M`-th root of an element of `A_ν`**, realised in `A_{ν+M}`. -/
noncomputable def ambRootAt (ν M : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) : Ambient F :=
  ambRootPoly F (ν + M) (ambPreimageAt F ν x hx)

lemma ambRootAt_pow (ν M : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) :
    (ambRootAt F ν M x hx) ^ (Nat.card F ^ M) = x := by
  rw [ambRootAt, ambRootPoly_apply, ambThetaNu_eval_pow_mul, ambThetaNu_pow_add,
    ambPreimageAt_spec]

lemma ambRootAt_mem (ν M : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) :
    ambRootAt F ν M x hx ∈ ambA F (ν + M) :=
  ambRootPoly_mem F (ν + M) _

lemma v_ambRootAt_pow (ν M : ℕ) (x : Ambient F) (hx : x ∈ ambA F ν) :
    (Valued.v (ambRootAt F ν M x hx)) ^ (Nat.card F ^ M) = Valued.v x := by
  rw [← map_pow, ambRootAt_pow]

end ZagierHoffmanPositiveChar
