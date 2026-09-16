import Submission.ZagierHoffmanProof.ABPAssemble

/-!
# The `(−1)`-twist of a polynomial with `A_0`-coefficients

Dac's dual `t`-motive `Φₛ` (Dac §4.2) has entries `(t − θ)^{σ_j}` and
`(t − θ)^{σ_{j-1}}·H_{s_j}^{(-1)}`, where `H_n` is the "flipped" Anderson–Thakur polynomial
(`H_n ∈ F_q[t][θ] = A_0[t]`) and `(-1)` is the coefficientwise `q^{-1}`-th power twist.

Since only nonnegative twists can be written as an operation on `A_ν`, we encode the `(-1)`-twist
as a **coefficientwise `q`-th root**, which for `A_0`-coefficients lands in `A_1`:

* `polyQRoot p hp` — the polynomial whose `m`-th coefficient is `ambRoot F 1 (p.coeff m) (hp m)`;
* ★ `polyQRoot_coeff`;
* ★ `polyQRoot_mem : ∀ m, (polyQRoot p hp).coeff m ∈ ambA F 1`;
* ★★ `polyTwist_one_polyQRoot : polyTwist 1 (polyQRoot p hp) = p`.

Because the `q`-th power map is injective (`ambPow_injective`, via `ambRoot_pow`), the choice of
root is forced, so `polyQRoot` is the honest `(-1)`-twist.  This is exactly what is needed to
define the criterion's input `Φ := (matrix with entries (t-θ^q)^{σ_j}, (t-θ^q)^{σ_{j-1}}Q_j)^{(-1)}`
from the *polynomial* matrix `A_{j,j} = (t-θ^q)^{σ_j}`, `A_{j,j-1} = (t-θ^q)^{σ_{j-1}}Q_j`.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma ambRoot_one_zero {h : (0 : Ambient F) ∈ ambA F 0} : ambRoot F 1 0 h = 0 := by
  have hpow : (ambRoot F 1 (0 : Ambient F) h) ^ Nat.card F = 0 := by
    simpa using ambRoot_pow F 1 (0 : Ambient F) h
  exact (pow_eq_zero_iff (FrobPow.ne_zero (Ambient F) (q := Nat.card F))).mp hpow

/-- The coefficientwise `q`-th root of a polynomial with `A_0`-coefficients (its `(-1)`-twist). -/
noncomputable def polyQRoot (p : Polynomial (Ambient F)) (hp : ∀ m, p.coeff m ∈ ambA F 0) :
    Polynomial (Ambient F) :=
  ∑ m ∈ p.support,
    (Polynomial.monomial m (ambRoot F 1 (p.coeff m) (hp m)) : Polynomial (Ambient F))

lemma polyQRoot_coeff (p : Polynomial (Ambient F)) (hp : ∀ m, p.coeff m ∈ ambA F 0) (m : ℕ) :
    (polyQRoot F p hp).coeff m = ambRoot F 1 (p.coeff m) (hp m) := by
  have hmem : ∀ b ∈ p.support, b ≠ m →
      (Polynomial.monomial b (ambRoot F 1 (p.coeff b) (hp b)) : Polynomial (Ambient F)).coeff m
        = 0 := by
    intro b _ hbm
    rw [Polynomial.coeff_monomial, if_neg hbm]
  have hnmem : m ∉ p.support →
      (Polynomial.monomial m (ambRoot F 1 (p.coeff m) (hp m)) : Polynomial (Ambient F)).coeff m
        = 0 := by
    intro hm
    rw [Polynomial.notMem_support_iff] at hm
    rw [Polynomial.coeff_monomial, if_pos rfl]
    simp only [hm]
    exact ambRoot_one_zero F
  rw [polyQRoot, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single m hmem hnmem, Polynomial.coeff_monomial, if_pos rfl]

lemma polyQRoot_mem (p : Polynomial (Ambient F)) (hp : ∀ m, p.coeff m ∈ ambA F 0) :
    ∀ m, (polyQRoot F p hp).coeff m ∈ ambA F 1 := by
  intro m
  rw [polyQRoot_coeff F p hp m]
  exact ambRoot_mem F 1 _ (hp m)

/-- **`polyQRoot` is the `(-1)`-twist**: its `(1)`-twist is the original polynomial. -/
theorem polyTwist_one_polyQRoot (p : Polynomial (Ambient F))
    (hp : ∀ m, p.coeff m ∈ ambA F 0) :
    polyTwist (q := Nat.card F) 1 (polyQRoot F p hp) = p := by
  ext m
  rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply]
  conv_lhs => rw [polyQRoot_coeff F p hp m]
  simpa using ambRoot_pow F 1 (p.coeff m) (hp m)

end ZagierHoffmanPositiveChar
