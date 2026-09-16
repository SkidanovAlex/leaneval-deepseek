import Submission.ZagierHoffmanProof.StepK24

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial
open scoped BigOperators

/-!
# Step K25: statement layer of the general stage-s collapse

Hsum_collapse0 (StepK24) is the `s = 0` anchor of the E-assembly:

    Hsum F (n+1) 1 = (X−X^q)⁻¹ · Σ_{t : Fin n → F} inv(cast(D1 n t)),
    D1 n t = Σ_{m<n+1} coeffSeq(n+1)(cons 0 t)(m+1)·hh 0 2 m.

The GENERAL stage-s collapse lemma (the per-stage iteration template; PLAN SESSION 156/157)
states, for each stage `s ≥ 0` and level `m ≥ 0` (a degree-(m+s+1) monic polynomial with
the lowest `s` coefficients already collapsed): writing the remaining coefficients as
`u : Fin m → F` and the current denominator as

    StateDen s m u := Σ_{m'<m+1} coeffSeq(m+s+1)(cons0_{s+1} u)(m'+s+1)·hh 0 (s+1) m'

(`cons0_{s+1} u` = the tuple `u` padded on the left with `s+1` zeros — indices 0..s are
the already-collapsed coefficients and `s+1 ≤ m'+s+1`; the `coeffSeq (m+s+1)` extension
supplies the monic leading `1` at the top index), the collapse of the next coefficient
(affine part, coefficient `hh 0 (s+1) 0 = 1`) reads

    Σ_{u : Fin (m+1) → F} inv(cast(StateDen s (m+1) u))
      = (X − X^{q^{s+1}})⁻¹ · Σ_{u' : Fin m → F} inv(cast(StateDen (s+1) m u')).

  • s = 0 instance (degree `m+1 = n+1`): the left side is `Hsum F (n+1) 1`
    (`St_zero_glue`/`Hsum_collapse0`) and the right side is its `D1` output — i.e.
    exactly Hsum_collapse0.
  • s = 1 instance: degree `m+2`, `StateDen 1 (m+1) t = D1 (m+1) t` and the output
    denominator is `StateDen 2 m u = D2 m u` (defined below).
  Proof structure per stage (identical to Hsum_collapse0): split `Fin (m+1)`-tuples by
  `sum_cons_split`, use the head-affineness (`D1_cons_add_zero`-analogue at stage s,
  coefficients beyond the head are head-independent), collapse the head sum by
  `Hsum_one_subst` at the c-independent part, factorise by `St_step` (StepK22) at the
  stage-s data, extract the factor `(X−X^{q^{s+1}})⁻¹`.

The stage-2 denominator `D2` (s=1 output, over the remaining `m` coefficients of a
degree-(m+2) polynomial) is defined below.  All declarations here are sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- the stage-2 denominator of the degree-(m+2) collapse, over the remaining
coefficients `u : Fin m → F` (`u⟨j⟩ = a_{j+2}`): `D2 m u := Σ_{m'<m+1} a_{m'+2}·hh 0 3 m'`
with the leading `a_{m+2} = 1` (via the `coeffSeq (m+2) (cons 0 (cons 0 u))` extension). -/
noncomputable def D2 (m : ℕ) (u : Fin m → F) : F[X] :=
  ∑ m' ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 2)) * hh F 0 3 m'

/-- record of the general statement: `D2` at level `m` is the `s=1` output denominator
`StateDen 2 m u` (definitional check of the index convention `m'+s+1 = m'+2`). -/
lemma D2_is_stage2 : D2 F = (fun (m : ℕ) (u : Fin m → F) =>
    ∑ m' ∈ Finset.range (m + 1), C (coeffSeq F (m + 2) (Fin.cons 0 (Fin.cons 0 u)) (m' + 2)) * hh F 0 3 m') := by
  rfl

end ZagierHoffmanPositiveChar
