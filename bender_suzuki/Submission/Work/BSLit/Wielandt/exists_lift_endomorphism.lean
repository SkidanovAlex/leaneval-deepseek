import Mathlib
import Submission.Work.BSLit.Wielandt.LiftIdempotentMatrix

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BSLit.Wielandt

/-! ## Note on the requested statement

The statement as originally written in this file was **not well-formed Lean 4** and could not be
made well-formed.  Its second occurrence of the reduction map read

```
= e (fun i => MonoidAlgebra.mapRingHom F
    (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp k)) hmm (x i)))
```

which (i) leaves the `(∀ x : …` group opened on the previous line unclosed — the parenthesis
balance is `+1`, and Lean's parser rejects the whole declaration with
`unexpected token ':='; expected ')', ',' or ':'` — (ii) contains the unfilled placeholder `hmm`
where `ZMod.castHom` expects its ring argument, and (iii) is ill-typed even after rebalancing the
parentheses, since `Nat.pos_iff_ne_zero : 0 < n ↔ n ≠ 0` makes `Nat.pos_iff_ne_zero.mp k` require a
proof of `0 < k` rather than `k : ℕ`, and since `ZMod.castHom … hmm` is then applied to `x i` with
`hmm` in the *type* argument position (`failed to synthesize instance of type class Ring hmm`).

What was meant — and what is stated and proved below — is the same reduction term as the first
occurrence, i.e. the ring hom `ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)`
applied to `x i`.  This is the formulation used by the requester in its own working files
(`_mltf/probe2.lean`, `Submission/Work/BSLit/Wielandt/FinrankRangeReduceGA.lean`).

## Lifting an idempotent endomorphism of `𝔽_p[F]^n` to `(ℤ/p^k)[F]^n`

`Work.BSLit.Wielandt.LiftIdempotentMatrix` lifts an idempotent matrix over the group algebra
`𝔽_p[F]` to an idempotent matrix over `(ℤ/p^k)[F]` reducing back to it.  Here we transfer that
statement to *linear maps*: every idempotent `A`-linear endomorphism `e` of `A^n`, `A = 𝔽_p[F]`,
is the coefficientwise reduction of an idempotent `B`-linear endomorphism `E'` of `B^n`,
`B = (ℤ/p^k)[F]`.

The obstruction is that `A` and `B` are **noncommutative** as soon as the finite group `F` is
nonabelian, so Mathlib's matrix/linear-map dictionary (`Matrix.toLin'`, `LinearMap.toMatrix'`,
`Matrix.mulVecLin`, `algEquivMatrix`) — all of which live under a `CommSemiring` hypothesis — does
not apply.  What *is* available for an arbitrary `Semiring R` is the row convention

* `Matrix.vecMulLinear M : (m → R) →ₗ[R] (n → R)`, `x ↦ x ᵥ* M`, anti-multiplicative in `M`
  (`Matrix.toLinearMapRight'_mul`), and
* `LinearMap.toMatrixRight' : ((m → R) →ₗ[R] (n → R)) ≃ₗ[Rᵐᵒᵖ] Matrix m n R`, whose inverse is
  `Matrix.vecMulLinear` (`Mathlib/LinearAlgebra/Matrix/ToLin.lean`).

So: take the matrix `Me := LinearMap.toMatrixRight' e` of `e`; it is idempotent because
`toMatrixRight'` is *anti*-multiplicative and `e` is idempotent.  Lift it to an idempotent `E'`
over `B` with `LiftIdempotentMatrix`, and set `E'lin := Matrix.vecMulLinear E'`.  Idempotency of
`E'lin` is `Matrix.vecMul_vecMul` plus `E' * E' = E'`, and the reduction condition is the
coefficientwise identity `φ ((v ᵥ* E') i) = ((φ ∘ v) ᵥ* E'.map φ) i`, i.e. `map_sum`/`map_mul`
together with `Matrix.map_apply`.-/

/-- **Lifting an idempotent endomorphism to `ℤ/p^k`.**  Let `F` be a finite group, `p` a prime,
`k ≥ 1` and `n : ℕ`.  Every idempotent `𝔽_p[F]`-linear endomorphism `e` of `(𝔽_p[F])^n` is the
coefficientwise reduction of an idempotent `(ℤ/p^k)[F]`-linear endomorphism `E'` of
`((ℤ/p^k)[F])^n`, the reduction being induced by `ZMod.castHom : ℤ/p^k →+* 𝔽_p`.

Route: `e` has matrix `LinearMap.toMatrixRight' e` in the row convention `x ↦ x ᵥ* M` (valid for
noncommutative coefficient rings), which is idempotent; `LiftIdempotentMatrix` lifts it to an
idempotent matrix `E'` over `(ℤ/p^k)[F]`, and `Matrix.vecMulLinear E'` is the required lift. -/
theorem exists_lift_endomorphism {F : Type*} [Group F] [Fintype F] {p k : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) {n : ℕ}
    (e : (Fin n → MonoidAlgebra (ZMod p) F) →ₗ[MonoidAlgebra (ZMod p) F]
        (Fin n → MonoidAlgebra (ZMod p) F)) (he : e * e = e) :
    ∃ E' : (Fin n → MonoidAlgebra (ZMod (p^k)) F) →ₗ[MonoidAlgebra (ZMod (p^k)) F]
        (Fin n → MonoidAlgebra (ZMod (p^k)) F),
      E' * E' = E' ∧
      (∀ x : Fin n → MonoidAlgebra (ZMod (p^k)) F,
        (fun i => MonoidAlgebra.mapRingHom F
            (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (E' x i))
          = e (fun i => MonoidAlgebra.mapRingHom F
              (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (x i))) := by
  classical
  -- the coefficientwise reduction `(ℤ/p^k)[F] →+* 𝔽_p[F]`
  set φ : MonoidAlgebra (ZMod (p ^ k)) F →+* MonoidAlgebra (ZMod p) F :=
    MonoidAlgebra.mapRingHom F (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p))
  -- the matrix of `e` in the row convention `x ↦ x ᵥ* M`
  set Me : Matrix (Fin n) (Fin n) (MonoidAlgebra (ZMod p) F) := LinearMap.toMatrixRight' e
    with hMe_def
  -- `he`, transported to the composition form used by the matrix dictionary
  have hcomp : e ∘ₗ e = e :=
    LinearMap.ext fun x => by rw [LinearMap.comp_apply, ← Module.End.mul_apply, he]
  -- `Me` is idempotent: `LinearMap.toMatrixRight'` is anti-multiplicative
  have hMe : Me * Me = Me := by
    rw [hMe_def, ← LinearMap.toMatrixRight'_comp e e, hcomp]
  -- lift `Me` to an idempotent matrix over `(ℤ/p^k)[F]`
  obtain ⟨E', hE'idem, hE'map⟩ := LiftIdempotentMatrix hk Me hMe
  -- `Matrix.vecMulLinear` inverts `LinearMap.toMatrixRight'`
  have htriv : Matrix.toLinearMapRight' Me = e := by
    rw [hMe_def]
    exact LinearEquiv.symm_apply_apply _ e
  -- the lift, as an endomorphism of `((ℤ/p^k)[F])^n`
  have hE'lin : (Matrix.vecMulLinear E') * (Matrix.vecMulLinear E') = Matrix.vecMulLinear E' :=
    LinearMap.ext fun v => by
      simp only [Module.End.mul_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hE'idem]
  refine ⟨Matrix.vecMulLinear E', hE'lin, ?_⟩
  intro x
  -- coefficientwise reduction commutes with the row convention
  have hmap : (fun i => φ ((Matrix.vecMulLinear E' x) i))
      = Matrix.vecMul (fun i => φ (x i)) (E'.map φ) := by
    funext i
    simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_apply_eq_sum, Matrix.map_apply, map_sum,
      map_mul]
  rw [hmap, hE'map]
  -- and the reduction of `E'` is the matrix of `e`
  rw [← htriv, Matrix.toLinearMapRight'_apply]

end Work.BSLit.Wielandt
