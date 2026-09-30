import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.applyDer_Qpoly_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Summands of the descended auxiliary polynomial `Q^{(J)}` (BW §20)

`Qdesc` (in `DefsAC`) is a sum over `lm : AuxIdx` of the terms of `Q` with
`λ_j ≡ μ_j (mod 2^J)`, in which `Y_j^{λ_j}` is replaced by `Y_j^{⌊λ_j/2^J⌋}` and `Y₀` by
`2^{-J}Y₀ + λ₋₁`.  We name the two factors of such a summand separately: the `Y₀`-part
`dy0part` and the torus monomial `dymon`; their product is `Qdescbase`. -/

namespace Work.BW

/-- The `Y₀`-part of a summand of `Qdesc` at level `J`: the value at `2^{-J}Y₀ + c₀` of the
`t₀`-th Hasse derivative of `(Δ(·;h))^d`. -/
noncomputable def dy0part {r : ℕ} (J h : ℕ) (c₀ : ℂ) (d t0 : ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  Polynomial.aeval
    (MvPolynomial.C (((2 : ℂ) ^ J)⁻¹) * MvPolynomial.X 0 + MvPolynomial.C c₀)
    (Polynomial.hasseDeriv t0 (deltaPoly h ^ d))

/-- The torus monomial `∏_j Y_j^{⌊μ_j/2^J⌋}` (`Y_j = X (j+1)`), the descended form of
`Y^μ`. -/
noncomputable def dymon {r : ℕ} (J : ℕ) (μ : Fin r → ℕ) : MvPolynomial (Fin (r + 1)) ℂ :=
  ymon (fun j => μ j / 2 ^ J)

/-- A summand of `Qdesc` at level `J` with residue `λ`: `Y₀`-part times torus monomial. -/
noncomputable def Qdescbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ)
    (lm : AuxIdx r h D0 Dj) (t0 : ℕ) : MvPolynomial (Fin (r + 1)) ℂ :=
  dy0part J h ((lm.1 : ℕ) : ℂ) ((lm.2.1 : ℕ) + 1) t0 * dymon J (fun j => (lm.2.2 j : ℕ))

end Work.BW
