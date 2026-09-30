import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary definitions for `Work.BW.stab_closedSub`.

`transl x : MR N →ₐ[ℂ] MR N` is a ℂ-algebra substitution depending on the parameter
`x : Fin (N+1) → ℂ`.  To say that "the coefficients of `transl x F` are polynomials in `x`"
we build the universal substitution `translFam : MR N →ₐ[ℂ] GPoly N`, whose values are
polynomials in the `N+1` group coordinates and whose coefficients lie in `MR N`; evaluating
those coordinates at `x` recovers `transl x`.

For a linear functional `μ` on `MR N` this turns `x ↦ μ (transl x F)` into the honest
polynomial `cruxPoly F μ`; `invSub K q` is the "denominator-cleared" pullback of `q` along
`x ↦ ginv x` inside `G`. -/

namespace Work.BW

/-- Polynomials in the `N + 1` group coordinates `Y₀,…,Y_N`, with coefficients in `MR N`:
the universal target of the substitution defining `transl`. -/
abbrev GPoly (N : ℕ) := MvPolynomial (Fin (N + 1)) (MR N)

/-- Universal graph of the substitution defining `transl`:
`X_{i0} ↦ X_{i0}`, `X_{01} ↦ X_{01} + Y₀X_{00}`, `X_{i+1,1} ↦ Y_{i+1}X_{i+1,1}`,
where `Y` are the group coordinates. -/
noncomputable def gCoord {N : ℕ} (v : Fin (N + 1) × Fin 2) : GPoly N :=
  open Classical in
  if v.2 = 0 then MvPolynomial.C (MvPolynomial.X v : MR N)
  else if v.1 = 0 then
    MvPolynomial.C (MvPolynomial.X v : MR N) +
      MvPolynomial.C (MvPolynomial.X (0, 0) : MR N) * (MvPolynomial.X 0 : GPoly N)
  else MvPolynomial.C (MvPolynomial.X v : MR N) * (MvPolynomial.X v.1 : GPoly N)

/-- The universal substitution: specialising the coordinates `Y` at `x` gives `transl x`. -/
noncomputable def translFam {N : ℕ} : MR N →ₐ[ℂ] GPoly N :=
  MvPolynomial.aeval gCoord

/-- The polynomial in the variables `x` representing `x ↦ μ (transl x F)`. -/
noncomputable def cruxPoly {N : ℕ} (F : MR N) (μ : MR N →ₗ[ℂ] ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ s ∈ (translFam F).support,
    MvPolynomial.C (μ ((translFam F).coeff s)) *
      s.prod (fun i e => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ^ e)

/-- The pullback of `q` along `x ↦ ginv x`, with the `gᵢ⁻¹` cleared by `K` extra powers
of `Y_{i+1}`: `eval g (invSub K q) = (∏ i, (g i.succ)^K) * eval (ginv g) q` on `G`. -/
noncomputable def invSub {N : ℕ} (K : ℕ) (q : MvPolynomial (Fin (N + 1)) ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ s ∈ q.support,
    MvPolynomial.C (q.coeff s) * ((-MvPolynomial.X (0 : Fin (N + 1)))^(s 0)) *
      ∏ i : Fin N, (MvPolynomial.X i.succ)^(K - s i.succ)

end Work.BW
