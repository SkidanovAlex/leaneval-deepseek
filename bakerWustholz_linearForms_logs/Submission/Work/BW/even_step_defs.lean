import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Definitions for the even step of the Kummer descent (`extrap_even_step`, BW pp. 57–58).

At descent level `J` we have `S^{(J)} = ξ^{-rJ}S`, `T^{(J)} = ξ^{rJ}T` (`SJ`, `TJ` in `DefsAC`).
The even step extrapolates the vanishing of `Q^{(J+1)}_{μ'}` from the odd integers in
`|s| ≤ 4S^{(J)}` to *all* integers there, at order `ξ^{r+1}T^{(J)}`. It runs the §19 Cauchy/Blaschke
argument with the lacunary Blaschke product `B'(·;X)`, the point bound `X = 2S'`,
`R = 7.2S'`, `η = 1/3`, `κ = 1`, `δ = 5S'`, where `S' = ⌊2S^{(J)}⌋`.

This file contains only the parameter definitions of that step: the two numerical conditions that
the extrapolation needs, `ev_h1` and `ev_h2`, are stated in terms of them. -/

namespace Work.BW

/-- `S' = ⌊2S^{(J)}⌋` (BW's `S'` in §19, used with the floors of `S^{(J)}`). -/
noncomputable def evSP (r J : ℕ) (S : ℝ) : ℕ := ⌊2 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * S)⌋₊

/-- `X = 2S'`: the range of the lacunary Blaschke product `B'(·;X)` (even by construction); the
known odd points `|l| ≤ 4S^{(J)}` and the unknown point `|s| ≤ 4S^{(J)}` all satisfy `|·| ≤ X + 2`. -/
noncomputable def evX (r J : ℕ) (S : ℝ) : ℕ := 2 * evSP r J S

/-- `R = 7.2S'` (BW §19). -/
noncomputable def evR (r J : ℕ) (S : ℝ) : ℝ := 7.2 * (evSP r J S : ℝ)

/-- `T' = ⌊(1−ξ)ξ^rT^{(J)}⌋`: the order to which the Taylor coefficients at the known points are
controlled (it is `≤` the known vanishing order `ξ^rT^{(J)}`). -/
noncomputable def evTp (r J : ℕ) (T : ℝ) : ℕ :=
  ⌊(1 - pxi r) * pxi r ^ r * (pxi r ^ (r * J) * T)⌋₊

/-- `δ = 5S'`: since `‖s‖ ≤ 4S^{(J)} ≤ 2S' + 2` and `R = 7.2S'`, we have `‖s‖ + δ ≤ R`; so `R/δ`
bounds the `R/(R-‖s‖)` factor of the Cauchy estimate. -/
noncomputable def evdelta (r J : ℕ) (S : ℝ) : ℝ := 5 * (evSP r J S : ℝ)

/-- The exponent `U` of the circle bound (16) at level `J+1` in the even step: with `‖z‖ = R` and
`|s| ≤ 4S^{(J)}` the `(16)`-exponent `dhT* + 1.055SD + 1.008((‖z‖+|s‖)/2^{J+1})D + kum_{J+1}`
(with `T* = ξT^{(J)} = ξ^{r+1}T^{(J)}`) is at most this. -/
noncomputable def evU (r d h : ℕ) (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  (d : ℝ) * (h : ℝ) * (pxi r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
    + 1.055 * (pS r d h : ℝ) * pD r d σ
    + 1.008 * ((evR r J (pS r d h : ℝ) + 4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ)))
        / 2 ^ (J + 1)) * pD r d σ
    + 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ

/-- The exponent `V` of the Taylor bound (21) at level `J+1` in the even step: with `m ≤ T'` and
`|l| ≤ X`, `|s| ≤ 4S^{(J)}`, the `(21)`-exponent `dhT* + (1.133 − 9·2^r)SD
+ 1.01((|l|+|s|)/2^{J+1})D + kum_{J+1}` (with `T* = ξ^rT^{(J)} = ξ^{r+rJ}T`) is at most this. -/
noncomputable def evV (r d h : ℕ) (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  (d : ℝ) * (h : ℝ) * (pxi r ^ r * (pxi r ^ (r * J) * (pT r d σ : ℝ)))
    + (1.133 - 9 * (2 : ℝ) ^ r) * (pS r d h : ℝ) * pD r d σ
    + 1.01 * (((evX r J (pS r d h : ℝ) : ℝ) +
          4 * (pxi r ^ (-((r * J : ℕ) : ℤ)) * (pS r d h : ℝ))) / 2 ^ (J + 1)) * pD r d σ
    + 0.044 * ((J + 1 : ℕ) : ℝ) / Real.log (2 * r * d) * (pS r d h : ℝ) * pD r d σ

/-- `W` with `‖B'(s;X)^{T'+1}‖ ≤ e^{-W}`: from (23') for the lacunary product, with
`max(|s|,X) ≤ X + 2` and `R = 7.2S'`. -/
noncomputable def evW (r d h : ℕ) (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  (((evTp r J (pT r d σ : ℝ) + 1 : ℕ)) : ℝ) * (evX r J (pS r d h : ℝ) : ℝ)
    * Real.log (evR r J (pS r d h : ℝ) / ((evX r J (pS r d h : ℝ) : ℝ) + 2))

/-- `Y` with `sup_{C_l}‖B'(s;X)/B'(z;X)‖^{T'+1} ≤ e^Y`: from (25) with `η = 1/3` and
`max(1,|s|/X)^X ≤ e^2`. -/
noncomputable def evY (r d h : ℕ) (σ : Fin r → ℝ) (J : ℕ) : ℝ :=
  (((evTp r J (pT r d σ : ℝ) + 1 : ℕ)) : ℝ)
    * ((evX r J (pS r d h : ℝ) : ℝ) + 2 * Real.log (evX r J (pS r d h : ℝ) : ℝ) + 3)

end Work.BW
