import Mathlib
import Submission.CDTPlan.Interfaces

/-!
# Area Z (`Submission.CDTPlan.ZeroEstimate`) — shared notes for the `Work/ZeroEst/` lemmas.

This module just re-exports `Submission.CDTPlan.Interfaces` so that the lemmas proved under
`Submission/Work/ZeroEst/` can see the blueprint definitions
(`auxSeries`, `embedVar`, `PolyIndependent`, `DClosed`, `ZeroEstimate`).
It also collects the proof strategy we follow, for the colleagues proving the sub-lemmas.

## Where we are going

`Work.ZeroEst.zero_estimate : ZeroEstimate` is assembled as

```
theorem zero_estimate : ZeroEstimate := by
  intro m f hpi hdc
  obtain ⟨C, hC⟩ := one_var m f hpi hdc
  exact ⟨C, reduction m f C hC⟩
```

with

* `Work.ZeroEst.one_var`   — the one-variable Shidlovsky bound (paper Thm `Shidlovsky`, ε = 0),
* `Work.ZeroEst.reduction` — the multivariate lift: *if* the one-variable bound holds for `f` with
  constant `C`, *then* `ZeroEstimate`'s conclusion holds for `f` with the same constant `C`.

## `one_var` (the deep piece)

Classical; see Lang, *Introduction to transcendental numbers*, Ch. VII §3 (proof of
Shidlovsky's lemma) or Shidlovsky, *Transcendental numbers*, §3.5 Lemma 8. Lang's proof is
elementary (no Galois theory) and goes as follows. Write `Q` for the rational matrix with
`Q i j = A i j / q`, `T = q`, and `Y = (f_1,…,f_m)ᵀ`, so `Y' = Q Y`. For a column `P⁽¹⁾ = P` of
polynomials put `P⁽ᵏ⁺¹⁾ = T (D + Qᵀ) P⁽ᵏ⁾` (`D = d/dx`); then `P⁽ᵏ⁾` has polynomial entries with
`deg P⁽ᵏ⁾_j ≤ maxdeg P + k·N₀`, and `F_k := ⟨P⁽ᵏ⁾, Y⟩` satisfies `F_{k+1} = T·D F_k`, whence
`ord F_k ≥ ord F_1 - (k-1)`.

Let `r` be the `ℚ(x)`-rank of the `m×m` matrix `(P⁽ᵏ⁾_j)_{1≤k,j≤m}`. One shows
`ord F_1 ≤ r · maxdeg P + C₀`:

* if `r = m`, `Δ := det(P⁽ᵏ⁾_j) ≠ 0`, `deg Δ ≤ m·maxdeg P + O(1)`, and Cramer's rule gives
  `Δ·f_v = Σ_k c_{k,v} F_k` with polynomial cofactors, so
  `ord F_1 - (m-1) ≤ ord(Δ f_v) ≤ deg Δ + ord f_v ≤ m·maxdeg P + O(1)`;
* if `r < m`, Lang's Lemma 2.4 (bounded degree of the rational functions expressing a dependence
  among the rows) yields `Q_v := T(y_v + Σ_{j>r} A_{v,j} y_j)`, a polynomial combination of the
  `y_j` of BOUNDED degree and with `ord(Q_v) ≥ ord F_1 - r + 1`; Lang's Lemma 2.1 (polynomial
  combinations of bounded degree have bounded order) bounds `ord Q_v`, giving the claim.

The two genuinely separate ingredients of Lang's proof are delegated on their own and are meant to be
imported by whoever proves `one_var`:

* `Work.ZeroEst.fixed_deg_order_bound` (Lang's Lemma 2.1): for a FIXED degree bound `d`, the order of
  a nonzero combination `Σ Pᵢ fᵢ` with `deg Pᵢ ≤ d` is bounded by a constant depending on `f` and `d`.
  Proof: the space `E := {Σ Pᵢ fᵢ : deg Pᵢ ≤ d}` is finite-dimensional; the kernels of the maps
  `E → ℚ^N` (first `N` Taylor coefficients) are a decreasing sequence of subspaces of `E` with zero
  intersection, hence vanish for some `N₀`, so every nonzero element of `E` has order `< N₀`.

* `Work.ZeroEst.ratdep` (Lang's Lemma 2.2): if `X ⊆ ℚ⟦z⟧` is a finite-dimensional `ℚ`-space and
  `φ, ψ ∈ X` with `ψ ≠ 0` and `φ/ψ ∈ ℚ(z)`, then `φ/ψ = P/Q` with `deg P, deg Q ≤ N` for a constant
  `N` depending only on `X`.  (In the application `X` is the span of monomials of bounded degree in
  the entries of a fundamental solution matrix, and it is even closed under `d/dz`; proving the
  special case of a `d/dz`-stable `X` suffices.  This is a finite-dimensionality statement about
  ratios of power series; it is the only non-linear-algebra input to Shidlovsky's lemma.)

## Already PROVED modules that `one_var` may import

* `Submission.Work.ZeroEst.ratdep` : `Work.ZeroEst.ratdep`
  — Lang's Lemma 2.2.  If `X ⊆ ℚ⟦z⟧` is finite-dimensional over `ℚ` and `φ, ψ ∈ X`, `ψ ≠ 0`,
  `Q·φ = P·ψ` for some `Q ≠ 0`, then one can choose `P, Q` with `deg P, deg Q ≤ N` (`N = N(X)`).
  This is what bounds the degrees of the rational functions occurring in Lang's Lemma 2.4.
* `Submission.Work.ZeroEst.fixed_deg_order_bound` : `Work.ZeroEst.fixed_deg_order_bound`
  — Lang's Lemma 2.1.  For a FIXED degree bound `d`, `ord (Σ Pᵢ fᵢ) ≤ N(f, d)` whenever
  `deg Pᵢ ≤ d` and the combination is nonzero.

Both can be imported directly (`import Submission.Work.ZeroEst.ratdep`,
`import Submission.Work.ZeroEst.fixed_deg_order_bound`); they only depend on `Mathlib`.

## Roadmap for `one_var`: use Lang's DIRECT argument (do NOT induct on `m`)

Put `theta = q * d/dx` on `V = span_{Q(x)}(f)`, and `Lam Q = q*Q' + Q*Aᵗ` on coefficient vectors
(`orbit q A P k = Lam^k P`), so `theta (langle Q,f rangle) = langle Lam Q, f rangle`
(this is `one_var.lean`'s `Lam_dot`), and `ord (theta U) >= ord U - 1`.

Let `R = Σ Pᵢ fᵢ != 0`, `deg Pᵢ < D`, `s = ord R`, and `F k = <orbit^k P, f>` (so `ord F k >= s-k`).
Let `r` be the `Q(x)`-rank of the `m × m` matrix `(orbit q A P k j)_{k,j<m}`.  Then:

* `ord F 1 <= r * maxdeg P + C0` is the goal; since `r <= m` this gives `ord R <= m*D + C`.

**Case `r = m`** (`case_det`): `Δ := det (orbit q A P k j) != 0`, `deg Δ <= m*D + O(1)`; the adjugate
identity `adj B * B = Δ • 1` gives, with `g k = F k`, `Δ * f_ℓ = Σ_k (adj B)_{ℓ k} * g k`, whence
`ord F 1 - (m-1) <= ord Δ + ord f_ℓ <= deg Δ + ord f_ℓ`.

**Case `r < m`** (`lang24` + `fixed_deg_order_bound`): the first `r` orbit vectors
`P_1,…,P_r` (coefficient vectors) are independent and span the orbit; pick `J`, `|J| = r`, with
`P_I := (orbit q A P k ℓ)_{k in [r], ℓ in J}` invertible, and let `A := P_I⁻¹ P_II` (`P_II` = the
same rows on `Jᶜ`).  Lang's Lemma 2.4 (`lang24`) says `deg A_{ℓ j} <= d0`, a constant independent of
`P` and `D` — this is where `ratdep` is used.  Set `ỹ_ℓ := f_ℓ + Σ_{j∉J} A_{ℓ j} f_j` and let
`T != 0` be a common denominator of the `A_{ℓ j}`; then `F k = Σ_{ℓ∈J} (orbit q A P k ℓ) * ỹ_ℓ` for
`k <= r`.  Cramer with `A_0 := det P_I`: `A_0 * ỹ_ℓ = Σ_{k<=r} (cofactor) * F k`.  Put
`H_ℓ := T * ỹ_ℓ = T f_ℓ + Σ_{j∉J} (T * A_{ℓ j}) f_j`, a polynomial combination of the `f`'s of
degree `<= deg T + d0`, so `ord H_ℓ <= N_1` by `fixed_deg_order_bound`.  Then
`ord (A_0 H_ℓ) = ord A_0 + ord H_ℓ <= deg A_0 + N_1`, while
`ord (A_0 H_ℓ) = ord T + ord (Σ (cofactor) F k) >= ord F r >= s - (r-1)`.  Hence
`s <= (r-1) + deg A_0 + N_1 <= m*D + C`.  (No induction on `m` is used, so the constant depends
only on `f`.)

**Warning.** An induction on `m` along the lines "if the orbit is dependent, produce a smaller system
`g` with `R = Σ cg_l g_l`, `deg cg_l < D + c0`, and apply the induction hypothesis to `g`" does NOT
by itself yield a constant depending only on the original `f`: the Shidlovsky constant of the
sub-system `g` depends on `g`, hence on `P` and `D`.  Lang's argument above handles the dependent
case directly, with the same constant.

## `reduction` (what we can do without any ODE theory)

Given the one-variable bound `h1` for the family `f`, let `G := auxSeries f Q ≠ 0` and let
`n : Fin d →₀ ℕ` be a monomial of `G` of MINIMAL total degree (`Finsupp.degree`).
For each coordinate `j : Fin d`, extract the coefficient of `x^{(2),n^{(2)}}`
(`x^{(2)}` = the variables `≠ j`), i.e. define
`Φ_j(G) : ℚ⟦x_j⟧`, `(Φ_j G)(t) := MvPowerSeries.coeff (n with its j-coordinate set to t) G`.

Then:
* `(Φ_j G)(n j) = coeff n G ≠ 0`, and `(Φ_j G)(t) = 0` for `t < n j`, because the exponent
  `n.update j t` has total degree `< n.degree` there. So `(Φ_j G).order = n j`.
* `Φ_j G` is a polynomial combination `Σ_{a:Fin m} (R_a : PowerSeries ℚ) * f a` with
  `R_a : Polynomial ℚ` of degree `< D`. Reason: `G = Σ_i Q_i(x)·∏_s f_{i_s}(x_s)`; the coefficient
  of `x^{(2),n^{(2)}}` in `Q_i · f_{i_j}(x_j) · ∏_{s≠j} f_{i_s}(x_s)` is a polynomial in `x_j`
  obtained from `Q_i` by keeping only the terms whose `x^{(2)}`-exponent is `≤ n^{(2)}`, times the
  constants `∏_{s≠j} coeff_{n_s - k_s} f_{i_s}`; its `x_j`-degree is `≤ deg_{x_j} Q_i < D`.
  Grouping by `a = i j` gives the `R_a`.
* Apply `h1` to the polynomials `R_a` (degree `< D`) and the nonzero series `Φ_j G`
  (`= Σ_a R_a f_a`): `n j = (Φ_j G).order ≤ m·D + C`.

That last step is the whole point: it is exactly how the paper's `jumps Cartesian` produces the
coordinate bounds, and it needs no machinery beyond `MvPowerSeries` coefficient extraction.
Note `m = 0` is vacuous (`auxSeries = 0`), `d = 0` is trivial (the only exponent is `0`).
-/

open Submission.CDTPlan
