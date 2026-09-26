/-
# The two analytic inputs of the cusp-`±1` *layer* bound (design doc)

## The goal this file serves

`Work.Asymptotics.cuspTile_seminorm_bound` (in `Submission/Work/Asymptotics/cuspTile_seminorm_bound.lean`)
is the `r`-seminorm bound `|r|^k ‖∂_r^l (kernelTransform (Kfun ℓ d) (n+w) ·) r‖ ≤ C (scale w)^N`
for `w ∈ E = KEpsilon` and `n = ±1`.

Its *proved* socket `cuspTile_seminorm_bound_of_layer` reduces it to the bound of the CKMRV layer
`layer (Gcusp ℓ d) ℓ d (n+w) · = layerLow + layerTrunc + highPart` on the tile.  The three pieces
are analysed separately:

* `layerLow ℓ d σ r = sinSq r · ∫_0^1 Kaxis K σ t · e^{-πr²t} dt` contains the **genuine pole**
  `z = w = σ - n` of `z ↦ K(σ,z)` (residue `n/(2π)`, `Work.Residues.hasResidue_Kfun_second'`),
  whose height `Im w ≤ 1/2` lies inside the integration interval;
* `layerTrunc` integrates `K - Aexp` over `[1,∞)` (no pole near the contour);
* `highPart` is the closed form of `sinSq r ∫_1^∞ Aexp e^{-πr²t}dt`.

## The two inputs defined here

* `TilePPWindow ℓ d` — the **principal-part window** on the tile: on `[Im w/2, 1]` the kernel
  differs from its translate pole `(n/2π)/(it - w)` by at most `C (scale w)^N`.
* `TileTail ℓ d` — the **tile cusp-`i∞` tail**: beyond height `1` the kernel differs from its
  cusp model `Aexp (Gcusp ℓ d)` by `O((scale w)^N t^M e^{-πt})`.

## The proof of `layerLow` on the tile from `TilePPWindow` (the plan)

`layerLow_tile_seminorm` (`Submission/Work/Asymptotics/Tile/tileLayerLow.lean`) splits
`(0,1] = (0, Im w/2] ∪ [Im w/2, 1]`:

1. **Below the pole** (`0 < t ≤ Im w/2`) the proved flatness `Kaxis_tile_flat_below_pole` gives
   `‖Kaxis K (n+w) t‖ ≤ c (scale w)^{N'} t^N` (for every `N`); together with the weight bound
   `|r|^k ‖∂_r^l (sinSq · · e^{-π·²t})‖ ≤ Γ t^{-(k+l)}` (`sinSq_gauss_seminorm`) and `N = k+l+1`
   this makes the integrand `≤ cΓ(scale w)^{N'} t`, whose integral over `(0, Im w/2]` is
   `≤ cΓ(scale w)^{N'}/8`.
2. **On `[Im w/2, 1]`** write `K = PP + R` with `PP(t) = (n/2π)/(it - w)`:
   * the `R`-part is bounded by `C (scale w)^N · Γ ∫_{Im w/2}^1 t^{-(k+l)}dt ≤ C' Γ (scale w)^{N+k+l}`;
   * for the `PP`-part split the *weight*:
     `∫ PP·∂^l h = ∂^l h(·, Im w)·∫ PP + ∫ PP·(∂^l h(·,t) - ∂^l h(·,Im w))dt`.
     The first term is controlled by `tile_pole_integral_decay 0 0` (the **signed** pole integral,
     which is where the logarithmic divergence of `∫|PP|` disappears) and by the weight bound at
     `t = Im w`; in the second term the mean-value factor `|t - Im w|` cancels the pole, because
     `|it - w|² = (t - Im w)² + (Re w)² ≥ (t - Im w)²`, and the remaining bound on
     `∂_t ∂^l_r h(r,·) = -π ∂^l_r(r² h)(r,·)` follows from the `r²`-weighted Leibniz rule applied
     to `sinSq_gauss_seminorm` with the pairs `(k+2,l)`, `(k+1,l-1)`, `(k,l-2)` together with the
     Gaussian decay `sup_r |r|^M e^{-πut} ≤ (M/(2πte·u))^{M/2}` (`abs_pow_mul_exp_le`).
3. Differentiation under the integral sign on the two sub-intervals is
   `iteratedDeriv_intervalIntegral_of_meas_bound_interval`
   (`Submission/Work/Asymptotics/Tile/tileIntervalDeriv.lean`), with the dominating functions
   `t ↦ c Γ_j (scale w)^{N'} t^{N-j}` on `(0, Im w/2]` (flatness) and the constant
   `t ↦ B Γ_j (2/Im w)^j` on `[Im w/2, 1]` (`B` bounding `Kaxis` there — this is where
   `Re w ≠ 0` is used).  Note for `Re w = 0` the pole sits *on* the contour: the integrand is not
   integrable, `∫_0^1 = 0` is Lean's junk value and `layerLow ≡ 0`; that case is handled at the
   level of the target (`kernelTransform` is the junk value `0` there, so the target is trivial).

## The proof of the tail (plan)

`TileTail` is the tile analogue of the proved cusp-`0` tails `Work.Asymptotics.EtailE_KPlus8`,
`EtailE_KPlus24`, `EtailE_KMinus8`, `EtailE_KMinus24` (base point `w ∈ E`, threshold
`Ethresh w t = 2 Im(S·w) + 1 ≤ t`) and of `Tile.Ncusp_tile_crude`/`Tile.Ncusp_tile_sharp` (the
`K_-` cusp part `Ncusp` at the tile points).  The threshold here is `t ≥ 1`; the `K_+` half at the
tile is the genuinely new piece (the translations `n +ᵥ w` are *not* related to `w` by the
`τ`-affine law `K(τ+1,·) = 2K(τ,·) - K(τ-1,·)` alone, since that law does not determine the
translate at `n = ±1` from `n = 0`).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-- **The principal-part window on the cusp-`±1` tiles.**  For `w ∈ E = KEpsilon`, `n = ±1` and
`Im w / 2 ≤ t ≤ 1`, the kernel `K(n+w, it)` differs from the principal part of its translate pole
`z = w` (residue `n/(2π)`) by at most `C (scale w)^N`.

Equivalently: the function `z ↦ K(n+w,z) - ((n/2π))/(z - w)` is *bounded* on the window
`{it : Im w/2 ≤ t ≤ 1}` by a power of `scale w`, uniformly in the tile.  (It is in fact
holomorphic in a neighbourhood of `z = w`, the pole being simple with residue `n/(2π)`; the
content of the statement is the uniformity of the bound on the *tile*, where `Re w → 0` makes the
pole approach the contour.) -/
def TilePPWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ n : ℤ,
    (n = 1 ∨ n = -1) → ∀ t : ℝ, w.im / 2 ≤ t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((t : ℂ) * Complex.I - (w : ℂ))⁻¹)‖
      ≤ C * (Work.Kernels.scale w) ^ N

/-- **The cusp-`i∞` tail on the cusp-`±1` tiles.**  For `w ∈ E`, `n = ±1` and
`scale w ≤ t` — a height above every pole of `z ↦ K(n+w,z)`, since all orbit heights are
`≤ 1/Im(n+w) = 1/Im w ≤ scale w` — the kernel `K(n+w, it)` differs from its cusp model
`Aexp (Gcusp ℓ d) (n+w) t` by `O((scale w)^N t^M e^{-πt})`.

This is the tile analogue of the proved cusp-`0` statement `Work.Asymptotics.ETAilE_one` (same
threshold `scale w`), and of `Work.Asymptotics.Khat_funnel_tail_sharp` on the funnel. -/
def TileTail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ n : ℤ,
    (n = 1 ∨ n = -1) → ∀ t : ℝ, Work.Kernels.scale w ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
      ≤ C * (Work.Kernels.scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t))

/-- **The polynomial window on the cusp-`±1` tiles.**  For `w ∈ E`, `n = ±1` and
`1 ≤ t ≤ scale w` (below every pole of `z ↦ K(n+w,z)`), the kernel `K(n+w, it)` differs from its
cusp model `Aexp (Gcusp ℓ d) (n+w) t` by `O((scale w)^N t^M)`.

This is the tile analogue of the proved cusp-`0` statement
`Work.Asymptotics.EpolyWindowE_one`. -/
def TileWin (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ n : ℤ,
    (n = 1 ∨ n = -1) → ∀ t : ℝ, 1 ≤ t → t ≤ Work.Kernels.scale w →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        - Aexp (Gcusp ℓ d) ((n : ℝ) +ᵥ w) t‖
      ≤ C * (Work.Kernels.scale w) ^ N * t ^ M

/-- **The cusp-`±1` tile as a set** (the same set as `Work.Asymptotics.cuspTile` of
`cuspTile_seminorm_bound.lean`, repeated here so that the tile layer analysis does not need the
file that carries the target). -/
def cuspTileSet : Set ℍ :=
  {σ | ∃ w : ℍ, w ∈ KEpsilon ∧ ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ σ = (n : ℝ) +ᵥ w}

end Work.Asymptotics
