/-
# `H6Pair6Aux/h6pair_N0_zero` — the `N₀` zero mode: `|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K α^{-9}(1+M)^4`

The `N₀`-half of the zero-mode estimate of Elgindi's Proposition `muestimate` (tex 1508--1526),
in the level-six coercivity class `H6Adm` of the strong-persistence route (`f` is a slice of the
modulation `g`): for `H6Adm α f`, `HkMem α 7 f` and `Xn α f ≤ M = |f|_{ℋ⁴}`,

`|L₁₂(N₀ α (F_*+f) f)(0)| ≤ 10⁵ · α^{-9} · (1+M)^4`   for `0 < α ≤ 1`.

This is the level-six analogue of the *proved* level-four row `Nonlinear.Pieces.rl0_bound`.  The
estimate involves **no** elliptic input (`N₀` is built from the explicit profile `F_*` and from
`f` alone), so it is proved here from three purely `ℋ⁴`-analytic pieces, each proved in a sibling
file of this directory:

* `l12_supAbs_open` — the pointwise `|L₁₂(f)(z)| ≤ 3|f|_{ℋ⁴}` (`z ≥ 0`) for `SmoothOpen` +
  `HkMem α 4` data (the `SmoothOpen` form of `Nonlinear.Pieces.supAbs_L12_le`);
* `contN0_open` — joint continuity of `N₀` on the open quadrant;
* `N0_sq_w_open` — the pointwise domination of `N₀²` by the `ℋ⁴`-integrand of `f`, with the two
  coefficients `A₀`, `B₀` of `Rl0Defs`.

The assembly (the `hsup`/`hcont`/`hpt` → conclusion reduction) is
`Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N0_zero_of_pieces` in `Rl0Pieces.lean`, which is
proved independently of the three pieces; this file only feeds them in.  The class transfer
`H6Adm α f → SmoothOpen f ∧ HkMem α 4 f` is `H6Adm.reg` plus `HkMem_four_of_six`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Rl0Pieces
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.l12_supAbs_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.contN0_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0_sq_w_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

theorem h6pair_N0_zero : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      |Work.Construction.L12 (Work.Construction.N0 α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) 0|
        ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  refine h6pair_N0_zero_of_pieces ?_ ?_ ?_
  · intro α g hα hα1 hso hmem
    exact l12_supAbs_open hα hα1 hso hmem
  · intro α g hα hα1 hso hmem
    exact contN0_open hα hα1 hso hmem
  · intro α g hα hα1 hso hL12g
    exact N0_sq_w_open hα hα1 hso hL12g

end Work.FTS.StrongPersist.H6Pair6Aux
