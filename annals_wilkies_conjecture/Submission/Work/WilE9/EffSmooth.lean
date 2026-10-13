/-
  WilE9 — the geometric input of the E9 assembly, stated as a *definition* so that the owners of
  E5/E7 have an exact, typed target to instantiate.

  Everything in this directory that E9 needs is proved except one geometric statement: near every
  point of the effectively smooth locus of a semi-Pfaffian set, the set *is* the zero set of
  `1 + m` equations whose Jacobian in the last `1 + m` coordinates is invertible (an ambient
  manifold description, not merely the fibrewise one supplied by `Stratum.Good`), and the locus
  is dense in the component.  See `STATUS.md` §2 for the analysis and for the two routes
  (strengthen the E5 stratum output, or fibre-cut with `E7_fiber_cut` in the split `(n, 1+m)` and
  then use the rank/dimension count).

  The conventions are those of `Work.WilE9.Ift.Basic`: the ambient space is `ℝ^{n + (1+m)}`, the
  *base* is the first `n` coordinates and the *fibre* the last `1 + m` (coordinate `n` is the
  graph coordinate `τ = ψ (f x)` and coordinates `n+1 … n+m` are the auxiliary `w`'s).
-/
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Filter Topology
namespace Work.WilE9
open WilkiesDesign WilkiesDesign.E

/-- **The geometric input of E9** (the only unproved input of the assembly; see `STATUS.md` §2).

For every bound `F` on the format there are a bound `a` on the format and a polynomial bound `b`
on the degree such that: for every semi-Pfaffian set `X ⊆ ℝ^{n + (1+m)}` of format `≤ F` and
every point `p` of it, there is a *smaller* semi-Pfaffian set `Y` — one basic condition `B` over
a chain `c` of the same length `X.r`, of format `≤ a` and degree `≤ b X.deg` — which is contained
in the connected component of `p` in `X.set`, is dense in it, and near every one of its points `z`
satisfies

* `Y.set` is locally *equal* to the zero set `{h = 0}` of `1 + m` EA polynomials `h`, and
* the Jacobian of `h` in the last `1 + m` coordinates is invertible at `z`.

The second point is what `WilE9.Ift.ift_exists` and `WilE9.Ift.ift_identity` consume: the
implicit function principle then writes the last `1 + m` coordinates as a `C^∞` function of the
first `n`, and BNZ's formula computes all its derivatives as `P_L / Q^{2|L|}` with degree
bounded additively in `|L|` (`WilE9.Deg.iftP_totalDegree_le`).  The density point is what makes
the resulting description of the derivative graph *complete* rather than merely dense. -/
def EffSmoothInput : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (n m : ℕ) (X : SemiPf (n + (1 + m))) (p : Fin (n + (1 + m)) → ℝ), X.fmt ≤ F →
      ∃ (c : EAChain (n + (1 + m)) X.r) (B : Basic (n + (1 + m)) X.r)
        (h : Fin (1 + m) → EAPoly (n + (1 + m)) X.r),
        (n + (1 + m) + X.r ≤ a) ∧ B.deg ≤ b.eval X.deg ∧
          (∀ z, z ∈ (⟨X.r, c, [B]⟩ : SemiPf (n + (1 + m))).set →
            z ∈ connectedComponentIn X.set p) ∧
          (∀ z ∈ (⟨X.r, c, [B]⟩ : SemiPf (n + (1 + m))).set,
            (∀ j, eaEval c (h j) z = 0) ∧
            (Matrix.of fun j l : Fin (1 + m) =>
              eaEval c (eaD c (Fin.natAdd n l) (h j)) z).det ≠ 0 ∧
            (∀ᶠ z' in 𝓝 z, (∀ j, eaEval c (h j) z' = 0) →
              z' ∈ (⟨X.r, c, [B]⟩ : SemiPf (n + (1 + m))).set)) ∧
          closure (⟨X.r, c, [B]⟩ : SemiPf (n + (1 + m))).set =
            closure (connectedComponentIn X.set p)

/-- The shape of the E9 assembly: `genSOMin.SharpDeriv` follows from the geometric input above
together with the results of areas E2 (components), E5/E6 (stratification, fibre closure) and E8
(`Gen ⊆ StarR`), all of which live in other parts of the tree. -/
def E9Reduction : Prop := EffSmoothInput → genSOMin.SharpDeriv

end Work.WilE9
