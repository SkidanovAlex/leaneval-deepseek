/-
  WilE9 / Sharp — the *geometric input* of the E9 assembly.

  BNZ §3 stratifies the ψ-image `Z` of the graph of `f` into *effectively smooth* pieces: at each
  point of a piece the `1 + m` equations `h` vanish, their Jacobian in the `1 + m` fibre
  coordinates is invertible (`dF₁ ∧ … ∧ dF_{N-n} ≠ 0`), and — this is what the implicit-function
  theorem part of the proof consumes — the set is *ambiently* locally the zero set of the
  equations.  The frozen `E5_strat` gives such a stratification only *fibrewise* (its `Good` is
  `{S.h = 0}` on the fibre over the base point) and only as an *exact* cover of the set, so the
  passage `E5_strat + E7_fiber_cut (+ E2_components) → EffStrat` still has to be carried out; see
  `Sharp/STATUS.md` §5.

  **Why `EffStrat` is not stated for an arbitrary `SemiPf` set and point.**  An earlier version
  asked, for every `SemiPf` set `X` and every `z₀ ∈ X.set`, for `Good` strata *inside*
  `connectedComponentIn X.set z₀` that are dense in it.  That version is false whenever the
  component is an isolated point: take `n ≥ 1` and `X.set = {z₀}` (e.g. `n = 1`, `m = 0`, the
  origin of `ℝ²` cut out by `x = 0, y = 0`).  Then every stratum's set is contained in `{z₀}`, and
  density forces one of them to be `{z₀}`; but at such a point the invertibility of the fibre
  Jacobian makes the zero set of the equations locally a graph over a neighbourhood of the base
  point — infinitely many points for `n ≥ 1` — contradicting the ambient locality clause of
  `Good`.  So no `Good` stratum can sit in a `0`-dimensional component.

  The version below is the statement BNZ actually use, in the `(n, 1 + m)` split that E9 needs,
  and it is not sensitive to degenerate components:

  * the strata are required to *project* into the prescribed set `Z` (this is what the assembly
    needs: every stratum point must map into `Z`), rather than to lie inside the component — so in
    the isolated-point case one can use the effectively smooth strata of the graph of `f` near
    `z₀`, which exist but are not contained in `X`;
  * the density is required in the *projection* of the component (i.e. in the `*`-piece), which
    is what the closure step of the assembly consumes;
  * the stratum's set must have at most `b X.deg` disjuncts (the degree `X.deg` alone does not
    bound the number of disjuncts — an empty disjunct has degree `0` — and the number of disjuncts
    is what the extended construction pays for).

  Everything downstream of this input is proved in this directory; the input itself is the
  E5/E7 owner's job (BV §3 + GV 1995 + Gabrielov 1998 for the ambient locality, as described in
  `Submission/Work/Wilkies/E/LEAD_E7_fiber_cut_fix.md`).
-/
import Submission.Work.WilE9.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical Filter Topology
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The canonical identification of the two writings of a `*`-piece's ambient dimension. -/
def stratInj {n m : ℕ} : Fin ((n + 1) + m) → Fin (n + (1 + m)) :=
  Fin.cast (by omega : (n + 1) + m = n + (1 + m))

/-- Projection of a point of the stratum's ambient `ℝ^{n + (1+m)}` to the first `n+1`
coordinates — the coordinates of the `*`-piece it comes from.  This is `projFirst (n+1) m`
after the canonical identification of the two ambient dimensions (`stratInj`).

It is defined here (rather than in `Vocab.lean`, where it is used together with the rest of the
extended-system vocabulary) because `EffStrat` below is stated in terms of it and
`Layout`/`PbSystem` import this file. -/
def stratProj {n m : ℕ} (w : Fin (n + (1 + m)) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => w (stratInj (Fin.castAdd m i))

/-- An effectively smooth stratum of the E9 assembly: an EA set `X : SemiPf (n + (1+m))` with
`1 + m` equations `h` (so that the number of equations equals the number of *fibre* coordinates,
the base being the first `n`).  This is `Stratum n (1 + m)` with `j := 1 + m`. -/
structure EffStratum (n m : ℕ) where
  X : SemiPf (n + (1 + m))
  h : Fin (1 + m) → EAPoly (n + (1 + m)) X.r

/-- The degree budget of a stratum: the degree of the set plus the atom degrees of the
equations. -/
def EffStratum.deg {n m : ℕ} (E : EffStratum n m) : ℕ :=
  E.X.deg + ∑ a, atomDeg (E.h a)

/-- **Effective smoothness** of a stratum: at every point of `X.set` the equations vanish, their
Jacobian in the `1 + m` fibre coordinates is invertible, and `X.set` is ambiently locally equal
to the zero set of the equations. -/
def EffStratum.Good {n m : ℕ} (E : EffStratum n m) : Prop :=
  ∀ z ∈ E.X.set,
    (∀ a, eaEval E.X.c (E.h a) z = 0) ∧
    (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
      eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a)) z).det ≠ 0 ∧
    (∀ᶠ z' in 𝓝 z, (∀ a, eaEval E.X.c (E.h a) z' = 0) → z' ∈ E.X.set)

/-- **The (superseded, and false) geometric input of E9.**

**This statement is FALSE, both with and without the `interior … = ∅` proviso below.**  The
sharp refutation is `WilkiesDesign.E.Gaps.not_effStrat` (the lead's design file
`sources/wilkiesE3E9/wilkies_E3E9_gaps.lean`, §GAP 2): take `n = 1`, `m = 0`, `X = {0} ⊆ ℝ²`,
`z₀ = 0`, `Z = {0}`; the interior of `{0}` is empty, so the proviso holds, and density forces a
stratum with `0 ∈ E.X.set ⊆ Z = {0}`, which `Good` contradicts (the invertible `1 × 1` fibre
Jacobian plus ambient locality make `E.X.set ⊇ {h = 0}` near `0`, a curve).

(Without the proviso one can also refute it with `n = m = 0`, `X` the whole cube and `z₀ = 0`:
see `Work.WilE9.Sharp.not_effStrat_unrestricted` and `EffStratUnrestricted` below.)

The definition is kept, with its body unchanged, because the lead's design file imports this
module and states `¬ EffStrat` against it.  The input that E9 actually uses is
`Work.WilE9G.EffStratAE` (`Submission/Work/WilE9G/Defs.lean`): strata carrying a base point, only
the component through it used, the covering almost everywhere, and the number of hidden fibre
coordinates free.  See `Sharp/AE/PLAN.md` (G5) and `Sharp/STATUS.md` §S4. -/
def EffStrat : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (n m : ℕ) (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
      (Z : Set (Fin (n + 1) → ℝ)),
      X.fmt ≤ F → z₀ ∈ X.set →
      interior (stratProj '' connectedComponentIn X.set z₀) = ∅ →
      (∀ w ∈ connectedComponentIn X.set z₀, stratProj w ∈ Z) →
      ∃ L : List (EffStratum n m), L.length ≤ b.eval X.deg ∧
        (∀ E ∈ L, E.X.fmt ≤ a ∧ E.deg ≤ b.eval X.deg ∧
          E.X.basics.length ≤ b.eval X.deg ∧ E.Good ∧
          (∀ w ∈ E.X.set, stratProj w ∈ Z)) ∧
        (∀ y : Fin (n + 1) → ℝ, y ∈ stratProj '' connectedComponentIn X.set z₀ →
          y ∈ closure (⋃ E ∈ L, stratProj '' E.X.set))

/-- **The unrestricted form of `EffStrat` — false.**  This is `EffStrat` with the
`interior … = ∅` proviso removed.  It is *refuted* by
`Work.WilE9.Sharp.not_effStrat_unrestricted`: take `n = m = 0`, `X` the whole cube `[-1,1]`
(in the one-coordinate ambient space) and `z₀ = 0`; then the component is `[-1,1]`, and a finite
union of projections of `Good` strata is a finite union of sets which are locally `{h = 0}` with
`h' ≠ 0`, hence cannot be dense in a nondegenerate interval (a `Good` stratum has empty interior,
and a finite union of closed sets of empty interior has empty interior).

The definition is kept here, next to `EffStrat`, so that the two forms can be compared. -/
def EffStratUnrestricted : Prop :=
  ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (n m : ℕ) (X : SemiPf (n + (1 + m))) (z₀ : Fin (n + (1 + m)) → ℝ)
      (Z : Set (Fin (n + 1) → ℝ)),
      X.fmt ≤ F → z₀ ∈ X.set →
      (∀ w ∈ connectedComponentIn X.set z₀, stratProj w ∈ Z) →
      ∃ L : List (EffStratum n m), L.length ≤ b.eval X.deg ∧
        (∀ E ∈ L, E.X.fmt ≤ a ∧ E.deg ≤ b.eval X.deg ∧
          E.X.basics.length ≤ b.eval X.deg ∧ E.Good ∧
          (∀ w ∈ E.X.set, stratProj w ∈ Z)) ∧
        (∀ y : Fin (n + 1) → ℝ, y ∈ stratProj '' connectedComponentIn X.set z₀ →
          y ∈ closure (⋃ E ∈ L, stratProj '' E.X.set))

/-- `EffStrat` is exactly the unrestricted form with the empty-interior proviso added. -/
theorem EffStrat_of_unrestricted_iff (h : EffStratUnrestricted) : EffStrat :=
  fun F => by
    obtain ⟨a, b, hb⟩ := h F
    exact ⟨a, b, fun n m X z₀ Z hf hz _ hZ => hb n m X z₀ Z hf hz hZ⟩

end Work.WilE9.Sharp
