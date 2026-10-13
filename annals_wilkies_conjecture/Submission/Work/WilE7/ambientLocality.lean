/-
  Area E7: **relative ambient locality of a `Good` stratum over a base cell.**

  This is the corrected replacement for the E9 owner's `Work.WilE9.Sharp.EffStrat` request (see
  `E7main_DESIGN.md` §4ter for the refutation of `EffStrat` as stated: for the minimal `Z`,
  `X.set = {0} ⊆ ℝ²`, `n = 1`, `m = 0`, `Z = {0}`, the `Z`-clause and density force a stratum
  whose `EffStratum.Good` would need an EA `h` with `h(0) = 0`, `∂h/∂x₁(0) ≠ 0` and
  `{h = 0} = {0}` near `0`; `hE5` also carries only the *fibrewise* locality).

  What is true, and is what the sheet lemma of `E7main_DESIGN.md` §4 (step (A)) consumes, is the
  *relative* form: over a base cell `C`, a stratum of a covering, pairwise-disjoint list is
  ambiently local at each of its points whose base lies in `C`, provided the foreign zeros of the
  stratum's equations are excluded from `C` through the locus `Forbidden`.

  **Proof** (dichotomy; no dimension theory, no `Good`, no `hE2`).  If the conclusion failed at
  `z`, there would be `z_k → z` with `h_S(z_k) = 0` (all equations of the stratum `S`) and
  `z_k ∉ S.X.set`.

  * If `z_k ∈ X.set` for infinitely many `k`, then `z_k ∈ S'` for some `S' ∈ L` with `S' ≠ S`;
    hence `z ∈ closure S'.X.set` and `z ∉ S'.X.set` (the strata are pairwise disjoint and
    `z ∈ S.X.set`), i.e. `z ∈ closure S'.X.set \ S'.X.set`, so `π_p(z) ∈ Forbidden ∩ C` by
    `hSub1` and `hForb` — contradiction.
  * Otherwise `z_k ∉ X.set` for infinitely many `k`; these `z_k` are zeros of `h_S` outside
    `S.X.set`, so `z` lies in `closure {y | h_S(y) = 0 ∧ y ∉ S.X.set}`, and `hSub2` + `hForb`
    contradict `π_p(z) ∈ C`.

  **Discharge of the two `⊆ Forbidden` inclusions** (in the assembly, not here): the frontier
  `closure S'.X.set \ S'.X.set` is the set of a `SemiPf` set with format `const(F)` and degree
  `poly_F(D)` by `hE6` at `p = 0` (`Work.WilE7.E6closure`, proved), and `{y | h_{S'}(y) = 0}` is
  the set of a `SemiPf` set over the same chain (write the equations `S'.h` into the basics, the
  `critSet` pattern of `FiberCutDefs.lean`); the closure of the difference is then again of the
  same provenance.  So both loci are built from the base family and avoided by the base cells.

  Encoding note: `𝓝` is *not* in resolution in a bare delegation payload (only `nhds` is), which
  is why this statement is filed as a module under this area's standard header rather than handed
  out as a payload; see `_probe_ambient.lean` for the probe evidence.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.ambientLocality_proved

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **Relative ambient locality.**  If the semi-Pfaffian set `X` is a union of the pairwise
disjoint strata of `L`, and `C` is a set of base points avoiding the locus `Forbidden`, which
contains both the frontiers of the strata and the closures of their foreign zero sets, then at
every point `z` of a stratum `S ∈ L` whose base lies in `C`, the equations of `S` have no
`S`-external zeros near `z`. -/
theorem ambientLocality_of_strat
    {p q : ℕ} (X : SemiPf (p + q)) (L : List (Stratum p q))
    (hcov : X.set = ⋃ S' ∈ L, S'.X.set)
    (hdisj : L.Pairwise (fun S' T => Disjoint S'.X.set T.X.set))
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, projFirst p q w ∉ C)
    (hSub1 : ∀ S' ∈ L, closure S'.X.set \ S'.X.set ⊆ Forbidden)
    (hSub2 : ∀ S' ∈ L, closure {y : Fin (p + q) → ℝ |
        (∀ a : Fin S'.j, eaEval S'.X.c (S'.h a) y = 0) ∧ y ∉ S'.X.set} ⊆ Forbidden)
    (S : Stratum p q) (hS : S ∈ L)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set)
    (hzC : projFirst p q z ∈ C) :
    ∀ᶠ z' in nhds z,
      (∀ a : Fin S.j, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set :=
  Work.WilE7.ambientLocality_proved X L hcov hdisj C Forbidden hForb hSub1 hSub2 S hS z hz hzC

end Work.WilE7
