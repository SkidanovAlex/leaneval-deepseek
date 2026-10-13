/-
  Area E7: **relative ambient locality of a stratum over a base cell** (`ambientLocality_proved`).

  Reference: `Submission/Work/WilE7/E7main_DESIGN.md` §4ter (and §4 step (A)), where the lemma is
  recorded as `ambientLocality_of_strat` (also written down as a target in
  `Submission/Work/WilE7/ambientLocality.lean`).  The statement proved here is that lemma with the
  projection-avoidance hypotheses `hC1`/`hC2` re-encoded as a single "forbidden locus"
  `Forbidden`, whose projection misses the base set `C`: an envelope cell `C` avoids the
  *closure* of every stratum frontier (`hSub1`) and of every "foreign zero" locus

      N_{S'} = {y | h_{S'}(y) = 0, y ∉ S'.X.set}   (`hSub2`).

  Proof (a one-step closure argument; no dimension theory, no `Good`, no implicit function
  theorem):

  * `hSub2` at `S' = S` (which is available because `hS : S ∈ L`) puts the closure of the
    `S`-external zero set `N_S` inside `Forbidden`.
  * `hForb` then says no point of `closure N_S` projects into `C`, and `projFirst p q z ∈ C`,
    so `z ∉ closure N_S`; equivalently `(closure N_S)ᶜ` is an open neighbourhood of `z`.
  * On that neighbourhood, `h_S(z') = 0` and `z' ∉ S.X.set` would force `z' ∈ N_S ⊆ closure N_S`,
    a contradiction; so the implication holds on a whole neighbourhood of `z`.

  Note (for the assembly): with `hSub2` quantified over *all* `S' ∈ L`, the hypotheses
  `hcov`, `hdisj`, `hSub1`, `hz` are not needed — the `S' = S` instance of `hSub2` already
  carries the whole avoidance content.  They are kept because the request fixes the statement.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Topology Filter

namespace Work.WilE7

/-- **Relative ambient locality.**  If the semi-Pfaffian set `X` is the union of the pairwise
disjoint strata of `L`, and the base set `C` avoids the projection of the envelope `Forbidden` —
which contains the closure of the frontier of every stratum and the closure of the set of
"foreign" zeros of every stratum's equations — then at every point `z` of a stratum `S ∈ L`
whose base `projFirst p q z` lies in `C`, the equations of `S` have no `S`-external zeros near
`z`: locally at `z`, a common zero of the equations of `S` belongs to `S.X.set`. -/
theorem ambientLocality_proved
    {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (L : List (WilkiesDesign.E.Stratum p q))
    (hcov : X.set = ⋃ S' ∈ L, S'.X.set)
    (hdisj : L.Pairwise (fun S' T => Disjoint S'.X.set T.X.set))
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hSub1 : ∀ S' ∈ L, closure S'.X.set \ S'.X.set ⊆ Forbidden)
    (hSub2 : ∀ S' ∈ L, closure {y : Fin (p + q) → ℝ |
        (∀ a : Fin S'.j, WilkiesDesign.E.eaEval S'.X.c (S'.h a) y = 0) ∧ y ∉ S'.X.set} ⊆ Forbidden)
    (S : WilkiesDesign.E.Stratum p q) (hS : S ∈ L)
    (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set)
    (hzC : WilkiesDesign.E.projFirst p q z ∈ C) :
    ∀ᶠ z' in nhds z,
      (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set := by
  -- The `S`-external zeros of the equations of `S`.
  have hsub : closure {y : Fin (p + q) → ℝ |
      (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) y = 0) ∧ y ∉ S.X.set} ⊆ Forbidden :=
    hSub2 S hS
  -- `z` is not in (the closure of) that locus, because it projects into `C`.
  have hzn : z ∉ closure {y : Fin (p + q) → ℝ |
      (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) y = 0) ∧ y ∉ S.X.set} :=
    fun hzcl => (hForb z (hsub hzcl)) hzC
  -- Hence a whole neighbourhood of `z` avoids it, and there the implication holds.
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzn] with z' hz'
  intro hzero
  by_contra hnotmem
  exact hz' (subset_closure ⟨hzero, hnotmem⟩)

end Work.WilE7
