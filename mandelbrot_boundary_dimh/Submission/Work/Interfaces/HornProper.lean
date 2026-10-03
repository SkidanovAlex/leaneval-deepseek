import Mathlib
import Submission.Work.Interfaces.HornParts

/-!
# The per-component clause of Shishikura's Lemma 5.4 as an interface object

This is the single remaining input of `Work.Horn.horn_germ_F0`, isolated as a first-class interface
object in the same style as `HornTopoStatement`/`HornSCStatement`.  It is deliberately

* **per family of petal components**, not a `∀ q` statement: a `∀ q` form ("for every germ
  expansion the spreads are immediate basins with a critical point") is REFUTABLE for `q ≥ 2`,
  because the counting step `Work.Horn.eq_one_of_invariant_disjoint` then contradicts the single
  critical value — see `NOTES_GERM_F0.md` §68.3;
* **confined to the bounded upper piece** (`B' i ⊆ {0} ∪ π '' BuOf`, clause 5 of
  `Work.Horn.petal_components_upper_local`): with this hypothesis the known whole-basin
  counterexample (a machine-checked infinite bounded fibre accumulating on
  `frontier D_g ∖ {0} ⊆ (insert 0 (π '' d.DE))ᶜ`, `H15-L2282`) is excluded, and no counterexample is
  known for the per-component claim;
* the honest content of the paper's "`g₀ : B_i → B_i` is a proper branched covering with at most one
  critical point, hence `B_i` is an immediate parabolic basin" — Shishikura *defines* an immediate
  basin to include properness and warns that a parabolic fixed point need not have one, so the
  properness clause cannot be free.

What is *proved* (this session) around it: the petal components exist and are `g`-invariant with the
capture property and sit in the upper piece (`Work.Horn.petal_components_upper_local`); properness of
such a component is *equivalent* to the per-component confinement
`closure (B' i ∩ g ⁻¹' L) ⊆ insert 0 (π '' d.DE)` (`Horn/component_confinement`'s prover); and
properness implies surjectivity `B' i ⊆ g '' B' i` (`Work.Horn.spread_surj_on_component`).  So the
only unproved clauses left below this object are properness, `SimplyConnectedSpace`, and the critical
point, and `Work.Horn.immediateBasin_has_critval_free` derives the critical point from properness +
simple connectivity + non-injectivity.
-/

namespace MandelDim

open Complex Set Metric Filter Topology

noncomputable section

/-- **The per-component conclusion of Lemma 5.4.**  For `f₀ ∈ 𝓕₀` with §4.1 data `d`, an immediate
basin `B` and the two end components `Bu`, `Bl` of `φ⁻¹(B) ∩ Dφ`: every family `B'` of components of
the parabolic basin `P = ParabolicBasin (pushdown d.E) D_g` that lies in the bounded upper piece
`{0} ∪ π '' BuOf` consists of immediate basins of `pushdown d.E` on `D_g`, each simply connected and
each containing a critical point. -/
def HornComponentStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ), InF0 f₀ D₀ → ∀ (d : ParabData f₀ D₀) {B : Set ℂ},
    IsImmediateBasin f₀ D₀ B → B.Nonempty → ∀ {η : ℝ} {Bu Bl : Set ℂ},
    Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (I * (η + 1)) →
    Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(I * (η + 1))) →
    Bu ∪ Bl ⊆ d.DE → {w : ℂ | η < w.im} ⊆ Bu → {w : ℂ | w.im < -η} ⊆ Bl →
    ∀ {q : ℕ} {B' : Fin q → Set ℂ},
    (∀ i, ∃ z ∈ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))),
      B' i = connectedComponentIn (ParabolicBasin (pushdown d.E)
        (insert 0 (piExp '' (Bu ∪ Bl)))) z) →
    (∀ i, B' i ⊆ insert 0 (piExp '' (BuOf d B))) →
    (∀ i, IsImmediateBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))) (B' i)) ∧
    (∀ i, SimplyConnectedSpace (B' i)) ∧
    (∀ i, ∃ z ∈ B' i, deriv (pushdown d.E) z = 0)

/-!
## What this object requires of `E` (established after the object was created)

`Horn/component_no_boundary_accumulation` was delegated (H15-L2498) and came back with a structural
result rather than a counterexample.  With `g = pushdown d.E`, `P = ParabolicBasin g D_g`, `C = B' i`
and `v = π (d.Φ c)`:

* under the object's hypotheses, `C` is a component of `g ⁻¹' C ∩ D_g`, so restricting the
  UNCONDITIONAL covering `Work.Horn.pushdown_covering` (`IsCoveringMapOn g {ζ ≠ 0 ∧ ζ ≠ v}`) over
  the base `C` makes `g : C → C` a covering map AWAY FROM `v = π (d.Φ c)`, i.e. a branched covering
  whose only possible branch value is `v` (and in the intended `q = 1` case `v ∈ C`, so it is
  genuinely branched there — the fibre over `v` consists of the critical points);
* the confinement `closure (C ∩ g ⁻¹' L) ⊆ insert 0 (π '' d.DE)` is therefore
  **equivalent to the properness clause** (via `bdry_Dg.isCompact_inter_preimage_iff_closure_subset`
  and `spread_proper.isCompact_inter_preimage_of_confinement`) and, by the same covering, to
  **`g : C → C` having FINITE degree**:
  * finite degree ⟹ `C ∩ g ⁻¹' L` is a compact union of sheets over `L`;
  * infinite degree ⟹ the fibre of `y ∈ C` is infinite, bounded
    (`Work.Horn.pushdown_fiber_bounded`) and discrete, its accumulation points lie outside `D_g`
    (`not_accPt_preimage_singleton_of_analytic`) and cannot all be `0` (because `deriv g 0 = 1 ≠ 0`
    makes `g` injective near `0`) — so the confinement fails.

So the content this object demands of the Écalle transformation `E = Φ ∘ φ` is *exactly*: `g` is a
finite-degree (branched) covering on each petal component — Shishikura's "`g₀ : B_i → B_i` is a
proper branched covering with at most one critical point", equivalently (★) of `NOTES_GERM_F0.md`
§69.2 ("each spread contains exactly one preimage of the critical value").  The interface exposes `E`
only through `E_upper`/`E_lower`, so a proof must come from §4.1/A.3's boundary behaviour of
`Ẽ = Φ₀ ∘ φ₀` on `∂Btil`; the natural next lemma is the *equivalence*
"confinement ⟺ finite degree of `g` on the petal components", which would turn the remaining
obligation into a degree computation amenable to the Riemann–Hurwitz bookkeeping already recorded in
§69.2.
-/
end

end MandelDim
