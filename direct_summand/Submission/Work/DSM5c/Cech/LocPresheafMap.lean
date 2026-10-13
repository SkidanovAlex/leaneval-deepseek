import Submission.Work.DSMap.Mix2

/-!
# The restriction maps of `locPresheaf` are algebra maps

`DSMap.Mix2.locPresheaf t G hG` (`Submission/Work/DSMap/Mix2.lean`) is the presheaf of
`W`-modules on `(Finset ι)ᵒᵖᵒᵖ` whose value at `S` is the `W`-subalgebra
`G S ⊆ W_{t_S} = Localization.Away (tS t S)`, and whose restriction maps are
`Subalgebra.inclusion ∘ locRes`.  Both are `W`-algebra maps, so every restriction map of
`locPresheaf` sends `algebraMap W (G S) w` to `algebraMap W (G T) w`.

This is used to prove that the (diagonal) coaugmentation of the perfected chart Čech complex is a
`0`-cocycle: the `σ`-component of `d 0 1 ∘ e` is the alternating sum
`+ algebraMap w - algebraMap w = 0`.

The two lemmas below are stated for an arbitrary family of subalgebras `G`; the instantiations
`G = chartRing t` and `G = perfChartRing p t` are the interesting cases.

**Elaboration note.**  Unfolding `locPresheaf`'s `map` field to its `Submodule.codRestrict`
description is a `rfl`-level definitional equality, but it is *not* cheap: the checks below need
`set_option maxHeartbeats 4000000`.  This is why the two lemmas are separated: the expensive
definitional equality is performed once, in `locPresheaf_map_apply_gen`, and
`locPresheaf_map_algebraMap` (and everything downstream) then uses the resulting rewrite.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.DSM5c.Cech

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

universe a

/-- **The components of a restriction map of `locPresheaf`**, in the raw coordinates of the
subalgebras `G S ⊆ W_{t_S}`: for `x ∈ G S`, the `T`-component of `(locPresheaf t G hG).map f x` is
`locRes t h` applied to the underlying element of `x`, where `h : S ⊆ T` is the relation induced by
`f`.  This is a definitional equality. -/
theorem locPresheaf_map_apply_gen {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]
    (t : ι → W) (G : ∀ S, Subalgebra W (Localization.Away (tS t S)))
    (hG : ∀ S T (h : S ⊆ T), (G S).map (locRes t h) ≤ G T)
    {S T : Finset ι} (f : op (op S) ⟶ op (op T)) (x : ↥(G S)) :
    ((locPresheaf t G hG).map f).hom x
      = ⟨locRes t (leOfHom f.unop.unop) x.1,
          hG _ _ (leOfHom f.unop.unop) ⟨x.1, x.2, rfl⟩⟩ :=
  rfl

/-- **The restriction maps of `locPresheaf` commute with the structure maps `algebraMap`.** -/
theorem locPresheaf_map_algebraMap {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]
    (t : ι → W) (G : ∀ S, Subalgebra W (Localization.Away (tS t S)))
    (hG : ∀ S T (h : S ⊆ T), (G S).map (locRes t h) ≤ G T)
    {S T : Finset ι} (f : op (op S) ⟶ op (op T)) (w : W) :
    ((locPresheaf t G hG).map f).hom (algebraMap W ↥(G S) w) = algebraMap W ↥(G T) w := by
  rw [locPresheaf_map_apply_gen t G hG f (algebraMap W ↥(G S) w)]
  refine Subtype.ext ?_
  show locRes t (leOfHom f.unop.unop)
      (((algebraMap W ↥(G S)) w : ↥(G S)) : Localization.Away (tS t S))
    = (((algebraMap W ↥(G T)) w : ↥(G T)) : Localization.Away (tS t T))
  rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
  exact AlgHom.commutes (locRes t (leOfHom f.unop.unop)) w

/-- **The restriction maps of the presheaf of perfected chart rings commute with `algebraMap`.**
This is `locPresheaf_map_algebraMap` at `G = perfChartRing p t`, i.e. at
`perfChartPresheaf p t = locPresheaf t (perfChartRing p t) _`. -/
theorem perfChartPresheaf_map_algebraMap {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R]
    {ι : Type a} [DecidableEq ι] (t : ι → R)
    {S T : Finset ι} (f : op (op S) ⟶ op (op T)) (w : R) :
    ((perfChartPresheaf p t).map f).hom (algebraMap R ↥(perfChartRing p t S) w)
      = algebraMap R ↥(perfChartRing p t T) w :=
  locPresheaf_map_algebraMap t (perfChartRing p t)
    (fun _ _ h => perfChartRing_map_le p t h) f w

end Work.DSM5c.Cech
