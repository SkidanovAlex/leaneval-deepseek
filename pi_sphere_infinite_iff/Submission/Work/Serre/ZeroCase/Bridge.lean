import Submission.Work.Serre.ZeroCase.Basic
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Hurewicz-type vanishing of the integral homology below the connectivity

If a space `X` has trivial homotopy groups `π_i(X, x₀)` for `i < f`, then its integral singular
homology vanishes in degrees `0 < j < f`.

This is the input the (homological form of the) Serre comparison in the stable range needs on its
fibre: the fibre of the general statement is only assumed to be homotopy `(f-1)`-connected.

The proof combines three ingredients, all available in the workspace:

* `π_i(X,x₀) = 0` for `i < f` makes the pair `(X, {x₀})` compressible in dimensions `≤ f-1`
  (`Work.Serre.compressRel_singleton_of_subsingleton_pi`), hence its relative homology vanishes in
  degrees `≤ f-1` (`Work.Serre.simpHom_of_compress`, `Work.Serre.simpHomVanishing`);
* the long exact sequence of the pair `(X, {x₀})`
  (`Work.Cohomology.hPair_exact₁/₂`) sandwiches `H_j(X)` between `H_j(↥{x₀})` and the relative
  groups: in degrees `j ≤ f-2` the map `H_j(↥{x₀}) → H_j(X)` is mono and epi, and in degree
  `j = f-1` it is epi;
* the positive-degree homology of the one-point space `↥{x₀}` vanishes
  (`Work.Cohomology.homologyContractible`).
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Vanishing of the integral homology below the connectivity.**  If `π_i(X, x₀)` is trivial for
every `i < f`, then `H_j(X; ℤ) = 0` for `0 < j < f`. -/
theorem isZero_singularChains_homology_of_pi_subsingleton {X : Type} [TopologicalSpace X] (x₀ : X)
    (f : ℕ) (h : ∀ i, i < f → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    ∀ j : ℕ, 0 < j → j < f →
      IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j) := by
  intro j hj hjl
  have hjM : j ≤ f - 1 := by omega
  -- the pair `(X, {x₀})` is compressible in dimensions `≤ f - 1`
  have hcomp : ∀ d, d ≤ f - 1 → Work.RatHurewicz.CompressRel X ({x₀} : Set X) d :=
    fun d hd => compressRel_singleton_of_subsingleton_pi x₀ d (h d (by omega))
  have hrel : ∀ n, n ≤ f - 1 →
      IsZero ((Work.Cohomology.relChains (TopCat.of X) ({x₀} : Set X)).homology n) := by
    intro n hn
    obtain ⟨H⟩ := simpHom_of_compress (f - 1) (fun d hd => hcomp d hd)
    exact simpHomVanishing H n hn
  -- the map `H_j(↥{x₀}) ⟶ H_j(X)` of the pair sequence is surjective
  have hsurj : Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of X) ({x₀} : Set X)) j) :=
    ShortComplex.Exact.epi_f (Work.Cohomology.hPair_exact₂ (TopCat.of X) ({x₀} : Set X) j)
      (IsZero.eq_zero_of_tgt (hrel j hjM) _)
  -- the positive-degree homology of the one-point space vanishes
  have hpt : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥({x₀} : Set X))).homology j) :=
    Work.Cohomology.homologyContractible j hj
  rcases lt_or_ge (j + 1) f with hlt | hge
  · -- `j + 1 ≤ f - 1`: the map is also injective, hence an isomorphism
    have hmono : Mono (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of X) ({x₀} : Set X)) j) :=
      ShortComplex.Exact.mono_g (Work.Cohomology.hPair_exact₁ (TopCat.of X) ({x₀} : Set X) j)
        (IsZero.eq_zero_of_src (hrel (j + 1) (by omega)) _)
    haveI := hsurj
    haveI := hmono
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of X) ({x₀} : Set X)) j) := isIso_of_mono_of_epi _
    exact IsZero.of_iso hpt (asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of X) ({x₀} : Set X)) j)).symm
  · -- `j = f - 1`: only surjectivity is used, and the source is a zero object
    haveI : Subsingleton ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥({x₀} : Set X))).homology j) :=
      ModuleCat.isZero_iff_subsingleton.mp hpt
    have hs := (ModuleCat.epi_iff_surjective _).mp hsurj
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
    obtain ⟨a', ha'⟩ := hs a
    obtain ⟨b', hb'⟩ := hs b
    rw [← ha', ← hb', Subsingleton.elim a' b']

end

end Work.Serre
