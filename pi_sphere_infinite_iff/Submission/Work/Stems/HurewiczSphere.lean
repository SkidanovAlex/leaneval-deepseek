import Mathlib
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.Pullback

set_option synthInstance.maxHeartbeats 400000

/-!
# The Hurewicz class of a based map `Sⁿ → X`

This is the first, model-independent half of the Hurewicz map.  For `n ≥ 1` we fix a generator
`u = sphereGenerator n hn` of `Hₙ(Sⁿ;ℤ) ≅ ℤ` (obtained from the workspace's computation
`Work.Cohomology.sphereHomologyTop`) and associate to a continuous map `f : Sⁿ → X` the class
`Hₙ(f)(u) ∈ Hₙ(X;ℤ)`.

The two facts proved here are exactly the ones that make the Hurewicz map well defined on homotopy
classes:

* `sphereGenerator_spec` — `u` is sent to `1` by the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`;
* `hurewiczClass_eq_of_homotopic` — homotopic maps have the same Hurewicz class (via the homotopy
  invariance of singular homology).

The remaining step (associating such a map `Sⁿ → X` to a *cube* `Ω^ (Fin n) X x₀` representative,
hence defining `hurewiczMap` on `HomotopyGroup (Fin n) X x₀`) is in `Stems/Hurewicz.lean`.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology

namespace Work.Stems

noncomputable section

/-- The sphere `Sⁿ ⊆ ℝ^{n+1}`, in the model used by `HomotopyGroup` and by
`Work.Cohomology.sphereHomologyTop`. -/
abbrev sphere (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The singular chain complex of `X` with `ℤ` coefficients. -/
abbrev chains (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Cohomology.singularChains ℤ X

/-- The chosen generator of `Hₙ(Sⁿ;ℤ)`, for `n ≥ 1`. -/
def sphereGenerator (n : ℕ) (hn : 1 ≤ n) : (chains (TopCat.of (sphere n))).homology n :=
  (Classical.choice (Work.Cohomology.sphereHomologyTop n hn)).inv.hom (1 : ℤ)

/-- `sphereGenerator` is the preimage of `1` under the chosen identification `Hₙ(Sⁿ;ℤ) ≅ ℤ`. -/
theorem sphereGenerator_spec (n : ℕ) (hn : 1 ≤ n) :
    (Classical.choice (Work.Cohomology.sphereHomologyTop n hn)).hom (sphereGenerator n hn) =
      (1 : ℤ) := by
  rw [sphereGenerator]
  simpa using congrFun (congrArg (fun f => ⇑f)
    (CategoryTheory.Iso.inv_hom_id (Classical.choice (Work.Cohomology.sphereHomologyTop n hn))))
    (1 : ℤ)

/-- The **Hurewicz class** of a continuous map `f : Sⁿ → X`: the push-forward of the generator of
`Hₙ(Sⁿ;ℤ)`. -/
def hurewiczClass (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (f : C(sphere n, X)) : (chains (TopCat.of X)).homology n :=
  HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ _ _ (TopCat.ofHom f)) n
    (sphereGenerator n hn)

/-- Homotopic maps have equal Hurewicz class. -/
theorem hurewiczClass_eq_of_homotopic (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    {f g : C(sphere n, X)} (h : f.Homotopic g) :
    hurewiczClass n hn f = hurewiczClass n hn g := by
  have hh : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := h.some
  have hcongr := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor hh
    (ModuleCat.of ℤ ℤ) n
  simp only [hurewiczClass, Work.Cohomology.chainMap]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ (sphereGenerator n hn)) hcongr

/-- Naturality of the Hurewicz class in the space. -/
theorem hurewiczClass_natural (n : ℕ) (hn : 1 ≤ n) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (g : C(X, Y)) (f : C(sphere n, X)) :
    hurewiczClass n hn (g.comp f) =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)) n
        (hurewiczClass n hn f) := by
  simp only [hurewiczClass, Work.Cohomology.chainMap]
  rw [TopCat.ofHom_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp]
  rfl

end

end Work.Stems
