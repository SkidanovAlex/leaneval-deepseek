import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.csrRelIso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The absolute comparison `H_*(q⁻¹W) ≅ H_*(W)` from a subset

If `S ⊆ W` and the pairs `(q⁻¹W, q⁻¹S)`, `(W,S)` have vanishing rational relative homology, then
the comparison `H_*(q⁻¹W) ≅ H_*(W)` is *equivalent* to the comparison `H_*(q⁻¹S) ≅ H_*(S)`, by the
long exact sequences of the two pairs.  This is the abstract step of the local model of the
`1`-cell step: it reduces the absolute comparison over a disjoint union of contractible open cells
to the comparison over a discrete set of points.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

noncomputable section

/-! ## The long exact sequence tools over `ℚ` -/

/-- If the third term of a short exact sequence of `ℚ`-chain complexes is acyclic, the first map is
a quasi-isomorphism. -/
theorem isIso_homologyMap_f_of_acyclic_X3 {S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (hS : S.ShortExact) (h : ∀ k, IsZero (S.X₃.homology k)) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap S.f k) := by
  haveI hmono : Mono (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.mono_g (hS.homology_exact₁ (k + 1) k (by simp [ComplexShape.down]))
      (IsZero.eq_zero_of_src (h (k + 1)) _)
  haveI hepi : Epi (HomologicalComplex.homologyMap S.f k) :=
    ShortComplex.Exact.epi_f (hS.homology_exact₂ k) (IsZero.eq_zero_of_tgt (h k) _)
  exact isIso_of_mono_of_epi _

/-- **The absolute comparison from a subset.** -/
theorem absComparison {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z] (q : C(E, Z))
    (S W : Set Z) (hSW : S ⊆ W) (N : ℕ)
    (hX : ∀ m : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of {x : E // q x ∈ W})
      {x : {x : E // q x ∈ W} | q x.1 ∈ S}).homology m))
    (hY : ∀ m : ℕ, IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of {x : Z // x ∈ W})
      {x : {x : Z // x ∈ W} | (x : Z) ∈ S}).homology m))
    (hS : ∀ k : ℕ, k ≤ N → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of {x : {x : E // q x ∈ W} | q x.1 ∈ S})
        (TopCat.of {x : {x : Z // x ∈ W} | (x : Z) ∈ S})
        (TopCat.ofHom ⟨fun x => ⟨⟨q x.1.1, x.1.2⟩, x.2⟩, by fun_prop⟩)) k)) :
    ∀ k : ℕ, k ≤ N → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of {x : E // q x ∈ W}) (TopCat.of {x : Z // x ∈ W})
        (TopCat.ofHom ⟨fun x => ⟨q x.1, x.2⟩, by fun_prop⟩)) k) := by
  intro k hk
  -- the two maps, named once and for all
  let gE : C({x : E // q x ∈ W}, {x : Z // x ∈ W}) := ⟨fun x => ⟨q x.1, x.2⟩, by fun_prop⟩
  let gA : C({x : {x : E // q x ∈ W} | q x.1 ∈ S}, {x : {x : Z // x ∈ W} | (x : Z) ∈ S}) :=
    ⟨fun x => ⟨⟨q x.1.1, x.1.2⟩, x.2⟩, by fun_prop⟩
  let XE : TopCat := TopCat.of {x : E // q x ∈ W}
  let XA : TopCat := TopCat.of {x : {x : E // q x ∈ W} | q x.1 ∈ S}
  let YE : TopCat := TopCat.of {x : Z // x ∈ W}
  let YA : TopCat := TopCat.of {x : {x : Z // x ∈ W} | (x : Z) ∈ S}
  haveI hα : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ XE {x : XE | q x.1 ∈ S}) k) :=
    isIso_homologyMap_f_of_acyclic_X3
      (Work.StemsB.relChainsR_shortExact ℚ XE {x : XE | q x.1 ∈ S}) hX k
  haveI hβ : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ YE {x : YE | (x : Z) ∈ S}) k) :=
    isIso_homologyMap_f_of_acyclic_X3
      (Work.StemsB.relChainsR_shortExact ℚ YE {x : YE | (x : Z) ∈ S}) hY k
  haveI hSi : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ XA YA
      (TopCat.ofHom gA)) k) := hS k hk
  -- the commuting square of chain maps
  have hsquare : Work.StemsB.relChainsRIncl ℚ XE {x : XE | q x.1 ∈ S} ≫
        Work.Cohomology.chainMap ℚ XE YE (TopCat.ofHom gE)
      = Work.Cohomology.chainMap ℚ XA YA (TopCat.ofHom gA) ≫
        Work.StemsB.relChainsRIncl ℚ YE {x : YE | (x : Z) ∈ S} := by
    simp only [Work.StemsB.relChainsRIncl]
    rw [Work.Serre.chainMap_compR, Work.Serre.chainMap_compR]
    rfl
  have h2 := congrArg (fun t => HomologicalComplex.homologyMap t k) hsquare
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h2
  let Ff := HomologicalComplex.homologyMap
    (Work.StemsB.relChainsRIncl ℚ XE {x : XE | q x.1 ∈ S}) k
  let Gg := HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ XE YE (TopCat.ofHom gE)) k
  have h3 : Ff ≫ Gg = HomologicalComplex.homologyMap
      (Work.StemsB.relChainsRIncl ℚ XE {x : XE | q x.1 ∈ S}) k ≫
      HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ XE YE (TopCat.ofHom gE)) k := rfl
  haveI hcomp : IsIso (Ff ≫ Gg) := by rw [h3, h2]; infer_instance
  change IsIso Gg
  exact IsIso.of_isIso_comp_left Ff Gg

end

end Work.Serre.OneCell
