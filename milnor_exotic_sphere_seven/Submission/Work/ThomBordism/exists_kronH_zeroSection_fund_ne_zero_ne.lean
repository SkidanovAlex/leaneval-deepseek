import Mathlib
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory AlgebraicTopology

/-!
# The Kronecker pairing with the fundamental class is nonzero on the normal total space,
*without* a connectedness hypothesis

`Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero` proves the non-degeneracy of the functional
`x ↦ ⟨(zeroSection E)^* x, V.c⟩` on `H⁸(ν; ℤ)` under the hypothesis `[ConnectedSpace V.pt]`.  The
only use of connectedness in its proof is the local-homology computation
`Work.ThomBordism.RelH_point_iso`, whose statement carries `[ConnectedSpace]` although its proof
does not: it is the composite of the excision localisation `Work.Cohomology.localHomology` (which
needs only a chart at the point) with two reindexings.  Connectedness of the *manifold* is not what
makes the local class nonzero — the local group is `ℤ` at every point, and `Man8.c_fund` says the
local class generates it, so the local class is nonzero *whatever* the other components do.

This file removes the hypothesis: `relH_point_iso_of_charted` is the connectedness-free local
homology computation, `exists_fundPairing_ne_zero_nonempty` is
`exists_fundPairing_ne_zero` with `[ConnectedSpace V.pt]` weakened to `Nonempty V.pt`, and the
target follows by the same retraction argument as before.
-/

/-- **The local group of a charted space is infinite cyclic** — the connectedness-free form of
`Work.ThomBordism.RelH_point_iso`: no compactness, Hausdorffness or connectedness is used. -/
theorem relH_point_iso_of_charted (n : ℕ) (hn : 1 ≤ n) (M : TopCat)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    Nonempty (Work.ThomBordism.RelH M n ({x} : Set M) ≅ ModuleCat.of ℤ ℤ) := by
  have hTop : (Work.Cohomology.relChains (TopCat.of ↑M) ({x} : Set ↑M)ᶜ).homology n
      = (Work.Cohomology.relChains M ({x} : Set ↑M)ᶜ).homology n := rfl
  obtain ⟨e⟩ := Work.Cohomology.localHomology n hn (M : Type) x
  have hh : ({x} : Set ↑M)ᶜ = {y : ↑M | y ≠ x} := by ext y; simp
  exact ⟨(eqToIso hTop).symm.trans ((eqToIso (congrArg (fun S : Set ↑M =>
    (Work.Cohomology.relChains (TopCat.of ↑M) S).homology n) hh)).trans e)⟩

/-- **`H⁸` of a nonempty closed oriented `8`-manifold contains a class pairing nontrivially with
the fundamental class.**  (`Work.ThomBordism.exists_fundPairing_ne_zero` with `Nonempty` in place of
`ConnectedSpace`.) -/
theorem exists_fundPairing_ne_zero_nonempty (V : Work.ThomBordism.Man8) (hne : Nonempty V.pt) :
    ∃ u : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj (TopCat.of V.pt))).homology 8,
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8 u V.c ≠ 0 := by
  classical
  set X : SSet := TopCat.toSSet.obj (TopCat.of V.pt) with hX
  have hc : Work.Orient.IsFundClass (TopCat.of V.pt) 8 V.c := fun x => V.c_fund x
  obtain ⟨x⟩ := hne
  obtain ⟨e⟩ := Work.ThomBordism.relH_point_iso_of_charted 8 (by norm_num) (TopCat.of V.pt) x
  -- the localisation at `x`
  let loc : (Work.Cohomology.chainC ℤ X).homology 8 →ₗ[ℤ]
      ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)) :=
    (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of V.pt)
        {y : V.pt | y ≠ x})) 8).hom
  have hloc : loc V.c = Work.Orient.locClass (TopCat.of V.pt) 8 V.c x := rfl
  -- the local generator is non-zero, since the local group is `ℤ` and it generates
  have hgen : loc V.c ≠ 0 := by
    intro h0
    have hz : Submodule.span ℤ
        ({(0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))} :
          Set ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) = ⊤ := by
      rw [show (0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))
          = loc V.c from h0.symm]
      rw [hloc]
      exact hc x
    have hbot : Submodule.span ℤ
        ({(0 : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))} :
          Set ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) = ⊥ :=
      Submodule.span_singleton_eq_bot.mpr rfl
    have hsub : Subsingleton ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)) := by
      refine ⟨fun a b => ?_⟩
      have htop : (⊤ : Submodule ℤ ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt)))
          = ⊥ := by rw [← hz, hbot]
      have ha : a = 0 := by
        have hmem : a ∈ (⊥ : Submodule ℤ
            ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) := by
          rw [← htop]; trivial
        simpa using hmem
      have hb : b = 0 := by
        have hmem : b ∈ (⊥ : Submodule ℤ
            ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8 ({x} : Set V.pt))) := by
          rw [← htop]; trivial
        simpa using hmem
      rw [ha, hb]
    have hsurj : Function.Surjective (e.hom.hom : ↥(Work.ThomBordism.RelH (TopCat.of V.pt) 8
        ({x} : Set V.pt)) → ℤ) := (ConcreteCategory.bijective_of_isIso e.hom).2
    have : Subsingleton ℤ := ⟨fun a b => by
      obtain ⟨p, rfl⟩ := hsurj a
      obtain ⟨q, rfl⟩ := hsurj b
      rw [Subsingleton.elim p q]⟩
    exact absurd (Subsingleton.elim (0 : ℤ) 1) (by norm_num)
  -- the functional `H₈ → ℤ` evaluating the local class at `x` in the model `ℤ`
  have hφ : (e.hom.hom.comp loc) V.c ≠ 0 := by
    intro h0
    refine hgen ((ConcreteCategory.bijective_of_isIso e.hom).1 ?_)
    rw [LinearMap.comp_apply] at h0
    rw [h0, map_zero]
  -- a cycle representing `V.c`
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((Work.Cohomology.chainC ℤ X).homologyπ 8)).mp inferInstance V.c
  -- a cocycle evaluating non-trivially on `z`
  obtain ⟨α, hα, hval⟩ :=
    Work.Cohomology.exists_cochain_of_functional X 8 (e.hom.hom.comp loc) z
  refine ⟨Work.Cohomology.cohomologyClassOf ℤ X α hα, ?_⟩
  have h1 : Work.Cohomology.kronH ℤ X 8 (Work.Cohomology.cohomologyClassOf ℤ X α hα)
      V.c ≠ 0 := by
    rw [← hz, Work.Cohomology.kronH_apply ℤ X α hα z, hval, hz]
    exact hφ
  exact h1

theorem exists_kronH_zeroSection_fund_ne_zero_ne {V : Work.ThomBordism.Man8}
    (hne : Nonempty V.pt) {k : ℕ} (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    ∃ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c ≠ 0 := by
  classical
  obtain ⟨u, hu⟩ := exists_fundPairing_ne_zero_nonempty V hne
  refine ⟨(Work.Thom.CohMap (normalProjTotal E) ℤ 8).hom u, ?_⟩
  have hcoe : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (normalProjTotal E) ℤ 8).hom u) = u := by
    rw [Work.Thom.CohMap_comp_apply (Work.Tubular.zeroSectionNormal E) (normalProjTotal E) ℤ 8 u,
      normalProjTotal_comp_zeroSection, Work.Thom.CohMap_id]
    rfl
  rw [hcoe]
  exact hu

end

end Work.ThomBordism
