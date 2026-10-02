import Mathlib
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Thom.stepDefs
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.RankTwo.RepRelCoh

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.Whitney.tcmSuspAux

noncomputable section

/-!
# The pairing of a relative class with a relative cycle, and its application to the cap map

`Work.Thom.stepSph` and `Work.Thom.stepDisc` are related by `Work.Thom.stepSph_spec`:

  `(capMapPairSph)^* (stepSph Y n (Mn n Y)) = stepDisc Y n (Mn n Y)`

in `H^n(Y × Dⁿ, Y × Sⁿ⁻¹; ℤ)`.  Consequently two *arbitrary* representatives `ψ`, `b` of these two
classes, with `ψ` a cocycle on the sphere-bundle pair `(Y × Sⁿ, SphB Y n)` and `b` one on the disc
pair `(Y × Dⁿ, DiscB Y n)`, pair equally with every chain `B` whose boundary is carried by the
disc `DiscB Y n`:

  `⟨(capMapPairSph)^* ψ, B⟩ = ⟨b, B⟩`.

The only ingredient is the general fact that the Kronecker pairing of a relative cocycle with a
relative cycle depends only on the relative cohomology class, proved here as
`kronecker_eq_of_relClassOf_eq` (the degree `k+1` case is
`Work.Cohomology.kronecker_relComplex_eq_of_homology_eq`; in degree zero the class of a cocycle is
the cocycle itself, since `d (prev 0) 0 = 0`).
-/

/-- **The Kronecker pairing of a relative cocycle with a relative cycle depends only on the
relative cohomology class.**  Two relative `n`-cocycles of the pair `(X, A)` with the same class
pair equally with every `n`-chain whose boundary is carried by `A`. -/
theorem kronecker_eq_of_relClassOf_eq {X : TopCat} (A : Set X) (n : ℕ)
    (γ γ' : ↥(relKern ℤ X A n))
    (hγ : relDiffLM ℤ X A n γ = 0) (hγ' : relDiffLM ℤ X A n γ' = 0)
    (h : relClassOf ℤ X A γ hγ = relClassOf ℤ X A γ' hγ')
    (Z : (singularChains ℤ X).X n)
    (hZ : IsSmallChain A (∅ : Set X) ((singularChains ℤ X).d n (n - 1) Z)) :
    kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) n from γ.1) Z
      = kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) n from γ'.1) Z := by
  rcases n with _ | k
  · -- degree zero: `homologyπ 0` is injective, since `d (prev 0) 0 = 0`
    have hshape : (relComplex ℤ X A).d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      HomologicalComplex.shape _ _ _ (by intro hh; simp [ComplexShape.up] at hh)
    have hk : (relComplex ℤ X A).toCycles ((ComplexShape.up ℕ).prev 0) 0
        ≫ (relComplex ℤ X A).iCycles 0 = 0 := by
      rw [HomologicalComplex.toCycles_i, hshape]
    have hd := congrArg (fun t =>
      (descH_K (relComplex ℤ X A) 0 ((relComplex ℤ X A).iCycles 0) hk).hom t) h
    have hzz : relCocycleOf ℤ X A γ hγ = relCocycleOf ℤ X A γ' hγ' :=
      iCycles_injective_K (relComplex ℤ X A) 0
        (by simpa only [relClassOf, descH_apply_K] using hd)
    have hγeq : γ = γ' := by
      rw [← iCycles_relCocycleOf ℤ X A γ hγ, ← iCycles_relCocycleOf ℤ X A γ' hγ', hzz]
    rw [hγeq]
  · -- degree `k+1`: the difference is a coboundary, and the pairing of a coboundary with a
    -- chain whose boundary is carried by `A` vanishes
    have hγd : (ModuleCat.Hom.hom ((relComplex ℤ X A).d (k + 1) (k + 1 + 1))) γ = 0 :=
      (relDiffLM_eq_zero_iff X A (k + 1) γ).mpr hγ
    have hγd' : (ModuleCat.Hom.hom ((relComplex ℤ X A).d (k + 1) (k + 1 + 1))) γ' = 0 :=
      (relDiffLM_eq_zero_iff X A (k + 1) γ').mpr hγ'
    have hlin : (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X A) (k + 1)))
        (cocycleOfK (relComplex ℤ X A) γ hγd)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X A) (k + 1)))
          (cocycleOfK (relComplex ℤ X A) γ' hγd') := by
      rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ X A γ hγ hγd,
        ← relClassOf_eq_homologyπ_cocycleOfK ℤ X A γ' hγ' hγd']
      exact h
    exact kronecker_relComplex_eq_of_homology_eq A k γ γ' hγd hγd' hlin Z hZ

theorem kronecker_capMapPairSph_eq
    (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (ψ : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MSph (n + 1))) (Work.Thom.SphB Y n) n))
    (hψrel : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MSph (n + 1))) (Work.Thom.SphB Y n) n ψ = 0)
    (hψclass : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MSph (n + 1))) (Work.Thom.SphB Y n) ψ hψrel
        = Work.Thom.stepSph Y n (Work.Thom.Mn n Y))
    (B : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).X n)
    (hB : Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y n) (∅ : Set (Y × Work.Thom.MBall n))
        ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).d n (n-1) B))
    (b : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MBall n)) (Work.Thom.DiscB Y n) n))
    (hb : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MBall n)) (Work.Thom.DiscB Y n) n b = 0)
    (hbc : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MBall n)) (Work.Thom.DiscB Y n) b hb
        = Work.Thom.stepDisc Y n (Work.Thom.Mn n Y)) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall n))
        (Work.Whitney.RankTwo.pullCM (Work.Thom.capMapPairSph Y n) ψ.1) B
      = Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall n)) b.1 B := by
  -- the pullback of `ψ` along the cap map is a representative of the disc class
  have hpair := kronecker_eq_of_relClassOf_eq
    (X := TopCat.of (Y × Work.Thom.MBall n)) (A := Work.Thom.DiscB Y n) n
    (Work.Cohomology.relMapLM (X₁ := TopCat.of (Y × Work.Thom.MBall n))
      (X₂ := TopCat.of (Y × Work.Thom.MSph (n + 1))) ℤ (Work.Thom.DiscB Y n) (Work.Thom.SphB Y n)
      (TopCat.ofHom (Work.Thom.capMapPairSph Y n)) (Work.Thom.CleanA.capMapPairSph_mem_mLower n) n ψ)
    b
    (Work.Cohomology.relDiffLM_relMapLM (X₁ := TopCat.of (Y × Work.Thom.MBall n))
      (X₂ := TopCat.of (Y × Work.Thom.MSph (n + 1))) ℤ (Work.Thom.DiscB Y n) (Work.Thom.SphB Y n)
      (TopCat.ofHom (Work.Thom.capMapPairSph Y n)) (Work.Thom.CleanA.capMapPairSph_mem_mLower n)
      ψ hψrel)
    hb
    (by
      rw [Work.Whitney.RankTwo.relClassOf_relMapLM (X₁ := TopCat.of (Y × Work.Thom.MBall n))
        (X₂ := TopCat.of (Y × Work.Thom.MSph (n + 1))) (Work.Thom.DiscB Y n) (Work.Thom.SphB Y n)
        (Work.Thom.capMapPairSph Y n) (Work.Thom.CleanA.capMapPairSph_mem_mLower n) n ψ hψrel _]
      rw [hψclass, Work.Thom.stepSph_spec Y n (Work.Thom.Mn n Y)]
      exact hbc.symm)
    B hB
  -- and its underlying cochain is exactly the stated pullback
  have hcoe : (show Work.Cohomology.Cochain ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall n)) n from
      (Work.Cohomology.relMapLM (X₁ := TopCat.of (Y × Work.Thom.MBall n))
        (X₂ := TopCat.of (Y × Work.Thom.MSph (n + 1))) ℤ (Work.Thom.DiscB Y n) (Work.Thom.SphB Y n)
        (TopCat.ofHom (Work.Thom.capMapPairSph Y n)) (Work.Thom.CleanA.capMapPairSph_mem_mLower n) n ψ).1)
      = Work.Whitney.RankTwo.pullCM (Work.Thom.capMapPairSph Y n) ψ.1 := rfl
  rw [hcoe] at hpair
  exact hpair

end

end Work.Whitney.tcmSuspAux
