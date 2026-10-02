import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.Tubular.relKronH_exists_eval_one
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.ThomBordism.nfRes_span_top_of_generator
import Submission.Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion
import Submission.Work.ThomBordism.fibreRelHomologyIso
import Submission.Work.ThomBordism.fibreDualGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

attribute [local instance 100] ZSMul.toSMul

namespace Work.ThomBordism

theorem fibreReading_collapseClass {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (x : V.pt)
    (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
    (hw : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1) :
    ∃ z : (Work.Cohomology.relChains (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x)).homology k,
      Submodule.span ℤ ({z} : Set _) = ⊤ ∧
      ∀ U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E),
        Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
            (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U) z
          = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E) (k + 8)
              ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
                (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U))
              (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  classical
  -- the normal data of the embedding (only needed to produce the fibre generator)
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  -- the local-degree generator of the Thom pair of the normal bundle
  obtain ⟨U₀, hspan₀, hU₀⟩ :=
    Work.ThomBordism.localDegreeGenExists hk E C.eps_pos C q hU hR hbox g hg hg2
  -- its restriction to the fibre generates the relative cohomology of the fibre pair
  have hgen : Submodule.span ℤ ({Work.ThomBordism.nfRes E x k U₀} : Set
      (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
        (Work.ThomBordism.nfPunct E x))) = ⊤ :=
    Work.ThomBordism.nfRes_span_top_of_generator hk E ND x hspan₀
  -- the fibre relative homology in degree `k` is `ℤ`
  obtain ⟨eM⟩ := Work.ThomBordism.fibreRelHomologyIso hk E x
  -- the dual generator of the fibre pair: the generator `z` of `H_k(ν_x, ν_x∖0)` pairing to `1`
  -- with the generator `nfRes U₀` of the relative cohomology of the fibre
  obtain ⟨z, hzspan, hzpair⟩ :=
    Work.ThomBordism.fibreDualGen E x eM (Work.ThomBordism.nfRes E x k U₀) hgen
  refine ⟨z, hzspan, ?_⟩
  intro U
  -- degree bookkeeping: `U` is a multiple of the generator `U₀`
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ
      ↥(Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)) U₀) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, hspan₀]
  obtain ⟨m, hm⟩ := hsurj U
  have hmU : U = m • U₀ := by
    rw [← hm, LinearMap.toSpanSingleton_apply]
  subst hmU
  -- the two sides are `ℤ`-linear in `U`
  have hL : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k
        (Work.ThomBordism.nfRes E x k (m • U₀)) z
      = m * Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k U₀) z := by
    rw [map_smul (Work.ThomBordism.nfRes E x k) m U₀,
      map_smul (Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k) m (Work.ThomBordism.nfRes E x k U₀),
      LinearMap.smul_apply, smul_eq_mul]
  have hcast : ∀ {a b : ℕ} (h : a = b) (m : ℤ)
      (y : Work.Thom.RelCoh ℤ a (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)),
      h ▸ (m • y) = m • (h ▸ y) := by
    intro a b h m y
    cases h
    rfl
  have hRlin : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w
          (m • U₀)))
        (Work.Tubular.collapseRelK8 C g hg hR hbox)
      = m * Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U₀))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
    rw [map_smul (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w) m U₀]
    rw [hcast (a := 8 + k) (b := k + 8) (Nat.add_comm 8 k) m
      (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w U₀)]
    rw [map_smul (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)) m
      ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U₀)),
      LinearMap.smul_apply, smul_eq_mul]
  rw [hL, hRlin, hzpair]
  -- the value of the right-hand side at the generator
  have h0R : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k w U₀))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = 1 := by
    rw [hU₀ w, hw]
  rw [h0R, mul_one]

end Work.ThomBordism
