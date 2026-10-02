import Mathlib
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.E3aStepDefs
import Submission.Work.Serre.RatTower.Defs
import Submission.Work.Serre.RatTower.AttachStepSetup
import Submission.Work.Serre.RatTower.pullbackFstRangeHomeo
import Submission.Work.Serre.RatTower.fiveLemmaTau2
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.PerCell.isIso_csrRelMapOf_homeo
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The `b = 1` relative invariant of the (rational) Serre pair comparison

`Work.Serre.B1Rel.RelGoodQ p N γ₀ g` says that the pair comparison map of the pullback of `p`
along `g : Γ → B`,
`Work.Serre.stagePairMapRat g p γ₀`, is an isomorphism on rational homology in degrees `< N` and
an epimorphism in degree `N`.  This is the rational counterpart of `Work.Serre.SPC.GoodN`.

`Work.Serre.B1Rel.propagateRelQ` is the propagation of the invariant across an arbitrary inclusion
of stages `incl : Γ → Γ'` (injective and inducing) with compatible structure maps `g' ∘ incl = g`,
given that the *step map*
`Work.Serre.E3aStep.stepMapQ p incl g' : C_*(Γ' ×_B E, (Γ' ×_B E)|_Γ;ℚ) → C_*(Γ', Γ;ℚ)`
is an isomorphism in degrees `< N` and an epimorphism in degree `N`.  The proof is the five lemma
for the middle term of the morphism of short exact sequences of the *triples*
`F ⊆ X₀ ⊆ X'` and `{γ₀'} ⊆ Γ ⊆ Γ'`, exactly as in `Work.Serre.RatTower.attachStepQ`, but written
for a generic inclusion (so that it applies to the `1`-cell steps of the skeleton as well as to the
`(n+2)`-cell steps of the tower).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.B1Rel

noncomputable section

/-- **The relative invariant of the `b = 1` induction**: the comparison map
`Work.Serre.stagePairMapRat g p γ₀` of the pullback of `p` along `g` is an isomorphism on rational
homology in degrees `< N` and an epimorphism in degree `N`. -/
def RelGoodQ {B E Γ : Type} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace Γ]
    (p : C(E, B)) (N : ℕ) (γ₀ : Γ) (g : C(Γ, B)) : Prop :=
  (∀ i : ℕ, i < N → CategoryTheory.IsIso
    (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat g p γ₀) i)) ∧
  CategoryTheory.Epi (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat g p γ₀) N)

/-- **Propagation of `RelGoodQ` along an inclusion of stages.** -/
theorem propagateRelQ {B E Γ Γ' : Type} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace Γ] [TopologicalSpace Γ'] (p : C(E, B)) (N : ℕ) (γ₀ : Γ) (g : C(Γ, B))
    (IH : RelGoodQ p N γ₀ g)
    (incl : C(Γ, Γ')) (hinj : Function.Injective incl) (hind : Topology.IsInducing incl)
    (g' : C(Γ', B)) (hrel : ∀ x, g' (incl x) = g x)
    (hstep : (∀ i : ℕ, i < N → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.Serre.E3aStep.stepMapQ p incl g') i)) ∧
      CategoryTheory.Epi
        (HomologicalComplex.homologyMap (Work.Serre.E3aStep.stepMapQ p incl g') N)) :
    RelGoodQ p N (incl γ₀) g' := by
  classical
  -- ## 0. The setup
  let γ₀' : Γ' := incl γ₀
  let P := Work.StemsB.Pullback g p
  let Q := Work.StemsB.Pullback g' p
  let q' : C(Q, Γ') := Work.StemsB.pullbackFst g' p
  let A : Set Γ' := Set.range incl
  let X₀ : Set Q := q' ⁻¹' A
  let F' : Set Q := q' ⁻¹' ({γ₀'} : Set Γ')
  let BF : Set ↥X₀ := {x | (x : Q) ∈ F'}
  let Bγ : Set ↥A := {y | (y : Γ') ∈ ({γ₀'} : Set Γ')}
  let F : Set P := (Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)
  have hemb : Topology.IsEmbedding incl := ⟨hind, hinj⟩
  have hγ₀'mem : γ₀' ∈ A := ⟨γ₀, rfl⟩
  have hsub : ({γ₀'} : Set Γ') ⊆ A := Set.singleton_subset_iff.mpr hγ₀'mem
  have hF'X₀ : F' ⊆ X₀ := Set.preimage_mono hsub
  -- ## 1. The homeomorphism `↥X₀ ≃ₜ Pullback g p`, and the pair `(X₀,F') ≅ (P,F)`
  obtain ⟨e, he1, he2, he3, he4⟩ :=
    Work.Serre.RatTower.pullbackFstRangeHomeo incl hinj hind g g' hrel p
  have hAB : ∀ x ∈ BF, e x ∈ F := by
    intro x hx
    have hx' : q' (x : Q) = γ₀' := Set.mem_singleton_iff.mp hx
    refine Set.mem_singleton_iff.mpr (hinj ?_)
    show incl ((e x).1.1) = incl γ₀
    rw [he1 x]
    exact hx'
  have hBA : ∀ y ∈ F, e.symm y ∈ BF := by
    intro y hy
    have hy' : y.1.1 = γ₀ := Set.mem_singleton_iff.mp hy
    show (e.symm y).1.1.1 ∈ ({γ₀'} : Set Γ')
    rw [he3 y, hy']
    exact Set.mem_singleton_iff.mpr rfl
  let eHom : TopCat.of ↥X₀ ⟶ TopCat.of P := Work.StemsB.sphHomeoHom e
  let eRestr : TopCat.of ↥BF ⟶ TopCat.of ↥F := Work.StemsB.pairRestrict eHom BF F hAB
  have wX : Work.Cohomology.subtypeIncl (TopCat.of ↥X₀) BF ≫ eHom
      = eRestr ≫ Work.Cohomology.subtypeIncl (TopCat.of P) F :=
    (Work.StemsB.pairRestrict_comp_subtypeIncl eHom BF F hAB).symm
  let cX := Work.Serre.csrRelMapOf (TopCat.of ↥X₀) (TopCat.of P) BF F eHom eRestr wX
  haveI hcX : IsIso cX :=
    Work.Serre.PerCell.isIso_csrRelMapOf_homeo (X := TopCat.of ↥X₀) (Y := TopCat.of P)
      e BF F hAB hBA wX
  -- ## 2. The homeomorphism `Γ ≃ₜ ↥A`, and the pair `(Γ,{γ₀}) ≅ (A,{γ₀'})`
  let homA : Γ ≃ₜ ↥A := hemb.toHomeomorph
  have hhomA_coe : ∀ γ : Γ, (homA γ : Γ') = incl γ := fun γ =>
    Topology.IsEmbedding.toHomeomorph_apply_coe hemb γ
  have hAB' : ∀ x ∈ ({γ₀} : Set Γ), homA x ∈ Bγ := by
    intro x hx
    have hx' : x = γ₀ := Set.mem_singleton_iff.mp hx
    rw [hx']
    show (homA γ₀ : Γ') ∈ ({γ₀'} : Set Γ')
    rw [hhomA_coe γ₀]
    exact Set.mem_singleton_iff.mpr rfl
  have hBA' : ∀ y ∈ Bγ, homA.symm y ∈ ({γ₀} : Set Γ) := by
    intro y hy
    have hy' : (y : Γ') = γ₀' := Set.mem_singleton_iff.mp hy
    refine Set.mem_singleton_iff.mpr ?_
    have hyy : y = homA γ₀ := by
      apply Subtype.ext
      rw [hhomA_coe γ₀, hy']
    rw [hyy, Homeomorph.symm_apply_apply]
  let hHomA : TopCat.of Γ ⟶ TopCat.of ↥A := Work.StemsB.sphHomeoHom homA
  let hRestrA : TopCat.of ↥({γ₀} : Set Γ) ⟶ TopCat.of ↥Bγ :=
    Work.StemsB.pairRestrict hHomA ({γ₀} : Set Γ) Bγ hAB'
  have wΓ : Work.Cohomology.subtypeIncl (TopCat.of Γ) ({γ₀} : Set Γ) ≫ hHomA
      = hRestrA ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥A) Bγ :=
    (Work.StemsB.pairRestrict_comp_subtypeIncl hHomA ({γ₀} : Set Γ) Bγ hAB').symm
  let cΓ := Work.Serre.csrRelMapOf (TopCat.of Γ) (TopCat.of ↥A) ({γ₀} : Set Γ) Bγ
    hHomA hRestrA wΓ
  haveI hcΓ : IsIso cΓ :=
    Work.Serre.PerCell.isIso_csrRelMapOf_homeo (X := TopCat.of Γ) (Y := TopCat.of ↥A)
      homA ({γ₀} : Set Γ) Bγ hAB' hBA' wΓ
  -- ## 3. The map of pairs `(X₀,F') → (A,{γ₀'})`
  let pjRestr : TopCat.of ↥F ⟶ TopCat.of ↥({γ₀} : Set Γ) :=
    Work.StemsB.pairRestrict (TopCat.ofHom (Work.StemsB.pullbackFst g p))
      F ({γ₀} : Set Γ) (fun _ hx => hx)
  let fm : TopCat.of ↥X₀ ⟶ TopCat.of ↥A :=
    (eHom ≫ TopCat.ofHom (Work.StemsB.pullbackFst g p)) ≫ hHomA
  let gm : TopCat.of ↥BF ⟶ TopCat.of ↥Bγ := (eRestr ≫ pjRestr) ≫ hRestrA
  have wm : Work.Cohomology.subtypeIncl (TopCat.of ↥X₀) BF ≫ fm
      = gm ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥A) Bγ := by
    apply TopCat.hom_ext
    ext x
    rfl
  let tauOne := Work.Serre.csrRelMapOf (TopCat.of ↥X₀) (TopCat.of ↥A) BF Bγ fm gm wm
  have hmap1 : fm ≫ Work.Cohomology.subtypeIncl (TopCat.of Γ') A
      = Work.Cohomology.subtypeIncl (TopCat.of Q) X₀ ≫ TopCat.ofHom q' := by
    apply TopCat.hom_ext
    ext x
    show (homA ((Work.StemsB.pullbackFst g p) (e x)) : Γ') = q' x.1
    rw [hhomA_coe]
    show incl ((e x).1.1) = q' x.1
    rw [he1 x]
    rfl
  -- ## 4. The identification of the first component
  have hident : tauOne = cX ≫ Work.Serre.stagePairMapRat g p γ₀ ≫ cΓ := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF))).1
    have h1 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ tauOne
        = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) :=
      Work.Serre.cokernel_π_csrRelMapOf
    have h2 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ cX
        = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F) :=
      Work.Serre.cokernel_π_csrRelMapOf
    have h3 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F)
          ≫ Work.Serre.stagePairMapRat g p γ₀
        = Work.Cohomology.chainMap ℚ (TopCat.of P) (TopCat.of Γ)
            (TopCat.ofHom (Work.StemsB.pullbackFst g p))
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ) ({γ₀} : Set Γ)) :=
      Work.Serre.RatTower.cokernel_π_stagePairMapRat g p γ₀
    have h4 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ) ({γ₀} : Set Γ)) ≫ cΓ
        = Work.Cohomology.chainMap ℚ (TopCat.of Γ) (TopCat.of ↥A) hHomA
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) :=
      Work.Serre.cokernel_π_csrRelMapOf
    rw [h1]
    symm
    calc cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF)
            ≫ (cX ≫ Work.Serre.stagePairMapRat g p γ₀ ≫ cΓ)
        = ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ cX)
              ≫ Work.Serre.stagePairMapRat g p γ₀) ≫ cΓ := by
          simp only [Category.assoc]
      _ = ((Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
              ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F))
              ≫ Work.Serre.stagePairMapRat g p γ₀) ≫ cΓ := by conv_lhs => rw [h2]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
              ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F))
            ≫ (Work.Serre.stagePairMapRat g p γ₀ ≫ cΓ) := by simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
            ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F)
                ≫ (Work.Serre.stagePairMapRat g p γ₀ ≫ cΓ)) := by simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
            ≫ ((cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of P) F)
                ≫ Work.Serre.stagePairMapRat g p γ₀) ≫ cΓ) := by simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
            ≫ ((Work.Cohomology.chainMap ℚ (TopCat.of P) (TopCat.of Γ)
                  (TopCat.ofHom (Work.StemsB.pullbackFst g p))
                ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ) ({γ₀} : Set Γ)))
                ≫ cΓ) := by conv_lhs => rw [h3]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
            ≫ (Work.Cohomology.chainMap ℚ (TopCat.of P) (TopCat.of Γ)
                  (TopCat.ofHom (Work.StemsB.pullbackFst g p))
                ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ) ({γ₀} : Set Γ))
                    ≫ cΓ)) := by simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
            ≫ (Work.Cohomology.chainMap ℚ (TopCat.of P) (TopCat.of Γ)
                  (TopCat.ofHom (Work.StemsB.pullbackFst g p))
                ≫ (Work.Cohomology.chainMap ℚ (TopCat.of Γ) (TopCat.of ↥A) hHomA
                    ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ))) := by
          conv_lhs => rw [h4]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of P) eHom
              ≫ Work.Cohomology.chainMap ℚ (TopCat.of P) (TopCat.of Γ)
                  (TopCat.ofHom (Work.StemsB.pullbackFst g p)))
            ≫ (Work.Cohomology.chainMap ℚ (TopCat.of Γ) (TopCat.of ↥A) hHomA
                ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ)) := by
          simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Γ)
              (eHom ≫ TopCat.ofHom (Work.StemsB.pullbackFst g p))
            ≫ (Work.Cohomology.chainMap ℚ (TopCat.of Γ) (TopCat.of ↥A) hHomA
                ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ)) := by
          conv_lhs => rw [← Work.Cohomology.chainMap_comp_relChains]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Γ)
              (eHom ≫ TopCat.ofHom (Work.StemsB.pullbackFst g p))
            ≫ Work.Cohomology.chainMap ℚ (TopCat.of Γ) (TopCat.of ↥A) hHomA)
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) := by
          simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A)
              ((eHom ≫ TopCat.ofHom (Work.StemsB.pullbackFst g p)) ≫ hHomA)
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) := by
          conv_lhs => rw [← Work.Cohomology.chainMap_comp_relChains]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) := rfl
  -- ## 5. The two short exact triple sequences
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.Serre.RatTower.tripleShortR (TopCat.of Q) F' X₀ hF'X₀
  let S₂ : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
    Work.Serre.RatTower.tripleShortR (TopCat.of Γ') ({γ₀'} : Set Γ') A hsub
  have hS₁ : S₁.ShortExact := Work.Serre.RatTower.tripleShortR_shortExact (TopCat.of Q) F' X₀ hF'X₀
  have hS₂ : S₂.ShortExact :=
    Work.Serre.RatTower.tripleShortR_shortExact (TopCat.of Γ') ({γ₀'} : Set Γ') A hsub
  -- ## 6. The two commutation squares
  have sq1 : tauOne ≫ S₂.f = S₁.f ≫ Work.Serre.stagePairMapRat g' p γ₀' := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF))).1
    have h1 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ tauOne
        = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) :=
      Work.Serre.cokernel_π_csrRelMapOf
    have h2 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) ≫ S₂.f
        = Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) :=
      Work.Serre.RatTower.cokernel_π_tripleShortR_f (TopCat.of Γ') ({γ₀'} : Set Γ') A hsub
    have h3 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
          ≫ Work.Serre.stagePairMapRat g' p γ₀'
        = Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) :=
      Work.Serre.RatTower.cokernel_π_stagePairMapRat g' p γ₀'
    have h4 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ S₁.f
        = Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F') :=
      Work.Serre.RatTower.cokernel_π_tripleShortR_f (TopCat.of Q) F' X₀ hF'X₀
    calc cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF)
            ≫ (tauOne ≫ S₂.f)
        = (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ tauOne) ≫ S₂.f := by
          simp only [Category.assoc]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ)) ≫ S₂.f := by
          conv_lhs => rw [h1]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
            ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥A) Bγ) ≫ S₂.f) := by
          simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
            ≫ (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A
                ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ'))) := by
          conv_lhs => rw [h2]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of ↥A) fm
            ≫ Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A)
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) := by
          simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Γ')
            (fm ≫ Work.Cohomology.subtypeIncl (TopCat.of Γ') A)
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) := by
          conv_lhs => rw [← Work.Cohomology.chainMap_comp_relChains]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Γ')
            (Work.Cohomology.subtypeIncl (TopCat.of Q) X₀ ≫ TopCat.ofHom q')
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) := by
          conv_lhs => rw [hmap1]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Q)
              (Work.Cohomology.subtypeIncl (TopCat.of Q) X₀)
            ≫ Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q'))
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) := by
          conv_lhs => rw [Work.Cohomology.chainMap_comp_relChains]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of ↥X₀) (TopCat.of Q)
              (Work.Cohomology.subtypeIncl (TopCat.of Q) X₀)
            ≫ (Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
                ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ'))) := by
          simp only [Category.assoc]
      _ = Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀
            ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
                ≫ Work.Serre.stagePairMapRat g' p γ₀') := by
          conv_lhs => rw [← h3]
      _ = (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F'))
            ≫ Work.Serre.stagePairMapRat g' p γ₀' := by simp only [Category.assoc]
      _ = (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF) ≫ S₁.f)
            ≫ Work.Serre.stagePairMapRat g' p γ₀' := by conv_lhs => rw [← h4]
      _ = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of ↥X₀) BF)
            ≫ (S₁.f ≫ Work.Serre.stagePairMapRat g' p γ₀') := by simp only [Category.assoc]
  have sq2 : Work.Serre.stagePairMapRat g' p γ₀' ≫ S₂.g
      = S₁.g ≫ Work.Serre.E3aStep.stepMapQ p incl g' := by
    apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F'))).1
    have h1 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
          ≫ Work.Serre.stagePairMapRat g' p γ₀'
        = Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ')) :=
      Work.Serre.RatTower.cokernel_π_stagePairMapRat g' p γ₀'
    have h2 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ'))
          ≫ S₂.g = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A) :=
      Work.Serre.RatTower.cokernel_π_tripleShortR_g (TopCat.of Γ') ({γ₀'} : Set Γ') A hsub
    have h3 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀)
          ≫ Work.Serre.E3aStep.stepMapQ p incl g'
        = Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A) := by
      have hrev : Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A)
          = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀)
            ≫ Work.Serre.E3aStep.stepMapQ p incl g' := by
        unfold Work.Serre.E3aStep.stepMapQ Work.Serre.relChainsRMapOf
        exact (Work.Cohomology.cokernel_π_map _ _ _ _ _).symm
      exact hrev.symm
    have h4 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F') ≫ S₁.g
        = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀) :=
      Work.Serre.RatTower.cokernel_π_tripleShortR_g (TopCat.of Q) F' X₀ hF'X₀
    calc cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
            ≫ (Work.Serre.stagePairMapRat g' p γ₀' ≫ S₂.g)
        = (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
            ≫ Work.Serre.stagePairMapRat g' p γ₀') ≫ S₂.g := by simp only [Category.assoc]
      _ = (Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ'))) ≫ S₂.g := by
          conv_lhs => rw [h1]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
            ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') ({γ₀'} : Set Γ'))
                ≫ S₂.g) := by simp only [Category.assoc]
      _ = Work.Cohomology.chainMap ℚ (TopCat.of Q) (TopCat.of Γ') (TopCat.ofHom q')
            ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Γ') A) := by
          conv_lhs => rw [h2]
      _ = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) X₀)
            ≫ Work.Serre.E3aStep.stepMapQ p incl g' := by conv_lhs => rw [← h3]
      _ = (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F') ≫ S₁.g)
            ≫ Work.Serre.E3aStep.stepMapQ p incl g' := by conv_lhs => rw [← h4]
      _ = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of Q) F')
            ≫ (S₁.g ≫ Work.Serre.E3aStep.stepMapQ p incl g') := by simp only [Category.assoc]
  -- ## 7. The morphism of short complexes
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk tauOne (Work.Serre.stagePairMapRat g' p γ₀')
    (Work.Serre.E3aStep.stepMapQ p incl g') sq1 sq2
  -- ## 8. The first component: from the induction hypothesis
  have hτ₁ : ∀ i : ℕ, i < N → IsIso (HomologicalComplex.homologyMap φ.τ₁ i) := by
    intro i hi
    have h : HomologicalComplex.homologyMap φ.τ₁ i
        = HomologicalComplex.homologyMap tauOne i := rfl
    rw [h, hident, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI : IsIso (HomologicalComplex.homologyMap cX i) :=
      Iso.isIso_hom (HomologicalComplex.homologyMapIso (asIso cX) i)
    haveI : IsIso (HomologicalComplex.homologyMap cΓ i) :=
      Iso.isIso_hom (HomologicalComplex.homologyMapIso (asIso cΓ) i)
    haveI : IsIso (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat g p γ₀) i) :=
      IH.1 i hi
    infer_instance
  have e₁ : Epi (HomologicalComplex.homologyMap φ.τ₁ N) := by
    have h : HomologicalComplex.homologyMap φ.τ₁ N
        = HomologicalComplex.homologyMap tauOne N := rfl
    rw [h, hident, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    haveI : Epi (HomologicalComplex.homologyMap cX N) := IsIso.epi_of_iso _
    haveI : Epi (HomologicalComplex.homologyMap cΓ N) := IsIso.epi_of_iso _
    haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat g p γ₀) N) := IH.2
    haveI : Epi (HomologicalComplex.homologyMap cX N
        ≫ HomologicalComplex.homologyMap (Work.Serre.stagePairMapRat g p γ₀) N) :=
      CategoryTheory.epi_comp _ _
    exact CategoryTheory.epi_comp _ _
  -- ## 9. The third component: the step hypothesis
  have hτ₃ : ∀ i : ℕ, i < N → IsIso (HomologicalComplex.homologyMap φ.τ₃ i) := by
    intro i hi
    exact hstep.1 i hi
  have e₃ : Epi (HomologicalComplex.homologyMap φ.τ₃ N) := hstep.2
  -- ## 10. The five lemma
  obtain ⟨hτ₂iso, hτ₂epi⟩ :=
    Work.Serre.RatTower.fiveLemmaTau2 φ hS₁ hS₂ N hτ₁ hτ₃ e₁ e₃
  exact ⟨hτ₂iso, hτ₂epi⟩

end

end Work.Serre.B1Rel
