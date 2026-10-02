import Mathlib
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.gtdUWith_eq_of_normalData
import Submission.Work.ThomBordism.gtdThomClass_flipPairs
import Submission.Work.ThomBordism.Signs.flipMap
import Submission.Work.ThomBordism.ogFlipInvolution
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.gtdU_localDegreeExists
import Submission.Work.ThomBordism.gtdUWith_eq_of_normalData_branch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- **An elementary `ℤ`-module statement.**  If two unit multiples of the same class `U` are both
annihilated-consistently by a family of linear functionals `Ψ i` (i.e. `Ψ i (a • U) = Ψ i (b • U)`
for all `i`), and one of the functionals takes a nonzero value on `U`, then `a = b`. -/
theorem zsmul_eq_of_forall_eq {M : Type*} [AddCommGroup M] [Module ℤ M] {ι : Type*}
    (Ψ : ι → M →ₗ[ℤ] ℤ) (R : ι → ℤ) (hnd : ∃ i, R i ≠ 0) {U : M} {a b : ℤ}
    (ha : ∀ i, Ψ i (a • U) = R i) (hb : ∀ i, Ψ i (b • U) = R i) : a = b := by
  obtain ⟨i₀, hi₀⟩ := hnd
  have h1 : a • Ψ i₀ U = R i₀ := (map_zsmul (Ψ i₀) a U).symm.trans (ha i₀)
  have h2 : b • Ψ i₀ U = R i₀ := (map_zsmul (Ψ i₀) b U).symm.trans (hb i₀)
  have hw : Ψ i₀ U ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at h1
    exact hi₀ h1.symm
  have h3 : a • Ψ i₀ U = b • Ψ i₀ U := h1.trans h2.symm
  have h4 : a * Ψ i₀ U = b * Ψ i₀ U := by simpa [zsmul_eq_mul] using h3
  exact mul_right_cancel₀ hw h4

/-- **The local-degree class is defined up to a unit, given non-degeneracy.**  If `a • U` and
`b • U` both implement the local degree of the tube data (`Work.ThomBordism.IsLocalDegreeClass`)
and the functional `x ↦ ⟨z^* x, V.c⟩` is not identically zero (which holds for a connected `V`,
`Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`), then `a = b`. -/
theorem isLocalDegreeClass_zsmul_eq {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} {C : Work.Tubular.TubeChart E ε}
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y.ofLp j| < R)
    (hnd : ∃ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c ≠ 0)
    {U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)} {a b : ℤ}
    (ha : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox (a • U))
    (hb : Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox (b • U)) : a = b := by
  classical
  let X := TopCat.of (Work.Tubular.NormalTotal E)
  let A := Work.Tubular.normalNonzero E
  let RHS : Work.Thom.Coh ℤ 8 X → ℤ := fun x =>
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
      ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c
  have hnd' : ∃ x : Work.Thom.Coh ℤ 8 X, RHS x ≠ 0 := hnd
  let Φ : Work.Thom.Coh ℤ 8 X → (Work.Thom.RelCoh ℤ k X A →ₗ[ℤ] ℤ) := fun x =>
    { toFun := fun W => Work.Tubular.relKronH X A (8 + k)
        ((Work.Cohomology.mixedCup X A 8 k x) W)
        ((Nat.add_comm 8 k).symm ▸ (Work.Tubular.collapseRelK8 C g hg hR hbox))
      map_add' := by
        intro u v
        rw [map_add (Work.Cohomology.mixedCup X A 8 k x) u v,
            LinearMap.map_add (Work.Tubular.relKronH X A (8 + k)) _ _,
            LinearMap.add_apply]
      map_smul' := by
        intro n u
        rw [LinearMap.map_smul (Work.Cohomology.mixedCup X A 8 k x) n u,
            LinearMap.map_smul (Work.Tubular.relKronH X A (8 + k)) n _,
            LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] }
  have hbridge : ∀ (W : Work.Thom.RelCoh ℤ k X A) (x : Work.Thom.Coh ℤ 8 X),
      Work.Tubular.relKronH X A (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup X A 8 k x W))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = Φ x W := by
    intro W x
    show Work.Tubular.relKronH X A (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup X A 8 k x W))
        (Work.Tubular.collapseRelK8 C g hg hR hbox)
      = Work.Tubular.relKronH X A (8 + k) ((Work.Cohomology.mixedCup X A 8 k x) W)
          ((Nat.add_comm 8 k).symm ▸ (Work.Tubular.collapseRelK8 C g hg hR hbox))
    exact (Work.Tubular.relKronH_bridgeA (Nat.add_comm 8 k)
      ((Work.Cohomology.mixedCup X A 8 k x W))
      (Work.Tubular.collapseRelK8 C g hg hR hbox)).symm
  have hA : ∀ x, Φ x (a • U) = RHS x := by
    intro x
    rw [← hbridge (a • U) x]
    exact ha x
  have hB : ∀ x, Φ x (b • U) = RHS x := by
    intro x
    rw [← hbridge (b • U) x]
    exact hb x
  exact zsmul_eq_of_forall_eq Φ RHS hnd' hA hB

/-- **The cross-branch comparison of the Gauss candidate.**  Two bundle maps into the tautological
bundle whose (plane, vector) data are the (`σ`-branched) Gauss data of *two different* normal data
of the same embedding determine the same `gtdU` up to the single sign `σ`: the positive branch
`σ = 1` is `Work.ThomBordism.gtdUWith_eq_of_normalData_branch`, the negative one is the
orientation flip `Work.ThomBordism.gtdThomClass_flipPairs` composed with it. -/
theorem gtdU_eq_zsmul_of_branch_aux
    {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hodd : Odd k)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND p.1))
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (G' : C((Work.Tubular.normalBundle E ND').TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm' : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND'),
      G' p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp' : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G' p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND' p.1)
    (hvec' : ∀ p, Work.ThomBordism.Grassmann.evalVec (G' p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND' p))) :
    Work.ThomBordism.gtdU E ND G hgm
      = (if σ = 1 then (1 : ℤ) else -1) • Work.ThomBordism.gtdU E ND' G' hgm' := by
  classical
  by_cases h1 : σ = 1
  · -- the positive branch: the datum independence of `gtdUWith`
    have hEq : Work.ThomBordism.gtdU E ND G hgm = Work.ThomBordism.gtdU E ND' G' hgm' := by
      rw [Work.ThomBordism.gtdU_eq_gtdUWith, Work.ThomBordism.gtdU_eq_gtdUWith]
      refine Work.ThomBordism.gtdUWith_eq_of_normalData_branch E ND ND' 1 (Or.inl rfl) hodd
        G hgm ?_ hvec G' hgm' ?_ hvec'
        (Work.ThomBordism.Grassmann.tautologicalThomClass k 10)
      · intro p
        have hp := hbp p
        rw [h1] at hp
        exact hp
      · intro p
        simpa using hbp' p
    rw [hEq, h1]
    simp
  · -- the negative branch: flip `G` back to the positive branch
    have hneg : σ = -1 := by
      rcases hσ with h | h
      · exact absurd h h1
      · exact h
    obtain ⟨F, hFproj, hFeval, hFzero⟩ := Work.ThomBordism.Signs.flipMap k 10
    let Gf : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) := F.comp G
    have hbpF : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (Gf p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1 := by
      intro p
      change (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (F (G p)) = _
      rw [hFproj, hbp p, if_neg h1, Work.ThomBordism.Grassmann.ogFlip_ogFlip]
    have hvecF : ∀ p, Work.ThomBordism.Grassmann.evalVec (Gf p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)) := by
      intro p
      change Work.ThomBordism.Grassmann.evalVec (F (G p)) = _
      rw [hFeval, hvec p]
    have hgmF : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        Gf p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10) := by
      intro p hp
      change F (G p) ∈ _
      exact hFzero (G p) (hgm p hp)
    have hbpFlip : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.ogFlip k 10
            ((⟨fun x => Work.ThomBordism.Grassmann.padGaussFun E ND x,
              Work.ThomBordism.Grassmann.continuous_padGaussFun E ND⟩ :
              C(V.pt, Work.ThomBordism.Grassmann.OG k 10)) p.1) := by
      intro p
      rw [hbp p, if_neg h1]
      rfl
    have hflip : (Work.Thom.relCohMap G
          (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm
          ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ
        = - ((Work.Thom.relCohMap Gf
          (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmF
          ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ) :=
      Work.ThomBordism.gtdThomClass_flipPairs (Work.Tubular.normalBundle E ND) hodd (by norm_num)
        ⟨fun x => Work.ThomBordism.Grassmann.padGaussFun E ND x,
          Work.ThomBordism.Grassmann.continuous_padGaussFun E ND⟩
        Gf hbpF G hbpFlip (fun p => by rw [hvecF p, hvec p]) hgmF hgm
    have hUm : Work.ThomBordism.gtdU E ND G hgm
        = - Work.ThomBordism.gtdU E ND Gf hgmF := by
      show (Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
          (Work.Tubular.normalNonzero E)
          (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.ThomBordism.gtd_mem E ND) ℤ k).hom
          ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
            (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm
            ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
        = - ((Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
          (Work.Tubular.normalNonzero E)
          (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.ThomBordism.gtd_mem E ND) ℤ k).hom
          ((Work.Thom.relCohMap Gf (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
            (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmF
            ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ))
      rw [hflip, map_neg]
    have hGf : Work.ThomBordism.gtdU E ND Gf hgmF
        = Work.ThomBordism.gtdU E ND' G' hgm' := by
      rw [Work.ThomBordism.gtdU_eq_gtdUWith, Work.ThomBordism.gtdU_eq_gtdUWith]
      exact Work.ThomBordism.gtdUWith_eq_of_normalData E ND ND' Gf hgmF hbpF hvecF G' hgm'
        hbp' hvec' (Work.ThomBordism.Grassmann.tautologicalThomClass k 10)
    rw [hUm, hGf, hneg]
    simp

theorem gaussBranch_uniform
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (hodd : Odd k) (hconn : ∀ i, ConnectedSpace (Fam i).pt)
    (hcan : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ i, ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
        (Gp : C((Work.Tubular.normalBundle (G.emb i) ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle (G.emb i) ND),
          Gp p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)),
        (∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (Gp p)
            = Work.ThomBordism.Grassmann.padGaussFun (G.emb i) ND p.1) ∧
        (∀ p, Work.ThomBordism.Grassmann.evalVec (Gp p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal (G.emb i) ND p))) ∧
        Work.ThomBordism.IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR (G.hbox i)
          (t • Work.ThomBordism.gtdU (G.emb i) ND Gp hgm)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ i, ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
        (Gc : C((Work.Tubular.normalBundle (G.emb i) ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle (G.emb i) ND),
          Gc p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)),
        G.pulledThom i = Work.ThomBordism.gtdU (G.emb i) ND Gc hgm ∧
        (∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (Gc p)
            = (if s = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
                (Work.ThomBordism.Grassmann.padGaussFun (G.emb i) ND p.1)) ∧
        (∀ p, Work.ThomBordism.Grassmann.evalVec (Gc p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal (G.emb i) ND p))) ∧
        (∀ (t : Fin (8 + k) → unitInterval),
          Work.Tubular.cubeToEuc (8 + k) G.R t ∈ (G.chart i).openTube →
            ∃ hne : Work.Tubular.alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i)
                (G.g i) (G.hg i) t ≠ D.t₀,
              G.gauss ⟨Work.Tubular.alphaV (G.chart i) G.hR (G.hbox i) D.t₀ (G.J i) (G.hJ i)
                  (G.g i) (G.hg i) t, hne⟩ =
                (if s = 1 then id else Work.ThomBordism.Grassmann.ogFlip k G.mU)
                  (Work.ThomBordism.padGaussFunM (G.emb i) ND G.mU G.hmU
                    ((G.chart i).inv (Work.Tubular.cubeToEuc (8 + k) G.R t)).1.1)) := by
  classical
  obtain ⟨t, ht, hcan'⟩ := hcan
  choose NDp Gp hgmp hbpP hvecP hldP using hcan'
  choose NDg Gg hgmg sg hsg hpte hbpg hvecg hgaussg using G.pulledThom_gauss
  -- the non-degeneracy of the local-degree functional
  have hnd : ∀ i, ∃ x : Work.Thom.Coh ℤ 8
      (TopCat.of (Work.Tubular.NormalTotal (G.emb i))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of (Fam i).pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal (G.emb i)) ℤ 8).hom x)
        (Fam i).c ≠ 0 := by
    intro i
    haveI := hconn i
    exact exists_kronH_zeroSection_fund_ne_zero (k := k) (G.emb i)
  -- the branch of the recorded Gauss datum is the canonical local-degree sign
  have hsign : ∀ i, sg i = t := by
    intro i
    have hcmp : G.pulledThom i
        = (if sg i = 1 then (1 : ℤ) else -1) •
            Work.ThomBordism.gtdU (G.emb i) (NDp i) (Gp i) (hgmp i) := by
      rw [hpte i]
      exact gtdU_eq_zsmul_of_branch_aux (G.emb i) (NDg i) (NDp i) (sg i) (hsg i) hodd
        (Gg i) (hgmg i) (hbpg i) (hvecg i) (Gp i) (hgmp i) (hbpP i) (hvecP i)
    have hld1 : Work.ThomBordism.IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR
        (G.hbox i)
        ((if sg i = 1 then (1 : ℤ) else -1) •
          Work.ThomBordism.gtdU (G.emb i) (NDp i) (Gp i) (hgmp i)) := by
      rw [← hcmp]
      exact G.localDegree i
    have hld2 : Work.ThomBordism.IsLocalDegreeClass (G.chart i) (G.g i) (G.hg i) G.hR
        (G.hbox i)
        (t • Work.ThomBordism.gtdU (G.emb i) (NDp i) (Gp i) (hgmp i)) := hldP i
    have heq : (if sg i = 1 then (1 : ℤ) else -1) = t :=
      isLocalDegreeClass_zsmul_eq (E := G.emb i) (C := G.chart i) (g := G.g i) (hg := G.hg i)
        (hR := G.hR) (hbox := G.hbox i) (hnd := hnd i)
        (U := Work.ThomBordism.gtdU (G.emb i) (NDp i) (Gp i) (hgmp i))
        (a := if sg i = 1 then (1 : ℤ) else -1) (b := t) hld1 hld2
    rcases hsg i with h | h <;> rw [h] at heq ⊢ <;> simpa using heq
  refine ⟨t, ht, ?_⟩
  intro i
  refine ⟨NDg i, Gg i, hgmg i, hpte i, ?_, hvecg i, ?_⟩
  · intro p
    have hp := hbpg i p
    rw [hsign i] at hp
    exact hp
  · intro u hu
    obtain ⟨hne, hval⟩ := hgaussg i u hu
    exact ⟨hne, by rw [hval, hsign i]⟩

end

end Work.ThomBordism
