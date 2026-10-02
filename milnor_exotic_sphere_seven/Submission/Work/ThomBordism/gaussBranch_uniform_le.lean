import Mathlib
import Submission.Work.ThomBordism.gaussBranch_uniform

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

/-! ## Removing the spurious `Odd k` hypotheses

`Work.ThomBordism.gaussBranch_uniform` is the uniformity of the Gauss branch, and the version below
(`gaussBranch_uniform_le`) drops its hypothesis `Odd k`, keeping only `1 ≤ k`.  The only place the
parity was used in the chain of proofs on disk is `gtdThomClass_flipPairs`, whose proof actually
never uses it: the universal flip identity `GtdFlip.gtdFlip_crux_of` is available for every rank
`1 ≤ k` (the orientation flip of the tautological bundle negates the Thom class in *every* rank,
since reversing the orientation of the fibre negates the generator of `H^k(D^k, S^{k-1})` for
each `k ≥ 1`).  We re-derive the three `Odd`-flavoured lemmas here without the parity hypothesis;
`Odd k` is then never needed again. -/

/-- **The orientation flip negates the tautological Thom class**, for every rank `k ≥ 1`
(no parity hypothesis).  Immediate from the chartwise computation
`GtdFlip.chartClassOgFlip` plus the coefficient compatibility `GtdFlip.chartCoeffCompat_taut`. -/
theorem gtdFlip_crux_le (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (Work.Thom.relCohMap (Work.ThomBordism.Grassmann.ogFlipTotal k m)
      (Work.ThomBordism.GtdFlip.Zc k m) (Work.ThomBordism.GtdFlip.Zc k m)
      (Work.ThomBordism.Grassmann.ogFlipTotal_mem k m) ℤ k).hom
      (Work.ThomBordism.GtdFlip.Tau k m)
      = -(Work.ThomBordism.GtdFlip.Tau k m) :=
  Work.ThomBordism.GtdFlip.gtdFlip_crux_of k m hk hm
    (fun S => Work.ThomBordism.GtdFlip.chartClassOgFlip k m hk S)
    (fun S T dS dT hdS hdT =>
      Work.ThomBordism.GtdFlip.chartCoeffCompat_taut k m hk S T dS dT hdS hdT)

/-- **The flip lemma for arbitrary bundle data, without parity.**  Verbatim copy of
`GtdFlip.gtdThomClass_flipPairs_of_crux` with the (unused) `Odd k` hypothesis replaced by
`1 ≤ k`; the crux input is `gtdFlip_crux_le`. -/
theorem gtdThomClass_flipPairs_le {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (gauss : C(B, Work.ThomBordism.Grassmann.OG k m))
    (Gplus : C(Z.TotalSpace, (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp : ∀ p : Z.TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (Gplus p) = gauss p.1)
    (Gminus : C(Z.TotalSpace, (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace))
    (hbp' : ∀ p : Z.TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (Gminus p)
        = Work.ThomBordism.Grassmann.ogFlip k m (gauss p.1))
    (hvec : ∀ p : Z.TotalSpace,
      Work.ThomBordism.Grassmann.evalVec (Gminus p)
        = Work.ThomBordism.Grassmann.evalVec (Gplus p))
    (hmem : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gplus p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m))
    (hmem' : ∀ p ∈ Work.Thom.zeroComplement Z,
      Gminus p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) :
    (Work.Thom.relCohMap Gminus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmem' ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ
      = - ((Work.Thom.relCohMap Gplus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmem ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ) := by
  classical
  have hG : Gminus = (Work.ThomBordism.Grassmann.ogFlipTotal k m).comp Gplus := by
    apply ContinuousMap.ext
    intro p
    refine Work.ThomBordism.Grassmann.evalVec_injective_of_proj_eq ?_ ?_
    · show (Gminus p).1 = (Work.ThomBordism.Grassmann.ogFlipTotal k m (Gplus p)).1
      have h1 : (Work.ThomBordism.Grassmann.ogFlipTotal k m (Gplus p)).1
          = Work.ThomBordism.Grassmann.ogFlip k m (gauss p.1) := by
        rw [Work.ThomBordism.Grassmann.ogFlipTotal_proj, ← hbp p]
      rw [h1, show (Gminus p).1 = Work.ThomBordism.Grassmann.ogFlip k m (gauss p.1) from hbp' p]
    · rw [ContinuousMap.comp_apply, Work.ThomBordism.Grassmann.ogFlipTotal_evalVec, hvec p]
  have hmemB : ∀ p ∈ Work.Thom.zeroComplement Z,
      (Work.ThomBordism.Grassmann.ogFlipTotal k m) (Gplus p)
        ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m) :=
    fun p hp => Work.ThomBordism.Grassmann.ogFlipTotal_mem k m _ (hmem p hp)
  have hL : (Work.Thom.relCohMap Gminus (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmem' ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ
      = (Work.Thom.relCohMap ((Work.ThomBordism.Grassmann.ogFlipTotal k m).comp Gplus)
        (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hmemB ℤ k).hom
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ :=
    congrArg (fun f => (ModuleCat.Hom.hom f)
        (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ)
      (Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) hG hmem' hmemB ℤ k)
  rw [hL]
  erw [← Work.Thom.relCohMap_compA_apply (Work.Thom.zeroComplement Z)
    (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m))
    (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k m)) Gplus
    (Work.ThomBordism.Grassmann.ogFlipTotal k m) hmem
    (Work.ThomBordism.Grassmann.ogFlipTotal_mem k m) hmemB ℤ k
    (Work.ThomBordism.Grassmann.tautologicalThomClass k m).τ]
  rw [gtdFlip_crux_le k m hk hm, map_neg]

/-- **The cross-branch comparison of the Gauss candidate, without parity.**  Verbatim copy of
`gtdU_eq_zsmul_of_branch_aux` with the `Odd k` hypothesis replaced by `1 ≤ k`: the positive branch
uses the unbranched datum independence `gtdUWith_eq_of_normalData` (the branch function is the
identity there) and the negative one the parity-free flip lemma `gtdThomClass_flipPairs_le`. -/
theorem gtdU_eq_zsmul_of_branch_aux_le
    {V : Work.ThomBordism.Man8} {k : ℕ}
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
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
      refine Work.ThomBordism.gtdUWith_eq_of_normalData E ND ND' G hgm ?_ hvec G' hgm' ?_ hvec'
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
      gtdThomClass_flipPairs_le (Work.Tubular.normalBundle E ND) hk (by norm_num)
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

/-- **Uniformity of the Gauss branch, at every rank `≥ 1`.**  The statement
`Work.ThomBordism.gaussBranch_uniform` with its `Odd k` hypothesis dropped (only `1 ≤ k` is kept);
the proof is that of `gaussBranch_uniform`, the parity-dependent step being supplied by
`gtdU_eq_zsmul_of_branch_aux_le`. -/
theorem gaussBranch_uniform_le
    {k : ℕ} (hk : 1 ≤ k) {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (hconn : ∀ i, ConnectedSpace (Fam i).pt)
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
      exact gtdU_eq_zsmul_of_branch_aux_le hk (G.emb i) (NDg i) (NDp i) (sg i) (hsg i)
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
