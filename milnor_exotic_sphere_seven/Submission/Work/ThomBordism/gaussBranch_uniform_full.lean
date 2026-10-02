import Mathlib
import Submission.Work.ThomBordism.gaussBranch_uniform_le
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero_ne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The branch uniformity of `pulledThom_gauss`, with NO parity and NO connectedness hypothesis

`Work.ThomBordism.gaussBranch_uniform` needs `(hodd : Odd k)` and `(∀ i, ConnectedSpace (Fam i).pt)`.
Both are vestigial for the last mile (see `NOTE_SESSION64.md` section 9):

* the parity is removed by `Work.ThomBordism.gaussBranch_uniform_le` (the flip chain only needs
  `1 ≤ k`);
* the connectedness is only used to produce one point of `(Fam i).pt` for the non-degeneracy
  `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`; the nonempty form
  `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero_ne` is what is needed, and
  `Work.PTGeometric.GenuineTubeGeometry.nonempty` provides `Nonempty (Fam i).pt` from `G` itself.

So the statement below holds at the exact generality of
`Work.PTGeometric.OrientationProducer`: the branch `s` of the field
`Work.PTGeometric.GenuineTubeGeometry.pulledThom_gauss` is ONE sign for all pieces, which is what the
boundary coordination of the last mile needs (`NOTE_SESSION64.md` sections 8-9).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

theorem gaussBranch_uniform_full
    {k : ℕ} (hk : 1 ≤ k) {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
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
    exact Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero_ne (G.nonempty i) (G.emb i)
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
