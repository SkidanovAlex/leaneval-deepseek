import Mathlib
import Submission.Work.ThomBordism._gtd.P7
import Submission.Work.ThomBordism.gtdFrameProj_padEuc
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.tubeThomRepOfNuPairing
import Submission.Work.ThomBordism.Signs.flipMap
import Submission.Work.ThomBordism.gtdThomClass_flipPairs
import Submission.Work.ThomBordism.gtdU_span_top
import Submission.Work.ThomBordism.Grassmann.ogFlipComapIso
import Submission.Work.ThomBordism.gtdNuPairing
import Submission.Work.ThomBordism._gtd.P5

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- **Packaging**: from a Gauss/classifying candidate `G` together with its one-point extension `J`,
the local-degree identity `hld` for `G`, the classifying bundle isomorphism `e`, and the fibrewise
(plane, vector) identity for `G` on the tube, produce the data demanded by the PTGEOMETRIC producer:
the based map on `Th(ν)`, its collapse representative, and the fibrewise coordinate clause. -/
theorem gcdCore {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hodd : Odd k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V)
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 10))
    (e : Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10) gauss)
      (Work.Tubular.normalBundle E ND))
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p) = gauss p.1)
    (J : C(OnePoint (Work.Tubular.normalBundle E ND).TotalSpace,
      OnePoint (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hJ : ∀ p, J (OnePoint.some p) = OnePoint.some (G p))
    (hJinf : J OnePoint.infty = OnePoint.infty)
    (hld : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
          (Work.ThomBordism.gtdU E ND G hgm)))
        (Work.Tubular.collapseRelK8 C g hg hR hbox)
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c)
    (hfibJ : ∀ y ∈ C.openTube,
      ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
        (J.comp ↑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
            (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p)
          = Work.PTGeometric.padEndEuc k 10 (by norm_num)
              (Work.PTGeometric.tubeNormalProj E C y) ∧
        Work.ThomBordism.Grassmann.evalVec p =
          Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2)) :
    ∃ (J' : C(OnePoint (Work.Tubular.NormalTotal E),
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).T))
      (hJ' : J' OnePoint.infty =
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀)
      (rep : Work.Tubular.TubeThomRep k
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N),
      rep.collapse = GenLoop.congr
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
        (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV C hR hbox
          (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
          J' hJ' g hg) ∧
      (∀ y ∈ C.openTube, ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
        J' (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p) =
          Work.PTGeometric.padEndEuc k 10 (by norm_num) (Work.PTGeometric.tubeNormalProj E C y) ∧
        Work.ThomBordism.Grassmann.evalVec p =
          Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) ∧
        p = G (Work.Tubular.normalToBundle E ND
          (Work.Tubular.normalBlowUp E ε (C.inv y)))) := by
  classical
  let ζ : C(OnePoint (Work.Tubular.NormalTotal E),
      OnePoint (Work.Tubular.normalBundle E ND).TotalSpace) :=
    (Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm
  obtain ⟨hν1, hν2⟩ :=
    gtdNuPairing hk hodd E ND N C q hU hR hbox g hg hg2 gauss e G hgm hbp J hJ hJinf hld
  have hζinf : ζ OnePoint.infty = OnePoint.infty := by
    change (⇑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
      OnePoint.infty = OnePoint.infty
    rw [Homeomorph.onePointCongr_symm_apply, OnePoint.map_infty]
  have hJ'inf : (J.comp ζ) OnePoint.infty = OnePoint.infty := by
    change J (ζ OnePoint.infty) = OnePoint.infty
    rw [hζinf, hJinf]
  obtain ⟨rep, hrep⟩ :=
    tubeThomRepOfNuPairing (D := Work.ThomBordism.connTarget k (by omega)
      (Work.ThomBordism.PhiG k (by omega))) E C hR hbox (J.comp ζ)
      (show (J.comp ζ) OnePoint.infty = (Work.ThomBordism.connTarget k (by omega)
          (Work.ThomBordism.PhiG k (by omega))).t₀ from by
        rw [show (Work.ThomBordism.connTarget k (by omega)
            (Work.ThomBordism.PhiG k (by omega))).t₀ = OnePoint.infty from rfl]
        exact hJ'inf)
      g hg hν1 hν2
  refine ⟨J.comp ζ, ?_, rep, hrep, ?_⟩
  · show (J.comp ζ) OnePoint.infty = (Work.ThomBordism.connTarget k (by omega)
        (Work.ThomBordism.PhiG k (by omega))).t₀
    rw [show (Work.ThomBordism.connTarget k (by omega)
        (Work.ThomBordism.PhiG k (by omega))).t₀ = OnePoint.infty from rfl]
    exact hJ'inf
  · intro y hy
    obtain ⟨p, hp1, hp2, hp3⟩ := hfibJ y hy
    refine ⟨p, hp1, hp2, hp3, ?_⟩
    have hζ : ζ (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        = OnePoint.some (Work.Tubular.normalToBundle E ND
            (Work.Tubular.normalBlowUp E ε (C.inv y))) := by
      change (⇑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
        (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = _
      rw [Homeomorph.onePointCongr_symm_apply, OnePoint.map_some,
        gtdEucNormalHomeomorph_symm_apply E ND]
    have h2 : (J.comp ζ) (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        = OnePoint.some (G (Work.Tubular.normalToBundle E ND
            (Work.Tubular.normalBlowUp E ε (C.inv y)))) := by
      change J (ζ (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))) = _
      rw [hζ, hJ]
    exact (OnePoint.some_eq_iff _ _).mp (hp1.symm.trans h2)


/-- **The per-member Gauss/tube data** (the assembly). -/
theorem gaussTubeDataAux {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hodd : Odd k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V)
    {ε : ℝ} (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε)
    (q : Work.Tubular.NormalSphSub E ε) (hU : IsCompact C.U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hldLD : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
            (Work.ThomBordism.gtdU E ND G hgm)))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c)
      (J : C(OnePoint (Work.Tubular.NormalTotal E),
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).T))
      (hJ : J OnePoint.infty =
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀)
      (rep : Work.Tubular.TubeThomRep k
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N),
      rep.collapse = GenLoop.congr
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
        (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV C hR hbox
          (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
          J hJ g hg) ∧
      (∀ y ∈ C.openTube, ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
        J (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p) =
          Work.PTGeometric.padEndEuc k 10 (by norm_num) (Work.PTGeometric.tubeNormalProj E C y) ∧
        Work.ThomBordism.Grassmann.evalVec p =
          Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) ∧
        p = G (Work.Tubular.normalToBundle E ND
          (Work.Tubular.normalBlowUp E ε (C.inv y)))) ∧
      ∃ (σ : ℤ), (σ = 1 ∨ σ = -1) ∧
        (∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
            = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND p.1)) ∧
        (∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
          Work.ThomBordism.Grassmann.evalVec (G p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) := by
  classical
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨Gp, hbpP, hvecP, hgmP, Jloc, hJloc, hJlocinf, hfibP⟩ :=
    gtdGaussCandidate E ND hε C q hU hR hbox g hg hg2
  obtain ⟨eP⟩ := padGaussClassifies E hk1 ND
  let gaussP : C(V.pt, Work.ThomBordism.Grassmann.OG k 10) :=
    ⟨Work.ThomBordism.Grassmann.padGaussFun E ND,
      Work.ThomBordism.Grassmann.continuous_padGaussFun E ND⟩
  let ζ : C(OnePoint (Work.Tubular.NormalTotal E),
      OnePoint (Work.Tubular.normalBundle E ND).TotalSpace) :=
    (Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm
  -- the fibrewise geometry of the candidate
  have hfibGp : ∀ y ∈ C.openTube,
      Work.PTGeometric.projOfPlane k 10
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
            (Gp (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y)))))
        = Work.PTGeometric.padEndEuc k 10 (by norm_num)
            (Work.PTGeometric.tubeNormalProj E C y) ∧
      Work.ThomBordism.Grassmann.evalVec
          (Gp (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))))
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) := by
    intro y hy
    obtain ⟨p, hp1, hp2, hp3⟩ := hfibP y hy
    have h1 : (Jloc.comp ζ) (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        = OnePoint.some (Gp (Work.Tubular.normalToBundle E ND
            (Work.Tubular.normalBlowUp E ε (C.inv y)))) := by
      change Jloc (ζ (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))) = _
      rw [show ζ (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
          = OnePoint.some (Work.Tubular.normalToBundle E ND
              (Work.Tubular.normalBlowUp E ε (C.inv y))) from by
        change (⇑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
          (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = _
        rw [Homeomorph.onePointCongr_symm_apply, OnePoint.map_some,
          gtdEucNormalHomeomorph_symm_apply E ND]]
      rw [hJloc]
    rw [h1] at hp1
    have hp : p = Gp (Work.Tubular.normalToBundle E ND
        (Work.Tubular.normalBlowUp E ε (C.inv y))) := ((OnePoint.some_eq_iff _ _).mp hp1).symm
    subst hp
    exact ⟨hp2, hp3⟩
  -- the classifying Thom class of the normal bundle
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) (CoverIdx V k) :=
    Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  have hproj : ∀ p : nu.TotalSpace, Work.Tubular.NormalTotal.proj (φ p) = p.1 := fun p => rfl
  have hlen : ∀ p : nu.TotalSpace,
      Work.Thom.fibreNorm nu p ≠ 0 ↔ Work.Tubular.normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  have hvec0 : ∀ x : V.pt, Work.Tubular.NormalTotal.vec (φ (Work.Thom.zeroSection nu x)) = 0 := by
    intro x
    show Work.Tubular.insCLM E ND ((Work.Tubular.normalBundle E ND).indexAt x) x
      (0 : Work.Tubular.Euc k) = 0
    exact map_zero _
  let Zb := Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10) gaussP
  obtain ⟨ψc, hψcp, hψcs, hfc, Tc, hTc⟩ := thomClassPullbackBundleComapRank
    (Work.ThomBordism.Grassmann.tautologicalBundle k 10) gaussP
    (Work.ThomBordism.Grassmann.tautologicalThomClass k 10) (n := k)
    (Work.ThomBordism.Grassmann.tautological_rank k 10).symm
  have hfe : ∀ x ∈ Work.Thom.zeroComplement nu, eP.invTotalSpace x ∈ Work.Thom.zeroComplement Zb := by
    intro x hx
    rw [Work.Thom.mem_zeroComplement] at hx ⊢
    show eP.inv x.1 x.2 ≠ 0
    intro h0
    have hE1 : eP.inv x.1 x.2 = 0 := h0
    have h2 : (show Work.Tubular.Euc k from x.2) = 0 := by
      rw [← eP.toTotalSpace_right_inv x]
      show eP.hom x.1 (eP.inv x.1 (x.2)) = 0
      rw [hE1, map_zero]
    exact hx h2
  obtain ⟨Th, hTh⟩ := thomClassNaturalityBundleIso Zb nu eP Tc hfe
  have hZ : Nonempty (Work.Thom.ThomClass nu k) := ⟨Th⟩
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) (CoverIdx V k) :=
    Work.TangentClasses.RealBundle.mapFibre eL nu
  obtain ⟨hψ, hψproj, hψnorm, hψzero⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ₁ : Z₁.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := hψ.symm.trans φ
  have hZ1 : Nonempty (Work.Thom.ThomClass Z₁ k) :=
    Work.Tubular.nonempty_thomClass_of_bundleIso (Work.Tubular.bundleIsoMapFibre eL nu) Th
  have hproj1 : ∀ p : Z₁.TotalSpace, Work.Tubular.NormalTotal.proj (ψ₁ p) = p.1 := by
    intro p
    show Work.Tubular.NormalTotal.proj (φ (hψ.symm p)) = p.1
    rw [hproj]
    have hh := hψproj (hψ.symm p)
    rw [hψ.apply_symm_apply] at hh
    exact hh.symm
  have hlen1 : ∀ p : Z₁.TotalSpace,
      Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (ψ₁ p) ≠ 0 := by
    intro p
    show Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ Work.Tubular.normalNorm E (φ (hψ.symm p)) ≠ 0
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    exact h3.trans (hlen (hψ.symm p))
  have hvec1 : ∀ x : V.pt, Work.Tubular.NormalTotal.vec (ψ₁ (Work.Thom.zeroSection Z₁ x)) = 0 := by
    intro x
    show Work.Tubular.NormalTotal.vec (φ (hψ.symm (Work.Thom.zeroSection Z₁ x))) = 0
    have hzz : hψ.symm (Work.Thom.zeroSection Z₁ x) = Work.Thom.zeroSection nu x := by
      rw [← hψ.injective.eq_iff, hψ.apply_symm_apply, hψzero]
    rw [hzz]
    exact hvec0 x
  obtain ⟨Ugen, hUgen_span, hUgen⟩ :=
    Work.ThomBordism.localDegreeSpan (V := V) (k := k) (E := E) hk1 Z₁ ψ₁ hproj1 hlen1 hvec1 hZ1
      q hU hR hbox g hg hg2
  -- the comparison isomorphism to ℤ
  have hspot : ∀ p : nu.TotalSpace, (p ∈ Work.Thom.zeroComplement nu) ↔
      (Work.Thom.fibreNorm nu p ≠ 0) := by
    intro p
    rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm, norm_ne_zero_iff]
  have hiff_φ : ∀ x : Work.Tubular.NormalTotal E,
      x ∈ Work.Tubular.normalNonzero E ↔ φ.symm x ∈ Work.Thom.zeroComplement nu := by
    intro x
    rw [Work.Tubular.mem_normalNonzero, hspot (φ.symm x), hlen (φ.symm x), φ.apply_symm_apply]
  have hmemψ' : ∀ p ∈ Work.Tubular.normalNonzero E, φ.symm p ∈ Work.Thom.zeroComplement nu :=
    fun p hp => (hiff_φ p).mp hp
  have hspot₁ : ∀ p : Z₁.TotalSpace, (p ∈ Work.Thom.zeroComplement Z₁) ↔
      (Work.Thom.fibreNorm Z₁ p ≠ 0) := by
    intro p
    have h1p : Work.Thom.fibreNorm Z₁ p = ‖(show Fin k → ℝ from p.2)‖ := rfl
    rw [Work.Thom.mem_zeroComplement, h1p, norm_ne_zero_iff]
  have hiff_ψ : ∀ p : nu.TotalSpace, p ∈ Work.Thom.zeroComplement nu ↔
      hψ p ∈ Work.Thom.zeroComplement Z₁ := by
    intro p
    rw [hspot p, hspot₁ (hψ p)]
    exact not_congr (hψnorm p).symm
  have hbij_ψ : Function.Bijective
      ((Work.Thom.relCohMap (↑hψ : C(nu.TotalSpace, Z₁.TotalSpace)) (Work.Thom.zeroComplement nu)
        (Work.Thom.zeroComplement Z₁) (fun p hp => (hiff_ψ p).mp hp) ℤ k).hom) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.zeroComplement nu)
      (Work.Thom.zeroComplement Z₁) hψ hiff_ψ ℤ k
  have hbij_φ : Function.Bijective
      ((Work.Thom.relCohMap (↑φ.symm : C(Work.Tubular.NormalTotal E, nu.TotalSpace))
        (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement nu) φ.symm hiff_φ ℤ k
  obtain ⟨eZ⟩ := Work.ThomBordism.openThomTopIso Z₁ (hk := hk1) hZ1
  let eM : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofBijective ((Work.Thom.relCohMap (↑φ.symm :
        C(Work.Tubular.NormalTotal E, nu.TotalSpace)) (Work.Tubular.normalNonzero E)
        (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom) hbij_φ).symm.trans
      ((LinearEquiv.ofBijective ((Work.Thom.relCohMap (↑hψ : C(nu.TotalSpace, Z₁.TotalSpace))
        (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement Z₁)
        (fun p hp => (hiff_ψ p).mp hp) ℤ k).hom) hbij_ψ).symm.trans eZ.toLinearEquiv)
  -- the generator property and the sign split
  have hspanP : Submodule.span ℤ
      ({Work.ThomBordism.gtdU E ND Gp hgmP} : Set (Work.Thom.RelCoh ℤ k
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤ :=
    Work.ThomBordism.gtdU_span_top hk1 E ND Gp hbpP hvecP hgmP
  have hUenP : Work.ThomBordism.gtdU E ND Gp hgmP = Ugen ∨
      Work.ThomBordism.gtdU E ND Gp hgmP = -Ugen :=
    Work.ThomBordism.eq_pm_of_span_eq_top_of_iso eM hspanP hUgen_span
  -- the orientation-flipped candidate
  obtain ⟨F, hFproj, hFeval, hFzero⟩ := Work.ThomBordism.Signs.flipMap k 10
  let Gm : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) := F.comp Gp
  have hbpM : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (Gm p)
      = Work.ThomBordism.Grassmann.ogFlip k 10 (Work.ThomBordism.Grassmann.padGaussFun E ND p.1) := by
    intro p
    change (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (F (Gp p)) = _
    rw [hFproj, hbpP]
  have hvecM : ∀ p, Work.ThomBordism.Grassmann.evalVec (Gm p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)) := by
    intro p
    change Work.ThomBordism.Grassmann.evalVec (F (Gp p)) = _
    rw [hFeval, hvecP]
  have hgmM : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      Gm p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10) := by
    intro p hp
    change F (Gp p) ∈ _
    exact hFzero (Gp p) (hgmP p hp)
  have hfibGm : ∀ y ∈ C.openTube,
      Work.PTGeometric.projOfPlane k 10
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
            (Gm (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y)))))
        = Work.PTGeometric.padEndEuc k 10 (by norm_num)
            (Work.PTGeometric.tubeNormalProj E C y) ∧
      Work.ThomBordism.Grassmann.evalVec
          (Gm (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))))
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) := by
    intro y hy
    have hp := hfibGp y hy
    refine ⟨?_, ?_⟩
    · rw [show (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
          (Gm (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))))
        = Work.ThomBordism.Grassmann.ogFlip k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
              (Gp (Work.Tubular.normalToBundle E ND
                (Work.Tubular.normalBlowUp E ε (C.inv y))))) from by
        rw [hbpM, hbpP]]
      rw [Work.ThomBordism.Grassmann.projOfPlane_ogFlip, hp.1]
    · rw [show Work.ThomBordism.Grassmann.evalVec
          (Gm (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))))
        = Work.ThomBordism.Grassmann.evalVec
            (Gp (Work.Tubular.normalToBundle E ND
              (Work.Tubular.normalBlowUp E ε (C.inv y)))) from by
        rw [hvecM, hvecP]]
      exact hp.2
  -- the flip negates the class
  have hflip : (Work.Thom.relCohMap Gm (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmM
        ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ
      = - ((Work.Thom.relCohMap Gp (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmP
        ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ) :=
    Work.ThomBordism.gtdThomClass_flipPairs (Work.Tubular.normalBundle E ND) hodd (by norm_num)
      gaussP Gp hbpP Gm hbpM (fun p => by rw [hvecM p, hvecP p]) hgmP hgmM
  have hUm : Work.ThomBordism.gtdU E ND Gm hgmM = - Work.ThomBordism.gtdU E ND Gp hgmP := by
    show (Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
        (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.ThomBordism.gtd_mem E ND) ℤ k).hom
        ((Work.Thom.relCohMap Gm (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmM
          ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ)
      = - ((Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
        (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.ThomBordism.gtd_mem E ND) ℤ k).hom
        ((Work.Thom.relCohMap Gp (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
          (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgmP
          ℤ k).hom (Work.ThomBordism.Grassmann.tautologicalThomClass k 10).τ))
    rw [hflip, map_neg]
  -- the orientation-flipped classifying isomorphism
  obtain ⟨eog⟩ := Work.ThomBordism.Grassmann.ogFlipComapIso k 10
  obtain ⟨e2M⟩ := Work.Thom.BundleIso_comap_exists
    (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (Work.ThomBordism.Grassmann.ogFlipCM k 10))
    (Work.ThomBordism.Grassmann.tautologicalBundle k 10) eog gaussP
  have hcompM : Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        ((Work.ThomBordism.Grassmann.ogFlipCM k 10).comp gaussP)
      = Work.Thom.bundleComap
          (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.ogFlipCM k 10)) gaussP :=
    (Work.Thom.bundleComap_comp (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (Work.ThomBordism.Grassmann.ogFlipCM k 10) gaussP).symm
  have eM' : Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        ((Work.ThomBordism.Grassmann.ogFlipCM k 10).comp gaussP))
      (Work.Tubular.normalBundle E ND) :=
    (Work.Thom.BundleIso.ofEq hcompM).trans (e2M.trans eP)
  -- the sign split
  rcases hUenP with hpos | hneg
  · have hld : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
            (Work.ThomBordism.gtdU E ND Gp hgmP)))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c := by
      intro x
      rw [hpos]
      exact hUgen x
    obtain ⟨J', hJ', rep', hrep', hfib'⟩ :=
      gcdCore hk hodd E ND N C q hU hR hbox g hg hg2 gaussP eP Gp hgmP hbpP
        Jloc hJloc hJlocinf hld hfibP
    refine ⟨ND, Gp, hgmP, hld, J', hJ', rep', hrep', hfib',
      ⟨1, Or.inl rfl, ?_, hvecP⟩⟩
    intro p
    rw [if_pos rfl]
    exact hbpP p
  · have hnegun : Work.ThomBordism.gtdU E ND Gp hgmP = -Ugen := hneg
    have hGmU : Work.ThomBordism.gtdU E ND Gm hgmM = Ugen := by
      rw [hUm, hnegun, neg_neg]
    obtain ⟨Jm, hJm, hJminf⟩ := Work.ThomBordism.onePointExtensionTaut E ND Gm hvecM
    have hfibJm : ∀ y ∈ C.openTube,
        ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
          (Jm.comp ↑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
              (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
          Work.PTGeometric.projOfPlane k 10
              ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p)
            = Work.PTGeometric.padEndEuc k 10 (by norm_num)
                (Work.PTGeometric.tubeNormalProj E C y) ∧
          Work.ThomBordism.Grassmann.evalVec p =
            Work.PTGeometric.padEuc k 10 (by norm_num)
              ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) := by
      intro y hy
      refine ⟨Gm (Work.Tubular.normalToBundle E ND (Work.Tubular.normalBlowUp E ε (C.inv y))),
        ?_, (hfibGm y hy).1, (hfibGm y hy).2⟩
      change Jm ((⇑(Homeomorph.onePointCongr (Work.Tubular.eucNormalHomeomorph E ND)).symm)
        (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))))
        = OnePoint.some (Gm (Work.Tubular.normalToBundle E ND
            (Work.Tubular.normalBlowUp E ε (C.inv y))))
      rw [Homeomorph.onePointCongr_symm_apply, OnePoint.map_some,
        gtdEucNormalHomeomorph_symm_apply E ND, hJm]
    have hld : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
            (Work.ThomBordism.gtdU E ND Gm hgmM)))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c := by
      intro x
      rw [hGmU]
      exact hUgen x
    obtain ⟨J', hJ', rep', hrep', hfib'⟩ :=
      gcdCore hk hodd E ND N C q hU hR hbox g hg hg2
        ((Work.ThomBordism.Grassmann.ogFlipCM k 10).comp gaussP) eM' Gm hgmM hbpM
        Jm hJm hJminf hld hfibJm
    refine ⟨ND, Gm, hgmM, hld, J', hJ', rep', hrep', hfib',
      ⟨-1, Or.inr rfl, ?_, hvecM⟩⟩
    intro p
    rw [if_neg (by norm_num : ¬ ((-1 : ℤ) = 1))]
    exact hbpM p

end

end Work.ThomBordism
