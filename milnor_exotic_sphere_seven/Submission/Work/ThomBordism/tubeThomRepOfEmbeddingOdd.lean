import Mathlib
import Submission.Work.ThomBordism.tubeConnForm
import Submission.Work.ThomBordism.tubeNumberStep
import Submission.Work.ThomBordism.tubeCastStep
import Submission.Work.ThomBordism.chainABridge
import Submission.Work.ThomBordism.absThomCompareUniversal
import Submission.Work.ThomBordism.absThomCompareNatural
import Submission.Work.ThomBordism.gaussClassifyingNDPad
import Submission.Work.ThomBordism.thomClassPullbackBundleComapRank
import Submission.Work.ThomBordism.normalWhitneyTorsion
import Submission.Work.ThomBordism.normLikeEuclideanNormal
import Submission.Work.ThomBordism.thomMapNaturalityBundleIso
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.Tubular.LocalDegreeAll
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.Interface
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.localDegreeSpan
import Submission.Work.ThomBordism.openThomTopIso
import Submission.Work.ThomBordism.thomPairTopHomologyIsoV2
import Submission.Work.Tubular.thomClass_span_top
import Submission.Work.ThomBordism.tubeCast
import Submission.Work.ThomBordism.thomClassNaturalityBundleIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom
open Work.Tubular

/-! ## The fibre reflection of the universal Thom space (local copy)

`Submission/Work/ThomBordism/thomReflect.lean` defines the same objects, but that module is under
construction by another agent and cannot be imported right now; the definitions below are
self-contained. -/

/-- **The fibrewise negation of a real bundle is a homeomorphism**: it is a continuous involution. -/
noncomputable def negMapHomeoOdd {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) : Z.TotalSpace ≃ₜ Z.TotalSpace where
  toFun := Grassmann.negMap Z
  invFun := Grassmann.negMap Z
  left_inv p := congrFun (congrArg DFunLike.coe (Grassmann.negMap_comp_negMap Z)) p
  right_inv p := congrFun (congrArg DFunLike.coe (Grassmann.negMap_comp_negMap Z)) p
  continuous_toFun := (Grassmann.negMap Z).continuous
  continuous_invFun := (Grassmann.negMap Z).continuous

/-- **The fibre reflection of the universal Thom space `Th γ_{k,m}`**: the one-point extension of
the fibrewise negation of the tautological bundle. -/
noncomputable def thomReflectOdd (k m : ℕ) :
    C(Grassmann.TautologicalThomSpace k m, Grassmann.TautologicalThomSpace k m) :=
  ⟨(Homeomorph.onePointCongr (negMapHomeoOdd (Grassmann.tautologicalBundle k m)) :
      OnePoint (Grassmann.tautologicalBundle k m).TotalSpace →
        OnePoint (Grassmann.tautologicalBundle k m).TotalSpace),
    (Homeomorph.onePointCongr (negMapHomeoOdd (Grassmann.tautologicalBundle k m))).continuous⟩

theorem thomReflectOdd_infty (k m : ℕ) :
    thomReflectOdd k m OnePoint.infty = OnePoint.infty := by
  show (Homeomorph.onePointCongr (negMapHomeoOdd (Grassmann.tautologicalBundle k m))) OnePoint.infty
    = OnePoint.infty
  rw [Homeomorph.onePointCongr_apply, OnePoint.map_infty]

theorem thomReflectOdd_some (k m : ℕ)
    (p : (Grassmann.tautologicalBundle k m).TotalSpace) :
    thomReflectOdd k m (OnePoint.some p)
      = OnePoint.some (Grassmann.negMap (Grassmann.tautologicalBundle k m) p) := by
  show (Homeomorph.onePointCongr (negMapHomeoOdd (Grassmann.tautologicalBundle k m)))
      (OnePoint.some p) = OnePoint.some (Grassmann.negMap (Grassmann.tautologicalBundle k m) p)
  rw [Homeomorph.onePointCongr_apply]
  rfl

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-! ## Degree-cast bookkeeping -/

theorem CohMap_castOdd {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {a b : ℕ} (h : a = b) (x : Work.Thom.Coh ℤ a Y) :
    (Work.Thom.CohMap f ℤ b).hom (h ▸ x) = h ▸ ((Work.Thom.CohMap f ℤ a).hom x) := by
  cases h; rfl

theorem relToAbs_castOdd {X : Type} [TopologicalSpace X] (A : Set X) {a b : ℕ} (h : a = b)
    (x : Work.Thom.RelCoh ℤ a X A) :
    (Work.Thom.relToAbs ℤ A b).hom (h ▸ x) = h ▸ ((Work.Thom.relToAbs ℤ A a).hom x) := by
  cases h; rfl

theorem relCohOfAbsZ_castOdd {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (N : NormLike Z) {a b : ℕ} (h : a = b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (x : Work.Thom.Coh ℤ a (OnePoint Z.TotalSpace)) :
    relCohOfAbsZ Z N hb (h ▸ x) = h ▸ (relCohOfAbsZ Z N ha x) := by
  apply (absNZRelToAbsBijective Z (absContractible Z N) hb).1
  rw [relToAbs_relCohOfAbsZ Z N hb (h ▸ x)]
  rw [show (Work.Thom.relToAbs ℤ (absNZ Z) b).hom (h ▸ (relCohOfAbsZ Z N ha x))
      = h ▸ ((Work.Thom.relToAbs ℤ (absNZ Z) a).hom (relCohOfAbsZ Z N ha x))
      from relToAbs_castOdd (absNZ Z) h _]
  rw [relToAbs_relCohOfAbsZ Z N ha x]

theorem relCoh_of_abs_eq_relCohOfAbsZ_odd {E : EmbeddingData V (8 + k)} {ι : Type}
    (Z : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι) (N : NormLike Z)
    (Ψ₁ : OnePoint Z.TotalSpace ≃ₜ OnePoint (NormalTotal E))
    (hmem : ∀ x ∈ Work.Tubular.onePointNonzero E, Ψ₁.symm x ∈ absNZ Z)
    (y : Work.Thom.Coh ℤ (k + 8) (OnePoint Z.TotalSpace)) :
    Work.Tubular.relCoh_of_abs E ((Work.Thom.CohMap Ψ₁.symm ℤ (k + 8)).hom y)
      = (Work.Thom.relCohMap Ψ₁.symm (Work.Tubular.onePointNonzero E) (absNZ Z) hmem ℤ (k + 8)).hom
          (relCohOfAbsZ Z N (show 2 ≤ k + 8 by omega) y) := by
  have hb := Work.Tubular.bijective_relToAbs_onePoint E (k + 6)
  rw [show k + 6 + 2 = k + 8 from by omega] at hb
  apply hb.1
  have hL : (Work.Thom.relToAbs ℤ (Work.Tubular.onePointNonzero E) (k + 8)).hom
      (Work.Tubular.relCoh_of_abs E ((Work.Thom.CohMap Ψ₁.symm ℤ (k + 8)).hom y))
      = (Work.Thom.CohMap Ψ₁.symm ℤ (k + 8)).hom y :=
    Work.Tubular.relToAbs_relCoh_of_abs E _
  have hnat := congrArg (fun (φ : Work.Thom.RelCoh ℤ (k + 8) (OnePoint Z.TotalSpace) (absNZ Z) ⟶
      Work.Thom.Coh ℤ (k + 8) (OnePoint (NormalTotal E))) => ModuleCat.Hom.hom φ)
    (Work.Thom.relCohMap_relToAbs (Ψ₁.symm) (Work.Tubular.onePointNonzero E) (absNZ Z) hmem ℤ (k + 8))
  simp only [ModuleCat.hom_comp] at hnat
  have hR : (Work.Thom.relToAbs ℤ (Work.Tubular.onePointNonzero E) (k + 8)).hom
      ((Work.Thom.relCohMap Ψ₁.symm (Work.Tubular.onePointNonzero E) (absNZ Z) hmem ℤ (k + 8)).hom
        (relCohOfAbsZ Z N (show 2 ≤ k + 8 by omega) y))
      = (Work.Thom.CohMap Ψ₁.symm ℤ (k + 8)).hom y := by
    have h := LinearMap.congr_fun hnat (relCohOfAbsZ Z N (show 2 ≤ k + 8 by omega) y)
    simp only [LinearMap.comp_apply] at h
    rw [relToAbs_relCohOfAbsZ Z N (show 2 ≤ k + 8 by omega) y] at h
    exact h
  rw [hL, hR]

/-! ## The universal class of the tautological bundle -/

abbrev uThomGen (k : ℕ) (x : Work.Thom.Coh ℤ 8 (Grassmann.OG k 10)) :
    Work.Thom.Coh ℤ (8 + k) (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) :=
  PhiZ (Grassmann.tautologicalBundle k 10) (tautNormLike k 10) (show 2 ≤ 8 + k by omega)
    (Work.Thom.thomMap (Grassmann.tautologicalBundle k 10) k
      (Grassmann.tautologicalThomClass k 10).τ 8 x)

abbrev uThomOdd (k : ℕ) :
    Work.Thom.Coh ℤ (8 + k) (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) :=
  uThomGen k (Grassmann.p1Sq k 10)

abbrev uThomOdd2 (k : ℕ) :
    Work.Thom.Coh ℤ (8 + k) (OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace) :=
  uThomGen k (Grassmann.p2 k 10)

/-- **The description of the ν-side class of the Pontryagin–Thom assembly.** -/
theorem nuClassDescriptionGen {E : EmbeddingData V (8 + k)}
    {ι : Type} (Z : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι)
    (Nν : NormLike Z)
    (ψ : Z.TotalSpace ≃ₜ NormalTotal E)
    (hmemψ : ∀ p ∈ Work.Tubular.normalNonzero E, ψ.symm p ∈ Work.Thom.zeroComplement Z)
    {gauss : C(V.pt, Grassmann.OG k 10)}
    (gF : C(Z.TotalSpace, (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbproj : ∀ p : Z.TotalSpace,
      Work.Thom.bundleProj (Grassmann.tautologicalBundle k 10) (gF p)
        = gauss (Work.Thom.bundleProj Z p))
    (hg : ∀ p ∈ Work.Thom.zeroComplement Z,
      gF p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10))
    (J₀ : C(OnePoint Z.TotalSpace, OnePoint (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hJ₀ : ∀ p : Z.TotalSpace, J₀ (OnePoint.some p) = OnePoint.some (gF p))
    (hJ₀inf : J₀ OnePoint.infty = OnePoint.infty)
    (x : Work.Thom.Coh ℤ 8 (Grassmann.OG k 10)) :
    Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
        (Work.Thom.CohMap (J₀.comp (Homeomorph.onePointCongr ψ).symm) ℤ (8 + k)).hom
          (uThomGen k x)))
      = (Nat.add_comm 8 k) ▸
        (Work.Thom.relCohMap (ψ.symm : C(NormalTotal E, Z.TotalSpace)) (Work.Tubular.normalNonzero E)
          (Work.Thom.zeroComplement Z) hmemψ ℤ (8 + k)).hom
          (Work.Thom.mixedCupC ℤ (Work.Thom.zeroComplement Z) 8 k
            ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ 8).hom
              ((Work.Thom.CohMap gauss ℤ 8).hom x))
            ((Work.Thom.relCohMap gF (Work.Thom.zeroComplement Z)
              (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hg
              ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ)) := by
  have hm : ∀ x ∈ Work.Tubular.onePointNonzero E,
      (Homeomorph.onePointCongr ψ).symm x ∈ absNZ Z := by
    intro x hx
    rcases Work.Tubular.mem_onePointNonzero.mp hx with rfl | ⟨q, hq, rfl⟩
    · show OnePoint.map ψ.symm OnePoint.infty ∈ absNZ Z
      rw [OnePoint.map_infty]
      exact Or.inr rfl
    · show OnePoint.map ψ.symm (OnePoint.some q) ∈ absNZ Z
      rw [OnePoint.map_some]
      exact Or.inl ⟨ψ.symm q, hmemψ q hq, rfl⟩
  have hCoh : (Work.Thom.CohMap (J₀.comp (Homeomorph.onePointCongr ψ).symm) ℤ (8 + k)).hom
        (uThomGen k x)
      = (Work.Thom.CohMap ((Homeomorph.onePointCongr ψ).symm :
          C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace)) ℤ (8 + k)).hom
        ((Work.Thom.CohMap J₀ ℤ (8 + k)).hom (uThomGen k x)) := by
    rw [Work.Thom.CohMap_comp ((Homeomorph.onePointCongr ψ).symm :
      C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace)) J₀ ℤ (8 + k)]
    rfl
  rw [hCoh]
  rw [← CohMap_castOdd ((Homeomorph.onePointCongr ψ).symm :
    C(OnePoint (NormalTotal E), OnePoint Z.TotalSpace)) (Nat.add_comm 8 k)
    ((Work.Thom.CohMap J₀ ℤ (8 + k)).hom (uThomGen k x))]
  rw [relCoh_of_abs_eq_relCohOfAbsZ_odd Z Nν (Homeomorph.onePointCongr ψ) hm]
  rw [Work.ThomBordism.compPull_compPullZ_absNZ (E := E) Z Nν ψ hmemψ (Homeomorph.onePointCongr ψ)
    (fun p => OnePoint.map_some ψ p) hm (k + 8)]
  rw [relCohOfAbsZ_castOdd Z Nν (Nat.add_comm 8 k) (by omega) (by omega)]
  rw [Work.ThomBordism.compPullZ_cast Nν (Nat.add_comm 8 k)]
  rw [Work.Thom.relCohMap_cast (ψ.symm : C(NormalTotal E, Z.TotalSpace))
    (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement Z) hmemψ (Nat.add_comm 8 k)]
  rw [Work.ThomBordism.universalClassPullbackPair (Grassmann.tautologicalBundle k 10) Z
    gauss gF hg hbproj (tautNormLike k 10) Nν J₀ hJ₀ hJ₀inf k
    (Grassmann.tautologicalThomClass k 10).τ x]

theorem span_cast_singleton_eq_top_invOdd {M : ℕ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module ℤ (M n)] {a b : ℕ} (h : a = b) (x : M a)
    (hx : Submodule.span ℤ ({(h ▸ x)} : Set (M b)) = ⊤) :
    Submodule.span ℤ ({x} : Set (M a)) = ⊤ := by
  have h2 := Work.Tubular.span_cast_singleton_eq_top (M := M) (b := a) h.symm (x := h ▸ x) hx
  rwa [show h.symm ▸ (h ▸ x) = x from by cases h; rfl] at h2

/-- **The two ν-side pairing identities of the Pontryagin–Thom assembly, per member.** -/
theorem nuPairingExistsOdd {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hkodd : Odd k) (E : EmbeddingData V (8 + k)) (N : NormalBundlData V)
    {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε) (hU : IsCompact C.U) {R : ℝ}
    (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y))) :
    ∃ (J : C(OnePoint (NormalTotal E),
        (connTarget k (by omega) (PhiG k (by omega))).T))
      (hJ : J OnePoint.infty = (connTarget k (by omega) (PhiG k (by omega))).t₀),
      (relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸
              (connTarget k (by omega) (PhiG k (by omega))).p1sqU)))))
          (collapseRelK8 C g hg hR hbox) = N.normalP1Sq) ∧
      (relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸
              (connTarget k (by omega) (PhiG k (by omega))).p2U)))))
          (collapseRelK8 C g hg hR hbox) = N.normalP2) := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hn : 2 ≤ 8 + k := by omega
  have hk10 : 10 ≤ k := by omega
  -- ================= geometric data =================
  obtain ⟨ND⟩ := exists_normalData_of_immersion E.e (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨gauss, ⟨e⟩⟩ := gaussClassifyingNDPad E hk1 ND
  let γ : Work.TangentClasses.RealBundle (Grassmann.OG k 10) (Grassmann.Amb k)
      (Grassmann.ChartIdx k 10) := Grassmann.tautologicalBundle k 10
  let Zb := Work.Thom.bundleComap γ gauss
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) (CoverIdx V k) :=
    Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  have hEucl : Work.Thom.IsEuclidean nu := Work.Tubular.isEuclidean_normalBundle E ND
  let NZnu : NormLike nu := Classical.choice (nonempty_normLike_of_isEuclidean nu hEucl)
  let NZg : NormLike γ := tautNormLike k 10
  have hproj : ∀ p : nu.TotalSpace, NormalTotal.proj (φ p) = p.1 := fun p => rfl
  have hlen : ∀ p : nu.TotalSpace,
      Work.Thom.fibreNorm nu p ≠ 0 ↔ normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  have hvec : ∀ x : V.pt, NormalTotal.vec (φ (Work.Thom.zeroSection nu x)) = 0 := by
    intro x
    show Work.Tubular.insCLM E ND ((Work.Tubular.normalBundle E ND).indexAt x) x (0 : Work.Tubular.Euc k) = 0
    exact map_zero _
  -- ================= the Thom class of the classifying bundle =================
  obtain ⟨ψc, hψcp, hψcs, hfc, Tc, hTc⟩ := thomClassPullbackBundleComapRank γ gauss (Grassmann.tautologicalThomClass k 10)
    (n := k) (Grassmann.tautological_rank k 10).symm
  have hfe : ∀ x ∈ Work.Thom.zeroComplement nu, e.invTotalSpace x ∈ Work.Thom.zeroComplement Zb := by
    intro x hx
    rw [Work.Thom.mem_zeroComplement] at hx ⊢
    show e.inv x.1 x.2 ≠ 0
    intro h0
    have hE1 : e.inv x.1 x.2 = 0 := h0
    have h2 : (show Work.Tubular.Euc k from x.2) = 0 := by
      rw [← e.toTotalSpace_right_inv x]
      show e.hom x.1 (e.inv x.1 (x.2)) = 0
      rw [hE1, map_zero]
    exact hx h2
  obtain ⟨Th, hTh⟩ := thomClassNaturalityBundleIso Zb nu e Tc hfe
  have hZ : Nonempty (Work.Thom.ThomClass nu k) := ⟨Th⟩
  -- ================= the local degree =================
  obtain ⟨eL⟩ : Nonempty (Work.Tubular.Euc k ≃L[ℝ] (Fin k → ℝ)) :=
    ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩
  let Z₁ : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) (CoverIdx V k) :=
    Work.TangentClasses.RealBundle.mapFibre eL nu
  obtain ⟨hψ, hψproj, hψnorm, hψzero⟩ := Work.Tubular.totalSpace_mapFibre_homeo eL nu
  let ψ₁ : Z₁.TotalSpace ≃ₜ NormalTotal E := hψ.symm.trans φ
  have hZ1 : Nonempty (Work.Thom.ThomClass Z₁ k) :=
    Work.Tubular.nonempty_thomClass_of_bundleIso (Work.Tubular.bundleIsoMapFibre eL nu) Th
  have hproj1 : ∀ p : Z₁.TotalSpace, NormalTotal.proj (ψ₁ p) = p.1 := by
    intro p
    show NormalTotal.proj (φ (hψ.symm p)) = p.1
    rw [hproj]
    have hh := hψproj (hψ.symm p)
    rw [hψ.apply_symm_apply] at hh
    exact hh.symm
  have hlen1 : ∀ p : Z₁.TotalSpace,
      Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ normalNorm E (ψ₁ p) ≠ 0 := by
    intro p
    show Work.Thom.fibreNorm Z₁ p ≠ 0 ↔ normalNorm E (φ (hψ.symm p)) ≠ 0
    have h3 : (Work.Thom.fibreNorm Z₁ p ≠ 0) ↔ (Work.Thom.fibreNorm nu (hψ.symm p) ≠ 0) := by
      have h4 := hψnorm (hψ.symm p)
      rw [hψ.apply_symm_apply] at h4
      exact not_congr h4
    exact h3.trans (hlen (hψ.symm p))
  have hvec1 : ∀ x : V.pt, NormalTotal.vec (ψ₁ (Work.Thom.zeroSection Z₁ x)) = 0 := by
    intro x
    show NormalTotal.vec (φ (hψ.symm (Work.Thom.zeroSection Z₁ x))) = 0
    have hzz : hψ.symm (Work.Thom.zeroSection Z₁ x) = Work.Thom.zeroSection nu x := by
      rw [← hψ.injective.eq_iff, hψ.apply_symm_apply, hψzero]
    rw [hzz]
    exact hvec x
  obtain ⟨Ugen, hUgen_span, hUgen⟩ :=
    localDegreeSpan (V := V) (k := k) (E := E) hk1 Z₁ ψ₁ hproj1 hlen1 hvec1 hZ1
      q hU hR hbox g hg hg2
  -- ================= the classifying one-point map =================
  let Ψc : C(OnePoint (NormalTotal E), OnePoint nu.TotalSpace) :=
    ↑((Homeomorph.onePointCongr φ).symm)
  let g' : C(OnePoint nu.TotalSpace, OnePoint γ.TotalSpace) := Work.Tubular.gaussThomMap γ nu gauss e
  let j₀ : C(nu.TotalSpace, γ.TotalSpace) :=
    (Work.Thom.totalMap γ gauss).comp ⟨e.invTotalSpace, e.continuous_inv⟩
  have hg'some : ∀ p : nu.TotalSpace, g' (OnePoint.some p) = OnePoint.some (j₀ p) := by
    intro p
    show Work.Tubular.gaussThomMap γ nu gauss e (OnePoint.some p) = _
    rw [Work.Tubular.gaussThomMap]
    show OnePoint.map (Work.Thom.totalMap γ gauss)
      (((Homeomorph.onePointCongr e.toHomeomorph).symm) (OnePoint.some p)) = _
    change OnePoint.map (Work.Thom.totalMap γ gauss)
      (OnePoint.some (e.invTotalSpace p)) = _
    rw [OnePoint.map_some]
    rfl
  have hg'inf : g' OnePoint.infty = OnePoint.infty :=
    Work.Tubular.gaussThomMap_infty γ nu gauss e
  -- ================= membership side conditions =================
  have hspot : ∀ p : nu.TotalSpace, (p ∈ Work.Thom.zeroComplement nu) ↔
      (Work.Thom.fibreNorm nu p ≠ 0) := by
    intro p
    rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm, norm_ne_zero_iff]
  have hiff_φ : ∀ x : NormalTotal E,
      x ∈ normalNonzero E ↔ φ.symm x ∈ Work.Thom.zeroComplement nu := by
    intro x
    rw [Work.Tubular.mem_normalNonzero, hspot (φ.symm x), hlen (φ.symm x), φ.apply_symm_apply]
  have hmemψ' : ∀ p ∈ normalNonzero E, φ.symm p ∈ Work.Thom.zeroComplement nu :=
    fun p hp => (hiff_φ p).mp hp
  have hmemΨ : ∀ x ∈ onePointNonzero E, ((Homeomorph.onePointCongr φ).symm) x ∈ absNZ nu := by
    intro x hx
    rcases mem_onePointNonzero.mp hx with rfl | ⟨p, hp, rfl⟩
    · show OnePoint.map φ.symm OnePoint.infty ∈ absNZ nu
      rw [OnePoint.map_infty]
      exact Or.inr rfl
    · show OnePoint.map φ.symm (OnePoint.some p) ∈ absNZ nu
      rw [OnePoint.map_some]
      exact Or.inl ⟨φ.symm p, hmemψ' p hp, rfl⟩
  have hgmem : ∀ p ∈ Work.Thom.zeroComplement nu, j₀ p ∈ Work.Thom.zeroComplement γ := by
    intro p hp
    exact Work.Thom.totalMap_mem_zeroComplement γ gauss _ (hfe p hp)
  have hbproj : ∀ p : nu.TotalSpace,
      Work.Thom.bundleProj γ (j₀ p) = gauss (Work.Thom.bundleProj nu p) := fun p => rfl
  -- ================= the honest class is a generator =================
  have hψct : ψc = Work.Thom.totalMap γ gauss := by
    apply ContinuousMap.ext
    intro p
    refine Bundle.TotalSpace.ext ?_ ?_
    · exact hψcp p
    · exact heq_of_eq (hψcs p)
  have hff : ψc.comp (↑(e.toHomeomorph.symm) : C(nu.TotalSpace, Zb.TotalSpace)) = j₀ := by
    rw [hψct]
    apply ContinuousMap.ext
    intro p
    rfl
  have hUh : Th.τ = (Work.Thom.relCohMap j₀ (Work.Thom.zeroComplement nu)
      (Work.Thom.zeroComplement γ) hgmem ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ := by
    rw [hTh, hTc]
    change (ModuleCat.Hom.hom ((Work.Thom.relCohMap ψc (Work.Thom.zeroComplement Zb)
        (Work.Thom.zeroComplement γ) hfc ℤ k) ≫
      (Work.Thom.relCohMap (↑(e.toHomeomorph.symm)) (Work.Thom.zeroComplement nu)
        (Work.Thom.zeroComplement Zb) hfe ℤ k))) (Grassmann.tautologicalThomClass k 10).τ
      = (Work.Thom.relCohMap j₀ (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
          hgmem ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ
    rw [Work.Thom.relCohMap_compA (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement Zb)
      (Work.Thom.zeroComplement γ) (↑(e.toHomeomorph.symm)) ψc hfe hfc
      (fun x hx => hfc ((e.toHomeomorph.symm : C(nu.TotalSpace, Zb.TotalSpace)) x) (hfe x hx)) ℤ k]
    exact congrArg (fun (φ' : Work.Thom.RelCoh ℤ k γ.TotalSpace
        (Work.Thom.zeroComplement γ) ⟶
        Work.Thom.RelCoh ℤ k (TopCat.of nu.TotalSpace) (Work.Thom.zeroComplement nu)) =>
        (ModuleCat.Hom.hom φ') (Grassmann.tautologicalThomClass k 10).τ)
      (Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
        hff _ hgmem ℤ k)
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  have hsurj_e : Function.Surjective
      ((Work.Thom.relCohMap (↑(e.toHomeomorph.symm)) (Work.Thom.zeroComplement nu)
        (Work.Thom.zeroComplement Zb) hfe ℤ k).hom) := by
    have hiff_e : ∀ x : nu.TotalSpace, x ∈ Work.Thom.zeroComplement nu ↔
        (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement Zb := by
      intro x
      constructor
      · intro hx
        exact e.symm.hom_ne_zero hx
      · intro hx
        have h2 : e.toHomeomorph (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement nu :=
          e.hom_ne_zero hx
        rwa [e.toHomeomorph.apply_symm_apply] at h2
    exact (Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.zeroComplement nu)
      (Work.Thom.zeroComplement Zb) e.toHomeomorph.symm hiff_e ℤ k).2
  have hspan_Tc : Submodule.span ℤ ({Tc.τ} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of Zb.TotalSpace) (Work.Thom.zeroComplement Zb))) = ⊤ :=
    span_cast_singleton_eq_top_invOdd
      (M := fun n => Work.Thom.RelCoh ℤ n (TopCat.of Zb.TotalSpace) (Work.Thom.zeroComplement Zb))
      (Nat.zero_add k).symm Tc.τ (Work.Tubular.thomClass_span_top Zb k Tc)
  have hspan_Th : Submodule.span ℤ ({Th.τ} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of nu.TotalSpace) (Work.Thom.zeroComplement nu))) = ⊤ := by
    rw [hTh]
    exact span_singleton_map_eq_top _ hsurj_e hspan_Tc
  have hbij_φ : Function.Bijective
      ((Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) (normalNonzero E)
        (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (normalNonzero E) (Work.Thom.zeroComplement nu)
      φ.symm hiff_φ ℤ k
  let Uh : Work.Thom.RelCoh ℤ k (TopCat.of nu.TotalSpace) (Work.Thom.zeroComplement nu) :=
    (Work.Thom.relCohMap j₀ (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
      hgmem ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ
  have hspan_Uh : Submodule.span ℤ ({Uh} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of nu.TotalSpace) (Work.Thom.zeroComplement nu))) = ⊤ := by
    rw [show Uh = Th.τ from hUh.symm]
    exact hspan_Th
  let Uen₀ : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) :=
    (Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) (normalNonzero E)
      (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom Uh
  have hspan_Uen₀ : Submodule.span ℤ ({Uen₀} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E))) = ⊤ := by
    show Submodule.span ℤ ({((Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      (normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom Uh)} : Set _) = ⊤
    exact span_singleton_map_eq_top _ hbij_φ.2 hspan_Uh
  obtain ⟨eZ⟩ := Work.ThomBordism.openThomTopIso Z₁ (hk := hk1) hZ1
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
  let eM : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofBijective ((Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      (normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom) hbij_φ).symm.trans
      ((LinearEquiv.ofBijective ((Work.Thom.relCohMap (↑hψ : C(nu.TotalSpace, Z₁.TotalSpace))
        (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement Z₁)
        (fun p hp => (hiff_ψ p).mp hp) ℤ k).hom) hbij_ψ).symm.trans
      eZ.toLinearEquiv)
  have hUen₀_pm : Uen₀ = Ugen ∨ Uen₀ = -Ugen :=
    eq_pm_of_span_eq_top_of_iso eM hspan_Uen₀ hUgen_span
  -- ================= the two ν-side classes and the numbers =================
  let y1 : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E)) :=
    (Work.Thom.CohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) ℤ 8).hom
      ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))
  let y2 : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E)) :=
    (Work.Thom.CohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) ℤ 8).hom
      ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))
  have hnum1 : (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom y1
      = (Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10) := by
    show (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) ℤ 8).hom
        ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
          ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))) = _
    rw [Work.Thom.CohMap_comp_apply (zeroSectionNormal E) (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      ℤ 8 ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))]
    rw [Work.Thom.CohMap_comp_apply
      ((↑φ.symm : C(NormalTotal E, nu.TotalSpace)).comp (zeroSectionNormal E))
      (Work.Thom.bundleProj nu) ℤ 8 ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10))]
    have hz : (Work.Thom.bundleProj nu).comp
        ((↑φ.symm : C(NormalTotal E, nu.TotalSpace)).comp (zeroSectionNormal E))
        = ContinuousMap.id V.pt := by
      ext x
      show (φ.symm (zeroSectionNormal E x)).1 = x
      rw [← hproj (φ.symm (zeroSectionNormal E x)), φ.apply_symm_apply]
      rfl
    rw [hz, Work.Thom.CohMap_id, ModuleCat.hom_id]
    rfl
  have hnum2 : (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom y2
      = (Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10) := by
    show (Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) ℤ 8).hom
        ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
          ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))) = _
    rw [Work.Thom.CohMap_comp_apply (zeroSectionNormal E) (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      ℤ 8 ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))]
    rw [Work.Thom.CohMap_comp_apply
      ((↑φ.symm : C(NormalTotal E, nu.TotalSpace)).comp (zeroSectionNormal E))
      (Work.Thom.bundleProj nu) ℤ 8 ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10))]
    have hz : (Work.Thom.bundleProj nu).comp
        ((↑φ.symm : C(NormalTotal E, nu.TotalSpace)).comp (zeroSectionNormal E))
        = ContinuousMap.id V.pt := by
      ext x
      show (φ.symm (zeroSectionNormal E x)).1 = x
      rw [← hproj (φ.symm (zeroSectionNormal E x)), φ.apply_symm_apply]
      rfl
    rw [hz, Work.Thom.CohMap_id, ModuleCat.hom_id]
    rfl

  -- ================= the class-description chains =================
  have chain1 : ∀ (jj : C(nu.TotalSpace, γ.TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement nu, jj p ∈ Work.Thom.zeroComplement γ)
      (hbp : ∀ p : nu.TotalSpace, Work.Thom.bundleProj γ (jj p) = gauss (Work.Thom.bundleProj nu p))
      (J₀ : C(OnePoint nu.TotalSpace, OnePoint γ.TotalSpace))
      (hJ₀ : ∀ p : nu.TotalSpace, J₀ (OnePoint.some p) = OnePoint.some (jj p))
      (hJ₀inf : J₀ OnePoint.infty = OnePoint.infty),
      relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          (Work.Thom.CohMap (J₀.comp ↑((Homeomorph.onePointCongr φ).symm)) ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸
            (connTarget k hk10 (PhiG k hn)).p1sqU))))
        (collapseRelK8 C g hg hR hbox)
      = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k y1
            ((Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) (normalNonzero E)
              (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom
              ((Work.Thom.relCohMap jj (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
                hgm ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ))))
          (collapseRelK8 C g hg hR hbox) := by
    intro jj hgm hbp J₀ hJ₀ hJ₀inf
    have hA : (Nat.add_comm 8 k).symm ▸ (connTarget k hk10 (PhiG k hn)).p1sqU = uThomGen k (Grassmann.p1Sq k 10) := by
      rw [show (connTarget k hk10 (PhiG k hn)).p1sqU
        = PhiG k hn (Work.Thom.thomMap γ k (Grassmann.tautologicalThomClass k 10).τ 8 (Grassmann.p1Sq k 10)) from rfl]
      exact PhiG_cast_symm k hn _
    rw [hA]
    rw [nuClassDescriptionGen (E := E) (gauss := gauss) nu NZnu φ hmemψ' jj hbp hgm J₀ hJ₀ hJ₀inf
      (Grassmann.p1Sq k 10)]
    rw [Work.Thom.mixedCupC_pairNatural (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      (normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' 8 k
      ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))
      ((Work.Thom.relCohMap jj (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
        hgm ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ)]
    rw [← Work.Tubular.mixedCup_topCatOf_eq_mixedCupC]
  have chain2 : ∀ (jj : C(nu.TotalSpace, γ.TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement nu, jj p ∈ Work.Thom.zeroComplement γ)
      (hbp : ∀ p : nu.TotalSpace, Work.Thom.bundleProj γ (jj p) = gauss (Work.Thom.bundleProj nu p))
      (J₀ : C(OnePoint nu.TotalSpace, OnePoint γ.TotalSpace))
      (hJ₀ : ∀ p : nu.TotalSpace, J₀ (OnePoint.some p) = OnePoint.some (jj p))
      (hJ₀inf : J₀ OnePoint.infty = OnePoint.infty),
      relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          (Work.Thom.CohMap (J₀.comp ↑((Homeomorph.onePointCongr φ).symm)) ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸
            (connTarget k hk10 (PhiG k hn)).p2U))))
        (collapseRelK8 C g hg hR hbox)
      = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k y2
            ((Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace)) (normalNonzero E)
              (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom
              ((Work.Thom.relCohMap jj (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
                hgm ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ))))
          (collapseRelK8 C g hg hR hbox) := by
    intro jj hgm hbp J₀ hJ₀ hJ₀inf
    have hA : (Nat.add_comm 8 k).symm ▸ (connTarget k hk10 (PhiG k hn)).p2U = uThomGen k (Grassmann.p2 k 10) := by
      rw [show (connTarget k hk10 (PhiG k hn)).p2U
        = PhiG k hn (Work.Thom.thomMap γ k (Grassmann.tautologicalThomClass k 10).τ 8 (Grassmann.p2 k 10)) from rfl]
      exact PhiG_cast_symm k hn _
    rw [hA]
    rw [nuClassDescriptionGen (E := E) (gauss := gauss) nu NZnu φ hmemψ' jj hbp hgm J₀ hJ₀ hJ₀inf
      (Grassmann.p2 k 10)]
    rw [Work.Thom.mixedCupC_pairNatural (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
      (normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' 8 k
      ((Work.Thom.CohMap (Work.Thom.bundleProj nu) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))
      ((Work.Thom.relCohMap jj (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
        hgm ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ)]
    rw [← Work.Tubular.mixedCup_topCatOf_eq_mixedCupC]
  -- ================= the evaluation of a pairing =================
  have eval1 : ∀ Uen : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E),
      Uen = Ugen →
      relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k y1 Uen))
        (collapseRelK8 C g hg hR hbox) = N.normalP1Sq := by
    intro Uen hU
    rw [hU, hUgen y1, hnum1]
    exact gauss_p1Sq_pairing E ND gauss e N
  have eval2 : ∀ Uen : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E),
      Uen = Ugen →
      relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k y2 Uen))
        (collapseRelK8 C g hg hR hbox) = N.normalP2 := by
    intro Uen hU
    rw [hU, hUgen y2, hnum2]
    exact gauss_p2_pairing E ND gauss e N
  -- ================= the reflection data =================
  have hPsiSinf : Ψc OnePoint.infty = OnePoint.infty := by
    show (↑((Homeomorph.onePointCongr φ).symm) :
      C(OnePoint (NormalTotal E), OnePoint nu.TotalSpace)) OnePoint.infty = OnePoint.infty
    rw [show (↑((Homeomorph.onePointCongr φ).symm) :
        C(OnePoint (NormalTotal E), OnePoint nu.TotalSpace)) OnePoint.infty
        = OnePoint.map (φ.symm : NormalTotal E → nu.TotalSpace) OnePoint.infty from rfl,
      OnePoint.map_infty]
  have hmem₁ : ∀ p ∈ Work.Thom.zeroComplement nu,
      (Grassmann.negMap γ) (j₀ p) ∈ Work.Thom.zeroComplement γ :=
    fun p hp => Grassmann.negMap_mem γ (j₀ p) (hgmem p hp)
  have hbp₁ : ∀ p : nu.TotalSpace,
      Work.Thom.bundleProj γ ((Grassmann.negMap γ) (j₀ p)) = gauss (Work.Thom.bundleProj nu p) :=
    fun p => hbproj p
  have hJ₁some : ∀ p : nu.TotalSpace,
      ((thomReflectOdd k 10).comp g') (OnePoint.some p)
        = OnePoint.some ((Grassmann.negMap γ) (j₀ p)) := by
    intro p
    rw [ContinuousMap.comp_apply, hg'some p, thomReflectOdd_some]
  have hJ₁inf : ((thomReflectOdd k 10).comp g') OnePoint.infty = OnePoint.infty := by
    rw [ContinuousMap.comp_apply, hg'inf, thomReflectOdd_infty]
  have hUν₁ : (Work.Thom.relCohMap ((Grassmann.negMap γ).comp j₀) (Work.Thom.zeroComplement nu)
        (Work.Thom.zeroComplement γ) hmem₁ ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ
      = - ((Work.Thom.relCohMap j₀ (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
          hgmem ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ) := by
    rw [← Work.Thom.relCohMap_compA (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
      (Work.Thom.zeroComplement γ) j₀ (Grassmann.negMap γ) hgmem (Grassmann.negMap_mem γ)
      hmem₁ ℤ k]
    change (Work.Thom.relCohMap j₀ (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement γ)
      hgmem ℤ k).hom ((Work.Thom.relCohMap (Grassmann.negMap γ) (Work.Thom.zeroComplement γ)
      (Work.Thom.zeroComplement γ) (Grassmann.negMap_mem γ) ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ) = _
    rw [Grassmann.tautological_negMap_thomClass k 10 hkodd]
    exact map_neg _ _
  -- ================= the sign split =================
  rcases hUen₀_pm with hpos | hneg
  · refine ⟨g'.comp ↑((Homeomorph.onePointCongr φ).symm), ?_, ?_, ?_⟩
    · show (g'.comp Ψc) OnePoint.infty = OnePoint.infty
      rw [ContinuousMap.comp_apply, hPsiSinf]
      exact hg'inf
    · have hc1 := chain1 j₀ hgmem hbproj g' hg'some hg'inf
      exact hc1.trans (eval1 _ hpos)
    · have hc2 := chain2 j₀ hgmem hbproj g' hg'some hg'inf
      exact hc2.trans (eval2 _ hpos)
  · have hUen₁ : (Work.Thom.relCohMap (↑φ.symm : C(NormalTotal E, nu.TotalSpace))
        (normalNonzero E) (Work.Thom.zeroComplement nu) hmemψ' ℤ k).hom
        ((Work.Thom.relCohMap ((Grassmann.negMap γ).comp j₀) (Work.Thom.zeroComplement nu)
          (Work.Thom.zeroComplement γ) hmem₁ ℤ k).hom (Grassmann.tautologicalThomClass k 10).τ) = Ugen := by
      rw [hUν₁, map_neg]
      show -Uen₀ = Ugen
      rw [hneg, neg_neg]
    refine ⟨(thomReflectOdd k 10).comp (g'.comp ↑((Homeomorph.onePointCongr φ).symm)), ?_, ?_, ?_⟩
    · show ((thomReflectOdd k 10).comp (g'.comp Ψc)) OnePoint.infty = OnePoint.infty
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hPsiSinf, hg'inf]
      exact thomReflectOdd_infty k 10
    · have hd1 := chain1 ((Grassmann.negMap γ).comp j₀) hmem₁ hbp₁ ((thomReflectOdd k 10).comp g')
        hJ₁some hJ₁inf
      exact hd1.trans (eval1 _ hUen₁)
    · have hd2 := chain2 ((Grassmann.negMap γ).comp j₀) hmem₁ hbp₁ ((thomReflectOdd k 10).comp g')
        hJ₁some hJ₁inf
      exact hd2.trans (eval2 _ hUen₁)


/-- **The per-member Pontryagin–Thom assembly at an odd codimension `k ≥ 11`.** -/
theorem tubeThomRepOfEmbeddingOdd (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hkodd : Odd k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V) :
    Nonempty (Work.Tubular.TubeThomRep k
      (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N) := by
  classical
  haveI : Nonempty V.pt := inferInstance
  obtain ⟨ε, hε, ⟨C⟩⟩ := Work.Tubular.hasTubularNeighbourhood E
  haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  obtain ⟨q⟩ := Work.Tubular.nonempty_normalSphSub E hε (by omega : 8 < 8 + k)
  have hU : IsCompact C.U := C.isCompact_U
  obtain ⟨g, hg2, hg, -⟩ := Work.Tubular.collapseToOnePoint E C q hU
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  obtain ⟨J, hJ, hpair1, hpair2⟩ :=
    nuPairingExistsOdd (V := V) hk hkodd E N C q hU hR.le hbox g hg hg2
  exact Work.Tubular.tubeThomRep_of_nuPairing E C hR.le hbox J hJ g hg hpair1 hpair2

end

end Work.ThomBordism
