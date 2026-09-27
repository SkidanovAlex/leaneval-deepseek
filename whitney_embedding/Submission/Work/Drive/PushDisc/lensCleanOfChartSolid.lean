import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.exists_cleanLens
import Submission.Work.Drive.PushDisc.range_mfderiv_eq_sheetASub_of_flat
import Submission.Work.Drive.PushDisc.regularDiscDefs
import Submission.Work.Drive.PushDisc.asymSignTransport
import Submission.Work.Drive.PushDisc.lensTangentRows
import Submission.Work.Drive.PushDisc.lensFingerBRows
import Submission.Work.Drive.PushDisc.compRangeSupEqTop
import Submission.Work.Drive.PushDisc.archSmulDerivCorners

set_option maxHeartbeats 2000000

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold
open Set

/-! ## Helpers for `lensCleanOfChartSolid` -/

/-- In a finite-dimensional real vector space, two subspaces that span everything and whose
dimensions add up to the dimension of the ambient space intersect trivially. -/
theorem inf_eq_bot_of_finrank_add {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    {P Q : Submodule ℝ E} (hsup : P ⊔ Q = ⊤)
    (hfin : Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q = Module.finrank ℝ E) : P ⊓ Q = ⊥ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hsup, finrank_top] at h
  exact Submodule.finrank_eq_zero.mp (by linarith)

/-- **The corner algebra of the lens.**  If `b ∈ Q`, `b ≠ 0` and `sheetASub k ⊓ Q = ⊥`, then for
`g = c • (eₓ - b)` (`c ≠ 0`) the pair `(g, eₓ)` is independent, `g` is off the sheet plane and off
`Q`.  This is the content of the two corner rows (`x = ±1`) of the lens disc. -/
theorem corner_algebra {k : ℕ} {Q : Submodule ℝ (Work.Drive.Whitney.Mdl k)}
    (hPQ : sheetASub k ⊓ Q = ⊥) {b g : Work.Drive.Whitney.Mdl k} (hbQ : b ∈ Q) (hb0 : b ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (hg : g = c • (((1 : ℝ), 0, 0, 0) - b)) :
    LinearIndependent ℝ ![g, ((1 : ℝ), 0, 0, 0)] ∧ g ∉ sheetASub k ∧ g ∉ Q := by
  have hex : (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) ∈ sheetASub k :=
    mem_sheetASub.mpr ⟨rfl, rfl⟩
  have hex0 : (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) ≠ 0 := by
    intro h
    have := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) h
    simp at this
  have h2 : c⁻¹ • g = (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) - b := by
    rw [hg, inv_smul_smul₀ hc]
  have hgP : g ∉ sheetASub k := by
    intro hgP
    have hb : b = (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) - c⁻¹ • g := by
      rw [h2, sub_sub_cancel]
    have hmem : b ∈ sheetASub k := by
      rw [hb]
      exact Submodule.sub_mem _ hex (Submodule.smul_mem _ _ hgP)
    have hbot : b ∈ sheetASub k ⊓ Q := ⟨hmem, hbQ⟩
    rw [hPQ] at hbot
    exact hb0 ((Submodule.mem_bot ℝ).mp hbot)
  have hgQ : g ∉ Q := by
    intro hgQ
    have heq : (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) = b + c⁻¹ • g := by
      rw [h2]; abel
    have hmem : (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) ∈ Q := by
      rw [heq]
      exact Submodule.add_mem _ hbQ (Submodule.smul_mem _ _ hgQ)
    have hbot : (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) ∈ sheetASub k ⊓ Q := ⟨hex, hmem⟩
    rw [hPQ] at hbot
    exact hex0 ((Submodule.mem_bot ℝ).mp hbot)
  have hg0 : g ≠ 0 := fun h => hgP (h ▸ Submodule.zero_mem _)
  refine ⟨?_, hgP, hgQ⟩
  rw [LinearIndependent.pair_iff' hg0]
  intro a ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hex0 ha.symm
  have hge : g = a⁻¹ • (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    rw [← ha, inv_smul_smul₀ ha0]
  have hspan : g ∈ Submodule.span ℝ ({(((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k)} : Set _) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨a⁻¹, hge.symm⟩
  exact hgP (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hex) hspan)


/-! ## Differentiability helpers -/

/-- **The corner algebra of the lens, negative form.**  Same as `corner_algebra` but with the
vector `d` of the value formula equal to `-a`, the vector appearing in the independence claim. -/
theorem corner_algebra_neg {k : ℕ} {Q : Submodule ℝ (Work.Drive.Whitney.Mdl k)}
    (hPQ : sheetASub k ⊓ Q = ⊥) {b g a d : Work.Drive.Whitney.Mdl k} (hbQ : b ∈ Q) (hb0 : b ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (ha : a ∈ sheetASub k) (ha0 : a ≠ 0) (hd : d = -a)
    (hg : g = c • (d - b)) :
    LinearIndependent ℝ ![g, a] ∧ g ∉ sheetASub k ∧ g ∉ Q := by
  have hdP : d ∈ sheetASub k := by rw [hd]; exact Submodule.neg_mem _ ha
  have hd0 : d ≠ 0 := by rw [hd]; intro h; exact ha0 (neg_eq_zero.mp h)
  have h2 : c⁻¹ • g = d - b := by rw [hg, inv_smul_smul₀ hc]
  have hgP : g ∉ sheetASub k := by
    intro hgP
    have hb : b = d - c⁻¹ • g := by rw [h2, sub_sub_cancel]
    have hmem : b ∈ sheetASub k := by
      rw [hb]
      exact Submodule.sub_mem _ hdP (Submodule.smul_mem _ _ hgP)
    have hbot : b ∈ sheetASub k ⊓ Q := ⟨hmem, hbQ⟩
    rw [hPQ] at hbot
    exact hb0 ((Submodule.mem_bot ℝ).mp hbot)
  have hgQ : g ∉ Q := by
    intro hgQ
    have heq : d = b + c⁻¹ • g := by rw [h2]; abel
    have hmem : d ∈ Q := by
      rw [heq]
      exact Submodule.add_mem _ hbQ (Submodule.smul_mem _ _ hgQ)
    have hbot : d ∈ sheetASub k ⊓ Q := ⟨hdP, hmem⟩
    rw [hPQ] at hbot
    rw [hd] at hbot
    exact ha0 (neg_eq_zero.mp ((Submodule.mem_bot ℝ).mp hbot))
  have hg0 : g ≠ 0 := fun h => hgP (h ▸ Submodule.zero_mem _)
  refine ⟨?_, hgP, hgQ⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right ha0⟩
  · exfalso
    have hspan : Submodule.span ℝ ({a} : Set (Work.Drive.Whitney.Mdl k)) ≤ sheetASub k :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ha)
    have hasn : a ∈ Submodule.span ℝ ({a} : Set (Work.Drive.Whitney.Mdl k)) :=
      Submodule.subset_span (Set.mem_singleton a)
    have hgspan : g ∈ Submodule.span ℝ ({a} : Set (Work.Drive.Whitney.Mdl k)) := by
      have hsa : s • g ∈ Submodule.span ℝ ({a} : Set (Work.Drive.Whitney.Mdl k)) := by
        have hsg : s • g = -(t • a) := eq_neg_of_add_eq_zero_left hst
        rw [hsg]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hasn)
      have hgg : g = s⁻¹ • (s • g) := (inv_smul_smul₀ hs g).symm
      rw [hgg]
      exact Submodule.smul_mem _ _ hsa
    have hb : b = d - c⁻¹ • g := by rw [h2, sub_sub_cancel]
    have hbspan : b ∈ Submodule.span ℝ ({a} : Set (Work.Drive.Whitney.Mdl k)) := by
      rw [hb]
      exact Submodule.sub_mem _
        (by rw [hd]; exact Submodule.neg_mem _ hasn)
        (Submodule.smul_mem _ _ hgspan)
    have hbot : b ∈ sheetASub k ⊓ Q := ⟨hspan hbspan, hbQ⟩
    rw [hPQ] at hbot
    exact hb0 ((Submodule.mem_bot ℝ).mp hbot)

/-- A map with a smooth right inverse has injective Fréchet derivative everywhere. -/
theorem lensFderivInjective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F} {Θ : F → E}
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (h : ∀ y : E, Θ (Φ y) = y) : ∀ z : E, Function.Injective (fderiv ℝ Φ z) := by
  intro z
  have hdiffΘ : DifferentiableAt ℝ Θ (Φ z) :=
    (hΘ.contDiffAt (x := Φ z)).differentiableAt (by simp)
  have hdiffΦ : DifferentiableAt ℝ Φ z :=
    (hΦ.contDiffAt (x := z)).differentiableAt (by simp)
  have hcomp : fderiv ℝ (fun y => Θ (Φ y)) z = (fderiv ℝ Θ (Φ z)).comp (fderiv ℝ Φ z) :=
    fderiv_comp (x := z) (f := Φ) (g := Θ) hdiffΘ hdiffΦ
  have hid : fderiv ℝ (fun y => Θ (Φ y)) z = ContinuousLinearMap.id ℝ E := by
    rw [show (fun y => Θ (Φ y)) = id from funext h, fderiv_id]
  have hkey : (fderiv ℝ Θ (Φ z)).comp (fderiv ℝ Φ z) = ContinuousLinearMap.id ℝ E :=
    hcomp.symm.trans hid
  intro a b hab
  have hh := congrArg (fun L : E →L[ℝ] E => L a) hkey
  have hhb := congrArg (fun L : E →L[ℝ] E => L b) hkey
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hh hhb
  rw [hab] at hh
  exact hh.symm.trans hhb

/-- The composite of an immersion with a map whose Fréchet derivative is injective everywhere is
immersive. -/
theorem lensMfderivCompInjective {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦinj : ∀ z : EuclideanSpace ℝ (Fin (2 * (k + 1))), Function.Injective (fderiv ℝ Φ z)) :
    ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y) := by
  intro y
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) y
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1)))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f y)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f y) :=
    mfderiv_comp y
      ((hΦ.contMDiff).contMDiffAt.mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_eq_fderiv]
  intro a b hab
  exact himm y (hΦinj (f y) hab)

/-- The range of the derivative of an injective map on a `(k+1)`-manifold into the model space has
dimension `k + 1`. -/
theorem lensFinrankRange {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (g : M → Work.Drive.Whitney.Mdl k) (y : M)
    (h : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) g y)) :
    Module.finrank ℝ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) g y).range = k + 1 := by
  have hker : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) g y).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr h
  haveI : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) y) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (k + 1))))
  have hran := LinearMap.finrank_range_add_finrank_ker
    ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) g y)).toLinearMap
  have hdom : Module.finrank ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) y) = k + 1 := by
    rw [show Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) y)
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) from rfl]
    simp
  rw [hker, finrank_bot, add_zero, hdom] at hran
  exact hran

theorem lensCleanOfChartSolid {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F) :
    Nonempty (Work.Drive.PushDisc.LWLensDisc k M C T F G) := by
  classical
  have hk : 2 ≤ k := by have h := C.hn; omega
  -- the composite `Φ₀ ∘ f`
  let gΦ : M → Work.Drive.Whitney.Mdl k := fun y : M => T.Φ₀ (C.f y)
  -- ## the derivative of `Φ₀` is injective, hence so is that of the composite
  have hΦ₀inj : ∀ z : EuclideanSpace ℝ (Fin (2 * (k + 1))),
      Function.Injective (fderiv ℝ T.Φ₀ z) :=
    lensFderivInjective T.hΦ₀sm T.hΘ₀sm T.hΘ₀Φ₀
  have hgmdi : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ y) :=
    lensMfderivCompInjective C.f C.hf C.himm T.Φ₀ T.hΦ₀sm hΦ₀inj
  -- ## the core curve `B` of the finger and its rows
  let B : ℝ → Work.Drive.Whitney.Mdl k := fun x : ℝ => G.S₂ (x, 0)
  have hBsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    G.hS₂sm.comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨hBinj, hBimm, hBoff, hBone, hBnegone⟩ := lensFingerBRows C T F G
  -- ## the Hadamard quotient `g` of `B - (·,0,0,0)`
  let eC : Work.Drive.Whitney.Mdl k ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (Work.Drive.PushDisc.mdlEquivL (n := k + 1) (k := k) rfl).toContinuousLinearEquiv
  let eT : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    (eC : Work.Drive.Whitney.Mdl k →L[ℝ] EuclideanSpace ℝ (Fin (2 * (k + 1))))
  let sT : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k :=
    (eC.symm : EuclideanSpace ℝ (Fin (2 * (k + 1))) →L[ℝ] Work.Drive.Whitney.Mdl k)
  let Aclm : ℝ →L[ℝ] Work.Drive.Whitney.Mdl k :=
    ContinuousLinearMap.inl ℝ ℝ (ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
  have hAclm : ∀ x : ℝ, Aclm x = ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := fun x => rfl
  have hBAsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => eT (B x - Aclm x)) :=
    eT.contDiff.comp (hBsm.sub Aclm.contDiff)
  have hBA1 : (fun x : ℝ => eT (B x - Aclm x)) 1 = 0 := by
    show eT (G.S₂ (1, (0 : EuclideanSpace ℝ (Fin k))) - Aclm 1) = 0
    rw [hBone, hAclm 1, sub_self, map_zero]
  have hBAm1 : (fun x : ℝ => eT (B x - Aclm x)) (-1) = 0 := by
    show eT (G.S₂ (-1, (0 : EuclideanSpace ℝ (Fin k))) - Aclm (-1)) = 0
    rw [hBnegone, hAclm (-1), sub_self, map_zero]
  obtain ⟨g', hg'sm, hg'val⟩ := exists_archQuot (n := k + 1) hBAsm hBA1 hBAm1
  let g : ℝ → Work.Drive.Whitney.Mdl k := fun x : ℝ => eC.symm (g' x)
  have hgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => eC.symm (g' x))
    exact sT.contDiff.comp hg'sm
  have hgval : ∀ x : ℝ, Work.Drive.PushDisc.arch x • g x = B x - Aclm x := by
    intro x
    have h3 : eC.symm (Work.Drive.PushDisc.arch x • g' x) = Work.Drive.PushDisc.arch x • g x := by
      rw [map_smul]
    rw [← h3, hg'val x]
    show eC.symm (eC (B x - Aclm x)) = B x - Aclm x
    rw [eC.symm_apply_apply]
  have hgval' : ∀ x : ℝ, Work.Drive.PushDisc.arch x • g x
      = B x - ((x, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := by
    intro x
    rw [hgval x, hAclm x]
  -- ## the tangent planes, as submodules of the model space
  let Rγ : M → Submodule ℝ (Work.Drive.Whitney.Mdl k) := fun y =>
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ y).range
  have hbotRan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Rγ (C.γ₁ (Work.Drive.Whitney.sigR x)) = sheetASub k := by
    intro x hx
    show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ
      (C.γ₁ (Work.Drive.Whitney.sigR x))).range = sheetASub k
    exact range_mfderiv_eq_sheetASub_of_flat (k := k) C.f C.hf T.Φ₀ T.hΦ₀sm hgmdi C.γ₁ C.hγ₁
      T.U₁ T.hU₁o T.hU₁arc T.hU₁row (Work.Drive.Whitney.sigR x)
      (Work.Drive.Whitney.sigR_mem_iff.mpr hx)
  have hTR := lensTangentRows C T F G
  have htopRan : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Rγ (C.γ₂ (Work.Drive.Whitney.sigR x))
        = Submodule.span ℝ (Set.range (Fin.cons (fderiv ℝ B x 1) (G.V x))) := by
    intro x hx
    show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ
      (C.γ₂ (Work.Drive.Whitney.sigR x))).range
        = Submodule.span ℝ (Set.range (Fin.cons (fderiv ℝ B x 1) (G.V x)))
    exact hTR.1 x hx
  have htopRank : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Module.finrank ℝ ↥(Rγ (C.γ₂ (Work.Drive.Whitney.sigR x))) = k + 1 := by
    intro x hx
    show Module.finrank ℝ ↥((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ
      (C.γ₂ (Work.Drive.Whitney.sigR x))).range) = k + 1
    exact hTR.2.1 x hx
  have htopMem : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      fderiv ℝ B x 1 ∈ Rγ (C.γ₂ (Work.Drive.Whitney.sigR x)) := by
    intro x hx
    show fderiv ℝ B x 1 ∈ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ
      (C.γ₂ (Work.Drive.Whitney.sigR x))).range
    exact hTR.2.2 x hx
  have hsupP : Rγ C.p₁ ⊔ Rγ C.p₂ = ⊤ := by
    show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ C.p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ C.p₂).range = ⊤
    exact compRangeSupEqTop (k := k) C.f C.hf T.Φ₀ T.hΦ₀sm hΦ₀inj C.p₁ C.p₂ C.hfp C.htransP
  have hsupQ : Rγ C.q₁ ⊔ Rγ C.q₂ = ⊤ := by
    show (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ C.q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ C.q₂).range = ⊤
    exact compRangeSupEqTop (k := k) C.f C.hf T.Φ₀ T.hΦ₀sm hΦ₀inj C.q₁ C.q₂ C.hfq C.htransQ
  have hfin : ∀ y : M, Module.finrank ℝ ↥(Rγ y) = k + 1 := by
    intro y
    show Module.finrank ℝ ↥((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ y).range) = k + 1
    exact lensFinrankRange (k := k) gΦ y (hgmdi y)
  have hq1r : Rγ (C.γ₁ 1) = sheetASub k := by
    have h := hbotRan 1 (by norm_num)
    rwa [Work.Drive.Whitney.sigR_one] at h
  have hp1r : Rγ (C.γ₁ 0) = sheetASub k := by
    have h := hbotRan (-1) (by norm_num)
    rwa [Work.Drive.Whitney.sigR_neg_one] at h
  have hsupQ1 : Rγ (C.γ₁ 1) ⊔ Rγ (C.γ₂ 1) = ⊤ := by
    rw [C.hγ₁1, C.hγ₂1]
    exact hsupQ
  have hsupP1 : Rγ (C.γ₁ 0) ⊔ Rγ (C.γ₂ 0) = ⊤ := by
    rw [C.hγ₁0, C.hγ₂0]
    exact hsupP
  have hinfQ1 : Rγ (C.γ₁ 1) ⊓ Rγ (C.γ₂ 1) = ⊥ := by
    have hsum : Module.finrank ℝ ↥(Rγ (C.γ₁ 1)) + Module.finrank ℝ ↥(Rγ (C.γ₂ 1))
        = Module.finrank ℝ (Work.Drive.Whitney.Mdl k) := by
      rw [hq1r, finrank_sheetASub, hfin (C.γ₂ 1), finrank_Mdl]
      omega
    exact inf_eq_bot_of_finrank_add (E := Work.Drive.Whitney.Mdl k) hsupQ1 hsum
  have hinfP1 : Rγ (C.γ₁ 0) ⊓ Rγ (C.γ₂ 0) = ⊥ := by
    have hsum : Module.finrank ℝ ↥(Rγ (C.γ₁ 0)) + Module.finrank ℝ ↥(Rγ (C.γ₂ 0))
        = Module.finrank ℝ (Work.Drive.Whitney.Mdl k) := by
      rw [hp1r, finrank_sheetASub, hfin (C.γ₂ 0), finrank_Mdl]
      omega
    exact inf_eq_bot_of_finrank_add (E := Work.Drive.Whitney.Mdl k) hsupP1 hsum
  have hPQq2 : sheetASub k ⊓ Rγ (C.γ₂ 1) = ⊥ := by
    rw [← hq1r]
    exact hinfQ1
  have hPQp2 : sheetASub k ⊓ Rγ (C.γ₂ 0) = ⊥ := by
    rw [← hp1r]
    exact hinfP1
  -- ## the corner rows
  have hb1mem : fderiv ℝ B 1 1 ∈ Rγ (C.γ₂ 1) := by
    have h := htopMem 1 (by norm_num)
    rwa [Work.Drive.Whitney.sigR_one] at h
  have hbm1mem : fderiv ℝ B (-1) 1 ∈ Rγ (C.γ₂ 0) := by
    have h := htopMem (-1) (by norm_num)
    rwa [Work.Drive.Whitney.sigR_neg_one] at h
  obtain ⟨hA1, hAm1⟩ := archSmulDerivCorners B g hgsm hBsm hgval'
  have hb1ne : fderiv ℝ B 1 1 ≠ 0 := hBimm 1 (by norm_num)
  have hbm1ne : fderiv ℝ B (-1) 1 ≠ 0 := hBimm (-1) (by norm_num)
  have hg1val : g 1 = (1 / 2 : ℝ) •
      ((((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) - fderiv ℝ B 1 1) := by
    have h2 : g 1 = (-2 : ℝ)⁻¹ •
        (fderiv ℝ B 1 1 - (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k)) := by
      rw [← hA1, inv_smul_smul₀ (by norm_num : (-2 : ℝ) ≠ 0)]
    rw [h2, show (-2 : ℝ)⁻¹ = -(1 / 2) from by norm_num]
    rw [neg_smul, ← neg_sub, smul_neg, neg_neg]
  have hgm1val : g (-1) = (-(1 / 2) : ℝ) •
      ((((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k) - fderiv ℝ B (-1) 1) := by
    have h2 : g (-1) = (2 : ℝ)⁻¹ •
        (fderiv ℝ B (-1) 1 - (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k)) := by
      rw [← hAm1, inv_smul_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h2, show (2 : ℝ)⁻¹ = (1 / 2) from by norm_num]
    rw [neg_smul, ← neg_sub, smul_neg]
  have hcor1 := corner_algebra (k := k) (Q := Rγ (C.γ₂ 1)) hPQq2 hb1mem hb1ne
    (c := (1 / 2 : ℝ)) (by norm_num) hg1val
  have hcorm1 := corner_algebra_neg (k := k) (Q := Rγ (C.γ₂ 0)) hPQp2 hbm1mem hbm1ne
    (a := (((-1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
    (d := (((1 : ℝ), 0, 0, 0) : Work.Drive.Whitney.Mdl k))
    (ha := mem_sheetASub.mpr ⟨rfl, rfl⟩)
    (ha0 := by intro h; simpa using congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) h)
    (hd := by simp)
    (c := (-(1 / 2) : ℝ)) (by norm_num) hgm1val
  have hcorn1 : LinearIndependent ℝ ![g 1, ((1 : ℝ), 0, 0, 0)] := hcor1.1
  have hg1 : g 1 ∉ sheetASub k := hcor1.2.1
  have hgc1 : g 1 ∉ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ (C.γ₂ 1)).range := hcor1.2.2
  have hcornm1 : LinearIndependent ℝ ![g (-1), ((-1 : ℝ), 0, 0, 0)] := hcorm1.1
  have hgm1 : g (-1) ∉ sheetASub k := hcorm1.2.1
  have hgcm1 : g (-1) ∉ (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) gΦ (C.γ₂ 0)).range := hcorm1.2.2
  -- ## the clean lens disc
  obtain ⟨Δ, hΔsm, -, -, hΔ0, hΔtop, -, hΔinj, hΔimm, hΔclean, hΔbot, hΔtop2⟩ :=
    exists_cleanLens (k := k) hk C.f C.hf T.Φ₀ T.hΦ₀sm hgmdi C.γ₁ C.γ₂ C.hγ₁smooth C.hγ₂smooth
      B g hBsm hgsm (fun x => (hgval' x).symm) hBinj hBimm hBoff hcorn1 hcornm1 hg1 hgm1
      G.V (fun x hx => hbotRan x hx) (fun x hx => htopRan x hx)
      (fun x hx => htopRank x hx) hgc1 hgcm1
  exact ⟨{ Δ := Δ
           hΔsm := hΔsm
           hΔ0 := hΔ0
           hΔ1 := fun x _ => hΔtop x
           hΔinj := hΔinj
           hΔimm := hΔimm
           hΔclean := hΔclean
           hbot := hΔbot
           htop := hΔtop2 }⟩

end Work.Drive.PushDisc
