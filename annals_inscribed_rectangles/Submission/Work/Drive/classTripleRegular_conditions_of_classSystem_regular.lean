import Mathlib
import Submission.Work.Drive.classTripleConversion
import Submission.Work.Drive.classTripleSystem
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.diffMap_generalPosition
import Submission.Work.Drive.sameKernel_transfer
import Submission.Work.Drive.exists_iso_of_ker_eq
import Submission.Work.Drive.map_projCoordFunDerivE_smul
import Submission.Work.Drive.fderiv_classSystem_y

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology LinearAlgebra.Projectivization

set_option maxHeartbeats 800000

noncomputable section

/-! ## Auxiliary linear algebra -/

/-- `L ∘ M` is injective iff `M` is injective and the range of `M` meets `ker L` trivially. -/
lemma injective_comp_iff_range_inf_ker {E F G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (L : F →ₗ[ℝ] G) (M : E →ₗ[ℝ] F) :
    Function.Injective (L.comp M) ↔
      Function.Injective M ∧ LinearMap.range M ⊓ LinearMap.ker L = ⊥ := by
  have key : ∀ x : E, L.comp M x = 0 ↔ M x ∈ LinearMap.ker L := by
    intro x; rw [LinearMap.mem_ker]; rfl
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, ?_⟩
    · have hz : L.comp M (a - b) = 0 := by
        rw [LinearMap.comp_apply, map_sub, map_sub, hab, sub_self]
      have h0 : a - b = 0 := by
        have := h (show L.comp M (a - b) = L.comp M 0 by
          rw [hz, LinearMap.comp_apply, map_zero, map_zero])
        simpa using this
      exact sub_eq_zero.mp h0
    · rw [Submodule.eq_bot_iff]
      rintro x ⟨⟨w, rfl⟩, hx⟩
      have hz : L.comp M w = 0 := (key w).mpr hx
      have h0 : w = 0 := by
        have := h (show L.comp M w = L.comp M 0 by
          rw [hz, LinearMap.comp_apply, map_zero, map_zero])
        simpa using this
      rw [h0, map_zero]
  · rintro ⟨hinj, hbot⟩ a b hab
    have hmem : M (a - b) ∈ LinearMap.range M ⊓ LinearMap.ker L := by
      exact ⟨⟨a - b, rfl⟩, (key (a - b)).mp (by
        have hab' : L (M a) = L (M b) := by simpa only [LinearMap.comp_apply] using hab
        rw [LinearMap.comp_apply, map_sub, map_sub, hab', sub_self])⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp (hinj (by rw [hmem, map_zero]))

/-- `qformRight v` is onto `ℝ³` for `v ≠ 0` (its kernel is the line `ℝ∙v`). -/
theorem qformRight_surjective (v : Eucl 3) (hv : v ≠ 0) :
    Function.Surjective (qformRight v) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker (qformRight v)
  rw [qformRight_ker v hv, finrank_span_singleton hv] at h
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [h4] at h
  rw [h3]
  omega

/-! ## The block embedding `(ℝ²)³ → ℝ⁶` -/

/-- The linear embedding whose `k`-th block is the `k`-th coordinate. -/
def blockEmbed : (Fin 3 → EuclideanSpace ℝ (Fin 2)) →ₗ[ℝ] Tgt 6 where
  toFun e := WithLp.toLp 2 (fun j : Fin 6 =>
    e ((finProdFinEquiv (m := 3) (n := 2)).symm j).1
      ((finProdFinEquiv (m := 3) (n := 2)).symm j).2)
  map_add' e e' := by
    ext j
    simp
  map_smul' c e := by
    ext j
    simp

lemma parCProj_blockEmbed (k : Fin 3) (e : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    parCProj k (blockEmbed e) = e k := by
  ext i
  simp [blockEmbed, parCProj_apply, parC]

lemma blockEmbed_surjective : Function.Surjective (blockEmbed :
    (Fin 3 → EuclideanSpace ℝ (Fin 2)) → Tgt 6) := by
  intro y
  refine ⟨fun k => parOf y k, ?_⟩
  ext j
  simp [blockEmbed, parC]

/-! ## The weighted difference map on `Tgt 6` -/

private noncomputable def wDiffMap (μ : Fin 3 → ℝ)
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))) :
    Tgt 6 →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  (((α 1).comp (parCProj 1).toLinearMap - μ 1 • ((α 0).comp (parCProj 0).toLinearMap)).prod
    ((α 2).comp (parCProj 2).toLinearMap - μ 2 • ((α 0).comp (parCProj 0).toLinearMap)))

private lemma wDiffMap_apply (μ : Fin 3 → ℝ)
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)))
    (z : Tgt 6) :
    wDiffMap μ α z =
      (α 1 (parCProj 1 z) - μ 1 • α 0 (parCProj 0 z),
       α 2 (parCProj 2 z) - μ 2 • α 0 (parCProj 0 z)) := rfl

/-- **The weighted difference map of three linear maps out of `ℝ²` is onto only in the general
position**: from the surjectivity of the blocks one gets injectivity of the three maps and the
triviality of the triple intersection of their ranges. -/
theorem weightedDiffMap_generalPosition (μ : Fin 3 → ℝ)
    (α : Fin 3 → (EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)))
    (hsurj : Function.Surjective (wDiffMap μ α)) :
    (∀ k, Function.Injective (α k)) ∧
      (⨅ k, LinearMap.range (α k) = ⊥) := by
  have hdim : Module.finrank ℝ (Tgt 6) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) := by
    rw [Module.finrank_prod]
    simp
  have hinj : Function.Injective (wDiffMap μ α) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have hker : ∀ z, wDiffMap μ α z = 0 → z = 0 := fun z hz => hinj (by rw [hz, map_zero])
  have inj0 : Function.Injective (α 0) := by
    intro u v huv
    have hα : α 0 (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hz : wDiffMap μ α (blockEmbed ![u - v, (0 : EuclideanSpace ℝ (Fin 2)), 0]) = 0 := by
      rw [wDiffMap_apply, parCProj_blockEmbed, parCProj_blockEmbed, parCProj_blockEmbed]
      simp [hα]
    have h0 : blockEmbed ![u - v, (0 : EuclideanSpace ℝ (Fin 2)), 0] = 0 := hker _ hz
    have h1 : u - v = 0 := by
      have hc := congrArg (fun z => parCProj 0 z) h0
      rw [parCProj_blockEmbed, map_zero] at hc
      simpa using hc
    exact sub_eq_zero.mp h1
  have inj1 : Function.Injective (α 1) := by
    intro u v huv
    have hα : α 1 (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hz : wDiffMap μ α (blockEmbed ![(0 : EuclideanSpace ℝ (Fin 2)), u - v, 0]) = 0 := by
      rw [wDiffMap_apply, parCProj_blockEmbed, parCProj_blockEmbed, parCProj_blockEmbed]
      simp [hα]
    have h0 : blockEmbed ![(0 : EuclideanSpace ℝ (Fin 2)), u - v, 0] = 0 := hker _ hz
    have h1 : u - v = 0 := by
      have hc := congrArg (fun z => parCProj 1 z) h0
      rw [parCProj_blockEmbed, map_zero] at hc
      simpa using hc
    exact sub_eq_zero.mp h1
  have inj2 : Function.Injective (α 2) := by
    intro u v huv
    have hα : α 2 (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hz : wDiffMap μ α (blockEmbed ![(0 : EuclideanSpace ℝ (Fin 2)), 0, u - v]) = 0 := by
      rw [wDiffMap_apply, parCProj_blockEmbed, parCProj_blockEmbed, parCProj_blockEmbed]
      simp [hα]
    have h0 : blockEmbed ![(0 : EuclideanSpace ℝ (Fin 2)), 0, u - v] = 0 := hker _ hz
    have h1 : u - v = 0 := by
      have hc := congrArg (fun z => parCProj 2 z) h0
      rw [parCProj_blockEmbed, map_zero] at hc
      simpa using hc
    exact sub_eq_zero.mp h1
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k
    · exact inj0
    · exact inj1
    · exact inj2
  · rw [Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_iInf] at hu
    obtain ⟨e0, he0⟩ := LinearMap.mem_range.mp (hu 0)
    obtain ⟨e1, he1⟩ := LinearMap.mem_range.mp (hu 1)
    obtain ⟨e2, he2⟩ := LinearMap.mem_range.mp (hu 2)
    have hz : wDiffMap μ α (blockEmbed ![e0, μ 1 • e1, μ 2 • e2]) = 0 := by
      rw [wDiffMap_apply, parCProj_blockEmbed, parCProj_blockEmbed, parCProj_blockEmbed]
      refine Prod.ext ?_ ?_ <;> simp [map_smul, he0, he1, he2]
    have h0 : blockEmbed ![e0, μ 1 • e1, μ 2 • e2] = 0 := hker _ hz
    have h1 : e0 = 0 := by
      have hc := congrArg (fun z => parCProj 0 z) h0
      rw [parCProj_blockEmbed, map_zero] at hc
      simpa using hc
    rw [← he0, h1, map_zero]

/-! ## Small bookkeeping lemmas -/

lemma mk2_parOf (y : Tgt 6) (k : Fin 3) :
    mk2 (parOf y k 0) (parOf y k 1) = parOf y k := by
  ext i
  fin_cases i <;> rfl

lemma fderiv_parOf (k : Fin 3) (y : Tgt 6) :
    fderiv ℝ (fun y' : Tgt 6 => parOf y' k) y = parCProj k := by
  have h : (fun y' : Tgt 6 => parOf y' k) = parCProj k :=
    funext (fun y' => (parCProj_apply_eq_parOf k y').symm)
  rw [h, ContinuousLinearMap.fderiv]

lemma fderiv_clm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (g : E → F) (x : E) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun x' => L (g x')) x = L.comp (fderiv ℝ g x) :=
  (L.hasFDerivAt.comp x hg.hasFDerivAt).fderiv

lemma iInf_fin3 (S : Fin 3 → Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :
    (⨅ k, S k) = S 0 ⊓ S 1 ⊓ S 2 := by
  apply le_antisymm
  · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  · refine le_iInf fun k => ?_
    fin_cases k
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right

/-! ## The conversion of `classSystem`-regularity into `hci`/`hV` -/

/-- **The conversion of `classSystem`-regularity into `hci`/`hV`** (proof plan in
`Submission/Work/Drive/L5_CHAIN_STATUS.md` §5; `hVsmooth` was added after the review gate caught that
`Work.Drive.fderiv_classSystem_y` and the projective-immersion lemmas need the smoothness of the
lift). -/
theorem classTripleRegular_conditions_of_classSystem_regular {m : ℕ}
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.Eucl 3)
    (hVne : ∀ k y, V k y ≠ 0)
    (hVsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V k))
    (hVcls : ∀ k y, y ∈ Submission.Drive.unitBox 1 →
      Projectivization.mk ℝ (V k y) (hVne k y) = Work.Drive.planeClassMap (P k) y)
    (A : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (p : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Tgt 6)
    (hy : ∀ k, (Work.Drive.parOf y k) 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
      (Work.Drive.parOf y k) 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hinj : ∀ k, Function.Injective ⇑(A k))
    (hzero : Work.Drive.classSystem V
      (fun _ k => (A k : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3)) p y = 0)
    (hreg : Function.Surjective (fderiv ℝ (fun y' : Work.Drive.Tgt 6 =>
      Work.Drive.classSystem V
        (fun _ k => (A k : Work.Drive.Eucl 3 →L[ℝ] Work.Drive.Eucl 3)) p y') y)) :
    (letI := Work.Drive.projCharted 3;
      (∀ k, Function.Injective (mfderiv (Work.Drive.Tm2) (Work.Drive.Tm3)
          (fun y' => (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.linCapping (A k) (P k y'))).2)
          (Work.Drive.mk2 ((Work.Drive.parOf y k) 0) ((Work.Drive.parOf y k) 1))))
      ∧ ((mfderiv (Work.Drive.Tm2) (Work.Drive.Tm3)
            (fun y' => (Work.Drive.cappingSpaceHomeoProj (Work.Drive.linCapping (A 0) (P 0 y'))).2)
            (Work.Drive.mk2 ((Work.Drive.parOf y 0) 0) ((Work.Drive.parOf y 0) 1))).range
          ⊓ (mfderiv (Work.Drive.Tm2) (Work.Drive.Tm3)
            (fun y' => (Work.Drive.cappingSpaceHomeoProj (Work.Drive.linCapping (A 1) (P 1 y'))).2)
            (Work.Drive.mk2 ((Work.Drive.parOf y 1) 0) ((Work.Drive.parOf y 1) 1))).range
          ⊓ (mfderiv (Work.Drive.Tm2) (Work.Drive.Tm3)
            (fun y' => (Work.Drive.cappingSpaceHomeoProj (Work.Drive.linCapping (A 2) (P 2 y'))).2)
            (Work.Drive.mk2 ((Work.Drive.parOf y 2) 0) ((Work.Drive.parOf y 2) 1))).range = ⊥)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  let B : EuclideanSpace ℝ (Fin m) → Fin 3 → Eucl 3 →L[ℝ] Eucl 3 :=
    fun _ k => (A k : Eucl 3 →L[ℝ] Eucl 3)
  -- 1. the perturbed lift values are non-zero
  have hvne : ∀ k, B p k (V k (parOf y k)) ≠ 0 := by
    intro k h
    have hh : (B p k) (V k (parOf y k)) = (B p k) 0 := by rw [h, map_zero]
    exact hVne k (parOf y k) ((hinj k) hh)
  -- 2. the three perturbed values are pairwise proportional
  obtain ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ :=
    (classSystem_eq_zero_iff V B p y (fun k => hVne k (parOf y k)) (fun k => hinj k)).mp hzero
  have hμ1 : a1 ≠ 0 := by
    intro h; rw [h, zero_smul] at ha1; exact hvne 1 ha1.symm
  have hμ2 : a2 ≠ 0 := by
    intro h; rw [h, zero_smul] at ha2; exact hvne 2 ha2.symm
  let v0 : Eucl 3 := B p 0 (V 0 (parOf y 0))
  have hv0 : v0 ≠ 0 := hvne 0
  let μ : Fin 3 → ℝ := ![1, a1, a2]
  have hμ : ∀ k, μ k ≠ 0 := by
    intro k; fin_cases k
    · simp [μ]
    · simpa [μ] using hμ1
    · simpa [μ] using hμ2
  have hvμ : ∀ k, μ k • v0 = B p k (V k (parOf y k)) := by
    intro k; fin_cases k
    · simp [μ, v0]
    · simpa [μ, v0] using ha1
    · simpa [μ, v0] using ha2
  -- 3. the perturbed class lifts
  let W : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3 := fun k y' => B p k (V k y')
  have hWne : ∀ k y', W k y' ≠ 0 := by
    intro k y' h
    have hh : W k y' = (B p k) 0 := by rw [h]; simp
    exact hVne k y' ((hinj k) hh)
  have hWsmooth : ∀ k, ContMDiffAt (𝓡 2) (𝓘(ℝ, Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (W k) (parOf y k) := by
    intro k
    have hWdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W k) :=
      ContDiff.continuousLinearMap_comp (B p k) (hVsmooth k)
    rw [contMDiffAt_iff_contDiffAt]
    exact hWdiff.contDiffAt
  -- 4. the derivatives of the lifts
  let K : Fin 3 → EuclideanSpace ℝ (Fin 2) →L[ℝ] Eucl 3 :=
    fun k => fderiv ℝ (W k) (parOf y k)
  have hK : ∀ k, K k = (B p k).comp (fderiv ℝ (V k) (parOf y k)) := by
    intro k
    exact fderiv_clm_comp (B p k) (V k) (parOf y k)
      ((hVsmooth k).contDiffAt.differentiableAt (by simp))
  let d : Fin 3 → Tgt 6 →L[ℝ] Eucl 3 :=
    fun k => fderiv ℝ (fun y' : Tgt 6 => B p k (V k (parOf y' k))) y
  have hdK : ∀ k, d k = (K k).comp (parCProj k) := by
    intro k
    show fderiv ℝ (fun y' : Tgt 6 => B p k (V k (parOf y' k))) y = (K k).comp (parCProj k)
    have hWd : DifferentiableAt ℝ (W k) (parOf y k) := by
      have hWdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W k) :=
        ContDiff.continuousLinearMap_comp (B p k) (hVsmooth k)
      exact hWdiff.contDiffAt.differentiableAt (by simp)
    have hVd : DifferentiableAt ℝ (fun y' : Tgt 6 => parOf y' k) y :=
      (parCProj k).differentiableAt
    have hchain : fderiv ℝ (fun y' : Tgt 6 => W k (parOf y' k)) y
        = (fderiv ℝ (W k) (parOf y k)).comp
            (fderiv ℝ (fun y' : Tgt 6 => parOf y' k) y) := by
      rw [show (fun y' : Tgt 6 => W k (parOf y' k))
          = W k ∘ (fun y' : Tgt 6 => parOf y' k) from rfl]
      rw [fderiv_comp y hWd hVd]
    have hfun : (fun y' : Tgt 6 => B p k (V k (parOf y' k))) =
        fun y' : Tgt 6 => W k (parOf y' k) := rfl
    rw [hfun, hchain, fderiv_parOf]
  -- 5. the class maps agree near the point with the explicit lifts
  have hbox : ∀ k, Submission.Drive.unitBox 1 ∈ 𝓝 (parOf y k) := by
    intro k
    have h0 : {y' : EuclideanSpace ℝ (Fin 2) | y' 0 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (parOf y k) :=
      (isOpen_Ioo.preimage (projImmCoordL (0 : Fin 2)).continuous).mem_nhds ((hy k).1)
    have h1 : {y' : EuclideanSpace ℝ (Fin 2) | y' 1 ∈ Set.Ioo (0 : ℝ) 1} ∈ 𝓝 (parOf y k) :=
      (isOpen_Ioo.preimage (projImmCoordL (1 : Fin 2)).continuous).mem_nhds ((hy k).2)
    refine Filter.mem_of_superset (Filter.inter_mem h0 h1) ?_
    rintro y' ⟨h0', h1'⟩ i
    fin_cases i
    · exact Set.Ioo_subset_Icc_self h0'
    · exact Set.Ioo_subset_Icc_self h1'
  have hmf_eq : ∀ k, mfderiv (𝓡 2) (𝓡 3)
        (fun y' => (cappingSpaceHomeoProj (linCapping (A k) (P k y'))).2) (parOf y k)
      = mfderiv (𝓡 2) (𝓡 3)
        (fun y' => Projectivization.mk ℝ (W k y') (hWne k y')) (parOf y k) := by
    intro k
    refine (Filter.EventuallyEq.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 3)
      (f := fun y' => Projectivization.mk ℝ (W k y') (hWne k y')) ?_).trans (by ext v; rfl)
    filter_upwards [hbox k] with y' hy'
    have h1 := congrFun (cls_linCapping_eq (A k) (P k)) y'
    simp only [Function.comp_apply] at h1
    rw [h1]
    have h2 : (cappingSpaceHomeoProj (P k y')).2
        = Projectivization.mk ℝ (V k y') (hVne k y') := (hVcls k y' hy').symm
    rw [h2]
    exact Projectivization.map_mk (A k : Eucl 3 →ₗ[ℝ] Eucl 3) (hinj k) (V k y') (hVne k y')
  -- 6. the paired difference map and its surjectivity
  let Gp : Tgt 6 → EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) := fun z =>
    (qform (d 0 z) (B p 1 (V 1 (parOf y 1))) + qform (B p 0 (V 0 (parOf y 0))) (d 1 z),
     qform (d 0 z) (B p 2 (V 2 (parOf y 2))) + qform (B p 0 (V 0 (parOf y 0))) (d 2 z))
  have hFderiv : ∀ z : Tgt 6,
      fderiv ℝ (fun y' : Tgt 6 => classSystem V B p y') y z = pair33 (Gp z).1 (Gp z).2 := by
    intro z
    have h := fderiv_classSystem_y V hVsmooth B p y z
    simpa only [Gp, d] using h
  have hGsurj : Function.Surjective Gp := by
    intro w
    obtain ⟨z, hz⟩ := hreg (pair33 w.1 w.2)
    have hpair : pair33 (Gp z).1 (Gp z).2 = pair33 w.1 w.2 := by
      rw [← hFderiv z]; exact hz
    exact ⟨z, pair33_injective hpair⟩
  -- 7. the general position of the three linear maps `π ∘ dV`
  let α : Fin 3 → EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun k => (qformRight v0).comp (K k).toLinearMap
  have hkey : ∀ z : Tgt 6, wDiffMap μ α z = Gp z := by
    intro z
    have hdz : ∀ k, d k z = K k (parCProj k z) := by
      intro k; rw [hdK k]; rfl
    have hαz : ∀ k, α k (parCProj k z) = qform v0 (d k z) := by
      intro k
      show (qformRight v0) ((K k) (parCProj k z)) = qform v0 (d k z)
      rw [← hdz k]
      rfl
    have hq : ∀ k, qform (B p 0 (V 0 (parOf y 0))) (d k z) = qform v0 (d k z) :=
      fun k => rfl
    have hs1 : qform (d 0 z) (B p 1 (V 1 (parOf y 1))) = -(a1 • qform v0 (d 0 z)) := by
      rw [← ha1, qform_smul_right, qform_antisymm', smul_neg]
    have hs2 : qform (d 0 z) (B p 2 (V 2 (parOf y 2))) = -(a2 • qform v0 (d 0 z)) := by
      rw [← ha2, qform_smul_right, qform_antisymm', smul_neg]
    rw [wDiffMap_apply]
    change (α 1 (parCProj 1 z) - μ 1 • α 0 (parCProj 0 z),
          α 2 (parCProj 2 z) - μ 2 • α 0 (parCProj 0 z)) =
        (qform (d 0 z) (B p 1 (V 1 (parOf y 1))) + qform (B p 0 (V 0 (parOf y 0))) (d 1 z),
         qform (d 0 z) (B p 2 (V 2 (parOf y 2))) + qform (B p 0 (V 0 (parOf y 0))) (d 2 z))
    rw [hαz 1, hq 1, hs1, hαz 2, hq 2, hs2, hαz 0,
      show μ 1 = a1 from by simp [μ], show μ 2 = a2 from by simp [μ]]
    refine Prod.ext ?_ ?_ <;> abel
  have hWsurj : Function.Surjective (wDiffMap μ α) := by
    rw [funext hkey]
    exact hGsurj
  obtain ⟨hαinj, hαinf⟩ := weightedDiffMap_generalPosition μ α hWsurj
  have hKgen : ∀ k, Function.Injective (K k) ∧
      LinearMap.range (K k).toLinearMap ⊓ Submodule.span ℝ ({v0} : Set (Eucl 3)) = ⊥ := by
    intro k
    have h := (injective_comp_iff_range_inf_ker (qformRight v0) (K k).toLinearMap).mp (hαinj k)
    rw [qformRight_ker v0 hv0] at h
    exact ⟨h.1, h.2⟩
  -- 8. the immersion of each perturbed class map
  have hcik : ∀ k, Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (fun y' => Projectivization.mk ℝ (W k y') (hWne k y')) (parOf y k)) := by
    intro k
    rw [injective_mfderiv_projMk_iff' (W k) (hWne k) (parOf y k) (hWsmooth k)]
    refine ⟨(hKgen k).1, ?_⟩
    have hspan : Submodule.span ℝ ({W k (parOf y k)} : Set (Eucl 3))
        = Submodule.span ℝ ({v0} : Set (Eucl 3)) := by
      exact (Submodule.span_singleton_eq_span_singleton.mpr
        ⟨Units.mk0 (μ k) (hμ k), by simpa using hvμ k⟩).symm
    rw [hspan]
    exact (hKgen k).2
  -- 9. the general position of the three ranges
  let i0 : Fin 4 := projChartIndexOf
    (Projectivization.mk ℝ (W 0 (parOf y 0)) (hWne 0 (parOf y 0)))
  have hvi : (W 0 (parOf y 0)).ofLp i0 ≠ 0 :=
    (mem_projChartSource_iff' (hWne 0 (parOf y 0))).mp (projChartIndexOf_spec _)
  have hW0 : W 0 (parOf y 0) = v0 := rfl
  have hbase_k : ∀ k, W k (parOf y k) = μ k • W 0 (parOf y 0) := by
    intro k
    rw [hW0]
    exact (hvμ k).symm
  have hrange_k : ∀ k, (mfderiv (𝓡 2) (𝓡 3)
        (fun y' => Projectivization.mk ℝ (W k y') (hWne k y')) (parOf y k)).range
      = Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
          (LinearMap.range (fderiv ℝ (W k) (parOf y k)).toLinearMap) := by
    intro k
    rw [range_mfderiv_projMk (W k) (hWne k) (parOf y k) (hWsmooth k)]
    have hmk : Projectivization.mk ℝ (W k (parOf y k)) (hWne k (parOf y k))
        = Projectivization.mk ℝ (W 0 (parOf y 0)) (hWne 0 (parOf y 0)) :=
      (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
        ⟨Units.mk0 (μ k) (hμ k), by rw [hW0]; simpa using hvμ k⟩
    have hik : projChartIndexOf (Projectivization.mk ℝ (W k (parOf y k)) (hWne k (parOf y k)))
        = i0 := congrArg projChartIndexOf hmk
    rw [hik]
    have hstep : Submodule.map (projCoordFunDerivE i0 (W k (parOf y k))).toLinearMap
          (LinearMap.range (fderiv ℝ (W k) (parOf y k)).toLinearMap)
        = Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
          (LinearMap.range (fderiv ℝ (W k) (parOf y k)).toLinearMap) := by
      rw [hbase_k k]
      exact map_projCoordFunDerivE_smul i0 (W 0 (parOf y 0)) (hμ k)
        (LinearMap.range (fderiv ℝ (W k) (parOf y k)).toLinearMap)
    rw [hstep]
  have hker : (qformRight v0).ker
      = (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap.ker := by
    rw [qformRight_ker v0 hv0]
    ext w
    rw [LinearMap.mem_ker]
    exact (projCoordFunDerivE_eq_zero_iff hvi w).symm
  have hVtriple : Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
          (LinearMap.range (K 0).toLinearMap)
        ⊓ Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
          (LinearMap.range (K 1).toLinearMap)
        ⊓ Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
          (LinearMap.range (K 2).toLinearMap) = ⊥ := by
    rw [← iInf_fin3 (fun k => Submodule.map (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap
      (LinearMap.range (K k).toLinearMap))]
    refine (sameKernel_transfer (qformRight v0)
      (projCoordFunDerivE i0 (W 0 (parOf y 0))).toLinearMap hker
      (qformRight_surjective v0 hv0) (fun k => LinearMap.range (K k).toLinearMap)).1.mp ?_
    have hLHS : (⨅ k, Submodule.map (qformRight v0)
        (LinearMap.range (K k).toLinearMap)) = ⊥ := by
      have heq : (fun k => Submodule.map (qformRight v0)
            (LinearMap.range (K k).toLinearMap)) = fun k => LinearMap.range (α k) := by
        funext k
        show Submodule.map (qformRight v0) (LinearMap.range (K k).toLinearMap)
          = LinearMap.range ((qformRight v0).comp (K k).toLinearMap)
        rw [LinearMap.range_comp]
      rw [heq, hαinf]
    exact hLHS
  have hVfinal : (mfderiv (𝓡 2) (𝓡 3)
        (fun y' => Projectivization.mk ℝ (W 0 y') (hWne 0 y')) (parOf y 0)).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3)
        (fun y' => Projectivization.mk ℝ (W 1 y') (hWne 1 y')) (parOf y 1)).range
      ⊓ (mfderiv (𝓡 2) (𝓡 3)
        (fun y' => Projectivization.mk ℝ (W 2 y') (hWne 2 y')) (parOf y 2)).range = ⊥ := by
    rw [hrange_k 0, hrange_k 1, hrange_k 2]
    exact hVtriple
  -- 10. assembly
  constructor
  · intro k
    rw [mk2_parOf y k, hmf_eq k]
    exact hcik k
  · rw [mk2_parOf y 0, mk2_parOf y 1, mk2_parOf y 2, hmf_eq 0, hmf_eq 1, hmf_eq 2]
    exact hVfinal

end

end Work.Drive
