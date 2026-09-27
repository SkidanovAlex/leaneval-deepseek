import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.CollarDefs
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Noncompact.CompressionTube.exists_collar_of_local_slabs
import Submission.Work.Isotopy.exists_localInverse_param

/-!
# Local slab sections along a compact arc

Local form of `Work.Noncompact.CompressionTube.collar_local_section`: at a point `γ s` of an arc
which carries a transverse coordinate `P` and a height `g` (both satisfying their defining
conditions on a window around `s`), the map `F = (P, g)` has an invertible derivative, and the
inverse function theorem provides a smooth local section of `F` over a slab, whose core is `γ` and
whose image may be taken inside any prescribed open neighbourhood of `γ s`.

All hypotheses are local to `s`; no properness, injectivity or second countability is used.
-/

namespace Work.Noncompact.Routing

open scoped Manifold ContDiff
open Topology Set Function Filter
open Work.Noncompact.CompressionTube

noncomputable section

set_option maxHeartbeats 1600000

/-- **A local slab section of `(P, g)` along the arc.** -/
theorem arc_local_section {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    {s η : ℝ} (hηpos : 0 < η)
    (hP0 : P (γ s) = 0) (hg0 : g (γ s) = s)
    (hPwin : ∀ t : ℝ, |t - s| < η → P (γ t) = 0)
    (hgwin : ∀ t : ℝ, |t - s| < η → g (γ t) = t)
    (htrans : Transverse γ g P s)
    {U : Set M} (hU : IsOpen U) (hγU : γ s ∈ U) :
    ∃ (r ε : ℝ) (σ : CollarParam n → M), 0 < r ∧ 0 < ε ∧ ε ≤ η ∧
      ContMDiffOn (MCprod n) (MC n) smoothOrder σ
        {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
      (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
      (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p) ∧
      (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → σ p ∈ U) := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s)
  have hcγ : γ s ∈ c.source := mem_chart_source _ (γ s)
  have hz0t : c (γ s) ∈ c.target := c.map_source hcγ
  have hcle : c.symm (c (γ s)) = γ s := c.left_inv hcγ
  set eta : M → CollarParam n := (fun x : M => (P x, g x)) with hetadef
  set etahat : EuclideanSpace ℝ (Fin n) → CollarParam n := eta ∘ c.symm with hetahat_def
  let w : TangentSpace (MC n) (c (γ s)) →L[ℝ] TangentSpace (MC n) (γ s) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  have hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  -- componentwise smoothness of the chart expression
  have hP1 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder
      (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z)) c.target :=
    hP.contMDiffOn.comp hcsymm (fun z _ => Set.mem_preimage.mpr (Set.mem_univ (c.symm z)))
  have hg1 : ContMDiffOn (MC n) MCreal smoothOrder
      (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z)) c.target :=
    hg.contMDiffOn.comp hcsymm (fun z _ => Set.mem_preimage.mpr (Set.mem_univ (c.symm z)))
  have hP1' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z)) c.target :=
    contMDiffOn_iff_contDiffOn.mp hP1
  have hg1' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z)) c.target :=
    contMDiffOn_iff_contDiffOn.mp hg1
  have hetahat_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etahat c.target := hP1'.prodMk hg1'
  have hetahat_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etahat (c (γ s)) :=
    hetahat_cd.contDiffAt (c.open_target.mem_nhds hz0t)
  -- injectivity of the chart's inverse differential
  have hcsymm_inj : Function.Injective w := by
    let Φ : PartialDiffeomorph (MC n) (MC n) (EuclideanSpace ℝ (Fin n)) M smoothOrder :=
      { toPartialEquiv := c.symm.toPartialEquiv
        open_source := c.open_target
        open_target := c.open_source
        contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hc
        contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hc }
    have hld : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder
        (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)) :=
      PartialDiffeomorph.isLocalDiffeomorphAt (I := MC n) (J := MC n) (n := smoothOrder)
        (φ := Φ) (x := c (γ s)) (hx := hz0t)
    have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    have hcoe := IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn
    rw [show w = mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
      from rfl, ← hcoe]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hld hn).injective
  -- componentwise chain rule
  have h1 : MDifferentiableAt (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)) :=
    (hcsymm.contMDiffAt (c.open_target.mem_nhds hz0t)).mdifferentiableAt (by simp [smoothOrder])
  have h2 : MDifferentiableAt (MC n) (MC (n - 1)) P (c.symm (c (γ s))) := by
    rw [hcle]; exact hP.mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt (MC n) MCreal g (c.symm (c (γ s))) := by
    rw [hcle]; exact hg.mdifferentiableAt (by simp)
  have hchainP : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z))
      (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (γ s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)))
      (c (γ s)) :=
    ((h2.hasMFDerivAt.comp (c (γ s)) h1.hasMFDerivAt)).hasFDerivAt
  have hchaing : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z))
      (mfderiv (MC n) MCreal g (c.symm (c (γ s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)))
      (c (γ s)) :=
    ((h3.hasMFDerivAt.comp (c (γ s)) h1.hasMFDerivAt)).hasFDerivAt
  have hderiv_inj : Function.Injective (fderiv ℝ etahat (c (γ s))) := by
    have hpair := hchainP.prodMk hchaing
    have hD : fderiv ℝ etahat (c (γ s)) =
        (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (γ s))) ∘SL w).prod
          (mfderiv (MC n) MCreal g (c.symm (c (γ s))) ∘SL w) := hpair.fderiv
    rw [hcle] at hD
    have hTinj : Function.Injective
        ((mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w).prod
          (mfderiv (MC n) MCreal g (γ s) ∘SL w)) := by
      intro y y' hyy'
      have h1 : (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) y
          = (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.fst hyy'
      have h2 : (mfderiv (MC n) MCreal g (γ s) ∘SL w) y
          = (mfderiv (MC n) MCreal g (γ s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.snd hyy'
      have h3 : mfderiv (MC n) (MC (n - 1)) P (γ s) (w (y - y')) = 0 := by
        have hA0 : (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h1, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hA0
      have h4 : mfderiv (MC n) MCreal g (γ s) (w (y - y')) = 0 := by
        have hB0 : (mfderiv (MC n) MCreal g (γ s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h2, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hB0
      have h5 : w (y - y') = 0 := htrans (w (y - y')) h3 h4
      have h6 : y - y' = 0 := hcsymm_inj (by simpa using h5)
      exact sub_eq_zero.mp h6
    rw [hD]
    exact hTinj
  -- the derivative as a linear equivalence and the partial homeomorphism
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (CollarParam n) := by
    simp only [CollarParam, Module.finrank_prod, finrank_euclideanSpace, Module.finrank_self,
      Fintype.card_fin]
    omega
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_of_injective hdim
    (fderiv ℝ etahat (c (γ s))) hderiv_inj
  have hL' : HasFDerivAt etahat (L : EuclideanSpace ℝ (Fin n) →L[ℝ] CollarParam n) (c (γ s)) :=
    HasFDerivAt.congr_fderiv (hetahat_at.differentiableAt (by simp)).hasFDerivAt hL.symm
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (CollarParam n) :=
    hetahat_at.toOpenPartialHomeomorph etahat hL' hn0 with hφdef
  have hφcoe : (φ : EuclideanSpace ℝ (Fin n) → CollarParam n) = etahat :=
    ContDiffAt.toOpenPartialHomeomorph_coe hetahat_at hL' hn0
  have hz0φ : c (γ s) ∈ φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hetahat_at hL' hn0
  have h0sφ : etahat (c (γ s)) ∈ φ.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hetahat_at hL' hn0
  have hz0s : etahat (c (γ s)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) := by
    show eta (c.symm (c (γ s))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
    rw [c.left_inv hcγ, hetadef]
    exact Prod.ext hP0 hg0
  -- the parametric inverse function theorem
  set G : ℝ × EuclideanSpace ℝ (Fin n) → CollarParam n := fun sz => etahat sz.2 with hGdef
  have hGcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.univ ×ˢ c.target) := by
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) (Set.univ ×ˢ c.target) := contDiffOn_snd
    exact hetahat_cd.comp h2 (fun sz hsz => hsz.2)
  have hGinj : Function.Injective
      (fun v : EuclideanSpace ℝ (Fin n) => fderiv ℝ G ((0 : ℝ), c (γ s)) (0, v)) := by
    have hfd2 : fderiv ℝ G ((0 : ℝ), c (γ s)) =
        (fderiv ℝ etahat (c (γ s))).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) := by
      have h1 : HasFDerivAt (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2)
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) ((0 : ℝ), c (γ s)) :=
        hasFDerivAt_snd
      have h2 : HasFDerivAt etahat (fderiv ℝ etahat (c (γ s)))
          ((fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) ((0 : ℝ), c (γ s))) :=
        (hetahat_at.differentiableAt (by simp)).hasFDerivAt
      exact (h2.comp ((0 : ℝ), c (γ s)) h1).fderiv
    intro v v' hvv
    rw [hfd2] at hvv
    simp only [ContinuousLinearMap.comp_apply] at hvv
    exact hderiv_inj (by simpa using hvv)
  obtain ⟨O, Udom, W, h, hOo, h0O, hUdomo, hz0Udom, hWo, hGs0W, hV, huncurry, hGmaps, hleft⟩ :=
    Work.Isotopy.exists_localInverse_param (E := EuclideanSpace ℝ (Fin n))
      (F := CollarParam n) G (Set.univ ×ˢ c.target) (isOpen_univ.prod c.open_target)
      (0 : ℝ) (c (γ s)) ⟨trivial, hz0t⟩ hGcd c.target c.open_target hz0t hGinj
  have hhsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h 0) W := by
    have hinner : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w' : CollarParam n => ((0 : ℝ), w')) W := contDiffOn_const.prodMk contDiffOn_id
    have hres := huncurry.comp hinner (fun w' hw' => ⟨h0O, hw'⟩)
    have hfun : (Function.uncurry h ∘ fun w' : CollarParam n => ((0 : ℝ), w'))
        = fun w' => h 0 w' := by
      funext w'; rfl
    rw [hfun] at hres
    exact hres
  have hz0φsymm : φ.symm (etahat (c (γ s))) = c (γ s) := by
    have h1 : φ (c (γ s)) = etahat (c (γ s)) := by rw [hφcoe]
    rw [← h1]
    exact φ.left_inv hz0φ
  have hagree : ∀ p : CollarParam n, p ∈ φ.target → φ.symm p ∈ Udom → φ.symm p = h 0 p := by
    intro p hp hUp
    have h1 : G (0, φ.symm p) = p := by
      show etahat (φ.symm p) = p
      rw [← hφcoe]
      exact φ.right_inv hp
    have h3 := hleft 0 h0O (φ.symm p) hUp
    rw [h1] at h3
    exact h3.symm
  have hφsymm_cont : ContinuousAt (φ.symm) (etahat (c (γ s))) :=
    (φ.continuousOn_invFun).continuousAt (φ.open_target.mem_nhds h0sφ)
  have hUmem : φ.symm ⁻¹' Udom ∈ 𝓝 (etahat (c (γ s))) := by
    refine hφsymm_cont.preimage_mem_nhds (hUdomo.mem_nhds ?_)
    rw [hz0φsymm]
    exact hz0Udom
  have hS : {p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ Udom} ∈ 𝓝 (etahat (c (γ s))) :=
    Filter.inter_mem (φ.open_target.mem_nhds h0sφ) hUmem
  have hbox : ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ Udom} ∩ W) ∈ 𝓝 (etahat (c (γ s))) :=
    Filter.inter_mem hS (hWo.mem_nhds hGs0W)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hbox
  have hγcont : Continuous γ := hγ.continuous
  have hcore_nhds : (fun t : ℝ => c (γ t)) ⁻¹' φ.source ∈ 𝓝 s :=
    ((c.continuousAt hcγ).comp hγcont.continuousAt) (φ.open_source.mem_nhds hz0φ)
  have hcsrc_nhds : γ ⁻¹' c.source ∈ 𝓝 s :=
    hγcont.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hcγ)
  obtain ⟨ε0, hε0pos, hε0sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hcore_nhds hcsrc_nhds)
  -- the final slab radii
  set ε₁ : ℝ := min (min (ρ / 2) ε0) η with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min (lt_min (by linarith) hε0pos) hηpos
  have hε₁η : ε₁ ≤ η := min_le_right _ _
  have hε₁ε0 : ε₁ ≤ ε0 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε₁ρ : ε₁ ≤ ρ / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  -- the smoothness of the section on the slab
  have hslab : {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁}
      ⊆ {p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ Udom} ∩ W := by
    intro p hp
    have hdist : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp.1]
      · rw [Real.dist_eq]; linarith [hp.2, hε₁ρ]
    exact hρsub (by rw [hz0s]; exact hdist)
  have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm)
      ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ Udom} ∩ W) := by
    refine (hhsm.mono Set.inter_subset_right).congr ?_
    intro p hp
    exact hagree p hp.1.1 hp.1.2
  have hsm2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
      (φ.symm) ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ Udom} ∩ W) :=
    contMDiffOn_iff_contDiffOn.mpr hsm1
  have hsm3 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
      (φ.symm) {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁} :=
    hsm2.mono hslab
  have hmaps : ∀ p ∈ {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁},
      φ.symm p ∈ c.target := by
    intro p hp
    have hp' := hslab hp
    have h1 : h 0 p ∈ c.target := hV 0 h0O p hp'.2
    rw [hagree p hp'.1.1 hp'.1.2]
    exact h1
  have hσsm : ContMDiffOn (MCprod n) (MC n) smoothOrder (fun p => c.symm (φ.symm p))
      {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁} := by
    have hcomp := hcsymm.comp hsm3 hmaps
    rw [← prodModel_eq_self (n := n)] at hcomp
    exact hcomp
  -- the core property
  have hcoreσ : ∀ t : ℝ, |t - s| < ε₁ → c.symm (φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) = γ t := by
    intro t ht
    have hmem : dist t s < ε0 := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le ht hε₁ε0
    have hsrc : γ t ∈ c.source := (hε0sub hmem).2
    have hφsrc : c (γ t) ∈ φ.source := (hε0sub hmem).1
    have htη : |t - s| < η := lt_of_lt_of_le ht hε₁η
    have hetacγ : etahat (c (γ t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
      show eta (c.symm (c (γ t))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)
      rw [c.left_inv hsrc, hetadef]
      exact Prod.ext (hPwin t htη) (hgwin t htη)
    have hsymm_eq : φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = c (γ t) := by
      have h1 : φ (c (γ t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
        rw [hφcoe]
        exact hetacγ
      have h2 : φ.symm (φ (c (γ t))) = c (γ t) := φ.left_inv hφsrc
      rwa [h1] at h2
    rw [hsymm_eq]
    exact c.left_inv hsrc
  -- the section property
  have hsectσ : ∀ p : CollarParam n, ‖p.1‖ < ρ / 2 → |p.2 - s| < ε₁ →
      (P (c.symm (φ.symm p)), g (c.symm (φ.symm p))) = p := by
    intro p hp1 hp2
    have hd : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp1]
      · rw [Real.dist_eq]; linarith [hp2, hε₁ρ]
    have hp' := hρsub (by rw [hz0s]; exact hd)
    have h1 : etahat (φ.symm p) = p := by
      rw [← hφcoe]
      exact φ.right_inv hp'.1.1
    show (P (c.symm (φ.symm p)), g (c.symm (φ.symm p))) = p
    change etahat (φ.symm p) = p
    exact h1
  -- the image of the slab lies in `U`
  have hmem_slab : ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) ∈
      {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁} := by
    refine ⟨by simpa using (by linarith : (0:ℝ) < ρ / 2), by simpa using hε₁pos⟩
  have hslab_open : IsOpen {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < ε₁} :=
    (isOpen_lt continuous_fst.norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const)
  have hσcont : ContinuousAt (fun p => c.symm (φ.symm p))
      ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) :=
    (hσsm.contMDiffAt (hslab_open.mem_nhds hmem_slab)).continuousAt
  have hσs : c.symm (φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) = γ s := by
    have h1 : φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = c (γ s) := by
      rw [← hz0s]
      exact hz0φsymm
    rw [h1]
    exact c.left_inv hcγ
  obtain ⟨δ, hδpos, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (hσcont.preimage_mem_nhds (hU.mem_nhds (hσs ▸ hγU)))
  refine ⟨min (ρ / 2) (δ / 2), min ε₁ (δ / 2), fun p => c.symm (φ.symm p),
    lt_min (by linarith) (by linarith), lt_min hε₁pos (by linarith),
    le_trans (min_le_left ε₁ (δ / 2)) hε₁η, ?_, ?_, ?_, ?_⟩
  · refine hσsm.mono ?_
    intro p hp
    exact ⟨lt_of_lt_of_le hp.1 (min_le_left _ _), lt_of_lt_of_le hp.2 (min_le_left _ _)⟩
  · intro t ht
    exact hcoreσ t (lt_of_lt_of_le ht (min_le_left _ _))
  · intro p hp1 hp2
    exact hsectσ p (lt_of_lt_of_le hp1 (min_le_left _ _)) (lt_of_lt_of_le hp2 (min_le_left _ _))
  · intro p hp1 hp2
    refine hδsub ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [dist_eq_norm, sub_zero]
      linarith [hp1, min_le_right (ρ / 2) (δ / 2), hδpos]
    · rw [Real.dist_eq]
      show |p.2 - s| < δ
      linarith [hp2, min_le_right ε₁ (δ / 2), hδpos]

end

end Work.Noncompact.Routing
