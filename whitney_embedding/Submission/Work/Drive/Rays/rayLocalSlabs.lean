import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CollarDefs
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Isotopy.exists_localInverse_param

/-!
# One-sided local slabs of the pair `(P, g)` along a proper embedded ray

This file proves the one-sided version of
`Work.Noncompact.CompressionTube.local_section_of_pair`: along a ray `r : ℝ → M` which is
smooth only on `Set.Ici 0`, a pair `(P, g) : M → ℝ^{n-1} × ℝ` with `P (r t) = 0`, `g (r t) = t`
for `t ≥ 0` and whose derivatives along `r` have trivial common kernel, is a local
diffeomorphism near `r s` for every `s ≥ 0`, in a way which is uniform in `s` on compact pieces.
The point of the one-sided statement is that only the values of `r` on `[0, ∞)` are used, which
is what a ray (rather than a line) provides.
-/

namespace Work.Drive.Rays

open scoped Manifold ContDiff Topology
open Work.Noncompact.CompressionTube

noncomputable section

/-- The product model with corners on `ℝ^{n-1} × ℝ` is the self model with corners. -/
theorem MCprod_eq_selfC (n : ℕ) :
    MCprod n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1)))
    (F := ℝ)).symm

set_option maxHeartbeats 1600000 in
/-- **The one-sided local section of the pair `(P, g)` at `s ≥ 0`.**

For `s ≥ 0` there is a radius `ρ > 0` and a smooth map `σ` on the slab
`{‖p.1‖ < ρ, |p.2 - s| < ρ}` which is a local inverse of `(P, g)`, has core `r` on `[0, ∞)`, and
whose image is contained in the given open set `W ⊇ r ([0, ∞))`. -/
theorem oneSidedLocalSection {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    (hgcore : ∀ t : ℝ, 0 ≤ t → g (r t) = t)
    (hPcore : ∀ t : ℝ, 0 ≤ t → P (r t) = 0)
    (hrW : ∀ t : ℝ, 0 ≤ t → r t ∈ W)
    (htrans : ∀ t : ℝ, 0 ≤ t → ∀ v : TangentSpace (MC n) (r t),
      mfderiv (MC n) (MC (n - 1)) P (r t) v = 0 →
      mfderiv (MC n) MCreal g (r t) v = 0 → v = 0)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ (ρ : ℝ), 0 < ρ ∧ ∃ (σ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M),
      ContMDiffOn (MCprod n) (MC n) smoothOrder σ
        {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < ρ ∧ |p.2 - s| < ρ} ∧
      (∀ t : ℝ, 0 ≤ t → |t - s| < ρ →
        σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ < ρ → |p.2 - s| < ρ →
        (P (σ p), g (σ p)) = p) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ < ρ → |p.2 - s| < ρ → σ p ∈ W) := by
  classical
  have hrcont : ContinuousWithinAt r (Set.Ici (0:ℝ)) s :=
    hrsm.continuousOn.continuousWithinAt hs
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (r s) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (r s)
  have hcr : r s ∈ c.source := mem_chart_source _ (r s)
  have hz0t : c (r s) ∈ c.target := c.map_source hcr
  have hcle : c.symm (c (r s)) = r s := c.left_inv hcr
  set eta : M → EuclideanSpace ℝ (Fin (n - 1)) × ℝ := (fun x : M => (P x, g x)) with hetadef
  set etahat : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    eta ∘ c.symm with hetahat_def
  let w : TangentSpace (MC n) (c (r s)) →L[ℝ] TangentSpace (MC n) (r s) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s))
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
  have hetahat_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etahat (c (r s)) :=
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
        (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s)) :=
      PartialDiffeomorph.isLocalDiffeomorphAt (I := MC n) (J := MC n) (n := smoothOrder)
        (φ := Φ) (x := c (r s)) (hx := hz0t)
    have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    have hcoe := IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn
    rw [show w = mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s))
      from rfl, ← hcoe]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hld hn).injective
  -- componentwise chain rule
  have h1 : MDifferentiableAt (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s)) :=
    (hcsymm.contMDiffAt (c.open_target.mem_nhds hz0t)).mdifferentiableAt (by simp [smoothOrder])
  have h2 : MDifferentiableAt (MC n) (MC (n - 1)) P (c.symm (c (r s))) := by
    rw [hcle]; exact hP.mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt (MC n) MCreal g (c.symm (c (r s))) := by
    rw [hcle]; exact hg.mdifferentiableAt (by simp)
  have hchainP : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z))
      (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (r s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s)))
      (c (r s)) :=
    ((h2.hasMFDerivAt.comp (c (r s)) h1.hasMFDerivAt)).hasFDerivAt
  have hchaing : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z))
      (mfderiv (MC n) MCreal g (c.symm (c (r s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (r s)))
      (c (r s)) :=
    ((h3.hasMFDerivAt.comp (c (r s)) h1.hasMFDerivAt)).hasFDerivAt
  have hderiv_inj : Function.Injective (fderiv ℝ etahat (c (r s))) := by
    have hpair := hchainP.prodMk hchaing
    have hD : fderiv ℝ etahat (c (r s)) =
        (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (r s))) ∘SL w).prod
          (mfderiv (MC n) MCreal g (c.symm (c (r s))) ∘SL w) := hpair.fderiv
    rw [hcle] at hD
    have hTinj : Function.Injective
        ((mfderiv (MC n) (MC (n - 1)) P (r s) ∘SL w).prod
          (mfderiv (MC n) MCreal g (r s) ∘SL w)) := by
      intro y y' hyy'
      have h1 : (mfderiv (MC n) (MC (n - 1)) P (r s) ∘SL w) y
          = (mfderiv (MC n) (MC (n - 1)) P (r s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.fst hyy'
      have h2 : (mfderiv (MC n) MCreal g (r s) ∘SL w) y
          = (mfderiv (MC n) MCreal g (r s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.snd hyy'
      have h3 : mfderiv (MC n) (MC (n - 1)) P (r s) (w (y - y')) = 0 := by
        have hA0 : (mfderiv (MC n) (MC (n - 1)) P (r s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h1, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hA0
      have h4 : mfderiv (MC n) MCreal g (r s) (w (y - y')) = 0 := by
        have hB0 : (mfderiv (MC n) MCreal g (r s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h2, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hB0
      have h5 : w (y - y') = 0 := htrans s hs (w (y - y')) h3 h4
      have h6 : y - y' = 0 := hcsymm_inj (by simpa using h5)
      exact sub_eq_zero.mp h6
    rw [hD]
    exact hTinj
  -- the derivative as a linear equivalence and the partial homeomorphism
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Module.finrank_self,
      Fintype.card_fin]
    omega
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_of_injective hdim
    (fderiv ℝ etahat (c (r s))) hderiv_inj
  have hL' : HasFDerivAt etahat
      (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (c (r s)) :=
    HasFDerivAt.congr_fderiv (hetahat_at.differentiableAt (by simp)).hasFDerivAt hL.symm
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
    hetahat_at.toOpenPartialHomeomorph etahat hL' hn0 with hφdef
  have hφcoe : (φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
      = etahat :=
    ContDiffAt.toOpenPartialHomeomorph_coe hetahat_at hL' hn0
  have hz0φ : c (r s) ∈ φ.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hetahat_at hL' hn0
  have h0sφ : etahat (c (r s)) ∈ φ.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hetahat_at hL' hn0
  have h0s : etahat (c (r s)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) := by
    show eta (c.symm (c (r s))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
    rw [hcle, hetadef]
    exact Prod.ext (hPcore s hs) (hgcore s hs)
  -- the parametric inverse function theorem
  set G : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun sz => etahat sz.2 with hGdef
  have hGcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.univ ×ˢ c.target) := by
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) (Set.univ ×ˢ c.target) :=
      contDiffOn_snd
    exact hetahat_cd.comp h2 (fun sz hsz => hsz.2)
  have hGinj : Function.Injective
      (fun v : EuclideanSpace ℝ (Fin n) => fderiv ℝ G ((0 : ℝ), c (r s)) (0, v)) := by
    have hfd2 : fderiv ℝ G ((0 : ℝ), c (r s)) =
        (fderiv ℝ etahat (c (r s))).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) := by
      have h1 : HasFDerivAt (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2)
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) ((0 : ℝ), c (r s)) :=
        hasFDerivAt_snd
      have h2 : HasFDerivAt etahat (fderiv ℝ etahat (c (r s)))
          ((fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) ((0 : ℝ), c (r s))) :=
        (hetahat_at.differentiableAt (by simp)).hasFDerivAt
      exact (h2.comp ((0 : ℝ), c (r s)) h1).fderiv
    intro v v' hvv
    rw [hfd2] at hvv
    simp only [ContinuousLinearMap.comp_apply] at hvv
    exact hderiv_inj (by simpa using hvv)
  obtain ⟨O, U, W', h, hOo, h0O, hUo, hz0U, hW'o, hGs0W', hV, huncurry, hGmaps, hleft⟩ :=
    Work.Isotopy.exists_localInverse_param (E := EuclideanSpace ℝ (Fin n))
      (F := EuclideanSpace ℝ (Fin (n - 1)) × ℝ) G (Set.univ ×ˢ c.target)
      (isOpen_univ.prod c.open_target) (0 : ℝ) (c (r s)) ⟨trivial, hz0t⟩ hGcd
      c.target c.open_target hz0t hGinj
  have hhsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h 0) W' := by
    have hinner : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w' : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((0 : ℝ), w')) W' :=
      contDiffOn_const.prodMk contDiffOn_id
    have hres := huncurry.comp hinner (fun w' hw' => ⟨h0O, hw'⟩)
    have hfun : (Function.uncurry h ∘ fun w' : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((0 : ℝ), w'))
        = fun w' => h 0 w' := by
      funext w'; rfl
    rw [hfun] at hres
    exact hres
  have hz0φsymm : φ.symm (etahat (c (r s))) = c (r s) := by
    have h1 : φ (c (r s)) = etahat (c (r s)) := by rw [hφcoe]
    rw [← h1]
    exact φ.left_inv hz0φ
  have hagree : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, p ∈ φ.target →
      φ.symm p ∈ U → φ.symm p = h 0 p := by
    intro p hp hUp
    have h1 : G (0, φ.symm p) = p := by
      show etahat (φ.symm p) = p
      rw [← hφcoe]
      exact φ.right_inv hp
    have h3 := hleft 0 h0O (φ.symm p) hUp
    rw [h1] at h3
    exact h3.symm
  have hφsymm_cont : ContinuousAt (φ.symm) (etahat (c (r s))) :=
    (φ.continuousOn_invFun).continuousAt (φ.open_target.mem_nhds h0sφ)
  have hUmem : φ.symm ⁻¹' U ∈ 𝓝 (etahat (c (r s))) := by
    refine hφsymm_cont.preimage_mem_nhds (hUo.mem_nhds ?_)
    rw [hz0φsymm]
    exact hz0U
  have hS : {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p ∈ φ.target ∧ φ.symm p ∈ U}
      ∈ 𝓝 (etahat (c (r s))) :=
    Filter.inter_mem (φ.open_target.mem_nhds h0sφ) hUmem
  have hbox : ({p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W')
      ∈ 𝓝 (etahat (c (r s))) :=
    Filter.inter_mem hS (hW'o.mem_nhds hGs0W')
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hbox
  -- the one-sided neighbourhood of `s` on which the ray is transported by the chart
  have hcore_nhds : (fun t : ℝ => c (r t)) ⁻¹' φ.source ∈ 𝓝[Set.Ici (0:ℝ)] s :=
    ((c.continuousAt hcr).comp_continuousWithinAt hrcont).preimage_mem_nhdsWithin
      (φ.open_source.mem_nhds hz0φ)
  have hcsrc_nhds : r ⁻¹' c.source ∈ 𝓝[Set.Ici (0:ℝ)] s :=
    hrcont.preimage_mem_nhdsWithin (c.open_source.mem_nhds hcr)
  obtain ⟨ε0, hε0pos, hε0sub⟩ :=
    Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hcore_nhds hcsrc_nhds)
  set ρ0 : ℝ := min (ρ / 2) ε0 with hρ0def
  have hρ0pos : 0 < ρ0 := lt_min (by linarith) hε0pos
  have hρ0half : ρ0 ≤ ρ / 2 := min_le_left _ _
  have hρ0ε : ρ0 ≤ ε0 := min_le_right _ _
  have hρ0ρ : ρ0 < ρ := by linarith
  -- Step 1: the smooth local section on the slab of radius `ρ0`
  have hslab : {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < ρ0 ∧ |p.2 - s| < ρ0}
      ⊆ ({p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W') := by
    intro p hp
    have hdist : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp.1, hρ0ρ]
      · rw [Real.dist_eq]; linarith [hp.2, hρ0ρ]
    exact hρsub (by rw [h0s]; exact hdist)
  have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm)
      ({p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W') := by
    refine (hhsm.mono Set.inter_subset_right).congr ?_
    intro p hp
    exact hagree p hp.1.1 hp.1.2
  have hsm2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
      (φ.symm)
      ({p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W') :=
    contMDiffOn_iff_contDiffOn.mpr hsm1
  have hsm3 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
      (φ.symm) {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < ρ0 ∧ |p.2 - s| < ρ0} :=
    hsm2.mono hslab
  have hmaps : ∀ p ∈ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < ρ0 ∧ |p.2 - s| < ρ0},
      φ.symm p ∈ c.target := by
    intro p hp
    have hp' := hslab hp
    have h1 : h 0 p ∈ c.target := hV 0 h0O p hp'.2
    rw [hagree p hp'.1.1 hp'.1.2]
    exact h1
  have hsm0 : ContMDiffOn (MCprod n) (MC n) smoothOrder (fun p => c.symm (φ.symm p))
      {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < ρ0 ∧ |p.2 - s| < ρ0} := by
    have hcomp := hcsymm.comp hsm3 hmaps
    rw [← MCprod_eq_selfC (n := n)] at hcomp
    exact hcomp
  have hcore0 : ∀ t : ℝ, 0 ≤ t → |t - s| < ρ0 →
      (fun p => c.symm (φ.symm p)) ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t := by
    intro t ht hts
    have hmem : dist t s < ε0 := by
      rw [Real.dist_eq]; linarith [hts, hρ0ε]
    have hsub := hε0sub ⟨hmem, ht⟩
    have hsrc : r t ∈ c.source := hsub.2
    have hφsrc : c (r t) ∈ φ.source := hsub.1
    have hetac : etahat (c (r t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
      show eta (c.symm (c (r t))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)
      rw [c.left_inv hsrc, hetadef]
      exact Prod.ext (hPcore t ht) (hgcore t ht)
    have hsymm_eq : φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = c (r t) := by
      have h1 : φ (c (r t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
        rw [hφcoe]
        exact hetac
      have h2 : φ.symm (φ (c (r t))) = c (r t) := φ.left_inv hφsrc
      rwa [h1] at h2
    show c.symm (φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) = r t
    rw [hsymm_eq]
    exact c.left_inv hsrc
  have hsec0 : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ < ρ0 → |p.2 - s| < ρ0 →
      (P ((fun p => c.symm (φ.symm p)) p), g ((fun p => c.symm (φ.symm p)) p)) = p := by
    intro p hp1 hp2
    have hd : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp1, hρ0ρ]
      · rw [Real.dist_eq]; linarith [hp2, hρ0ρ]
    have hp' := hρsub (by rw [h0s]; exact hd)
    have h1 : etahat (φ.symm p) = p := by
      rw [← hφcoe]
      exact φ.right_inv hp'.1.1
    simpa only [hetahat_def, hetadef, Function.comp_def] using h1
  -- Step 2: shrink the slab so that its image lies in the open set `W`
  have hσcont : ContinuousAt (fun p => c.symm (φ.symm p))
      (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) := by
    refine (hsm0.continuousOn).continuousAt ?_
    rw [Metric.mem_nhds_iff]
    refine ⟨ρ0, hρ0pos, ?_⟩
    intro p hp
    have hpball : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ0 :=
      Metric.mem_ball.mp hp
    have hp' : max (dist p.1 (0 : EuclideanSpace ℝ (Fin (n - 1)))) (dist p.2 s) < ρ0 := by
      rwa [Prod.dist_eq] at hpball
    exact ⟨by simpa [dist_eq_norm] using lt_of_le_of_lt (le_max_left _ _) hp',
      by simpa [Real.dist_eq] using lt_of_le_of_lt (le_max_right _ _) hp'⟩
  have hσ0s : (fun p => c.symm (φ.symm p))
      (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) = r s :=
    hcore0 s hs (by rw [sub_self, abs_zero]; exact hρ0pos)
  have hσ0s' : c.symm (φ.symm (((0 : EuclideanSpace ℝ (Fin (n - 1))), s))) = r s := by
    simpa using hσ0s
  have hWnhds : (fun p => c.symm (φ.symm p)) ⁻¹' W
      ∈ 𝓝 (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) :=
    hσcont.preimage_mem_nhds (by rw [hσ0s']; exact hW.mem_nhds (hrW s hs))
  obtain ⟨ρ2, hρ2pos, hρ2sub⟩ := Metric.mem_nhds_iff.mp hWnhds
  set δ : ℝ := min (ρ0 / 2) ρ2 with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) hρ2pos
  have hδρ0 : δ < ρ0 := by
    have h1 : δ ≤ ρ0 / 2 := min_le_left _ _
    linarith
  have hδρ2 : δ ≤ ρ2 := min_le_right _ _
  refine ⟨δ, hδpos, fun p => c.symm (φ.symm p), ?_, ?_, ?_, ?_⟩
  · refine hsm0.mono ?_
    rintro p ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h1 (le_of_lt hδρ0), lt_of_lt_of_le h2 (le_of_lt hδρ0)⟩
  · intro t ht hts
    exact hcore0 t ht (lt_of_lt_of_le hts (le_of_lt hδρ0))
  · intro p hp1 hp2
    exact hsec0 p (lt_of_lt_of_le hp1 (le_of_lt hδρ0)) (lt_of_lt_of_le hp2 (le_of_lt hδρ0))
  · intro p hp1 hp2
    have hd : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ2 := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp1, hδρ2]
      · rw [Real.dist_eq]; linarith [hp2, hδρ2]
    exact hρ2sub hd

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
/-- One-sided local slabs of the pair `(P, g) = (P, g) : M → ℝ^{n-1} × ℝ` along a proper embedded
ray `r`. -/
theorem rayLocalSlabs {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) {r : ℝ → M}
    (hrsm : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    (hgcore : ∀ t : ℝ, 0 ≤ t → g (r t) = t)
    (hPcore : ∀ t : ℝ, 0 ≤ t → P (r t) = 0)
    (hrW : ∀ t : ℝ, 0 ≤ t → r t ∈ W)
    (htrans : ∀ t : ℝ, 0 ≤ t → ∀ v : TangentSpace (MC n) (r t),
      mfderiv (MC n) (MC (n - 1)) P (r t) v = 0 →
      mfderiv (MC n) MCreal g (r t) v = 0 → v = 0) :
    ∃ (rad eps : ℝ → ℝ) (σ : ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M),
      (∀ s : ℝ, 0 ≤ s → 0 < rad s) ∧ (∀ s : ℝ, 0 < eps s) ∧
      (∀ s : ℝ, 0 ≤ s → ContMDiffOn (MCprod n) (MC n) smoothOrder (σ s)
        {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < rad s ∧ |p.2 - s| < eps s}) ∧
      (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| < eps s →
        σ s ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t) ∧
      (∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ), 0 ≤ s →
        ‖p.1‖ < rad s → |p.2 - s| < eps s → (P (σ s p), g (σ s p)) = p) ∧
      (∀ (s : ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ), 0 ≤ s →
        ‖p.1‖ < rad s → |p.2 - s| < eps s → σ s p ∈ W) := by
  classical
  have hkey : ∀ s : ℝ, ∃ z : ℝ × (EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M),
      0 < z.1 ∧
      (0 ≤ s → ContMDiffOn (MCprod n) (MC n) smoothOrder z.2
        {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ < z.1 ∧ |p.2 - s| < z.1}) ∧
      (0 ≤ s → ∀ t : ℝ, 0 ≤ t → |t - s| < z.1 →
        z.2 ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = r t) ∧
      (0 ≤ s → ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        ‖p.1‖ < z.1 → |p.2 - s| < z.1 → (P (z.2 p), g (z.2 p)) = p) ∧
      (0 ≤ s → ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        ‖p.1‖ < z.1 → |p.2 - s| < z.1 → z.2 p ∈ W) := by
    intro s
    by_cases hs : 0 ≤ s
    · obtain ⟨ρ, hρ, σ, hA, hB, hC, hD⟩ :=
        oneSidedLocalSection hn hW hrsm hg hP hgcore hPcore hrW htrans s hs
      exact ⟨(ρ, σ), hρ, fun _ => hA, fun _ => hB, fun _ => hC, fun _ => hD⟩
    · exact ⟨(1, fun _ => r 0), one_pos, fun h => absurd h hs, fun h => absurd h hs,
        fun h => absurd h hs, fun h => absurd h hs⟩
  let rad : ℝ → ℝ := fun s => (Classical.choose (hkey s)).1
  let σ : ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M := fun s => (Classical.choose (hkey s)).2
  refine ⟨rad, rad, σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (Classical.choose_spec (hkey s)).1
  · intro s
    exact (Classical.choose_spec (hkey s)).1
  · intro s hs
    exact (Classical.choose_spec (hkey s)).2.1 hs
  · intro s t hs ht hts
    exact (Classical.choose_spec (hkey s)).2.2.1 hs t ht hts
  · intro s p hs hp1 hp2
    exact (Classical.choose_spec (hkey s)).2.2.2.1 hs p hp1 hp2
  · intro s p hs hp1 hp2
    exact (Classical.choose_spec (hkey s)).2.2.2.2 hs p hp1 hp2

end

end Work.Drive.Rays
