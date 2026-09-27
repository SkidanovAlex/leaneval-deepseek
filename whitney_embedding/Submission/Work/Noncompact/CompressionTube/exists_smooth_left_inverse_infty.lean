import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.smooth_left_inverse_tools
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Whitney.exists_sheet_model

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

/-- **Local smooth left inverse of a smooth immersed curve.**

Let `γ : ℝ → M` be a smooth curve in a smooth `n`-manifold whose derivative is injective at `s`
(so that `t ↦ (c (γ t)) j` is a local diffeomorphism of `ℝ` for a suitable chart `c` at `γ s` and
a suitable coordinate `j`).  Then `γ s` has an open neighbourhood `U` carrying a smooth function
`F` with `F (γ t) = t` whenever `γ t ∈ U`.

Only the closedness of `range γ` (a consequence of properness) is used beyond the smoothness of
`γ` at `s`. -/
theorem exists_local_left_inverse {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) infOrder M]
    [T2Space M] [SecondCountableTopology M] {γ : ℝ → M}
    (hγ : ContMDiff MCreal (MC n) infOrder γ) (hprop : IsProperMap γ)
    (hinj : Function.Injective γ)
    (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s)) (s : ℝ) :
    ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ γ s ∈ U ∧
      ContMDiffOn (MC n) MCreal infOrder F U ∧ ∀ t : ℝ, γ t ∈ U → F (γ t) = t := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s) with hc_def
  have hc : c ∈ IsManifold.maximalAtlas (MC n) infOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s)
  have hmem : γ s ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) (γ s)
  have hI : IsOpen (γ ⁻¹' c.source) := c.open_source.preimage hγ.continuous
  have hsI : s ∈ γ ⁻¹' c.source := hmem
  -- the chart expression of `γ` is smooth on a neighbourhood of `s`
  have hh_smooth : ContDiffOn ℝ infOrder (fun t => c (γ t)) (γ ⁻¹' c.source) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_of_mem_maximalAtlas hc).comp hγ.contMDiffOn (fun t ht => ht))
  have hh_inj : Function.Injective (fderiv ℝ (fun t => c (γ t)) s) :=
    injective_fderiv_chart_comp hγ hc himm hmem
  -- pick a chart coordinate in which the derivative is nonzero
  have hne : fderiv ℝ (fun t => c (γ t)) s 1 ≠ 0 := fun h0 =>
    one_ne_zero (hh_inj (by rw [h0, map_zero]))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (fderiv ℝ (fun t => c (γ t)) s 1) j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (PiLp.ext hcon)
  let u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) j
  have hu_apply : ∀ y : EuclideanSpace ℝ (Fin n), u y = y j := fun y => by
    simp [u, PiLp.proj_apply]
  -- the corresponding scalar coordinate function
  have hG_smooth : ContDiffOn ℝ infOrder (fun t => u (c (γ t))) (γ ⁻¹' c.source) :=
    u.contDiff.comp_contDiffOn hh_smooth
  have hG_fderiv : fderiv ℝ (fun t => u (c (γ t))) s =
      u ∘L fderiv ℝ (fun t => c (γ t)) s := by
    have hhat : HasFDerivAt (fun t => c (γ t)) (fderiv ℝ (fun t => c (γ t)) s) s :=
      (hh_smooth.contDiffAt (hI.mem_nhds hsI)).differentiableAt (by simp) |>.hasFDerivAt
    exact (u.hasFDerivAt.comp s hhat).fderiv
  have hG_inj : Function.Injective (fderiv ℝ (fun t => u (c (γ t))) s) := by
    rw [hG_fderiv]
    have hU1 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) 1 ≠ 0 := by
      simpa [hu_apply] using hj
    intro x y hxy
    have h2 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1) = 0 := by
      calc (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1)
          = (u ∘L fderiv ℝ (fun t => c (γ t)) s) ((x - y) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hU1
  -- the inverse function theorem: the coordinate function has a smooth local inverse
  obtain ⟨L, O, W, hOo, hOs, hWo, hsW, hWV, hLGa, hLsmooth, hLO, hLG, huniq⟩ :=
    Work.Whitney.exists_localInverse_smooth_on (fun t => u (c (γ t))) (γ ⁻¹' c.source) hI s hsI
      hG_smooth hG_inj
  -- an open neighbourhood of `s` on which the inverse identity may be used
  have hGcont : ContinuousAt (fun t => u (c (γ t))) s :=
    (hG_smooth.contDiffAt (hI.mem_nhds hsI)).continuousAt
  obtain ⟨J₁, hJ₁sub, hJ₁open, hsJ₁⟩ :=
    mem_nhds_iff.mp (hGcont.preimage_mem_nhds (hOo.mem_nhds hOs))
  set J : Set ℝ := W ∩ J₁ with hJ_def
  have hJopen : IsOpen J := hWo.inter hJ₁open
  have hsJ : s ∈ J := ⟨hsW, hsJ₁⟩
  -- the local data
  set U : Set M := (γ '' Jᶜ)ᶜ ∩ (c.source ∩ (fun x => u (c x)) ⁻¹' O) with hU_def
  have hUo : IsOpen U := by
    rw [hU_def]
    refine ((hprop.isClosedMap Jᶜ hJopen.isClosed_compl).isOpen_compl).inter ?_
    exact (u.continuous.comp_continuousOn c.continuousOn).isOpen_inter_preimage
      c.open_source hOo
  refine ⟨U, fun x => L (u (c x)), hUo, ?_, ?_, ?_⟩
  · -- `γ s ∈ U`
    refine ⟨?_, hmem, ?_⟩
    · simp only [mem_compl_iff, mem_image, not_exists, not_and]
      intro t ht hts
      rw [hinj hts] at ht
      exact ht hsJ
    · exact hOs
  · -- smoothness of `L ∘ u ∘ c` on `U`
    have hcU : ContMDiffOn (MC n) (MC n) infOrder (c : M → EuclideanSpace ℝ (Fin n)) U :=
      (contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => hx.2.1)
    have hucU : ContMDiffOn (MC n) MCreal infOrder (fun x => u (c x)) U :=
      u.contMDiff.comp_contMDiffOn hcU
    exact hLsmooth.contMDiffOn.comp hucU (fun x hx => hx.2.2)
  · -- the left inverse property
    intro t ht
    have htJ : t ∈ J := by
      by_contra htJ
      exact ht.1 ⟨t, htJ, rfl⟩
    have hGtO : u (c (γ t)) ∈ O := hJ₁sub htJ.2
    have hz : t = L (u (c (γ t))) := huniq (u (c (γ t))) hGtO t htJ.1 rfl
    show L (u (c (γ t))) = t
    exact hz.symm

theorem exists_smooth_left_inverse_infty {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SecondCountableTopology M] {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (hinj : Function.Injective γ) (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s)) : ∃ g : M → ℝ, ContMDiff (MC n) MCreal ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ s : ℝ, g (γ s) = s := by
  have _hn : 2 ≤ n := hn
  have key : ∀ s : ℝ, ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ γ s ∈ U ∧
      ContMDiffOn (MC n) MCreal infOrder F U ∧ ∀ t : ℝ, γ t ∈ U → F (γ t) = t :=
    fun s => exists_local_left_inverse hγ hprop hinj himm s
  choose U F hprops using key
  exact smooth_left_inverse_of_local hprop U (fun s => (hprops s).1)
    (fun s => (hprops s).2.1) F (fun s => (hprops s).2.2.1)
    (fun s t ht => (hprops s).2.2.2 t ht)

end

end Work.Noncompact.CompressionTube
