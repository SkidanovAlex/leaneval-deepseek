import Mathlib
import Submission.Work.Drive.N2.LevelSetDefs
import Submission.Work.Drive.N2.nondegCrit_iff_chart
import Submission.Work.Drive.N2.isCritical_iff_chartRep
import Submission.Work.Drive.N2.LevelModelAux
import Submission.Work.Drive.N2.localInverseContDiffOnNhd

/-!
# The local model of a regular level set of a smooth function on a surface

`Work.Drive.N2.levelModelExists`: at a point `y` of the level set `f ⁻¹' {t}` of a smooth function
`f` on a surface `M` at which `f` is not critical, the level set is locally a smooth graph in the
chart at `y`.

The argument: the chart representation `g = f ∘ (chartAt E2 y.1).symm` is smooth near the chart point
`p`, and its derivative at `p` is non-zero (`isCritical_iff_chartRep`).  One of the two partial
derivatives of `g` at `p` is then non-zero, say in the direction of the `j`-th coordinate; the map
`Phi g j`, which keeps the `i`-th coordinate (the other one) and replaces the `j`-th coordinate by
`g`, is a local diffeomorphism near `p` (`injective_fderiv_Phi` and the local inverse function
theorem `localInverseContDiffOnNhd`).  Its local inverse parametrises the level set, and the smooth
graph description of the level set follows.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- Packaging of the local graph description of the level set of `g = chartRep f y.1` over the
coordinate `i` into a `LevelModel`. -/
private theorem levelModel_of_partial
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ) (t : ℝ) (y : LevelSet f t)
    (hsmooth : ContDiffOn ℝ ∞ (chartRep f y.1) (chartAt E2 y.1).target)
    (hgp : chartRep f y.1 ((chartAt E2 y.1) y.1) = t)
    {i j : Fin 2} (hij : j ≠ i)
    (hne : fderiv ℝ (chartRep f y.1) ((chartAt E2 y.1) y.1)
      (EuclideanSpace.single j (1 : ℝ)) ≠ 0) :
    Nonempty (LevelModel f t y) := by
  classical
  have hU : IsOpen (chartAt E2 y.1).target := (chartAt E2 y.1).open_target
  have hp : (chartAt E2 y.1) y.1 ∈ (chartAt E2 y.1).target :=
    (chartAt E2 y.1).map_source (mem_chart_source E2 y.1)
  have hΦcont : ContinuousOn (Phi (chartRep f y.1) j) (chartAt E2 y.1).target :=
    (Phi_contDiffOn hsmooth j).continuousOn
  obtain ⟨S, W, σ, hS, hW, hWU, hgpS, hpW, hσ, hσW, hσl, hσr⟩ :=
    localInverseContDiffOnNhd (Phi (chartRep f y.1) j) (chartAt E2 y.1).target hU
      (Phi_contDiffOn hsmooth j) ((chartAt E2 y.1) y.1) hp (injective_fderiv_Phi hU hsmooth hp j hne)
  refine ⟨i, ((chartAt E2 y.1).target ∩ (Phi (chartRep f y.1) j) ⁻¹' S) ∩ W, ?_,
    (fun s : ℝ => σ (ptF ((chartAt E2 y.1) y.1) i j t s)),
    {s : ℝ | ptF ((chartAt E2 y.1) y.1) i j t s ∈ S}, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hΦcont.isOpen_inter_preimage hU hS).inter hW
  · exact hS.preimage (ptF_contDiff ((chartAt E2 y.1) y.1) i j t).continuous
  · have h1 : ptF ((chartAt E2 y.1) y.1) i j t (((chartAt E2 y.1) y.1).ofLp i)
        = Phi (chartRep f y.1) j ((chartAt E2 y.1) y.1) :=
      (Phi_eq_ptF hij ((chartAt E2 y.1) y.1) rfl hgp).symm
    show ptF ((chartAt E2 y.1) y.1) i j t (((chartAt E2 y.1) y.1).ofLp i) ∈ S
    rw [h1]; exact hgpS
  · have hptf : ContDiffOn ℝ ∞ (fun s : ℝ => ptF ((chartAt E2 y.1) y.1) i j t s)
        {s : ℝ | ptF ((chartAt E2 y.1) y.1) i j t s ∈ S} :=
      (ptF_contDiff ((chartAt E2 y.1) y.1) i j t).contDiffOn.mono (Set.subset_univ _)
    exact hσ.comp hptf (fun s hs => hs)
  · have h1 : ptF ((chartAt E2 y.1) y.1) i j t (((chartAt E2 y.1) y.1).ofLp i)
        = Phi (chartRep f y.1) j ((chartAt E2 y.1) y.1) :=
      (Phi_eq_ptF hij ((chartAt E2 y.1) y.1) rfl hgp).symm
    show σ (ptF ((chartAt E2 y.1) y.1) i j t (((chartAt E2 y.1) y.1).ofLp i))
        = (chartAt E2 y.1) y.1
    rw [h1]
    exact hσr ((chartAt E2 y.1) y.1) hpW
  · intro s hs
    have hWs : σ (ptF ((chartAt E2 y.1) y.1) i j t s) ∈ W := hσW _ hs
    exact ⟨⟨hWU hWs, by
      show Phi (chartRep f y.1) j (σ (ptF ((chartAt E2 y.1) y.1) i j t s)) ∈ S
      rw [hσl _ hs]; exact hs⟩, hWs⟩
  · intro s hs
    exact hWU (hσW _ hs)
  · intro s hs
    show (σ (ptF ((chartAt E2 y.1) y.1) i j t s)).ofLp i = s
    rw [← Phi_ofLp_of_ne (chartRep f y.1) j _ (Ne.symm hij), hσl _ hs, ptF_ofLp_i _ hij]
  · intro s hs
    have h1 : (Phi (chartRep f y.1) j (σ (ptF ((chartAt E2 y.1) y.1) i j t s))).ofLp j = t := by
      rw [hσl _ hs, ptF_ofLp_j _ hij]
    rw [Phi_ofLp_self] at h1
    exact h1
  · intro v hv hgv
    have hvS : v ∈ (Phi (chartRep f y.1) j) ⁻¹' S := hv.1.2
    have hPhiv : Phi (chartRep f y.1) j v = ptF ((chartAt E2 y.1) y.1) i j t (v.ofLp i) :=
      Phi_eq_ptF hij _ rfl (by simpa only [chartRep] using hgv)
    show ptF ((chartAt E2 y.1) y.1) i j t (v.ofLp i) ∈ S
    rw [← hPhiv]; exact hvS
  · intro v hv hgv
    have hPhiv : Phi (chartRep f y.1) j v = ptF ((chartAt E2 y.1) y.1) i j t (v.ofLp i) :=
      Phi_eq_ptF hij _ rfl (by simpa only [chartRep] using hgv)
    show σ (ptF ((chartAt E2 y.1) y.1) i j t (v.ofLp i)) = v
    rw [← hPhiv]
    exact hσr v hv.2

theorem levelModelExists {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ) (t : ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (y : LevelSet f t) (hreg : ¬ Work.Drive.Morse.IsCritical f y.1) :
    Nonempty (LevelModel f t y) := by
  classical
  have hsmooth : ContDiffOn ℝ ∞ (chartRep f y.1) (chartAt E2 y.1).target :=
    contDiffOn_chartRep_center f hf y.1
  have hgp : chartRep f y.1 ((chartAt E2 y.1) y.1) = t := by
    show f ((chartAt E2 y.1).symm ((chartAt E2 y.1) y.1)) = t
    rw [(chartAt E2 y.1).left_inv (mem_chart_source E2 y.1)]
    exact y.2
  have hne : fderiv ℝ (chartRep f y.1) ((chartAt E2 y.1) y.1) ≠ 0 := by
    have h1 : fderiv ℝ (fun z => f ((extChartAt (𝓡 2) y.1).symm z))
        ((extChartAt (𝓡 2) y.1) y.1) ≠ 0 := by
      have h4 : ¬ Work.Drive.Morse.IsCritical f y.1 ↔
          ¬ fderiv ℝ (fun z => f ((extChartAt (𝓡 2) y.1).symm z))
            ((extChartAt (𝓡 2) y.1) y.1) = 0 := by
        simp only [Work.Drive.Morse.IsCritical]
        exact (Work.Drive.N2.isCritical_iff_chartRep f hf y.1 y.1 (mem_extChartAt_source _)).not
      exact h4.mp hreg
    have h6 : (extChartAt (𝓡 2) y.1) y.1 = (chartAt E2 y.1) y.1 := by
      simp [extChartAt, OpenPartialHomeomorph.extend]
    rw [Work.Drive.N2.extChartAt_self_symm_coe_chart, h6] at h1
    exact h1
  have hd : fderiv ℝ (chartRep f y.1) ((chartAt E2 y.1) y.1)
        (EuclideanSpace.single 0 (1 : ℝ)) ≠ 0 ∨
      fderiv ℝ (chartRep f y.1) ((chartAt E2 y.1) y.1)
        (EuclideanSpace.single 1 (1 : ℝ)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext v
    rw [E2_decomp v, map_add, map_smul, map_smul, h.1, h.2, smul_zero, smul_zero, add_zero]
    simp
  rcases hd with h0 | h1
  · exact levelModel_of_partial f t y hsmooth hgp (i := 1) (j := 0) (by decide) h0
  · exact levelModel_of_partial f t y hsmooth hgp (i := 0) (j := 1) (by decide) h1

end Work.Drive.N2
