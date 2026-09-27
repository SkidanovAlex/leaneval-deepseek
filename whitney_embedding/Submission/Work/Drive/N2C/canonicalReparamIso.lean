import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.roundConfigPicture
import Submission.Work.Drive.N2C.circlePhase
import Submission.Work.Drive.N2C.circlePhaseCover
import Submission.Work.Drive.N2C.circlePhaseAssembly
import Submission.Work.Drive.N2C.exists_modOne_phase_nhd
import Submission.Work.Drive.N2C.contDiff_invFun_of_strictMono
import Submission.Work.Drive.N2C.exists_reparam_unitCircle
import Submission.Work.Drive.N2C.reparamSlideData
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The canonical-reparametrisation isotopy (`N2C`, the last mile of the coherent-window assembly)

`Work.Drive.N2C.canonicalReparamIso`: two parametrisations `L`, `L'` of the same regular level
`f ⁻¹' {b}` by `n` periodic curves, related by a smooth orientation-preserving reparametrisation
`h` (`L'γ i x = Lγ i (h i x)`), carry the *same* round picture: the picture read from a disjoint
round configuration `D` through `L'` and the picture read through `L` are joined by a level isotopy.

The proof is the "sliding" isotopy `e s (Lγ i x) = D.circle i ((1 - σ s) * (h i)⁻¹ x + σ s * x)`.

The auxiliary material is organised as follows:

* `Work.Drive.N2C.canonicalReparam_chartDeriv_ne_zero` — the chart representative of an immersed
  curve has non-zero derivative;
* `Work.Drive.N2C.canonicalReparam_localPhase` — the inverse function theorem in a chart: every
  point of an immersed curve has a neighbourhood on which a smooth function reads the parameter;
* `Work.Drive.N2C.canonicalReparam_phaseCover` — the finite phase cover of the curve, from the local
  phase and the elementary "modulo the period" shrinking (`exists_modOne_phase_nhd`);
* `Work.Drive.N2C.canonicalReparam_jointExtension` — a jointly smooth `1`-periodic family on the
  curve extends to the surface (`exists_contMDiff_extend_of_circlePhaseCover`);
* `Work.Drive.N2C.canonicalReparam_bump` — the smooth partition of unity along the curves;
* `Work.Drive.N2C.canonicalReparam_of_slide` — the assembly: the sliding family `r` of
  reparametrisations (`Work.Drive.N2C.reparamSlideData`) gives the level isotopy.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
  [SecondCountableTopology M] [CompactSpace M]

/-! ## The local phase of an immersed curve -/

/-- **The chart representative of an immersed curve has non-zero derivative.** -/
theorem canonicalReparam_chartDeriv_ne_zero (γ : ℝ → M)
    (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 ≠ 0) (t₀ : ℝ) :
    (fderiv ℝ (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀) 1 ≠ 0 := by
  intro h0
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hsrc : γ t₀ ∈ (chartAt E2 (γ t₀)).source := mem_chart_source E2 (γ t₀)
  have hchartrep_at : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀ := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀ :=
      (contMDiffOn_chart (I := 𝓡 2) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := γ t₀)).contMDiffAt
        ((chartAt E2 (γ t₀)).open_source.mem_nhds hsrc) |>.comp t₀ hγsm.contMDiffAt
    exact h1.mdifferentiableAt hnz
  have hsymm_at : MDifferentiableAt (𝓡 2) (𝓡 2) (chartAt E2 (γ t₀)).symm
      ((chartAt E2 (γ t₀)) (γ t₀)) := by
    have h1 : ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (chartAt E2 (γ t₀)).symm
        ((chartAt E2 (γ t₀)) (γ t₀)) :=
      ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := γ t₀))).contMDiffAt
        ((chartAt E2 (γ t₀)).open_target.mem_nhds ((chartAt E2 (γ t₀)).map_source hsrc))
    exact h1.mdifferentiableAt hnz
  have hcomp_chart : ((chartAt E2 (γ t₀)).symm ∘
      (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s))) =ᶠ[𝓝 t₀] γ := by
    refine Filter.mem_of_superset
      (((chartAt E2 (γ t₀)).open_source.preimage hγsm.continuous).mem_nhds hsrc)
      (fun s hs => ?_)
    exact (chartAt E2 (γ t₀)).left_inv hs
  have h0' : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀) 1 = 0 := by
    rw [mfderiv_eq_fderiv]
    exact h0
  have hcr : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t₀
      = (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 (γ t₀)).symm
          ((chartAt E2 (γ t₀)) (γ t₀))).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀) := by
    rw [← hcomp_chart.mfderiv_eq_v433]
    exact mfderiv_comp (f := fun s : ℝ => (chartAt E2 (γ t₀)) (γ s))
      (g := (chartAt E2 (γ t₀)).symm) t₀ hsymm_at hchartrep_at
  have h1 : ((mfderiv (𝓡 2) (𝓡 2) (chartAt E2 (γ t₀)).symm
        ((chartAt E2 (γ t₀)) (γ t₀))).comp
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun s : ℝ => (chartAt E2 (γ t₀)) (γ s)) t₀)) 1 = 0 := by
    rw [ContinuousLinearMap.comp_apply, h0', ContinuousLinearMap.map_zero]
  exact himm t₀ (hcr ▸ h1)

/-- **The local phase of an immersed curve.**  Every point of a `C^∞` immersed curve in a surface
has a neighbourhood on which a `C^∞` function reads the parameter of the curve. -/
theorem canonicalReparam_localPhase (γ : ℝ → M)
    (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 ≠ 0) (t₀ : ℝ) :
    ∃ (U : Set M) (φ : M → ℝ), IsOpen U ∧ γ t₀ ∈ U ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) φ U ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), φ (γ t) = t := by
  classical
  have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hsrc : γ t₀ ∈ (chartAt E2 (γ t₀)).source := mem_chart_source E2 (γ t₀)
  -- the coordinate functional on the chart representative of the curve
  set c : ℝ → E2 := fun s => (chartAt E2 (γ t₀)) (γ s) with hc
  set v : E2 := (fderiv ℝ c t₀) 1 with hv
  have hvne : v ≠ 0 := canonicalReparam_chartDeriv_ne_zero γ hγsm himm t₀
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, v.ofLp i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hvne (WithLp.ofLp_injective 2 (by funext j; simpa using h j))
  -- the parameter function `k = levelCoordProj i ∘ c` along the curve
  set k : ℝ → ℝ := fun x => levelCoordProj i (c x) with hk
  set K : M → ℝ := fun y => levelCoordProj i ((chartAt E2 (γ t₀)) y) with hK
  have hKk : ∀ x : ℝ, K (γ x) = k x := fun x => rfl
  have hU₀open : IsOpen (γ ⁻¹' (chartAt E2 (γ t₀)).source) :=
    (chartAt E2 (γ t₀)).open_source.preimage hγsm.continuous
  have hchart_comp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (chartAt E2 (γ t₀)) (γ x)) (γ ⁻¹' (chartAt E2 (γ t₀)).source) :=
    contMDiffOn_iff_contDiffOn.mp <|
      (contMDiffOn_chart (I := 𝓡 2) (x := γ t₀)).comp hγsm.contMDiffOn
        (fun x hx => hx)
  have hk_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) k
      (γ ⁻¹' (chartAt E2 (γ t₀)).source) := by
    have := (levelCoordProj i).contDiff.comp_contDiffOn hchart_comp
    simpa only [k, hc, Function.comp_def] using this
  have hk_fderiv1 : (fderiv ℝ k t₀) 1 ≠ 0 := by
    have hcd_c : DifferentiableAt ℝ c t₀ := by
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c t₀ :=
        hchart_comp.contDiffAt (hU₀open.mem_nhds hsrc)
      exact h1.differentiableAt hnz
    have htarget : HasFDerivAt k (((levelCoordProj i : E2 →L[ℝ] ℝ)).comp (fderiv ℝ c t₀)) t₀ :=
      (levelCoordProj i).hasFDerivAt.comp t₀ hcd_c.hasFDerivAt
    rw [htarget.fderiv, ContinuousLinearMap.comp_apply, levelCoordProj_apply]
    exact hi
  -- the local inverse of `k` at `t₀`
  obtain ⟨S, W, σ, hSopen, hWopen, hWsub, hkS, ht₀W, hσ_cd, hσ_mem, hσ_left, hσ_right⟩ :=
    Work.Drive.N2.localInverseContDiffOnNhd k (γ ⁻¹' (chartAt E2 (γ t₀)).source) hU₀open
      hk_cd t₀ hsrc (by
        intro x y hxy
        have hsub : (fderiv ℝ k t₀) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        have hsmul : (x - y) • ((fderiv ℝ k t₀) 1) = 0 := by
          rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
          exact hsub
        rcases smul_eq_zero.mp hsmul with h | h
        · linarith
        · exact absurd h hk_fderiv1)
  -- the phase function and its domain
  refine ⟨(chartAt E2 (γ t₀)).source ∩ K ⁻¹' S, fun y => σ (K y), ?_, ?_, ?_, ?_⟩
  · have hKcont : ContinuousOn K (chartAt E2 (γ t₀)).source := by
      have hch : ContinuousOn (fun y : M => (chartAt E2 (γ t₀)) y)
          (chartAt E2 (γ t₀)).source :=
        (contMDiffOn_chart (I := 𝓡 2) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := γ t₀)).continuousOn
      exact (levelCoordProj i).continuous.comp_continuousOn hch
    exact ContinuousOn.isOpen_inter_preimage hKcont (chartAt E2 (γ t₀)).open_source hSopen
  · exact ⟨hsrc, hkS⟩
  · -- smoothness of the phase
    have hK_cd : ContMDiffOn (𝓡 2) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) K
        (chartAt E2 (γ t₀)).source := by
      have hch : ContMDiffOn (𝓡 2) (𝓘(ℝ, E2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => (chartAt E2 (γ t₀)) y) (chartAt E2 (γ t₀)).source :=
        contMDiffOn_chart
      have h2 := ((levelCoordProj i : E2 →L[ℝ] ℝ)).contMDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) |>.contMDiffOn
          |>.comp (t := Set.univ) hch (fun y _ => Set.mem_univ _)
      simpa only [K, Function.comp_def] using h2
    have hσ_md : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) σ S :=
      contMDiffOn_iff_contDiffOn.mpr hσ_cd
    exact hσ_md.comp (hK_cd.mono Set.inter_subset_left) (fun y hy => hy.2)
  · -- the phase reads the parameter near `t₀`
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds ht₀W)
    refine ⟨ε, hεpos, ?_⟩
    intro t ht
    have htW : t ∈ W := hεsub (by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [Set.mem_Ioo] at ht
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩)
    exact hσ_right t htW

/-! ## The phase cover and the extension of a periodic family -/

/-- **A finite phase cover of a periodic embedded circle.** -/
theorem canonicalReparam_phaseCover {γ : ℝ → M} (hγc : Continuous γ)
    (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hper : Function.Periodic γ 1) (hinj : Set.InjOn γ (Set.Ico 0 1))
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (CirclePhaseCover γ ι) := by
  refine exists_circlePhaseCover_of_localPhase hγc hper (fun t₀ => ?_)
  obtain ⟨U, φ, hU, hUt, hφ, δ, hδ, hφγ⟩ :=
    canonicalReparam_localPhase γ hγsm himm t₀
  set δ' : ℝ := min δ (1 / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'le : 2 * δ' ≤ 1 := by
    have : δ' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hφγ' : ∀ t ∈ Set.Ioo (t₀ - δ') (t₀ + δ'), φ (γ t) = t := by
    intro t ht
    exact hφγ t ⟨by linarith [ht.1, min_le_left δ (1 / 2)],
      by linarith [ht.2, min_le_left δ (1 / 2)]⟩
  obtain ⟨U', hU'open, hU't, hU'sub, hphase⟩ :=
    exists_modOne_phase_nhd hγc hper hinj hU hUt hφ hδ'pos hδ'le hφγ'
  exact ⟨U', φ, hU'open, hU't, hφ.mono hU'sub, hphase⟩

/-- **A jointly smooth `1`-periodic family on a periodic embedded circle extends to the surface.** -/
theorem canonicalReparam_jointExtension {γ : ℝ → M} (hγc : Continuous γ)
    (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hper : Function.Periodic γ 1) (hinj : Set.InjOn γ (Set.Ico 0 1))
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 ≠ 0)
    (A : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A p.1 p.2))
    (hperA : ∀ (s x : ℝ), A s (x + 1) = A s x) :
    ∃ G : ℝ → M → EuclideanSpace ℝ (Fin 3),
      ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => G p.1 p.2) ∧
      (∀ (s : ℝ) (x : ℝ), G s (γ x) = A s x) := by
  obtain ⟨ι, hι, ⟨C⟩⟩ := canonicalReparam_phaseCover hγc hγsm hper hinj himm
  exact exists_contMDiff_extend_of_circlePhaseCover hγc hper C A hA hperA


/-! ## The round picture of a configuration -/

/-- The round picture is smooth. -/
theorem canonicalReparam_roundPic_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) roundPic := by
  have h : roundPic = fun t : ℝ => mkCLM (![Real.cos t, Real.sin t, (0 : ℝ)] : Fin 3 → ℝ) := by
    funext t
    rw [roundPic_eq_mkCLM]
  rw [h]
  refine mkCLM.contDiff.comp ?_
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The round picture is `2π`-periodic. -/
theorem canonicalReparam_roundPic_addTwoPi (t : ℝ) : roundPic (t + 2 * Real.pi) = roundPic t := by
  have h : t + 2 * Real.pi = 2 * Real.pi + t := by ring
  rw [h, roundPic_add]
  simp [Real.cos_two_pi, Real.sin_two_pi]

/-- The circle of a round configuration is smooth. -/
theorem canonicalReparam_circle_contDiff {m : ℕ} (D : RoundConfig m) (i : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => D.circle i t) := by
  have h : (fun t : ℝ => D.circle i t)
      = fun t : ℝ => D.pos i + D.rad i • roundPic (D.phase i + 2 * Real.pi * t) := rfl
  rw [h]
  have harg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => D.phase i + (2 * Real.pi) * t) := by fun_prop
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => D.rad i • roundPic (D.phase i + (2 * Real.pi) * t)) :=
    (contDiff_const (c := D.rad i)).smul (canonicalReparam_roundPic_contDiff.comp harg)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => D.pos i + D.rad i • roundPic (D.phase i + (2 * Real.pi) * t)) :=
    contDiff_const.add h2
  simpa [RoundConfig.circle] using h3

/-- The circle of a round configuration is `1`-periodic in its parameter. -/
theorem canonicalReparam_circle_addOne {m : ℕ} (D : RoundConfig m) (i : Fin m) (t : ℝ) :
    D.circle i (t + 1) = D.circle i t := by
  simp only [RoundConfig.circle]
  have harg : D.phase i + 2 * Real.pi * (t + 1) = (D.phase i + 2 * Real.pi * t) + 2 * Real.pi := by
    ring
  rw [harg, canonicalReparam_roundPic_addTwoPi]

/-! ## A smooth partition of unity along the curves -/

/-- A smooth function which is `1` on the `i`-th curve and `0` on all the others. -/
theorem canonicalReparam_bump {n : ℕ} (γ : Fin n → ℝ → M)
    (hcont : ∀ i, Continuous (γ i))
    (hper : ∀ (i : Fin n) (x : ℝ), γ i (x + 1) = γ i x)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))) :
    ∃ χ : Fin n → M → ℝ,
      (∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i)) ∧
      (∀ (i : Fin n) (x : ℝ), χ i (γ i x) = 1) ∧
      (∀ (i j : Fin n), j ≠ i → ∀ x : ℝ, χ i (γ j x) = 0) := by
  classical
  have hrange : ∀ i : Fin n, Set.range (γ i) = γ i '' Set.Icc (0 : ℝ) 1 := by
    intro i
    have hper' : Function.Periodic (γ i) 1 := fun x => hper i x
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Int.fract x, ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩, ?_⟩
      have h1 := (hper'.zsmul ⌊x⌋ (Int.fract x)).symm
      simp only [zsmul_one] at h1
      rw [Int.fract_add_floor] at h1
      exact h1
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
  have hbump : ∀ i : Fin n, ∃ χ : M → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ t : ℝ, χ (γ i t) = 1) ∧ (∀ j : Fin n, j ≠ i → ∀ t : ℝ, χ (γ j t) = 0) := by
    intro i
    have hKi : IsCompact (Set.range (γ i)) := by
      rw [hrange i]
      exact isCompact_Icc.image (hcont i)
    have hKo : IsCompact (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      refine isCompact_iUnion fun j => ?_
      rw [hrange j.1]
      exact isCompact_Icc.image (hcont j.1)
    have hdisj' : Disjoint (Set.range (γ i))
        (⋃ j : {j : Fin n // j ≠ i}, Set.range (γ j.1)) := by
      rw [Set.disjoint_iUnion_right]
      intro j
      exact hdisj i j.1 (Ne.symm j.2)
    obtain ⟨U, W, hUo, hWo, hKU, hKW, hUW⟩ :=
      SeparatedNhds.of_isCompact_isCompact hKi hKo hdisj'
    obtain ⟨χ, V, hχsm, hχsupp, hVopen, hKV, hχone, _⟩ :=
      exists_contMDiff_bump_tsupport hKi hUo hKU
    refine ⟨χ, hχsm, ?_, ?_⟩
    · intro t
      exact hχone _ (hKV ⟨t, rfl⟩)
    · intro j hj t
      by_contra hne
      have h1 : γ j t ∈ Function.support χ := by rwa [Function.mem_support]
      have h3 : γ j t ∈ U := hχsupp (subset_closure h1)
      have h4 : γ j t ∈ W := hKW (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ⟨t, rfl⟩⟩)
      exact Set.disjoint_left.mp hUW h3 h4
  choose χ hχsm hχone hχzero using hbump
  exact ⟨χ, hχsm, hχone, hχzero⟩

/-! ## The assembly -/

/-- **The reparametrisation slide gives the isotopy.**  Given the sliding family `r` of
reparametrisations (`r 0 i = (h i)⁻¹`, `r 1 i = id`, jointly smooth, `1`-equivariant, strictly
increasing with non-vanishing derivative), the round picture read through `L'` is isotopic, through
pictures of the level, to the round picture read through `L`. -/
theorem canonicalReparamIso_of_slide {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n : ℕ} (L L' : LevelCurves f b n) (D : RoundConfig n) (hD : D.Disjoint)
    (h : Fin n → ℝ → ℝ) (hcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i))
    (hper : ∀ (i : Fin n) (x : ℝ), h i (x + 1) = h i x + 1)
    (hmono : ∀ (i : Fin n) (x : ℝ), 0 < deriv (h i) x)
    (hrel : ∀ (i : Fin n) (x : ℝ), L'.γ i x = L.γ i (h i x))
    (r : ℝ → Fin n → ℝ → ℝ)
    (hr0 : ∀ (i : Fin n) (x : ℝ), r 0 i x = Function.invFun (h i) x)
    (hr1 : ∀ (i : Fin n) (x : ℝ), r 1 i x = x)
    (hrcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => r p.1 i p.2))
    (hrper : ∀ (i : Fin n) (s x : ℝ), r s i (x + 1) = r s i x + 1)
    (hrmono : ∀ (i : Fin n) (s : ℝ), StrictMono (r s i))
    (hrderiv : ∀ (i : Fin n) (s x : ℝ), deriv (fun y : ℝ => r s i y) x ≠ 0) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L'.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = D.circle i x) := by
  classical
  by_cases hn : n = 0
  · subst hn
    have hempty : ∀ x : M, f x ≠ b := by
      intro x hx
      obtain ⟨i, t, -⟩ := L.cover x hx
      exact i.elim0
    refine ⟨fun _ _ => 0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s y hy
      exact absurd hy (hempty y)
    · intro s x y hx hy _
      exact absurd hx (hempty x)
    · intro s y hy
      exact absurd hy (hempty y)
    · intro i
      exact i.elim0
    · intro i
      exact i.elim0
  · haveI hfin : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have hnz : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    -- each curve is an immersion
    have hcurve_imm : ∀ (i : Fin n) (t : ℝ),
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (L.γ i) t 1 ≠ 0 := by
      intro i t h1
      obtain ⟨v, hvne, hv0⟩ := Work.Drive.N2.exists_ne_zero_ker
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (L.γ i t))
      obtain ⟨s, hs⟩ := L.ker i t v hv0
      have hsa : s • (1 : TangentSpace 𝓘(ℝ, ℝ) t) = s := by
        show s * 1 = s
        ring
      have hs0 : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (L.γ i) t) s = 0 := by
        conv_lhs => rw [← hsa, ContinuousLinearMap.map_smul]
        rw [h1, smul_zero]
      rw [hs] at hs0
      exact hvne hs0
    -- the extension of each curve's picture to the surface
    have hext : ∀ i : Fin n, ∃ Φ : ℝ → M → EuclideanSpace ℝ (Fin 3),
        ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M => Φ p.1 p.2) ∧
        (∀ (s x : ℝ), Φ s (L.γ i x) = D.circle i (r s i x)) := by
      intro i
      have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => D.circle i (r p.1 i p.2)) :=
        (canonicalReparam_circle_contDiff D i).comp (hrcd i)
      have hperA : ∀ (s x : ℝ), D.circle i (r s i (x + 1)) = D.circle i (r s i x) := by
        intro s x
        rw [hrper i s x]
        exact canonicalReparam_circle_addOne D i _
      exact canonicalReparam_jointExtension (γ := L.γ i) (L.sm i).continuous (L.sm i)
        (fun x => L.per i x) (L.injIco i) (hcurve_imm i) (fun s x => D.circle i (r s i x)) hA hperA
    choose Φ hΦsm hΦval using hext
    -- the partition of unity along the curves
    obtain ⟨χ, hχsm, hχone, hχzero⟩ :=
      canonicalReparam_bump L.γ (fun i => (L.sm i).continuous) (fun i x => L.per i x) L.disj
    -- the isotopy
    set e : ℝ → M → EuclideanSpace ℝ (Fin 3) := fun s y => ∑ i, χ i y • Φ i s y with he
    have hEsm : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => e p.1 p.2) := by
      rw [he]
      refine ContMDiff.sum fun i _ => ?_
      exact ((hχsm i).comp contMDiff_snd).smul (hΦsm i)
    have hval : ∀ (j : Fin n) (s x : ℝ), e s (L.γ j x) = D.circle j (r s j x) := by
      intro j s x
      rw [he]
      show (∑ i, χ i (L.γ j x) • Φ i s (L.γ j x)) = D.circle j (r s j x)
      rw [Finset.sum_eq_single j]
      · rw [hχone j x, one_smul]
        exact hΦval j s x
      · intro i _ hij
        rw [hχzero i j (Ne.symm hij) x, zero_smul]
      · intro hmem
        exact absurd (Finset.mem_univ j) hmem
    refine ⟨e, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s y hy
      exact hEsm.contMDiffAt
    · -- injectivity on the level
      intro s x y hx hy hxy
      obtain ⟨i, a, rfl⟩ := L.cover x hx
      obtain ⟨j, b, rfl⟩ := L.cover y hy
      rw [hval i s a, hval j s b] at hxy
      by_cases hij : i = j
      · subst hij
        obtain ⟨k, hk⟩ := circle_eq_mod_one D i hxy
        have hBper : Function.Periodic (fun z : ℝ => r s i z - z) 1 := by
          intro z
          simp only
          rw [hrper i s z]
          ring
        have hBk := hBper.zsmul k b
        simp only [zsmul_one] at hBk
        have hAeq : r s i (b + (k : ℝ)) = r s i a := by linarith
        have hab : b + (k : ℝ) = a := (hrmono i s).injective hAeq
        rw [← hab]
        have hLk : L.γ i (b + (k : ℝ)) = L.γ i b := by
          have hper' : Function.Periodic (L.γ i) 1 := fun x => L.per i x
          have h1 := hper'.zsmul k b
          simpa only [zsmul_one] using h1
        exact hLk
      · exact absurd hxy (hD i j hij (r s i a) (r s j b))
    · -- immersivity on `ker df`
      intro s y hy v hv hv0
      obtain ⟨i, a, rfl⟩ := L.cover y hy
      obtain ⟨t', ht'⟩ := L.ker i a v hv
      -- differentiability of the two factors of the first chain rule
      have hPdiff : MDifferentiableAt (𝓡 2) (𝓡 3) (fun w : M => e s w) (L.γ i a) := by
        have h3 : ContMDiffAt (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun w : M => (s, w)) (L.γ i a) :=
          (contMDiffAt_const (c := s)).prodMk contMDiffAt_id
        have h4 := ((hEsm.contMDiffAt (x := (s, L.γ i a))).comp (L.γ i a) h3).mdifferentiableAt hnz
        simpa [Function.comp_def] using h4
      have hγdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) (L.γ i) a :=
        ((L.sm i).contMDiffAt).mdifferentiableAt hnz
      -- the composite `e s ∘ L.γ i` is the reparametrised circle
      have hfun_eq : ((fun w : M => e s w) ∘ (L.γ i))
          = fun u : ℝ => D.circle i (r s i u) := by
        funext u
        exact hval i s u
      have hz1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ((fun w : M => e s w) ∘ (L.γ i)) a t'
          = mfderiv (𝓡 2) (𝓡 3) (fun w : M => e s w) (L.γ i a)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (L.γ i) a t') := by
        rw [mfderiv_comp (f := L.γ i) (g := fun w : M => e s w) (x := a) hPdiff hγdiff]
        rfl
      have hcirc : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun u : ℝ => D.circle i (r s i u)) a t' = 0 := by
        have h1 : mfderiv (𝓡 2) (𝓡 3) (fun w : M => e s w) (L.γ i a) v = 0 := hv0
        rw [← ht'] at h1
        rw [← hz1, hfun_eq] at h1
        exact h1
      -- the second chain rule, in the Euclidean (`fderiv`) world
      have hr_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => r s i y) :=
        (hrcd i).comp (contDiff_const.prodMk contDiff_id)
      have hr_diff_e : DifferentiableAt ℝ (fun y : ℝ => r s i y) a :=
        (hr_cd.differentiable (by simp)).differentiableAt
      have hc_diff_e : DifferentiableAt ℝ (fun t : ℝ => D.circle i t) (r s i a) :=
        ((canonicalReparam_circle_contDiff D i).differentiable (by simp)).differentiableAt
      have hcf : (fderiv ℝ (fun u : ℝ => D.circle i (r s i u)) a) t' = 0 := by
        rw [mfderiv_eq_fderiv] at hcirc
        exact hcirc
      have hch : fderiv ℝ (fun u : ℝ => D.circle i (r s i u)) a
          = (fderiv ℝ (fun t : ℝ => D.circle i t) (r s i a)).comp
              (fderiv ℝ (fun y : ℝ => r s i y) a) := by
        have h := fderiv_comp (f := fun y : ℝ => r s i y)
          (g := fun t : ℝ => D.circle i t) a hc_diff_e hr_diff_e
        simpa [Function.comp_def] using h
      have hval2 : (fderiv ℝ (fun t : ℝ => D.circle i t) (r s i a))
          ((fderiv ℝ (fun y : ℝ => r s i y) a) t') = 0 := by
        have h := hcf
        rw [hch, ContinuousLinearMap.comp_apply] at h
        exact h
      -- the derivative of the circle is injective
      have hLc : Function.Injective (fderiv ℝ (fun t : ℝ => D.circle i t) (r s i a)) := by
        intro p q hpq
        have hsub : (fderiv ℝ (fun t : ℝ => D.circle i t) (r s i a)) (p - q) = 0 := by
          rw [map_sub, hpq, sub_self]
        have hsmul : (p - q) • ((fderiv ℝ (fun t : ℝ => D.circle i t) (r s i a)) 1) = 0 := by
          rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
          exact hsub
        rcases smul_eq_zero.mp hsmul with h | h
        · linarith
        · exact absurd h (circle_deriv_ne_zero D i (r s i a))
      have hLr0 : (fderiv ℝ (fun y : ℝ => r s i y) a) t' = 0 :=
        hLc (by rw [hval2, map_zero])
      have hLr1 : (fderiv ℝ (fun y : ℝ => r s i y) a) 1 ≠ 0 := hrderiv i s a
      have hsw : t' • ((fderiv ℝ (fun y : ℝ => r s i y) a) 1) = 0 := by
        have h := hLr0
        rw [show (fderiv ℝ (fun y : ℝ => r s i y) a) t'
              = (fderiv ℝ (fun y : ℝ => r s i y) a) (t' • (1 : ℝ)) from by
            rw [smul_eq_mul, mul_one],
          ContinuousLinearMap.map_smul] at h
        exact h
      have ht'0 : t' = 0 := by
        rcases smul_eq_zero.mp hsw with h | h
        · exact h
        · exact absurd h hLr1
      have hfin : v = 0 := by
        have h1 : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (L.γ i) a t' = 0 := by
          rw [ht'0]
          exact map_zero _
        rw [ht'] at h1
        exact h1
      exact hfin
    · -- the picture read through `L'` at time `0`
      intro i x
      rw [hrel i x, hval i 0 (h i x), hr0 i (h i x),
        Function.leftInverse_invFun (strictMono_of_deriv_pos (hmono i)).injective x]
    · -- the picture read through `L` at time `1`
      intro i x
      rw [hval i 1 x, hr1 i x]


/-! ## The target -/

theorem canonicalReparamIso {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {n : ℕ} (L L' : Work.Drive.N2C.LevelCurves f b n)
    (D : Work.Drive.N2.RoundConfig n) (hD : D.Disjoint)
    (h : Fin n → ℝ → ℝ) (hcd : ∀ i : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i))
    (hper : ∀ (i : Fin n) (x : ℝ), h i (x + 1) = h i x + 1)
    (hmono : ∀ (i : Fin n) (x : ℝ), 0 < deriv (h i) x)
    (hrel : ∀ (i : Fin n) (x : ℝ), L'.γ i x = L.γ i (h i x)) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), Work.Drive.N2C.IsLevelIsotopy f b e ∧
      (∀ (i : Fin n) (x : ℝ), e 0 (L'.γ i x) = D.circle i x) ∧
      (∀ (i : Fin n) (x : ℝ), e 1 (L.γ i x) = D.circle i x) := by
  obtain ⟨r, hr0, hr1, hrcd, hrper, hrmono, hrderiv⟩ :=
    Work.Drive.N2C.reparamSlideData h hcd hper hmono
  exact canonicalReparamIso_of_slide hf hreg L L' D hD h hcd hper hmono hrel r hr0 hr1 hrcd
    hrper hrmono hrderiv

end

end Work.Drive.N2C
