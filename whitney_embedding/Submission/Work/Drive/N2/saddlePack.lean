import Mathlib
import Submission.Work.Drive.N2.saddleChartLayer
import Submission.Work.Drive.N2.canonChartOfScaled
import Submission.Work.Drive.N2.im_sq_eq_of_flow_closedODE

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

/-- Scaling a complex number by a real number scales the real part of its square by the square of
the scalar. -/
private lemma pack_re_sq_ofReal_mul (r : ℝ) (z : ℂ) :
    ((((r : ℂ) * z) ^ 2).re) = r ^ 2 * (z ^ 2).re := by
  have h : ((r : ℂ) * z) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * z ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow]
  rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The scaled saddle coordinate is injective on the whole source of its chart. -/
private lemma cl_injOn_saddleZ_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) {σc : ℂ} (hσc : σc ≠ 0) :
    Set.InjOn (cl_saddleZ D σc) (D.φ D.j).source := by
  have hb : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := D.hρ D.j; positivity)
  have hc : σc / ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := div_ne_zero hσc hb
  intro x hx y hy hxy
  have h1 : chartZ (D.φ D.j) x = chartZ (D.φ D.j) y := by
    refine mul_left_cancel₀ hc ?_
    rw [← cl_saddleZ_eq, ← cl_saddleZ_eq]
    exact hxy
  have h3 : D.φ D.j x = D.φ D.j y :=
    cl_chartZLM_injective (by simpa [cl_chartZ_eq_chartZLM] using h1)
  exact (D.φ D.j).injOn hx hy h3

/-- The differential of the scaled saddle coordinate is injective on the whole source of its
chart. -/
private lemma cl_injective_mfderiv_saddleZ_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) {σc : ℂ} (hσc : σc ≠ 0)
    {x : M} (hx : x ∈ (D.φ D.j).source) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) (cl_saddleZ D σc) x) := by
  have hb : ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (by have := D.hρ D.j; positivity)
  have hc : σc / ((D.ρ D.j / 8 : ℝ) : ℂ) ≠ 0 := div_ne_zero hσc hb
  intro u v huv
  have huv' : cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))
      (cl_chartZLM ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) u))
      = cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ))
        (cl_chartZLM ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) v)) := by
    rw [← cl_mfderiv_saddleZ_apply D σc hx u, ← cl_mfderiv_saddleZ_apply D σc hx v]
    exact huv
  have h1 : cl_chartZLM ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) u)
      = cl_chartZLM ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) v) :=
    cl_scaleCLM_injective hc huv'
  have h2 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) u
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (fun y => D.φ D.j y) x) v :=
    cl_chartZLM_injective h1
  exact cl_injective_mfderiv_chart (D.hφ D.j) (D.hφ' D.j) hx h2

/-- The scaled saddle coordinate is smooth on the whole source of its chart. -/
private lemma cl_contMDiffOn_saddleZ_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (σc : ℂ) :
    ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (cl_saddleZ D σc)
      (D.φ D.j).source := by
  have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => cl_chartZLM (D.φ D.j y)) (D.φ D.j).source :=
    cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j)
  have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => cl_scaleCLM (σc / ((D.ρ D.j / 8 : ℝ) : ℂ)) (cl_chartZLM (D.φ D.j y)))
      (D.φ D.j).source :=
    (cl_scaleCLM _).contMDiff.comp_contMDiffOn h1
  refine h2.congr (fun y _ => ?_)
  rw [cl_scaleCLM_apply, cl_saddleZ_eq, cl_chartZ_eq_chartZLM]

/-- **The canonical saddle chart package.**  For a `WindowDatum` whose marked chart has opposite
signs (`s₁ = -s₂`) and a canonical scalar `σc ∈ {1, I}` with the matching sign, there is a chart
`φ'` with the same source and the same model balls as the datum's chart, a complex coordinate
`Zs = φ' 0 + i · φ' 1`, a rescaling `Z = Zs / (ρ/8)` and the radius `lam0 = ρ/8`, satisfying the
smoothness, injectivity, immersion and level laws, the `(1, -1)` chart ODE in the `φ'` coordinates
with multiplier `chartMult lam0`, and the invariance of `Im (Zs ·)²` along `C j`-confined traces. -/
private theorem saddlePack_aux {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) {σc : ℂ} {s₁ s₂ : ℝ}
    (hσc : σc = 1 ∨ σc = Complex.I)
    (hs1 : D.s₁ D.j = s₁) (hs2 : D.s₂ D.j = s₂) (hsgn : s₁ = -s₂)
    (hσcsq : σc * σc = ((s₁ : ℝ) : ℂ)) (hσcn : ‖σc‖ = 1)
    (hre1 : σc.re * s₁ = σc.re) (him2 : σc.im * s₂ = σc.im)
    (him1 : σc.im * s₁ = -σc.im) (hre2 : σc.re * s₂ = -σc.re) :
    ∃ (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs Z : M → ℂ) (lam0 : ℝ),
      0 < lam0 ∧ lam0 = D.ρ D.j / 8 ∧
      φ'.source = (D.φ D.j).source ∧
      (∀ r : ℝ, modelBall φ' r = modelBall (D.φ D.j) r) ∧
      (∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) ∧
      (∀ y : M, Zs y = (lam0 : ℂ) * Z y) ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source ∧
      Set.InjOn Z (D.φ D.j).source ∧
      (∀ x ∈ (D.φ D.j).source,
        Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) Z x)) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re) ∧
      (∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
          (chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
          (chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t) ∧
      (∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im) := by
  classical
  have hlam0pos : 0 < D.ρ D.j / 8 := by have := D.hρ D.j; positivity
  have hlam0ne : ((D.ρ D.j / 8 : ℝ)) ≠ 0 := ne_of_gt hlam0pos
  have hL : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    rwa [Complex.ofReal_ne_zero]
  have hσc0 : σc ≠ 0 := by
    rcases hσc with rfl | rfl
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  obtain ⟨φ', hsrc', hball', hsm', hlin⟩ :=
    canonChartOfScaled (D.φ D.j) (cl_saddleZ D σc) hlam0ne (D.hφ D.j) hσc
      (fun y => cl_saddleZ_apply D σc y)
  set Zs : M → ℂ := fun y => ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I with hZsdef
  set Z : M → ℂ := fun y => ((((D.ρ D.j / 8 : ℝ)) : ℂ))⁻¹ * Zs y with hZdef
  have hZs_eq : ∀ y ∈ (D.φ D.j).source,
      Zs y = (((D.ρ D.j / 8 : ℝ)) : ℂ) * cl_saddleZ D σc y := by
    intro y hy
    show ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * cl_saddleZ D σc y
    exact hlin y hy
  have hZ_eq : ∀ y ∈ (D.φ D.j).source, Z y = cl_saddleZ D σc y := by
    intro y hy
    have h1 : Z y = ((((D.ρ D.j / 8 : ℝ)) : ℂ))⁻¹ * Zs y := by rw [hZdef]
    rw [h1, hZs_eq y hy, ← mul_assoc, inv_mul_cancel₀ hL, one_mul]
  -- smoothness of the two coordinates
  have hZs_sm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Zs (D.φ D.j).source := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => cl_chartZLM (φ' y)) (D.φ D.j).source :=
      cl_chartZLM.contMDiff.comp_contMDiffOn (by rw [← hsrc']; exact hsm')
    refine h1.congr (fun y _ => ?_)
    rw [cl_chartZLM_apply]
  have hZ_sm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source := by
    have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => cl_scaleCLM ((((D.ρ D.j / 8 : ℝ)) : ℂ))⁻¹ (Zs y)) (D.φ D.j).source :=
      (cl_scaleCLM _).contMDiff.comp_contMDiffOn hZs_sm
    refine h1.congr (fun y _ => ?_)
    rw [cl_scaleCLM_apply]
  have hZ_inj : Set.InjOn Z (D.φ D.j).source := by
    intro x hx y hy hxy
    rw [hZ_eq x hx, hZ_eq y hy] at hxy
    exact cl_injOn_saddleZ_source D hσc0 hx hy hxy
  have hZ_imm : ∀ x ∈ (D.φ D.j).source,
      Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) Z x) := by
    intro x hx
    have hev : Z =ᶠ[𝓝 x] cl_saddleZ D σc := by
      refine Filter.eventually_of_mem ((D.φ D.j).open_source.mem_nhds hx) ?_
      intro y hy
      exact hZ_eq y hy
    rw [Filter.EventuallyEq.mfderiv_eq hev]
    exact cl_injective_mfderiv_saddleZ_source D hσc0 hx
  -- the flow rows
  have hODE' : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        (chartMult ((D.ρ D.j / 8)) (‖φ' (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        (chartMult ((D.ρ D.j / 8)) (‖φ' (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t := by
    intro y t hy
    have htC : D.Φ (t, y) ∈ D.C D.j := hy t ⟨min_le_right _ _, le_max_right _ _⟩
    have htS : D.Φ (t, y) ∈ (D.φ D.j).source := D.hCsub D.j htC
    have hcont : ContinuousAt (fun σ : ℝ => D.Φ (σ, y)) t :=
      D.hΦsm.continuous.continuousAt.comp (by fun_prop)
    have hev : ∀ᶠ σ in 𝓝 t, D.Φ (σ, y) ∈ (D.φ D.j).source :=
      hcont.eventually ((D.φ D.j).open_source.mem_nhds htS)
    have hval0 : φ' (D.Φ (t, y)) 0 = (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (t, y))).re := by
      have hh := congrArg Complex.re (hlin (D.Φ (t, y)) htS)
      simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, cl_re_ofReal_mul] using hh
    have hval1 : φ' (D.Φ (t, y)) 1 = (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (t, y))).im := by
      have hh := congrArg Complex.im (hlin (D.Φ (t, y)) htS)
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, cl_im_ofReal_mul] using hh
    have hnorm : ‖φ' (D.Φ (t, y))‖ = (D.ρ D.j / 8) * ‖cl_saddleZ D σc (D.Φ (t, y))‖ := by
      rw [← cl_norm_chartZLM (φ' (D.Φ (t, y))), cl_chartZLM_apply, hlin (D.Φ (t, y)) htS,
        norm_mul, Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs,
        abs_of_pos hlam0pos]
    have harg : ‖φ' (D.Φ (t, y))‖ ^ 2
        = (D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (t, y))‖ ^ 2 := by
      rw [hnorm]; ring
    have hfun0 : (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
        =ᶠ[𝓝 t] (fun σ : ℝ => (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (σ, y))).re) := by
      filter_upwards [hev] with σ hσ
      have hh := congrArg Complex.re (hlin (D.Φ (σ, y)) hσ)
      simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, cl_re_ofReal_mul] using hh
    have hfun1 : (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
        =ᶠ[𝓝 t] (fun σ : ℝ => (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (σ, y))).im) := by
      filter_upwards [hev] with σ hσ
      have hh := congrArg Complex.im (hlin (D.Φ (σ, y)) hσ)
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, cl_im_ofReal_mul] using hh
    have hZc := cl_hasDerivAt_saddleZ D hs1 hs2 hσcn hre1 him2 him1 hre2 hy
    constructor
    · have h0 : HasDerivAt
          (fun σ : ℝ => (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (σ, y))).re)
          ((D.ρ D.j / 8) * (chartMult (D.ρ D.j / 8)
            ((D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (t, y))‖ ^ 2)
            * (cl_saddleZ D σc (D.Φ (t, y))).re)) t := hZc.1.const_mul _
      have hφ0 := h0.congr_of_eventuallyEq hfun0
      refine hφ0.congr_deriv ?_
      rw [← harg, hval0]
      ring
    · have h1 : HasDerivAt
          (fun σ : ℝ => (D.ρ D.j / 8) * (cl_saddleZ D σc (D.Φ (σ, y))).im)
          ((D.ρ D.j / 8) * (chartMult (D.ρ D.j / 8)
            ((D.ρ D.j / 8) ^ 2 * ‖cl_saddleZ D σc (D.Φ (t, y))‖ ^ 2)
            * (-(cl_saddleZ D σc (D.Φ (t, y))).im))) t := hZc.2.const_mul _
      have hφ1 := h1.congr_of_eventuallyEq hfun1
      refine hφ1.congr_deriv ?_
      rw [← harg, hval1]
      ring
  have hLast : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im := by
    intro y t hy
    exact im_sq_eq_of_flow_closedODE (Φ := D.Φ) φ' Zs (fun m => rfl) (D.ρ D.j / 8)
      hODE' D.hΦ0 y t hy
  refine ⟨φ', Zs, Z, D.ρ D.j / 8, hlam0pos, rfl, hsrc', hball', ?_, ?_, hZ_sm, hZ_inj, hZ_imm,
    ?_, ?_, hODE', hLast⟩
  · intro y
    show ((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I
      = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I
    rfl
  · intro y
    have h1 : Z y = ((((D.ρ D.j / 8 : ℝ)) : ℂ))⁻¹ * Zs y := by rw [hZdef]
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  · intro y hy
    rw [hZ_eq y hy]
    exact cl_saddleZ_level D hs1 hs2 hsgn hσcsq hy
  · intro y hy
    rw [hZs_eq y hy, pack_re_sq_ofReal_mul]
    exact cl_saddleZ_level D hs1 hs2 hsgn hσcsq hy

theorem saddlePack {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j) :
    ∃ (φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Zs Z : M → ℂ) (lam0 : ℝ),
      0 < lam0 ∧ lam0 = D.ρ D.j / 8 ∧
      φ'.source = (D.φ D.j).source ∧
      (∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall (D.φ D.j) r) ∧
      (∀ y : M, Zs y = (φ' y 0 : ℂ) + (φ' y 1 : ℂ) * Complex.I) ∧
      (∀ y : M, Zs y = (lam0 : ℂ) * Z y) ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source ∧
      Set.InjOn Z (D.φ D.j).source ∧
      (∀ x ∈ (D.φ D.j).source,
        Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℂ) Z x)) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re) ∧
      (∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re) ∧
      (∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 0)
          (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ' (D.Φ (t, y)) 0)) t ∧
        HasDerivAt (fun σ : ℝ => φ' (D.Φ (σ, y)) 1)
          (Work.Drive.N2.chartMult lam0 (‖φ' (D.Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ' (D.Φ (t, y)) 1)) t) ∧
      (∀ (y : M) (t : ℝ),
        (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
        ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im) := by
  rcases D.hsgn D.j with ⟨h1, h2⟩
  rcases h1 with h1 | h1
  · have hs2 : D.s₂ D.j = -1 := by linarith [hsgn, h1]
    exact saddlePack_aux D (Or.inl rfl) h1 hs2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hs2 : D.s₂ D.j = 1 := by linarith [hsgn, h1]
    have hI : Complex.I * Complex.I = (((-1 : ℝ)) : ℂ) := by
      rw [Complex.I_mul_I]; norm_num
    exact saddlePack_aux D (Or.inr rfl) h1 hs2 (by norm_num) hI (by simp) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)

end Work.Drive.N2
