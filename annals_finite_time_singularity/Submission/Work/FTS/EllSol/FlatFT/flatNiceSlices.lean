/-
Copyright: work module for the Elgindi finite-time singularity project.

# Slice and Plancherel facts for `NiceFlat` data

This file collects the `t`-Fourier-slice facts needed for `flat2DAgmonNice`:

* the `t`-support of a `NiceFlat` datum is uniformly compact, and the same holds for its
  `θ`-partials;
* the `t`-slices of the datum and of its `θ`-partials are smooth, so the slices `Φ_ξ` admit
  `θ`-derivatives which are the slices of the `θ`-partials (`slice_hasDerivAt`);
* `Φ_ξ` vanishes at `θ = 0` and `θ = π/2` (as *values*, for every `ξ`);
* the Plancherel identities at a fixed angle `θ`:
  `∫_ξ (2πξ)^{2k} ‖Φ_ξ(θ)‖² = ∫_t (∂_t^k g(t,θ))²` (`k = 0,1,2`),
  `∫_ξ (2πξ)² ‖Φ_ξ'(θ)‖² = ∫_t (∂_t∂_θg(t,θ))²` and
  `∫_ξ ‖Φ_ξ''(θ)‖² = ∫_t (∂_θ²g(t,θ))²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.slice_hasDerivAt
import Submission.Work.FTS.EllSol.FlatFT.pth_contDiffOn_succ
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
abbrev nfStrip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem nfStrip_isOpen : IsOpen nfStrip := isOpen_univ.prod isOpen_Ioo

variable {g : ℝ → ℝ → ℝ}

/-! ## The uniform support in `t` -/

theorem niceFlat_supp (hg : NiceFlat g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → g t θ = 0 := by
  obtain ⟨-, -, -, N, hN⟩ := hg
  exact ⟨max N 0, le_max_right _ _, fun t θ ht => hN t θ (lt_of_le_of_lt (le_max_left _ _) ht)⟩

theorem pth_eq_zero_of_forall {t θ : ℝ} (h : ∀ θ' : ℝ, g t θ' = 0) : pth g t θ = 0 := by
  simp only [pth]
  rw [show (fun θ' : ℝ => g t θ') = fun _ => (0 : ℝ) from funext h]
  simp

theorem pth_pth_eq_zero_of_forall {t θ : ℝ} (h : ∀ θ' : ℝ, pth g t θ' = 0) :
    pth (pth g) t θ = 0 := by
  simp only [pth] at h ⊢
  rw [show (fun θ' : ℝ => deriv (fun θ'' : ℝ => g t θ'') θ') = fun _ => (0 : ℝ) from funext h]
  simp

/-- The `t`-slice of a `NiceFlat` datum, as a complex-valued function, has compact support. -/
theorem niceFlat_hasCompactSupport (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (g t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [hM t θ hMt]

theorem niceFlat_hasCompactSupport_pth (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (pth g t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [pth_eq_zero_of_forall (fun θ' => hM t θ' hMt)]

theorem niceFlat_hasCompactSupport_pthpth (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (pth (pth g) t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [pth_pth_eq_zero_of_forall (fun θ' => pth_eq_zero_of_forall (fun θ'' => hM t θ'' hMt))]

/-! ## Smoothness of the `t`-slices -/

theorem contDiff_ofReal_comp {f : ℝ → ℝ} {n : ℕ} (h : ContDiff ℝ n f) :
    ContDiff ℝ n (fun t : ℝ => (f t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp h

theorem niceFlat_slice_contDiff (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    {n : ℕ} (hn : n ≤ 2) : ContDiff ℝ n (fun t : ℝ => g t θ) := by
  have hn' : (n : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by exact_mod_cast hn
  have h := (hg.1.of_le hn').comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ n (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

theorem niceFlat_slice_pth_contDiff (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {n : ℕ} (hn : n ≤ 1) :
    ContDiff ℝ n (fun t : ℝ => pth g t θ) := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (pth g)) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen hg.1
  have hn' : (n : WithTop ℕ∞) ≤ (1 : WithTop ℕ∞) := by exact_mod_cast hn
  have h := (h1.of_le hn').comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ n (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

theorem niceFlat_slice_pthpth_contDiff (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 0 (fun t : ℝ => pth (pth g) t θ) := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (pth g)) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen hg.1
  have h2 : ContDiffOn ℝ 0 (Function.uncurry (pth (pth g))) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen h1
  have h := h2.comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ 0 (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

/-! ## The derivative rule for the coercions -/

theorem deriv_ofReal_comp {f : ℝ → ℝ} {x : ℝ} (hd : DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ => (f t : ℂ)) x = ((deriv f x : ℝ) : ℂ) :=
  (hd.hasDerivAt.ofReal_comp).deriv

theorem normSq_ofReal' (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

theorem slice_eq_slice1' (g : ℝ → ℝ → ℝ) (ξ θ : ℝ) :
    slice g ξ θ = slice1 (fun t : ℝ => (g t θ : ℂ)) ξ := rfl

theorem slice_eq_zero (hg : NiceFlat g) (ξ : ℝ) : slice g ξ 0 = 0 := by
  simp only [slice]
  rw [show (fun t : ℝ => (g t 0 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      = fun _ => (0 : ℂ) from funext fun t => by rw [hg.2.1 t, Complex.ofReal_zero, zero_mul]]
  simp

theorem slice_eq_zero_pi (hg : NiceFlat g) (ξ : ℝ) : slice g ξ (Real.pi / 2) = 0 := by
  simp only [slice]
  rw [show (fun t : ℝ => (g t (Real.pi / 2) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      = fun _ => (0 : ℂ) from funext fun t => by rw [hg.2.2.1 t, Complex.ofReal_zero, zero_mul]]
  simp

/-! ## The Plancherel identities at a fixed angle -/

/-- `∫_ξ ‖Φ_ξ(θ)‖² = ∫_t g(t,θ)²`. -/
theorem plancherel_slice_zero (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, ‖slice g ξ θ‖ ^ 2 = ∫ t : ℝ, (g t θ) ^ 2 := by
  have hcont : Continuous (fun t : ℝ => (g t θ : ℂ)) :=
    (contDiff_ofReal_comp (niceFlat_slice_contDiff hg hθ (n := 0) (by norm_num))).continuous
  have hsupp := niceFlat_hasCompactSupport hg θ
  calc ∫ ξ : ℝ, ‖slice g ξ θ‖ ^ 2
      = ∫ ξ : ℝ, ‖slice1 (fun t : ℝ => (g t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [slice_eq_slice1']
    _ = ∫ t : ℝ, ‖(g t θ : ℂ)‖ ^ 2 := plancherelSlice1 _ hcont hsupp
    _ = ∫ t : ℝ, (g t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_ofReal' (g t θ))

/-- `∫_ξ (2πξ)²‖Φ_ξ(θ)‖² = ∫_t (∂_tg(t,θ))²`. -/
theorem plancherel_slice_one (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice g ξ θ‖ ^ 2 = ∫ t : ℝ, (pz g t θ) ^ 2 := by
  have hs1 := niceFlat_slice_contDiff hg hθ (n := 1) (by norm_num)
  have hcd := contDiff_ofReal_comp hs1
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hderiv : deriv (fun t : ℝ => (g t θ : ℂ)) = fun t : ℝ => (pz g t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hs1 (by norm_num)).differentiableAt]
    rfl
  calc ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice g ξ θ‖ ^ 2
      = ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice1 (fun t : ℝ => (g t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [slice_eq_slice1']
    _ = ∫ t : ℝ, ‖deriv (fun t : ℝ => (g t θ : ℂ)) t‖ ^ 2 :=
        plancherelSlice1Deriv _ hcd hsupp
    _ = ∫ t : ℝ, ‖(pz g t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, (pz g t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_ofReal' (pz g t θ))

/-- `∫_ξ (2πξ)⁴‖Φ_ξ(θ)‖² = ∫_t (∂_t²g(t,θ))²`. -/
theorem plancherel_slice_two (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 4 * ‖slice g ξ θ‖ ^ 2 = ∫ t : ℝ, (pz (pz g) t θ) ^ 2 := by
  have hs1 := niceFlat_slice_contDiff hg hθ (n := 1) (by norm_num)
  have hs2 := niceFlat_slice_contDiff hg hθ (n := 2) (by norm_num)
  have hcd1 := contDiff_ofReal_comp hs1
  have hsupp := niceFlat_hasCompactSupport hg θ
  have hderiv1 : deriv (fun t : ℝ => (g t θ : ℂ)) = fun t : ℝ => (pz g t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hs2 (by norm_num)).differentiableAt]
    rfl
  have hslice_deriv : ∀ ξ : ℝ,
      slice1 (fun t : ℝ => (pz g t θ : ℂ)) ξ = (2 * Real.pi * Complex.I * ξ) * slice g ξ θ := by
    intro ξ
    have h := slice1_deriv (fun t : ℝ => (g t θ : ℂ)) hcd1 hsupp ξ
    rw [hderiv1] at h
    rw [slice_eq_slice1']
    exact h
  have hpz_cd : ContDiff ℝ 1 (fun t : ℝ => pz g t θ) := by
    simp only [pz]
    fun_prop
  have hpz_supp : HasCompactSupport (fun t : ℝ => (pz g t θ : ℂ)) := by
    obtain ⟨M, -, hM⟩ := niceFlat_supp hg
    refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
    have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
    have hev : (fun t' : ℝ => g t' θ) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      have hopen : {t' : ℝ | M < |t'|} ∈ 𝓝 t :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds hMt
      filter_upwards [hopen] with t' ht'
      exact hM t' θ ht'
    have hzero : pz g t θ = 0 := by
      simp only [pz]
      rw [hev.deriv_eq]
      simp
    simp [hzero]
  have h := plancherelSlice1Deriv (fun t : ℝ => (pz g t θ : ℂ))
    (contDiff_ofReal_comp hpz_cd) hpz_supp
  have hderiv2 : deriv (fun t : ℝ => (pz g t θ : ℂ)) = fun t : ℝ => (pz (pz g) t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hpz_cd (by norm_num)).differentiableAt]
    rfl
  calc ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 4 * ‖slice g ξ θ‖ ^ 2
      = ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2
          * ‖slice1 (fun t : ℝ => (pz g t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [hslice_deriv ξ, norm_sq_mul_two_pi_I]
        ring
    _ = ∫ t : ℝ, ‖deriv (fun t : ℝ => (pz g t θ : ℂ)) t‖ ^ 2 := h
    _ = ∫ t : ℝ, ‖(pz (pz g) t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv2]
    _ = ∫ t : ℝ, (pz (pz g) t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_ofReal' (pz (pz g) t θ))

/-- `∫_ξ (2πξ)²‖Φ_ξ'(θ)‖² = ∫_t (∂_t∂_θg(t,θ))²`. -/
theorem plancherel_slice_mixed (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2
      = ∫ t : ℝ, (pz (pth g) t θ) ^ 2 := by
  have hs1 := niceFlat_slice_pth_contDiff hg hθ (n := 1) (by norm_num)
  have hcd := contDiff_ofReal_comp hs1
  have hsupp := niceFlat_hasCompactSupport_pth hg θ
  have hderiv : deriv (fun t : ℝ => (pth g t θ : ℂ)) = fun t : ℝ => (pz (pth g) t θ : ℂ) := by
    funext t
    rw [deriv_ofReal_comp (ContDiff.differentiable hs1 (by norm_num)).differentiableAt]
    rfl
  calc ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖deriv (fun θ' => slice g ξ θ') θ‖ ^ 2
      = ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2
          * ‖slice1 (fun t : ℝ => (pth g t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [(slice_hasDerivAt g hg ξ hθ).1.deriv, slice_eq_slice1']
    _ = ∫ t : ℝ, ‖deriv (fun t : ℝ => (pth g t θ : ℂ)) t‖ ^ 2 :=
        plancherelSlice1Deriv _ hcd hsupp
    _ = ∫ t : ℝ, ‖(pz (pth g) t θ : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hderiv]
    _ = ∫ t : ℝ, (pz (pth g) t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => normSq_ofReal' (pz (pth g) t θ))

/-- `∫_ξ ‖Φ_ξ''(θ)‖² = ∫_t (∂_θ²g(t,θ))²`. -/
theorem plancherel_slice_pthpth (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2
      = ∫ t : ℝ, (pth (pth g) t θ) ^ 2 := by
  have hs0 := niceFlat_slice_pthpth_contDiff hg hθ
  have hcont : Continuous (fun t : ℝ => (pth (pth g) t θ : ℂ)) :=
    (contDiff_ofReal_comp hs0).continuous
  have hsupp := niceFlat_hasCompactSupport_pthpth hg θ
  calc ∫ ξ : ℝ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2
      = ∫ ξ : ℝ, ‖slice1 (fun t : ℝ => (pth (pth g) t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        have hev : (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') =ᶠ[𝓝 θ]
            (fun θ' => slice (pth g) ξ θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
          exact (slice_hasDerivAt g hg ξ hθ').1.deriv
        rw [hev.deriv_eq, (slice_hasDerivAt g hg ξ hθ).2.deriv, slice_eq_slice1']
    _ = ∫ t : ℝ, ‖(pth (pth g) t θ : ℂ)‖ ^ 2 := plancherelSlice1 _ hcont hsupp
    _ = ∫ t : ℝ, (pth (pth g) t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t =>
          normSq_ofReal' (pth (pth g) t θ))

end

end Work.FTS.EllSol.FlatFT
