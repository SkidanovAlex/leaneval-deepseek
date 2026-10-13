/-
# `Work.FTS.PhiStar.FamDerivDivLinv` — the resummation identity `∂_θ(e_m / sin 2θ) = Linv (λ_m e_m)`

With the Dirichlet eigenbasis `e_m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` of `L₀` (eigenvalue
`λ_m = 2m(2m+5)`, `Gegenbauer.eFam_Lzero`) and the zero-moment inverse

  `Linv h θ = -(sin²θ cos³θ)⁻¹ ∫_0^θ sin²t cos³t · h t / sin 2t dt`,

the claim of this file is the pointwise identity on `(0, π/2)`

  `∂_θ (e_m θ / sin 2θ) = Linv (λ_m · e_m) θ`.

**Why it is true.**  Write `σ = sin 2θ`, `μ = σ² cos θ / 4 = sin²θ cos³θ`, `v = e_m/σ`, `W = v'`
and `H = λ_m e_m`.  The substitution identity `Lzero1_sin2_mul` together with the eigenvalue
equation `eFam_Lzero` gives the second-order equation

  `H = -σ W' + (6 - 10 cos²θ) W`,   i.e.  `σ W' = (6 - 10 cos²θ) W - H`,

on `(0, π/2)`.  Multiplying by `μ/σ` and using the elementary trigonometric identity
`σμ' + μ(6 - 10cos²θ) = 0` (i.e. `2 sinθ cos⁴θ - 3 sin³θ cos²θ
+ sin²θcos³θ(6 - 10cos²θ)/(2 sinθ cosθ) = 0`) gives

  `(μ W)' = -μ H / σ`   on `(0, π/2)`.

Since `Linv h` is exactly `-μ⁻¹ ∫_0^θ μ h/σ`, the function `Φ = μ W + ∫_0^θ μH/σ` is a primitive
of `0` on `(0, π/2)`, hence constant there; and `Φ` tends to `0` at `0⁺` (`∫_0^θ μH/σ` is
`O(θ²)` by `abs_LinvPrim_le`, and `μ W = (cos θ/4)(e_m'·σ - e_m·σ')` tends to
`(1/4)(e_m'(0)·0 - e_m(0)·2) = 0` because `gC (2m+1) 0 = 0`).  So `Φ ≡ 0`, i.e.
`μ W = -∫_0^θ μH/σ`, which after multiplying by `-μ⁻¹` is the claim.

The only "hard" ingredients are `Lzero1_sin2_mul` (`LinvI_solves`) and the elementary limit
analysis above; everything else is bookkeeping.

**Note on the notation `π`.**  The statement is the one requested; `open scoped Real` is needed
for `π` to denote `Real.pi` (as in every other module of this chapter).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.LinvI_solves
import Submission.Work.FTS.PhiStar.PsiDivS2Ode
import Submission.Work.FTS.PhiStar.LinvFlat.Linv_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts about `eFam`, `s2` and `μ` -/

/-- `eFam m 0 = 0`: the Dirichlet eigenfunctions vanish at the left endpoint (the odd-indexed
Gegenbauer polynomials vanish at the origin). -/
lemma eFam_zero_end (m : ℕ) : Gegenbauer.eFam m 0 = 0 := by
  simp only [Gegenbauer.eFam, Real.sin_zero, Real.cos_zero, one_mul]
  exact Gegenbauer.gC_odd_zero m

/-- The angular eigenfunctions are `C³`. -/
lemma contDiff_eFam_fam (m : ℕ) : ContDiff ℝ 3 (Gegenbauer.eFam m) :=
  Real.contDiff_cos.mul ((Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

/-- `deriv (sin (2·)) = 2 cos (2·)`. -/
lemma deriv_s2_fam : deriv Work.Construction.s2 = fun t : ℝ => 2 * Real.cos (2 * t) := by
  funext t
  have h : HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (Real.cos (2 * t) * 2) t :=
    (Real.hasDerivAt_sin (2 * t)).comp t (by simpa using (hasDerivAt_id t).const_mul 2)
  rw [show Work.Construction.s2 = fun s : ℝ => Real.sin (2 * s)
    from funext Work.Construction.s2_eq, h.deriv]
  ring

lemma differentiable_s2_fam : Differentiable ℝ Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun s : ℝ => Real.sin (2 * s)
    from funext Work.Construction.s2_eq]
  fun_prop

/-- `sin 2θ` vanishes at the origin. -/
lemma s2_zero_end : Work.Construction.s2 0 = 0 := by
  rw [Work.Construction.s2_eq, mul_zero, Real.sin_zero]

/-! ## Differentiability of `v = e_m / sin 2θ` and of `v'` -/

lemma differentiableOn_div_s2 (m : ℕ) :
    DifferentiableOn ℝ (fun t : ℝ => Gegenbauer.eFam m t / Work.Construction.s2 t)
      (Set.Ioo 0 (π / 2)) := by
  intro t ht
  exact ((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt
    |>.div (differentiable_s2_fam.differentiableAt) (linv_s2_ne_zero ht)
    |>.differentiableWithinAt

/-- The explicit form of `v'` on the open interval. -/
lemma deriv_div_s2_eventuallyEq (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) =ᶠ[𝓝 t]
      fun s : ℝ => (deriv (Gegenbauer.eFam m) s * Work.Construction.s2 s
        - Gegenbauer.eFam m s * deriv Work.Construction.s2 s)
          / Work.Construction.s2 s ^ 2 := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  have hde : HasDerivAt (Gegenbauer.eFam m) (deriv (Gegenbauer.eFam m) s) s :=
    (((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt).hasDerivAt
  have hds : HasDerivAt Work.Construction.s2 (deriv Work.Construction.s2 s) s :=
    (differentiable_s2_fam.differentiableAt).hasDerivAt
  exact (hde.div hds (linv_s2_ne_zero hs)).deriv

/-- The explicit value of `v'` at a point of the open interval. -/
lemma deriv_div_s2_eq (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) t
      = (deriv (Gegenbauer.eFam m) t * Work.Construction.s2 t
        - Gegenbauer.eFam m t * deriv Work.Construction.s2 t)
          / Work.Construction.s2 t ^ 2 :=
  (deriv_div_s2_eventuallyEq m ht).eq_of_nhds

/-- `v'` is differentiable on the open interval. -/
lemma differentiableOn_deriv_div_s2 (m : ℕ) :
    DifferentiableOn ℝ (deriv (fun t : ℝ => Gegenbauer.eFam m t / Work.Construction.s2 t))
      (Set.Ioo 0 (π / 2)) := by
  intro t ht
  refine (DifferentiableAt.congr_of_eventuallyEq ?_
    (deriv_div_s2_eventuallyEq m ht)).differentiableWithinAt
  have hde : DifferentiableAt ℝ (deriv (Gegenbauer.eFam m)) t :=
    ((ContDiff.deriv' (n := 2) (contDiff_eFam_fam m)).differentiable (by norm_num)).differentiableAt
  have hds : DifferentiableAt ℝ (deriv Work.Construction.s2) t := by
    rw [deriv_s2_fam]; fun_prop
  have he : DifferentiableAt ℝ (Gegenbauer.eFam m) t :=
    ((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt
  have hs2 : DifferentiableAt ℝ Work.Construction.s2 t := differentiable_s2_fam.differentiableAt
  exact ((hde.mul hs2).sub (he.mul hds)).div (hs2.pow 2) (pow_ne_zero 2 (linv_s2_ne_zero ht))

/-! ## The `Lzero1`-congruence and the second-order equation for `v` -/

/-- `Lzero1` only depends on the germ of the function. -/
lemma Lzero1_congr_of_eventuallyEq {f g : ℝ → ℝ} {θ : ℝ} (h : f =ᶠ[𝓝 θ] g) :
    Work.FTS.EllipticEst.Lzero1 f θ = Work.FTS.EllipticEst.Lzero1 g θ := by
  simp only [Work.FTS.EllipticEst.Lzero1]
  have h2 : deriv (deriv f) θ = deriv (deriv g) θ := h.deriv.deriv_eq
  have h3 : (fun t : ℝ => Real.tan t * f t) =ᶠ[𝓝 θ] (fun t : ℝ => Real.tan t * g t) :=
    (Filter.EventuallyEq.refl (𝓝 θ) (fun t : ℝ => Real.tan t)).mul h
  rw [h2, h3.deriv_eq, h.eq_of_nhds]

/-- The second-order equation satisfied by `v = e_m / sin 2θ`: with `H = λ_m e_m`,

  `-sin 2θ · v'' + (6 - 10 cos²θ) v' = H`. -/
lemma deriv2_ode (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    -Real.sin (2 * x)
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      + (6 - 10 * Real.cos x ^ 2)
        * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
      = Gegenbauer.lam m * Gegenbauer.eFam m x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hsub := Lzero1_sin2_mul (v := fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)
    hx (differentiableOn_div_s2 m) (differentiableOn_deriv_div_s2 m)
  have hcongr : Work.FTS.EllipticEst.Lzero1
        (fun s : ℝ => Real.sin (2 * s) * (Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = Work.FTS.EllipticEst.Lzero1 (Gegenbauer.eFam m) x := by
    refine Lzero1_congr_of_eventuallyEq ?_
    have hmem : ∀ᶠ s in 𝓝 x, Work.Construction.s2 s ≠ 0 :=
      continuous_s2.continuousAt.eventually_ne (linv_s2_ne_zero hx)
    filter_upwards [hmem] with s hs
    show Real.sin (2 * s) * (Gegenbauer.eFam m s / Work.Construction.s2 s) = Gegenbauer.eFam m s
    rw [← Work.Construction.s2_eq, mul_div_assoc', mul_div_cancel_left₀ _ hs]
  have hLz : Work.FTS.EllipticEst.Lzero1 (Gegenbauer.eFam m) x
      = Gegenbauer.lam m * Gegenbauer.eFam m x := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero (Gegenbauer.eFam m) 0]
    exact Gegenbauer.eFam_Lzero m hcos 0
  exact (hsub.symm.trans hcongr).trans hLz

/-! ## The key algebraic identity and the derivative of `μ v'` -/

/-- `σμ' + μ(6 - 10cos²θ) = 0` with `σ = sin 2θ`, `μ = sin²θcos³θ` — the reason
`(μ v')' = -μ H/σ` follows from the second-order equation. -/
lemma linv_mu_key (x : ℝ) :
    Real.sin (2 * x) * (2 * Real.sin x * Real.cos x ^ 4 - 3 * Real.sin x ^ 3 * Real.cos x ^ 2)
      + (Real.sin x ^ 2 * Real.cos x ^ 3) * (6 - 10 * Real.cos x ^ 2) = 0 := by
  have h1 := Real.sin_sq_add_cos_sq x
  rw [Real.sin_two_mul]
  linear_combination (-(6 * Real.sin x ^ 2 * Real.cos x ^ 3)) * h1

/-- The value of the derivative of `θ ↦ μ θ · v' θ` on the open interval:

  `(2 sinθcos⁴θ - 3 sin³θcos²θ) v' + μ v'' = -μ H / sin 2θ`. -/
lemma linvMu_mul_deriv_value (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    (2 * Real.sin x * Real.cos x ^ 4 - 3 * Real.sin x ^ 3 * Real.cos x ^ 2)
        * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
      + LinvMu x
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = -(LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x)
          / Work.Construction.s2 x) := by
  have hσ : Real.sin (2 * x) ≠ 0 := by
    rw [← Work.Construction.s2_eq]; exact linv_s2_ne_zero hx
  have hODE := deriv2_ode m hx
  have hODE' : Real.sin (2 * x)
        * deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = (6 - 10 * Real.cos x ^ 2)
          * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
        - Gegenbauer.lam m * Gegenbauer.eFam m x := by
    linarith [hODE]
  have hW' : deriv (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s)) x
      = ((6 - 10 * Real.cos x ^ 2)
            * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x
          - Gegenbauer.lam m * Gegenbauer.eFam m x) / Real.sin (2 * x) := by
    rw [eq_div_iff hσ]; linarith [hODE']
  have hkey := linv_mu_key x
  rw [hW', LinvMu, show Work.Construction.s2 x = Real.sin (2 * x)
    from Work.Construction.s2_eq x]
  field_simp
  linear_combination (deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) x) * hkey

/-! ## A bound for the source and the limits at `0⁺` -/

/-- `s ↦ λ_m e_m(s)` is bounded on the open angular interval. -/
lemma lam_eFam_bdd (m : ℕ) :
    ∃ M : ℝ, ∀ s ∈ Set.Ioo 0 (π / 2),
      |Gegenbauer.lam m * Gegenbauer.eFam m s| ≤ M := by
  have hcont : ContinuousOn (fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (Set.Icc 0 (π / 2)) :=
    (continuous_const.mul ((contDiff_eFam_fam m).continuous)).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun s hs => by
    have h := hM s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    rwa [Real.norm_eq_abs] at h⟩

lemma lam_eFam_contOn (m : ℕ) :
    ContinuousOn (fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (Set.Ioo 0 (π / 2)) :=
  (continuous_const.mul ((contDiff_eFam_fam m).continuous)).continuousOn

/-- `ε ↦ μ ε · v' ε → 0` at `0⁺`: on `(0, π/2)` it equals the continuous expression
`(cos ε/4)(e_m' ε · sin 2ε - e_m ε · (sin 2·)' ε)`, whose value at `0` is `0`. -/
lemma tendsto_linvMu_mul_deriv_div_s2 (m : ℕ) :
    Tendsto (fun ε : ℝ =>
        LinvMu ε * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcont : ContinuousAt (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε)) 0 := by
    refine ContinuousAt.mul ?_ ?_
    · exact (Real.continuous_cos.continuousAt).div_const 4
    · refine ContinuousAt.sub (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul ?_ ?_)
      · exact (ContDiff.deriv' (n := 2) (contDiff_eFam_fam m)).continuous.continuousAt
      · exact differentiable_s2_fam.continuous.continuousAt
      · exact (contDiff_eFam_fam m).continuous.continuousAt
      · rw [deriv_s2_fam]; fun_prop
  have h0 : Real.cos 0 / 4 * (deriv (Gegenbauer.eFam m) 0 * Work.Construction.s2 0
      - Gegenbauer.eFam m 0 * deriv Work.Construction.s2 0) = 0 := by
    simp [eFam_zero_end m]
  have hlim : Tendsto (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h1 := hcont.tendsto
    rwa [h0] at h1
  have hlim' : Tendsto (fun ε : ℝ => Real.cos ε / 4
      * (deriv (Gegenbauer.eFam m) ε * Work.Construction.s2 ε
        - Gegenbauer.eFam m ε * deriv Work.Construction.s2 ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hlim.mono_left nhdsWithin_le_nhds
  refine hlim'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])] with ε hε
  refine (Eq.symm ?_)
  have hε' : ε ∈ Set.Ioo 0 (π / 2) := ⟨hε.1, hε.2⟩
  have hsin : Real.sin ε ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hε.1 (by linarith [Real.pi_pos, hε.2]))
  have hcos : Real.cos ε ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hε.1], hε.2⟩)
  have hval : LinvMu ε / Work.Construction.s2 ε ^ 2 = Real.cos ε / 4 := by
    rw [LinvMu, Work.Construction.s2_eq, Real.sin_two_mul]
    field_simp
    ring
  rw [deriv_div_s2_eq m hε', mul_div_assoc', mul_div_right_comm, hval]

/-- `ε ↦ ∫_0^ε μ H / sin 2θ → 0` at `0⁺` (`O(ε²)`). -/
lemma tendsto_LinvPrim_fam (m : ℕ) :
    Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..ε,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨M, hM⟩ := lam_eFam_bdd m
  have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(∫ s in (0 : ℝ)..ε,
          LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)‖
        ≤ M * ε ^ 2 / 4 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])] with ε hε
    rw [Real.norm_eq_abs]
    exact abs_LinvPrim_le (lam_eFam_contOn m) hM ⟨hε.1, hε.2⟩ ⟨hε.1, le_rfl⟩
  have hg : Tendsto (fun ε : ℝ => M * ε ^ 2 / 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h2 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun ε : ℝ => ε ^ 2 := by fun_prop
      simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun ε : ℝ => M * ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (M * 0)) := h2.const_mul M
    rw [mul_zero] at h3
    have h4 : Tendsto (fun ε : ℝ => M * ε ^ 2 / 4) (𝓝[>] (0 : ℝ)) (𝓝 (0 / 4)) := h3.div_const 4
    rwa [zero_div] at h4
  have habs : Tendsto (fun ε : ℝ => ‖(∫ s in (0 : ℝ)..ε,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbd hg
  exact tendsto_zero_iff_norm_tendsto_zero.mpr habs

/-! ## The constancy argument -/

/-- `Φ m t = μ t · v'(t) + ∫_0^t μ H / sin 2θ`, the quantity whose constancy on `(0, π/2)`
encodes the identity `μ v' = -∫_0^· μH/σ`. -/
def PhiFam (m : ℕ) : ℝ → ℝ := fun t : ℝ =>
  LinvMu t * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) t
    + ∫ s in (0 : ℝ)..t,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s

lemma PhiFam_apply (m : ℕ) (t : ℝ) :
    PhiFam m t = LinvMu t * deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) t
      + ∫ s in (0 : ℝ)..t,
          LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s := rfl

/-- The derivative of `Φ = μ v' + ∫_0^θ μH/σ` vanishes at every point of `(0, π/2)`. -/
lemma PhiFam_hasDerivAt_zero (m : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (PhiFam m) 0 x := by
  set V : ℝ → ℝ :=
    deriv (fun s : ℝ => Gegenbauer.eFam m s / Work.Construction.s2 s) with hV
  have hW : HasDerivAt V (deriv V x) x :=
    ((differentiableOn_deriv_div_s2 m x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hA : HasDerivAt (fun t : ℝ => LinvMu t * V t)
      (-(LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x) / Work.Construction.s2 x)) x := by
    refine ((hasDerivAt_LinvMu x).mul hW).congr_deriv ?_
    exact linvMu_mul_deriv_value m hx
  have hB : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s)
      (LinvMu x * (Gegenbauer.lam m * Gegenbauer.eFam m x) / Work.Construction.s2 x) x :=
    hasDerivAt_LinvPrim (h := fun s : ℝ => Gegenbauer.lam m * Gegenbauer.eFam m s)
      (lam_eFam_contOn m) (lam_eFam_bdd m) hx
  exact (hA.add hB).congr_deriv (by ring)

/-- `Φ = μ v' + ∫_0^θ μH/σ` vanishes identically on `(0, π/2)`. -/
lemma PhiFam_eq_zero (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : PhiFam m θ = 0 := by
  have hderiv : ∀ x ∈ Set.Ioo 0 (π / 2), HasDerivAt (PhiFam m) 0 x :=
    fun x hx => PhiFam_hasDerivAt_zero m hx
  have hconst : ∀ ε : ℝ, 0 < ε → ε < θ → PhiFam m θ = PhiFam m ε := by
    intro ε hε0 hεθ
    have hmin : min ε θ = ε := min_eq_left hεθ.le
    have hmax : max ε θ = θ := max_eq_right hεθ.le
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := PhiFam m) (f' := fun _ : ℝ => 0)
      (a := ε) (b := θ)
      (fun y hy => hderiv y ⟨lt_of_lt_of_le hε0 (by rw [← hmin]; exact hy.1),
        lt_of_le_of_lt (by rw [← hmax]; exact hy.2) hθ.2⟩)
      intervalIntegrable_const
    rw [intervalIntegral.integral_zero] at h
    linarith
  have hlim0 : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 (0 + 0)) :=
      (tendsto_linvMu_mul_deriv_div_s2 m).add (tendsto_LinvPrim_fam m)
    rwa [add_zero] at h
  have hevent : PhiFam m =ᶠ[𝓝[>] (0 : ℝ)] fun _ => PhiFam m θ := by
    filter_upwards [Ioo_mem_nhdsGT hθ.1] with ε hε
    exact (hconst ε hε.1 hε.2).symm
  have hlimθ : Tendsto (PhiFam m) (𝓝[>] (0 : ℝ)) (𝓝 (PhiFam m θ)) :=
    tendsto_const_nhds.congr' hevent.symm
  have h00 : (0 : ℝ) = PhiFam m θ := tendsto_nhds_unique hlim0 hlimθ
  exact h00.symm

/-! ## The target identity -/

theorem FamDerivDivLinv (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : deriv (fun θ' => Work.FTS.PhiStar.Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ = Work.FTS.PhiStar.Linv (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
  have hΦ := PhiFam_eq_zero m hθ
  have hΦ' : LinvMu θ * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ
      + (∫ s in (0 : ℝ)..θ,
          LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s) = 0 := hΦ
  have hμ : LinvMu θ ≠ 0 := LinvMu_ne_zero_of_mem_Ioo hθ
  have hIP : LinvPrim (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') θ
      = -(LinvMu θ * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ) := by
    change (∫ s in (0 : ℝ)..θ,
        LinvMu s * (Gegenbauer.lam m * Gegenbauer.eFam m s) / Work.Construction.s2 s) = _
    linarith [hΦ']
  rw [Linv_apply, hIP]
  have hfin : -((LinvMu θ)⁻¹ * -(LinvMu θ
        * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ))
      = deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ := by
    rw [show -((LinvMu θ)⁻¹ * -(LinvMu θ
          * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ))
        = ((LinvMu θ)⁻¹ * LinvMu θ)
          * deriv (fun θ' => Gegenbauer.eFam m θ' / Work.Construction.s2 θ') θ from by ring,
      inv_mul_cancel₀ hμ, one_mul]
  exact hfin.symm

end Work.FTS.PhiStar
