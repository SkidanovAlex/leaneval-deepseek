import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.factor_prod_prof
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.H2.StarPkg.divZWlInf_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.dthIter_Vs_le_WlInf
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.dthIter_Gam_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Lop_iter_mul_of_contDiffOn
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0_interval_lower
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.theta_majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-!
# Row 19 — the `Vs0`-part of the coefficient contributes nothing to the `ℋ⁴`-norm

The target is `Work.Spaces.HkSq α 4 f = 0` for

  `f(z,θ) = V(Φ̃_*)(0,θ) · D_zF_*(z,θ)`.

Because `D_zF_*(z,θ) = (αΓ(θ)/c)·prof(z)` (`Vs0Defs.Gs_eq_prof`), the coefficient factorises
as `f = proff · Ufun` with `proff(z) = 2z(1−z)/(1+z)³` and
`Ufun(θ) = V(Φ̃_*)(0,θ)·αΓ(θ)/c` (this is the content of `factor_prod_prof`).

Two cases:

* if `Ufun` vanishes on `(0,π/2)` then so does every `θ`-derivative of `f` on the open
  quadrant, and at the two endpoints the weights `w/sin(2θ)^{η/2}`, `Wt` vanish: the whole
  `ℋ⁴`-integrand is `0` pointwise, hence `HkSq = 0`;
* otherwise `Ufun` is nonzero somewhere in `(0,π/2)`, so near `z = 0` the `i = 0` term of the
  integrand is `≥ c/z²`; the `θ`-integral of the integrand is therefore `≥ c'/z²`, its
  `z`-integral diverges at the origin, and by the totalised convention of the Bochner integral
  (`MeasureTheory.integral_undef`) the value of `HkSq` is `0`.
-/

/-! ## Smoothness of the factorisation -/

/-- The radial profile `2z(1−z)/(1+z)³` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_prof :
    ContDiffOn ℝ Work.Stability.smoothOrder prof (Set.Ioi (-1 : ℝ)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 2 * z * (1 - z)) (Set.Ioi (-1 : ℝ)) := by fun_prop
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (-1 : ℝ)) := by fun_prop
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < 1 + z := by
      rw [Set.mem_Ioi] at hz; linarith
    exact pow_ne_zero 3 (ne_of_gt h1)
  have h := hnum.div hden hne
  refine h.congr ?_
  intro z _
  simp only [Pi.div_apply, prof]

/-- `proff` is `SmoothQuad`. -/
theorem smoothQuad_proff : Work.FTS.LocData.SmoothQuad proff := by
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_fst
  have h := contDiffOn_prof.comp hfst (fun p hp => hp.1)
  have h' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => proff p.1 p.2)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := h
  exact h'

/-- The `θ`-slice `Vs0 = V(Φ̃_*)(0,·)` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_Vs0_theta {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Vs0 α Φs θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h : Work.FTS.LocData.SmoothQuad (Vs0f α Φs) :=
    contDiffOn_Vs0f (α := α) (Cs := Cs) (Φs := Φs) hα hs
  exact Work.FTS.LocData.SmoothQuad.curry_θ h
    (show (0 : ℝ) ∈ Set.Ioi (-1) by norm_num)

/-- The angular factor `Ufun α Φs` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_Ufun {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Ufun α Φs) (Set.Ioo 0 (Real.pi / 2)) := by
  have hV := contDiffOn_Vs0_theta (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hG := Work.FTS.LocData.contDiffOn_Gam_Ioo α
  have hc : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun _ : ℝ => α / Work.Spaces.c α) (Set.Ioo 0 (Real.pi / 2)) := contDiffOn_const
  have h := hV.mul (hc.mul hG)
  refine h.congr ?_
  intro θ _
  simp only [Ufun]
  ring

/-- The factorised row-19 coefficient `proff·Ufun` is `SmoothQuad`. -/
theorem smoothQuad_fFac {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad (fun z θ => proff z θ * Ufun α Φs θ) := by
  have hV : Work.FTS.LocData.SmoothQuad (fun z θ => Vs0 α Φs θ) :=
    Work.FTS.LocData.smoothQuad_of_snd (contDiffOn_Vs0_theta (α := α) (Cs := Cs) (Φs := Φs) hα hs)
  have hG : Work.FTS.LocData.SmoothQuad (fun z θ => Work.Spaces.Gam α θ) :=
    Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α)
  have h2 : Work.FTS.LocData.SmoothQuad
      (fun z θ => (α / Work.Spaces.c α) * (Vs0 α Φs θ * Work.Spaces.Gam α θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul (α / Work.Spaces.c α)
      (Work.FTS.LocData.smoothQuad_mul hV hG)
  have h := Work.FTS.LocData.smoothQuad_mul smoothQuad_proff h2
  refine h.congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, Ufun]
  ring

/-- The `ℋ⁴`-integrand of the factorised coefficient is continuous on the open quadrant. -/
theorem continuousOn_HkIntegrand_fFac {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 _
    (smoothQuad_fFac (α := α) (Cs := Cs) (Φs := Φs) hα hs)

/-! ## The open-interval `angmul` vanishing -/

/-- If the angular profile `a` vanishes on the open interval `(0,π/2)`, then every
`D_θ`-iterate of `a·f` vanishes on the closed interval `Iθ` (for `i ≥ 1`).  This is the
open-interval form of `Work.FTS.Nonlinear.N4Fields.DthIter_angmul_eq_zero`, which is what the
`Vs0`-case of the row needs (`Vs0` is only known to vanish on the *open* interval). -/
theorem DthIter_angmul_eq_zero_open (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (ha0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), a θ = 0) :
    ∀ i : ℕ, 1 ≤ i → ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.DthIter i (fun z θ => a θ * f z θ) z θ = 0 := by
  -- the one-step statement on the open interval
  have hstep : ∀ (G : ℝ → ℝ → ℝ),
      (∀ z θ', θ' ∈ Set.Ioo 0 (Real.pi / 2) → G z θ' = 0) →
      ∀ z θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Work.Spaces.Dth G z θ = 0 := by
    intro G hG z θ hθ
    rw [Work.Spaces.Dth, Work.Spaces.pth]
    have hnb : (fun θ' : ℝ => G z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with θ' hθ'
      exact hG z θ' hθ'
    rw [hnb.deriv_eq, deriv_const, mul_zero]
  have hmain : ∀ i : ℕ, 1 ≤ i → ∀ z θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DthIter i (fun z θ => a θ * f z θ) z θ = 0 := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ m ih =>
        intro _ z θ hθ
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · subst h0
          exact hstep (fun z θ => a θ * f z θ)
            (fun z θ' hθ' => by rw [ha0 θ' hθ', zero_mul]) z θ hθ
        · rw [Work.Spaces.DthIter_succ]
          exact hstep (Work.Spaces.DthIter m (fun z θ => a θ * f z θ))
            (fun z θ' hθ' => ih hpos z θ' hθ') z θ hθ
  intro i hi z θ hθ
  by_cases h : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · exact hmain i hi z θ h
  · have hsin : Real.sin (2 * θ) = 0 := by
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0]; simp
      · have h1 : θ = Real.pi / 2 := by
          rcases eq_or_lt_of_le hθ.2 with h2 | h2
          · exact h2
          · exact absurd ⟨h0, h2⟩ h
        rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    exact Work.Coercivity.DthIter_eq_zero_of_sin_eq_zero
      (fun z θ => a θ * f z θ) i hi θ hsin z

/-! ### Placeholders for lemmas proved in parallel by the fleet

These five statements are being proved in sibling files of this directory; they are stated here
temporarily so that the main argument type-checks against their interfaces. -/

/-! ## Case B: the angular-derivative bound on the factor -/

/-- `Lop`-iterates of a constant multiple. -/
lemma Lop_iter_const_mul (c : ℝ) (u : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.Lop^[i] (fun θ => c * u θ) = fun θ => c * Work.Spaces.Lop^[i] u θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.Lop]
      rw [deriv_const_mul_field]
      ring

/-- On `Iθ` the angular weight `(α + sin 2θ)·sin(2θ)^{α/5}` is nonnegative. -/
lemma angW_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact mul_nonneg (add_nonneg (le_of_lt hα) h0) (Real.rpow_nonneg h0 _)

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on `Iθ`, for `α > 0`. -/
lemma rpow_neg_eta_le_neg_gam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    have := Work.Spaces.eta_lt_one
    rw [Work.Spaces.gam]
    linarith
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, Real.zero_rpow (by have := Work.Spaces.eta_pos; linarith : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (by rw [Work.Spaces.gam]; have := Work.Spaces.eta_pos; linarith)]
  · exact Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) (by linarith)

/-- **The `θ`-derivative bound on the angular factor**: for every `i ≤ 4`,
`|D_θ^i U| ≤ C·(Γ + (α + sin 2θ)·sin(2θ)^{α/5})`. -/
theorem Lop_iter_Ufun_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Lop^[i] (Ufun α Φs) θ|
        ≤ C * (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨Cg₀, hCg₀pos, hCg₀⟩ := dthIter_Gam_le (α := α) hα
  set Cg : ℝ := max Cg₀ 1 with hCgdef
  have hCgpos : 0 < Cg := lt_max_of_lt_right zero_lt_one
  have hCg1 : (1 : ℝ) ≤ Cg := le_max_right _ _
  have hCg : ∀ i : ℕ, i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Lop^[i] (fun θ => Work.Spaces.Gam α θ) θ| ≤ Cg * Work.Spaces.Gam α θ := by
    intro i hi θ hθ
    refine le_trans (hCg₀ i hi θ hθ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hc0 : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le (c_pos_of_pos hα).le
  set A : ℝ := Work.Spaces.WlInf α 4 (Vs α Φs) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef, Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hs.V.1)
      (Work.Spaces.wlThSum_nonneg α 4 _ hs.V.1)
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hAc0 : 0 ≤ A * (α / Work.Spaces.c α) :=
    mul_nonneg hA0 (div_nonneg hα.le hcpos.le)
  refine ⟨(1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg) * 400, by positivity, ?_⟩
  intro i hi4 θ hθ
  have hWnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := angW_nonneg hα hθ
  have hGnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hGle : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hVs0b : |Vs0 α Φs θ| ≤ A := by
    rw [hAdef]
    exact Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_WlInf_of_mem hs.V.1 le_rfl
      Work.Spaces.zero_mem_Iz hθ
  have hL1 : ∀ a : ℕ, 1 ≤ a → a ≤ 4 →
      |Work.Spaces.Lop^[a] (Vs0 α Φs) θ|
        ≤ A * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro a ha1 ha4
    have h := dthIter_Vs_le_WlInf (α := α) (Cs := Cs) (Φs := Φs) hα hs a ha1 ha4
      0 Work.Spaces.zero_mem_Iz θ hθ
    have heq : Work.Spaces.Lop^[a] (Vs0 α Φs) θ
        = Work.Spaces.DthIter a (Vs α Φs) 0 θ := by
      simpa using (congrFun
        (Work.Spaces.DthIter_eq_iterate_Lop a (Vs α Φs) 0) θ).symm
    rw [heq, hAdef]
    nlinarith [h, hA0, hWnn, hAdef]
  have hL2 : ∀ b : ℕ, b ≤ 4 →
      |Work.Spaces.Lop^[b] (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ|
        ≤ (α / Work.Spaces.c α) * Cg * Work.Spaces.Gam α θ := by
    intro b hb
    rw [Lop_iter_const_mul]
    simp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (div_nonneg hα.le hcpos.le)]
    calc (α / Work.Spaces.c α) * |Work.Spaces.Lop^[b] (fun θ => Work.Spaces.Gam α θ) θ|
        ≤ (α / Work.Spaces.c α) * (Cg * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left (hCg b hb θ hθ) (div_nonneg hα.le hcpos.le)
      _ = (α / Work.Spaces.c α) * Cg * Work.Spaces.Gam α θ := by ring_nf
  have hmain : |Work.Spaces.Lop^[i] (Ufun α Φs) θ|
      ≤ (80 * (A * (α / Work.Spaces.c α) * Cg))
          * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hU : |Ufun α Φs θ| ≤ A * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
        rw [Ufun, abs_mul]
        have h2 : |α * Work.Spaces.Gam α θ / Work.Spaces.c α|
            = α / Work.Spaces.c α * Work.Spaces.Gam α θ := by
          rw [abs_of_nonneg (div_nonneg (mul_nonneg hα.le hGnn) hcpos.le)]
          ring
        rw [h2]
        calc |Vs0 α Φs θ| * (α / Work.Spaces.c α * Work.Spaces.Gam α θ)
            ≤ A * (α / Work.Spaces.c α * Work.Spaces.Gam α θ) :=
              mul_le_mul_of_nonneg_right hVs0b (mul_nonneg (div_nonneg hα.le hcpos.le) hGnn)
          _ = A * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by ring_nf
      calc |Ufun α Φs θ| ≤ A * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := hU
        _ ≤ A * (α / Work.Spaces.c α) * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_le_mul_of_nonneg_left (by linarith [hGnn, hWnn]) hAc0
        _ ≤ (80 * (A * (α / Work.Spaces.c α) * Cg))
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hGnn hWnn)
            have h8 : (1 : ℝ) ≤ 80 * Cg := by linarith [hCg1]
            calc A * (α / Work.Spaces.c α) = 1 * (A * (α / Work.Spaces.c α)) := by ring_nf
              _ ≤ (80 * Cg) * (A * (α / Work.Spaces.c α)) :=
                  mul_le_mul_of_nonneg_right h8 hAc0
              _ = 80 * (A * (α / Work.Spaces.c α) * Cg) := by ring_nf
    · have hLeib := Lop_iter_mul_of_contDiffOn (u := Vs0 α Φs)
          (v := fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) isOpen_Ioo
          ((contDiffOn_Vs0_theta (α := α) (Cs := Cs) (Φs := Φs) hα hs).of_le
            (Work.FTS.H2.StarPkg.natCast_le_smoothOrder (i + 1)))
          (((contDiffOn_const (c := α / Work.Spaces.c α)).mul
            (Work.FTS.LocData.contDiffOn_Gam_Ioo α)).of_le
            (Work.FTS.H2.StarPkg.natCast_le_smoothOrder (i + 1)))
      by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · have hUe : Ufun α Φs = fun θ => Vs0 α Φs θ
            * ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ) := by
          funext θ'; simp only [Ufun]; ring
        have hsum := hLeib θ hθo
        rw [show (Vs0 α Φs * fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ)
            = (fun θ => Vs0 α Φs θ * ((α / Work.Spaces.c α) * Work.Spaces.Gam α θ))
            from rfl] at hsum
        rw [hUe, hsum]
        have hterm : ∀ a ∈ Finset.range (i + 1),
            |(i.choose a : ℝ) * (Work.Spaces.Lop^[a] (Vs0 α Φs) θ
                * Work.Spaces.Lop^[i - a]
                    (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ)|
              ≤ 16 * (A * (α / Work.Spaces.c α) * Cg
                  * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * Work.Spaces.Gam α θ) := by
          intro a ha
          have hai : a < i + 1 := Finset.mem_range.mp ha
          have hchoose : (i.choose a : ℝ) ≤ 16 := by
            have h1 : i.choose a ≤ 2 ^ i := by
              have hm : a ∈ Finset.range (i + 1) := Finset.mem_range.mpr hai
              have h2 := Finset.single_le_sum (f := fun b => i.choose b)
                (fun b _ => Nat.zero_le _) hm
              simpa [Nat.sum_range_choose] using h2
            have h2 : 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi4
            have h3 : i.choose a ≤ 2 ^ 4 := le_trans h1 h2
            exact_mod_cast h3
          have hla : a ≤ 4 := le_trans (Nat.lt_succ_iff.mp hai) hi4
          have hlb : i - a ≤ 4 := le_trans (Nat.sub_le i a) hi4
          have hf1 : |Work.Spaces.Lop^[a] (Vs0 α Φs) θ|
              ≤ A * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rcases Nat.eq_zero_or_pos a with h0 | hpos'
            · subst h0
              simp only [Function.iterate_zero_apply]
              nlinarith [hVs0b, hA0, hWnn]
            · exact hL1 a hpos' hla
          have hf2 := hL2 (i - a) hlb
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose a))]
          have hpos : 0 ≤ A * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_nonneg hA0 (by linarith [hWnn])
          have hstep : (i.choose a : ℝ)
                * (|Work.Spaces.Lop^[a] (Vs0 α Φs) θ|
                  * |Work.Spaces.Lop^[i - a]
                      (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ|)
              ≤ 16 * (A * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * ((α / Work.Spaces.c α) * Cg * Work.Spaces.Gam α θ) := by
                have h1 : (i.choose a : ℝ)
                    * (|Work.Spaces.Lop^[a] (Vs0 α Φs) θ|
                      * |Work.Spaces.Lop^[i - a]
                          (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ|)
                    = ((i.choose a : ℝ) * |Work.Spaces.Lop^[a] (Vs0 α Φs) θ|)
                      * |Work.Spaces.Lop^[i - a]
                          (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ| := by
                  ring
                rw [h1]
                refine mul_le_mul ?_ hf2 (abs_nonneg _) (by positivity)
                exact mul_le_mul hchoose hf1 (abs_nonneg _) (by norm_num)
          calc (i.choose a : ℝ)
                * (|Work.Spaces.Lop^[a] (Vs0 α Φs) θ|
                  * |Work.Spaces.Lop^[i - a]
                      (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ|)
              ≤ 16 * (A * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * ((α / Work.Spaces.c α) * Cg * Work.Spaces.Gam α θ) := hstep
            _ ≤ 16 * (A * (α / Work.Spaces.c α) * Cg
                  * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * Work.Spaces.Gam α θ) := by exact le_of_eq (by ring)
        have hsum2 := Finset.abs_sum_le_sum_abs
          (fun a => (i.choose a : ℝ) * (Work.Spaces.Lop^[a] (Vs0 α Φs) θ
              * Work.Spaces.Lop^[i - a]
                  (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ))
          (Finset.range (i + 1))
        refine le_trans hsum2 ?_
        have hcard : (Finset.range (i + 1)).card = i + 1 := Finset.card_range (i + 1)
        have h5 : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
          have : i + 1 ≤ 5 := by omega
          exact_mod_cast this
        calc ∑ a ∈ Finset.range (i + 1),
              |(i.choose a : ℝ) * (Work.Spaces.Lop^[a] (Vs0 α Φs) θ
                  * Work.Spaces.Lop^[i - a]
                      (fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ) θ)|
            ≤ ∑ _a ∈ Finset.range (i + 1),
                16 * (A * (α / Work.Spaces.c α) * Cg
                    * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * Work.Spaces.Gam α θ) := Finset.sum_le_sum hterm
          _ = ((i + 1 : ℕ) : ℝ) * (16 * (A * (α / Work.Spaces.c α) * Cg
                    * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * Work.Spaces.Gam α θ)) := by
                rw [Finset.sum_const, hcard, nsmul_eq_mul]
          _ ≤ 80 * (A * (α / Work.Spaces.c α) * Cg
                    * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * Work.Spaces.Gam α θ) := by
                have hbx : 0 ≤ A * (α / Work.Spaces.c α) * Cg
                    * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * Work.Spaces.Gam α θ := by positivity
                nlinarith [h5, hbx]
          _ ≤ (80 * (A * (α / Work.Spaces.c α) * Cg))
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
                have hx : 0 ≤ 80 * (A * (α / Work.Spaces.c α) * Cg) := by positivity
                have hy : (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * Work.Spaces.Gam α θ
                    ≤ Work.Spaces.Gam α θ
                      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
                  nlinarith [hGnn, hWnn, hGle]
                calc 80 * (A * (α / Work.Spaces.c α) * Cg
                      * (1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                      * Work.Spaces.Gam α θ)
                    = (80 * (A * (α / Work.Spaces.c α) * Cg))
                      * ((1 + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                          * Work.Spaces.Gam α θ) := by ring
                  _ ≤ (80 * (A * (α / Work.Spaces.c α) * Cg))
                      * (Work.Spaces.Gam α θ
                        + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
                      mul_le_mul_of_nonneg_left hy hx
      · have hsin : Real.sin (2 * θ) = 0 := by
          rcases eq_or_lt_of_le hθ.1 with h1 | h1
          · rw [← h1]; simp
          · have h2 : θ = Real.pi / 2 := by
              rcases eq_or_lt_of_le hθ.2 with h2 | h2
              · exact h2
              · exact absurd ⟨h1, h2⟩ hθo
            rw [h2, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        have hzero : Work.Spaces.Lop^[i] (Ufun α Φs) θ = 0 := by
          have hthis : Work.Spaces.Lop^[i] (Ufun α Φs) θ
              = Work.Spaces.DthIter i (fun (_ : ℝ) θ' => Ufun α Φs θ') 0 θ := by
            simpa using (congrFun
              (Work.Spaces.DthIter_eq_iterate_Lop i (fun (_ : ℝ) θ' => Ufun α Φs θ') 0) θ).symm
          rw [hthis, Work.Coercivity.DthIter_eq_zero_of_sin_eq_zero
            (fun (_ : ℝ) θ' => Ufun α Φs θ') i hpos θ hsin 0]
        rw [hzero, abs_zero]
        have : 0 ≤ A * (α / Work.Spaces.c α) * Cg := by positivity
        nlinarith [this, hGnn, hWnn]
  have hconst : 80 * (A * (α / Work.Spaces.c α) * Cg)
      ≤ (1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg) * 400 := by
    have hA1 : A ≤ 1 + A := by linarith
    have hc1 : α / Work.Spaces.c α ≤ 1 + α / Work.Spaces.c α := by linarith
    have hC1 : Cg ≤ 1 + Cg := by linarith
    have hstep : A * (α / Work.Spaces.c α) * Cg
        ≤ (1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg) := by
      refine mul_le_mul (mul_le_mul hA1 hc1 hc0 (by linarith)) hC1 hCgpos.le (by positivity)
    calc 80 * (A * (α / Work.Spaces.c α) * Cg)
        ≤ 80 * ((1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ 400 * ((1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg) * 400 := by ring_nf
  have hfin : (80 * (A * (α / Work.Spaces.c α) * Cg))
        * (Work.Spaces.Gam α θ
          + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      ≤ ((1 + A) * (1 + α / Work.Spaces.c α) * (1 + Cg) * 400)
        * (Work.Spaces.Gam α θ + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_le_mul_of_nonneg_right hconst (add_nonneg hGnn hWnn)
  exact le_trans hmain hfin


/-! ## Case B: the majorant and the divergence at the origin -/

/-- A `θ`-independent bound for the `D_z`-iterates of `proff`. -/
def profBnd (z : ℝ) : ℝ := ∑ i ∈ Finset.range 5, |(Work.Spaces.DzIter i proff) z 0|

lemma profBnd_nonneg (z : ℝ) : 0 ≤ profBnd z :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

lemma abs_DzIter_proff_le (i : ℕ) (hi : i ≤ 4) (z θ : ℝ) :
    |(Work.Spaces.DzIter i proff) z θ| ≤ profBnd z := by
  have h := Work.FTS.LocDataExt.DzIter_z_only_apply
    (fun z : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) i z θ
  have h' : (Work.Spaces.DzIter i proff) z θ
      = (Work.Spaces.DzIter i (fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3)) z 0 := h
  rw [h', profBnd]
  exact Finset.single_le_sum
    (f := fun j => |(Work.Spaces.DzIter j (fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3)) z 0|)
    (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

/-- `(w z / sin(2θ)^{η/2})² ≤ (w z)²·sin(2θ)^{-γ}` on `Iθ`. -/
lemma wdiv_sq_le {α z θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2,
      ← Real.rpow_mul h0]
    congr 1
    ring
  rw [div_pow, h1, div_eq_mul_inv, ← Real.rpow_neg h0 (Work.Spaces.eta)]
  exact mul_le_mul_of_nonneg_left (rpow_neg_eta_le_neg_gam hα hθ) (sq_nonneg _)

/-- `Wt α z θ ^ 2 = (w z)²·sin(2θ)^{-γ}`. -/
lemma Wt_sq {α z θ : ℝ} (h0 : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
    ← Real.rpow_mul h0]
  congr 1
  ring

/-- **The pointwise majorant** of the `ℋ⁴`-integrand of the factorised coefficient. -/
theorem integrand_le_majorant {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ → ℝ, (∀ z, 0 < K z) ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ
        ≤ K z * ((Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  obtain ⟨C, hCpos, hC⟩ := Lop_iter_Ufun_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  refine ⟨fun z => 30 * (1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2, ?_, ?_⟩
  · intro z
    have h1 : (0 : ℝ) ≤ profBnd z := profBnd_nonneg z
    have h2 : (0 : ℝ) ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    positivity
  · intro z hz θ hθ
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    set G : ℝ := Work.Spaces.Gam α θ with hGdef
    set W : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) with hWdef
    have hGnn : 0 ≤ G := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hWnn : 0 ≤ W := angW_nonneg hα hθ
    have hC0 : 0 ≤ C := hCpos.le
    have hB0 : 0 ≤ profBnd z := profBnd_nonneg z
    have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hS0 : 0 ≤ C * (G + W) := mul_nonneg hC0 (by linarith [hGnn, hWnn])
    have hW20 : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      positivity
    set Q : ℝ := profBnd z ^ 2 * (C * (G + W)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) with hQdef
    have hQ0 : 0 ≤ Q := by rw [hQdef]; positivity
    have hthree : ∀ (a b c : ℝ), a ^ 2 ≤ profBnd z ^ 2 → b ^ 2 ≤ (C * (G + W)) ^ 2 →
        c ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) →
        (a ^ 2 * b ^ 2) * c ^ 2 ≤ Q := by
      intro a b c ha hb hc
      calc (a ^ 2 * b ^ 2) * c ^ 2
          ≤ (profBnd z ^ 2 * (C * (G + W)) ^ 2)
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
            mul_le_mul (mul_le_mul ha hb (sq_nonneg b) (by positivity)) hc
              (sq_nonneg c) (by positivity)
        _ = Q := by rw [hQdef]
    have hterm1 : ∀ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 ≤ Q := by
      intro i hi
      have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
          = (Work.Spaces.DzIter i proff) z θ * Ufun α Φs θ :=
        (factor_prod_prof (Ufun α Φs) i 0 z θ).1
      have hA : ((Work.Spaces.DzIter i proff) z θ) ^ 2 ≤ profBnd z ^ 2 :=
        sq_le_sq.mpr (by rw [abs_of_nonneg hB0]; exact abs_DzIter_proff_le i hi4 z θ)
      have hB : (Ufun α Φs θ) ^ 2 ≤ (C * (G + W)) ^ 2 := by
        have h := hC 0 (by norm_num) θ hθ
        have h' : |Ufun α Φs θ| ≤ C * (G + W) := by
          have he : C * (G + W) = C * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            rw [hGdef, hWdef]
          rw [he]
          exact h
        exact sq_le_sq.mpr (by rwa [abs_of_nonneg hS0])
      have h4 : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        wdiv_sq_le hα hθ
      have hgoal : ((Work.Spaces.DzIter i proff) z θ * Ufun α Φs θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((Work.Spaces.DzIter i proff) z θ) ^ 2 * (Ufun α Φs θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
      rw [h1, hgoal]
      exact hthree _ _ _ hA hB h4
    have hterm2 : ∀ i j : ℕ,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ Q := by
      intro i j
      split_ifs with hc
      · have hi4 : i ≤ 4 := by omega
        have hj4 : j ≤ 4 := by omega
        have h1 : Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
            = (Work.Spaces.DzIter j proff) z θ * Work.Spaces.Lop^[i] (Ufun α Φs) θ :=
          (factor_prod_prof (Ufun α Φs) i j z θ).2.2
        have hA : ((Work.Spaces.DzIter j proff) z θ) ^ 2 ≤ profBnd z ^ 2 :=
          sq_le_sq.mpr (by rw [abs_of_nonneg hB0]; exact abs_DzIter_proff_le j hj4 z θ)
        have hB : (Work.Spaces.Lop^[i] (Ufun α Φs) θ) ^ 2 ≤ (C * (G + W)) ^ 2 := by
          have h := hC i hi4 θ hθ
          have h' : |Work.Spaces.Lop^[i] (Ufun α Φs) θ| ≤ C * (G + W) := by
            have he : C * (G + W) = C * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              rw [hGdef, hWdef]
            rw [he]
            exact h
          exact sq_le_sq.mpr (by rwa [abs_of_nonneg hS0])
        have h4 : (Work.Spaces.Wt α z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          le_of_eq (Wt_sq h0)
        have hgoal : ((Work.Spaces.DzIter j proff) z θ * Work.Spaces.Lop^[i] (Ufun α Φs) θ
              * Work.Spaces.Wt α z θ) ^ 2
            = ((Work.Spaces.DzIter j proff) z θ) ^ 2
              * (Work.Spaces.Lop^[i] (Ufun α Φs) θ) ^ 2
              * (Work.Spaces.Wt α z θ) ^ 2 := by ring
        rw [h1, hgoal]
        exact hthree _ _ _ hA hB h4
      · exact hQ0
    rw [Work.Spaces.HkIntegrand]
    have hsum1 : (∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * Q := by
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (4 + 1), Q := Finset.sum_le_sum hterm1
        _ = 5 * Q := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hsum2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
        else 0) ≤ 25 * Q := by
      have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0) ≤ 5 * Q := by
        intro i
        calc (∑ j ∈ Finset.range (4 + 1),
              if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0)
            ≤ ∑ _j ∈ Finset.range (4 + 1), Q := Finset.sum_le_sum (fun j _ => hterm2 i j)
          _ = 5 * Q := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
      calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ _i ∈ Finset.range (4 + 1), 5 * Q := Finset.sum_le_sum (fun i _ => hinner i)
        _ = 25 * Q := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
            ring
    have htotal : 5 * Q + 25 * Q ≤ 30 * (1 + profBnd z) ^ 2 * (1 + C) ^ 2
        * (1 + Work.Spaces.w z) ^ 2
        * ((G + W) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      have h5Q : 5 * Q + 25 * Q = 30 * Q := by ring
      have hP : profBnd z ^ 2 ≤ (1 + profBnd z) ^ 2 := by nlinarith [hB0]
      have hCc : C ^ 2 ≤ (1 + C) ^ 2 := by nlinarith [hC0]
      have hw : (Work.Spaces.w z) ^ 2 ≤ (1 + Work.Spaces.w z) ^ 2 := by nlinarith [hw0]
      have hcore : profBnd z ^ 2 * (C * (G + W)) ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2
            * (G + W) ^ 2 := by
        rw [mul_pow]
        calc profBnd z ^ 2 * (C ^ 2 * (G + W) ^ 2) * (Work.Spaces.w z) ^ 2
            ≤ (1 + profBnd z) ^ 2 * ((1 + C) ^ 2 * (G + W) ^ 2)
              * (1 + Work.Spaces.w z) ^ 2 := by
              refine mul_le_mul ?_ hw (sq_nonneg _) (by positivity)
              exact mul_le_mul hP (mul_le_mul_of_nonneg_right hCc (by positivity))
                (by positivity) (by positivity)
          _ = (1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2
              * (G + W) ^ 2 := by ring
      rw [h5Q, hQdef]
      calc 30 * (profBnd z ^ 2 * (C * (G + W)) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = 30 * ((profBnd z ^ 2 * (C * (G + W)) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ ≤ 30 * (((1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2
              * (G + W) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcore (by positivity))
              (by norm_num)
        _ = 30 * (1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2
              * ((G + W) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    calc (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0)
        ≤ 5 * Q + 25 * Q := add_le_add hsum1 hsum2
      _ ≤ 30 * (1 + profBnd z) ^ 2 * (1 + C) ^ 2 * (1 + Work.Spaces.w z) ^ 2
            * ((G + W) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := htotal


/-- The `θ`-slices of the `ℋ⁴`-integrand of the factorised coefficient are integrable for
`z > 0` (domination by the majorant of `integrand_le_majorant`). -/
theorem integrableOn_slice {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ)
        Work.Spaces.Iθ := by
  obtain ⟨K, hKpos, hK⟩ := integrand_le_majorant (α := α) (Cs := Cs) (Φs := Φs) hα hs
  obtain ⟨hmaj1, hmaj2⟩ := theta_majorant_integrable (α := α) hα
  intro z hz
  have hint : MeasureTheory.IntegrableOn (fun θ => K z * ((Work.Spaces.Gam α θ
      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    hmaj2.const_mul (K z)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
        (fun z θ => proff z θ * Ufun α Φs θ) p.1 p.2)
      (continuousOn_HkIntegrand_fFac (α := α) (Cs := Cs) (Φs := Φs) hα hs) hz
  refine MeasureTheory.Integrable.mono' hint haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
  exact hK z (le_of_lt hz) θ hθ

/-- **The lower bound at the origin.**  If the angular factor does not vanish on `(0,π/2)`,
then near `z = 0` the `θ`-integral of the `ℋ⁴`-integrand is `≥ c/z²`. -/
theorem slice_lower_bound {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2))
    (hUne : Ufun α Φs θ₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, 0 < z → z < 1 / 2 →
      c / z ^ 2 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ := by
  have hVs0ne : Vs0 α Φs θ₀ ≠ 0 := by
    intro h0
    exact hUne (by rw [Ufun, h0, zero_mul])
  obtain ⟨a, b, c₀, ha0, haθ, hθb, hb, hc₀, hlow⟩ :=
    Vs0_interval_lower (α := α) (Cs := Cs) (Φs := Φs) hα hs hθ₀ hVs0ne
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hcb : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hb]⟩
  set g₀ : ℝ := (Real.sin a * Real.cos b ^ 2) ^ (α / 3) with hg₀def
  have hg₀pos : 0 < g₀ := by
    rw [hg₀def]
    refine Real.rpow_pos_of_pos ?_ _
    have hsa : 0 < Real.sin a :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])
    positivity
  have hsa0 : 0 ≤ Real.sin a :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])).le
  have hGam_low : ∀ θ ∈ Set.Ioo a b, g₀ ≤ Work.Spaces.Gam α θ := by
    intro θ hθ
    have hsa0' : 0 ≤ Real.sin a * Real.cos b ^ 2 := mul_nonneg hsa0 (sq_nonneg _)
    have hsb : Real.sin a * Real.cos b ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 := by
      have hs : Real.sin a ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := a) (y := θ)
          (by linarith [ha0, Real.pi_pos]) (le_of_lt (lt_trans hθ.2 hb)) (le_of_lt hθ.1)
      have hcθ : 0 ≤ Real.cos θ :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩).le
      have hc : Real.cos b ^ 2 ≤ Real.cos θ ^ 2 := by
        have h1 : Real.cos b ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := b)
            (le_of_lt (lt_trans ha0 hθ.1)) (by linarith [hb, Real.pi_pos]) (le_of_lt hθ.2)
        nlinarith [h1, hcb.le, hcθ]
      exact mul_le_mul hs hc (sq_nonneg _)
        (Real.sin_nonneg_of_mem_Icc ⟨le_of_lt (lt_trans ha0 hθ.1),
          by linarith [hθ.2, hb, Real.pi_pos]⟩)
    rw [hg₀def, Work.Spaces.Gam]
    exact Real.rpow_le_rpow hsa0' hsb (by linarith)
  set K₀ : ℝ := c₀ * α * g₀ / (4 * Work.Spaces.c α) with hK₀def
  have hK₀pos : 0 < K₀ := by
    rw [hK₀def]
    exact div_pos (mul_pos (mul_pos hc₀ hα) hg₀pos) (mul_pos (by norm_num) hcpos)
  set cc : ℝ := K₀ ^ 2 / 16 with hccdef
  have hccpos : 0 < cc := by
    rw [hccdef]
    exact div_pos (pow_pos hK₀pos 2) (by norm_num)
  refine ⟨(b - a) * cc, mul_pos (by linarith [haθ, hθb]) hccpos, ?_⟩
  intro z hz0 hz1
  have hint := integrableOn_slice (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz0
  have hw0z : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_nonneg (by positivity) (by positivity)
  have hpt : ∀ θ ∈ Set.Ioo a b,
      cc / z ^ 2 ≤ ((fun z θ => proff z θ * Ufun α Φs θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt (lt_trans ha0 hθ.1), le_of_lt (lt_trans hθ.2 hb)⟩
    have hX0 : 0 < Real.sin (2 * θ) := by
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hX1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsp : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hX0 _
    have hsp1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hX0.le hX1 (by rw [Work.Spaces.eta]; norm_num)
    have hprof : z / 4 ≤ |prof z| := by
      have h1 : 0 ≤ 2 * z * (1 - z) := by nlinarith [hz0, hz1]
      have h2 : 0 < (1 + z) ^ 3 := pow_pos (by linarith) 3
      rw [prof, abs_of_nonneg (div_nonneg h1 h2.le), le_div_iff₀ h2]
      have h3 : (1 + z) ^ 3 ≤ 27 / 8 := by
        have h4 : 1 + z ≤ 3 / 2 := by linarith
        nlinarith [hz0, sq_nonneg (1 + z), h4]
      nlinarith [hz0, hz1, h3]
    have hU : K₀ ≤ |Ufun α Φs θ| := by
      have h1 := hlow θ hθ
      have h2 := hGam_low θ hθ
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
      rw [Ufun, abs_mul, abs_of_nonneg (div_nonneg (mul_nonneg hα.le hG0) hcpos.le)]
      rw [hK₀def]
      have h3 : c₀ * g₀ ≤ |Vs0 α Φs θ| * Work.Spaces.Gam α θ :=
        mul_le_mul h1 h2 hg₀pos.le (abs_nonneg _)
      have h4 : 0 ≤ |Vs0 α Φs θ| * Work.Spaces.Gam α θ :=
        mul_nonneg (abs_nonneg _) hG0
      calc c₀ * α * g₀ / (4 * Work.Spaces.c α)
          = α * (c₀ * g₀) * ((4 * Work.Spaces.c α)⁻¹) := by rw [div_eq_mul_inv]; ring
        _ ≤ α * (|Vs0 α Φs θ| * Work.Spaces.Gam α θ) * ((4 * Work.Spaces.c α)⁻¹) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hα.le) (by positivity)
        _ ≤ α * (|Vs0 α Φs θ| * Work.Spaces.Gam α θ) * (Work.Spaces.c α)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [inv_le_inv₀ (by positivity) hcpos]
            linarith [hcpos]
        _ = |Vs0 α Φs θ| * (α * Work.Spaces.Gam α θ / Work.Spaces.c α) := by
            rw [div_eq_mul_inv]; ring
    have hw : 1 / z ^ 2 ≤ |Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| := by
      have hw1 : 1 / z ^ 2 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
        rw [div_mul_cancel₀ 1 (ne_of_gt (by positivity : (0 : ℝ) < z ^ 2))]
        nlinarith [hz0]
      have hprod : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        div_nonneg hw0z hsp.le
      rw [abs_of_nonneg hprod]
      have h2 : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        rw [le_div_iff₀ hsp]
        nlinarith [hw0z, hsp1]
      linarith
    have hsq1 : (z / 4) ^ 2 ≤ (prof z) ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 4)]; exact hprof)
    have hsq2 : K₀ ^ 2 ≤ (Ufun α Φs θ) ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_nonneg hK₀pos.le]; exact hU)
    have hsq3 : (1 / z ^ 2) ^ 2
        ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / z ^ 2)]; exact hw)
    have hgoal : ((fun z θ => proff z θ * Ufun α Φs θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (prof z) ^ 2 * (Ufun α Φs θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      rw [show (fun z θ => proff z θ * Ufun α Φs θ) z θ = prof z * Ufun α Φs θ from rfl]
      ring
    have h2 : cc / z ^ 2 = ((z / 4) * K₀ * (1 / z ^ 2)) ^ 2 := by
      rw [hccdef, hK₀def]
      field_simp
      ring
    rw [h2, hgoal]
    rw [show ((z / 4) * K₀ * (1 / z ^ 2)) ^ 2
        = (z / 4) ^ 2 * K₀ ^ 2 * (1 / z ^ 2) ^ 2 from by ring]
    exact mul_le_mul (mul_le_mul hsq1 hsq2 (sq_nonneg _) (by positivity)) hsq3
      (sq_nonneg _) (by positivity)
  -- the indicator comparison
  have hstep : (∫ θ in Work.Spaces.Iθ, (Set.Ioo a b).indicator (fun _ => cc / z ^ 2) θ)
      ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
    · refine Eventually.of_forall fun θ => ?_
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]
        exact div_nonneg hccpos.le (by positivity)
      · rw [Set.indicator_of_notMem h]
        exact le_refl 0
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]
        exact le_trans (hpt θ h)
          (Work.Spaces.sq_le_HkIntegrand_z α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ 0
            (by norm_num))
      · rw [Set.indicator_of_notMem h]
        exact Work.Spaces.HkIntegrand_nonneg α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ
  have hval : (∫ θ in Work.Spaces.Iθ, (Set.Ioo a b).indicator (fun _ => cc / z ^ 2) θ)
      = (b - a) * cc / z ^ 2 := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    have hsub : Set.Ioo a b ⊆ Work.Spaces.Iθ := fun θ h =>
      ⟨le_of_lt (lt_trans ha0 h.1), le_of_lt (lt_trans h.2 hb)⟩
    rw [MeasureTheory.setIntegral_const]
    have hreal : (MeasureTheory.volume.restrict Work.Spaces.Iθ).real (Set.Ioo a b) = b - a := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    rw [hreal]
    ring
  rw [hval] at hstep
  exact hstep

/-! ## The main dichotomy on the angular factor -/

theorem HkSq_Vs0_mul_Gs_eq_zero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.Spaces.HkSq α 4 (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.Vs0 α Φs θ
        * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = 0 := by
  -- reduce to the factorised form on the open quadrant
  rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
    (fun z θ _ _ _ => Vs0_mul_Gs_eq_prof (α := α) (Φs := Φs) hα (by linarith : (-1 : ℝ) < z))]
  by_cases hU : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Ufun α Φs θ = 0
  · -- ## Case A: the angular factor vanishes
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ = 0 := by
      intro z θ hθ
      by_cases hθo : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · have hLop : ∀ i : ℕ, i ≤ 4 → Work.Spaces.Lop^[i] (Ufun α Φs) θ = 0 := by
          intro i hi
          rcases Nat.eq_zero_or_pos i with h0 | hpos
          · subst h0
            simpa using hU θ hθo
          · have h := DthIter_angmul_eq_zero_open (Ufun α Φs) (fun _ _ => (1 : ℝ)) hU i hpos
              0 θ ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
            have hfun : (fun z θ' => Ufun α Φs θ' * (1 : ℝ))
                = fun (_ : ℝ) θ' => Ufun α Φs θ' := by
              funext z θ'; rw [mul_one]
            rw [hfun] at h
            have heq : Work.Spaces.Lop^[i] (Ufun α Φs) θ
                = Work.Spaces.DthIter i (fun (_ : ℝ) θ' => Ufun α Φs θ') 0 θ := by
              simpa using (congrFun
                (Work.Spaces.DthIter_eq_iterate_Lop i (fun (_ : ℝ) θ' => Ufun α Φs θ') 0) θ).symm
            rw [heq, h]
        rw [Work.Spaces.HkIntegrand]
        have h1 : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => proff z θ * Ufun α Φs θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [(factor_prod_prof (Ufun α Φs) i 0 z θ).1, hU θ hθo]
          ring
        have h2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => proff z θ * Ufun α Φs θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          split_ifs with hc
          · rw [(factor_prod_prof (Ufun α Φs) i j z θ).2.2,
              hLop i (by omega)]
            ring
          · rfl
        rw [h1, h2, add_zero]
      · have hsin : Real.sin (2 * θ) = 0 := by
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · rw [← h0]; simp
          · have h1 : θ = Real.pi / 2 := by
              rcases eq_or_lt_of_le hθ.2 with h2 | h2
              · exact h2
              · exact absurd ⟨h0, h2⟩ hθo
            rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        exact Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 4
          (fun z θ => proff z θ * Ufun α Φs θ) z θ hsin
    have hinner : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ) = 0 := by
      intro z
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hzero z θ hθ)
    rw [Work.Spaces.HkSq]
    simp only [hinner, MeasureTheory.integral_zero]
  · -- ## Case B: the angular factor is nonzero somewhere
    push_neg at hU
    obtain ⟨θ₀, hθ₀, hUne⟩ := hU
    obtain ⟨c, hcpos, hclow⟩ := slice_lower_bound (α := α) (Cs := Cs) (Φs := Φs) hα hs hθ₀ hUne
    have hnotint : ¬ MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ)
        Work.Spaces.Iz := by
      intro hint
      have h1 : MeasureTheory.IntegrableOn
          (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z θ => proff z θ * Ufun α Φs θ) z θ)
          (Set.Ioo 0 (1 / 2)) :=
        hint.mono_set (fun z hz => le_of_lt hz.1)
      have h2 : MeasureTheory.IntegrableOn (fun z : ℝ => c / z ^ 2) (Set.Ioo 0 (1 / 2)) := by
        refine MeasureTheory.Integrable.mono' h1 ?_ ?_
        · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
          exact continuousOn_const.div (continuousOn_id.pow 2)
            (fun z hz => pow_ne_zero 2 (ne_of_gt hz.1))
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
          rw [Real.norm_of_nonneg (by positivity)]
          exact hclow z hz.1 hz.2
      have h3 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ)))
          (Set.Ioo 0 (1 / 2)) := by
        have h4 : MeasureTheory.IntegrableOn (fun z : ℝ => c⁻¹ * (c / z ^ 2))
            (Set.Ioo 0 (1 / 2)) := h2.const_mul c⁻¹
        refine h4.congr ?_
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
        have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz.1)
        have hcz : c ≠ 0 := ne_of_gt hcpos
        show c⁻¹ * (c / z ^ 2) = z ^ (-(2 : ℝ))
        rw [Real.rpow_neg (le_of_lt hz.1) 2, Real.rpow_two, div_eq_mul_inv]
        field_simp
      have h5 : ¬ MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ)))
          (Set.Ioo 0 (1 / 2)) := by
        rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)]
        norm_num
      exact h5 h3
    rw [Work.Spaces.HkSq]
    exact MeasureTheory.integral_undef hnotint

end Work.FTS.Nonlinear.Pieces.RNP.row19
