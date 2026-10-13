/-
# `lamDzDeriv`: the moment `lam n F` commutes with the radial operator `D_z`

The angular moment of the truncated source is

  `lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ`,

with `zetaR n` the angular cutoff of `CptApp.Defs` — supported in `(1/n, π/2 - 1/n)`, hence
strictly inside the *open* angular interval `(0, π/2)`, where `F` is assumed to be only
`C^∞` (`Work.FTS.EllipticEst.SmoothOpen`).  Because the angular integral is therefore a
*local* (compactly supported) operation in `θ`, the operator `D_z = z ∂_z` may be pulled
through it:

  `D_z^m (fun z _ => lam n F z) z 0 = ∫_θ zetaR n θ · D_z^m F z θ · sinθcos²θ`   (`z > 0`).

The proof is the induction on `m` whose step is differentiation under the angular integral
(`Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0`).  Its two data hypotheses —
integrability of the base slice and a uniform bound on the candidate derivative on a
`z`-neighbourhood — are supplied here from compactness: `supp (zetaR n) ⊆ (0,π/2)` is
compact, `D_z^m F` and `∂_z D_z^m F` are continuous on the open quadrant, and the closed
`z`-intervals involved are compact too.  No decay or integrability of `F` itself is needed.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option maxHeartbeats 800000

/-! ## Elementary facts about the angular cutoff `zetaR` and the weight `sinθcos²θ` -/

theorem cut01_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : cut01 t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

theorem cut01_nonneg (t : ℝ) : 0 ≤ cut01 t := Real.smoothTransition.nonneg t

theorem cut01_le_one (t : ℝ) : cut01 t ≤ 1 := Real.smoothTransition.le_one t

theorem continuous_cut01 : Continuous cut01 := Real.smoothTransition.continuous

theorem abs_cut01_le_one (t : ℝ) : |cut01 t| ≤ 1 := by
  rw [abs_of_nonneg (cut01_nonneg t)]
  exact cut01_le_one t

/-- The angular cutoff vanishes to the left of `1/n` (`n ≥ 1`). -/
theorem zetaR_eq_zero_of_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : θ ≤ 1 / (n : ℝ)) :
    zetaR n θ = 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have h1 : (n : ℝ) * θ ≤ 1 := by
    calc (n : ℝ) * θ ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hθ hnpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]
  rw [zetaR, cut01_eq_zero_of_nonpos (show (n : ℝ) * θ - 1 ≤ 0 by linarith), zero_mul]

/-- The angular cutoff vanishes to the right of `π/2 - 1/n` (`n ≥ 1`). -/
theorem zetaR_eq_zero_of_ge {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : Real.pi / 2 - 1 / (n : ℝ) ≤ θ) : zetaR n θ = 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have h1 : (n : ℝ) * (Real.pi / 2 - θ) ≤ 1 := by
    calc (n : ℝ) * (Real.pi / 2 - θ) ≤ (n : ℝ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hnpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hnpos)]
  rw [zetaR, cut01_eq_zero_of_nonpos (show (n : ℝ) * (Real.pi / 2 - θ) - 1 ≤ 0 by linarith),
    mul_zero]

theorem zetaR_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ zetaR n θ := by
  rw [zetaR]
  exact mul_nonneg (cut01_nonneg _) (cut01_nonneg _)

theorem abs_zetaR_le_one (n : ℕ) (θ : ℝ) : |zetaR n θ| ≤ 1 := by
  have h1 : |cut01 ((n : ℝ) * θ - 1)| ≤ 1 := abs_cut01_le_one _
  have h2 : |cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1)| ≤ 1 := abs_cut01_le_one _
  rw [zetaR, abs_mul]
  calc |cut01 ((n : ℝ) * θ - 1)| * |cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1)|
      ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem continuous_zetaR (n : ℕ) : Continuous (zetaR n) := by
  change Continuous (fun θ : ℝ =>
    cut01 ((n : ℝ) * θ - 1) * cut01 ((n : ℝ) * (Real.pi / 2 - θ) - 1))
  refine Continuous.mul (continuous_cut01.comp ?_) (continuous_cut01.comp ?_) <;> fun_prop

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

theorem abs_sinCos2_le_one (θ : ℝ) : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  rw [Work.Elliptic.sinCos2, abs_mul]
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ), sq_abs (Real.cos θ)]
  calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
        mul_le_mul (Real.abs_sin_le_one θ) h2 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]
  exact measurableSet_Icc

/-! ## A uniform bound on a closed rectangle inside the open quadrant -/

/-- On a closed rectangle `[a,b] × [c,d]` strictly inside the open quadrant, a function
continuous on the open quadrant is bounded. -/
theorem exists_bound_rect {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (Function.uncurry H) Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ‖H x θ‖ ≤ C := by
  have hsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨x, θ⟩ ⟨hx, hθ⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod isCompact_Icc) (hH.mono hsub)
  refine ⟨max C 1, le_trans zero_le_one (le_max_right C 1), fun x hx θ hθ => ?_⟩
  have h := hC (x, θ) ⟨hx, hθ⟩
  rw [Function.uncurry] at h
  exact le_trans h (le_max_left _ _)

/-! ## Differentiation under the angular integral -/

/-- **Differentiation of the truncated moment under the angular integral.**  For `z > 0`,
the function `x ↦ ∫_θ zetaR n θ · D_z^m F x θ · sinθcos²θ` is differentiable at `z` with
derivative `∫_θ zetaR n θ · ∂_z(D_z^m F) z θ · sinθcos²θ`. -/
theorem hasDerivAt_lamSlice {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ)
      (∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ * Work.Elliptic.sinCos2 θ) z := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
  have hcpos : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hdlt : Real.pi / 2 - 1 / (n : ℝ) < Real.pi / 2 := by linarith
  have hV : IsOpen (Set.Ioo (z / 2) (2 * z)) := isOpen_Ioo
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hVpos : ∀ x ∈ Set.Ioo (z / 2) (2 * z), 0 < x := fun x hx => by linarith [hx.1, hz]
  -- continuity of the angular factors
  have hζc : ContinuousOn (fun p : ℝ × ℝ => zetaR n p.2) Work.FTS.EllipticEst.Q0 :=
    (continuous_zetaR n).comp_continuousOn continuousOn_snd
  have hsc : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuous_sinCos2.comp_continuousOn continuousOn_snd
  have hHc : ContinuousOn (Function.uncurry (Work.Spaces.DzIter m F))
      Work.FTS.EllipticEst.Q0 := (hsm.DzIter m).continuousOn
  have hHc' : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m F)))
      Work.FTS.EllipticEst.Q0 := ((hsm.DzIter m).pz).continuousOn
  have hg : ContinuousOn (Function.uncurry (fun x θ =>
      zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => zetaR n θ * Work.Spaces.DzIter m F x θ *
        Work.Elliptic.sinCos2 θ)
        = fun p : ℝ × ℝ => zetaR n p.2 * Function.uncurry (Work.Spaces.DzIter m F) p *
            Work.Elliptic.sinCos2 p.2 := by
      funext p
      rcases p with ⟨x, θ⟩
      rfl
    rw [hfun]
    exact (hζc.mul hHc).mul hsc
  have hg' : ContinuousOn (Function.uncurry (fun x θ =>
      zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun x θ => zetaR n θ *
        Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ)
        = fun p : ℝ × ℝ => zetaR n p.2 *
            Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m F)) p *
            Work.Elliptic.sinCos2 p.2 := by
      funext p
      rcases p with ⟨x, θ⟩
      rfl
    rw [hfun]
    exact (hζc.mul hHc').mul hsc
  -- integrability of the base slice: the integrand is supported on a compact subset of
  -- `(1/n, π/2 - 1/n)`, where `D_z^m F z ·` is bounded
  obtain ⟨C1, hC1n, hC1⟩ := exists_bound_rect hHc (a := z) (b := z)
    (c := 1 / (n : ℝ)) (d := Real.pi / 2 - 1 / (n : ℝ)) hz hcpos hdlt
  have hbnd1 : ∀ θ ∈ Work.Spaces.Iθ,
      ‖zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ‖ ≤ max C1 1 := by
    intro θ _
    rcases le_or_gt θ (1 / (n : ℝ)) with h | h
    · rw [zetaR_eq_zero_of_le hn h]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C1 1)
    rcases le_or_gt (Real.pi / 2 - 1 / (n : ℝ)) θ with h2 | h2
    · rw [zetaR_eq_zero_of_ge hn h2]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C1 1)
    · have hθmem : θ ∈ Set.Icc (1 / (n : ℝ)) (Real.pi / 2 - 1 / (n : ℝ)) := ⟨h.le, h2.le⟩
      have h1 : ‖Work.Spaces.DzIter m F z θ‖ ≤ C1 := hC1 z (by simp) θ hθmem
      calc ‖zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ‖
          = ‖zetaR n θ‖ * ‖Work.Spaces.DzIter m F z θ‖ * ‖Work.Elliptic.sinCos2 θ‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * (max C1 1) * 1 := by
            refine mul_le_mul
              (mul_le_mul (abs_zetaR_le_one n θ) (le_trans h1 (le_max_left C1 1))
                (norm_nonneg _) (by norm_num)) (abs_sinCos2_le_one θ) (norm_nonneg _) ?_
            have hmax : (0 : ℝ) ≤ max C1 1 := le_trans zero_le_one (le_max_right C1 1)
            exact mul_nonneg zero_le_one hmax
        _ = max C1 1 := by ring
  have hint : Integrable (fun θ => zetaR n θ * Work.Spaces.DzIter m F z θ *
      Work.Elliptic.sinCos2 θ) (volume.restrict Work.Spaces.Iθ) := by
    have hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
      Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
    refine MeasureTheory.Integrable.of_bound
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hg hz) (max C1 1) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ hbnd1
  -- the uniform bound on the candidate derivative over the `z`-interval
  obtain ⟨C2, hC2n, hC2⟩ := exists_bound_rect hHc' (a := z / 2) (b := 2 * z)
    (c := 1 / (n : ℝ)) (d := Real.pi / 2 - 1 / (n : ℝ)) (by linarith) hcpos hdlt
  have hbnd2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∀ x ∈ Set.Ioo (z / 2) (2 * z),
        ‖zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ‖ ≤ max C2 1 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iθ (fun θ _ x hx => ?_)
    rcases le_or_gt θ (1 / (n : ℝ)) with h | h
    · rw [zetaR_eq_zero_of_le hn h]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C2 1)
    rcases le_or_gt (Real.pi / 2 - 1 / (n : ℝ)) θ with h2 | h2
    · rw [zetaR_eq_zero_of_ge hn h2]
      simp only [zero_mul, norm_zero]
      exact le_trans zero_le_one (le_max_right C2 1)
    · have hθmem : θ ∈ Set.Icc (1 / (n : ℝ)) (Real.pi / 2 - 1 / (n : ℝ)) := ⟨h.le, h2.le⟩
      have hxmem : x ∈ Set.Icc (z / 2) (2 * z) := ⟨hx.1.le, hx.2.le⟩
      have h1 : ‖Work.Spaces.pz (Work.Spaces.DzIter m F) x θ‖ ≤ C2 := hC2 x hxmem θ hθmem
      calc ‖zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
            Work.Elliptic.sinCos2 θ‖
          = ‖zetaR n θ‖ * ‖Work.Spaces.pz (Work.Spaces.DzIter m F) x θ‖ *
              ‖Work.Elliptic.sinCos2 θ‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * (max C2 1) * 1 := by
            refine mul_le_mul
              (mul_le_mul (abs_zetaR_le_one n θ) (le_trans h1 (le_max_left C2 1))
                (norm_nonneg _) (by norm_num)) (abs_sinCos2_le_one θ) (norm_nonneg _) ?_
            have hmax : (0 : ℝ) ≤ max C2 1 := le_trans zero_le_one (le_max_right C2 1)
            exact mul_nonneg zero_le_one hmax
        _ = max C2 1 := by ring
  -- the pointwise derivative of the slice
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => zetaR n θ * Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ)
        (zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ) x := by
    intro θ hθ x hx
    have hx0 : 0 < x := hVpos x hx
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.DzIter m F)) (x, θ) :=
      (((hsm.DzIter m).forall 1).differentiableOn (by norm_num)).differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hx0, hθ.1, hθ.2⟩))
    have h1 : HasDerivAt (fun y => Work.Spaces.DzIter m F y θ)
        (Work.Spaces.pz (Work.Spaces.DzIter m F) x θ) x :=
      (Work.Spaces.differentiableAt_curry_left hd).hasDerivAt
    have h2 := (h1.mul_const (Work.Elliptic.sinCos2 θ)).const_mul (zetaR n θ)
    have heq : (fun y => zetaR n θ * Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ)
        = fun y => zetaR n θ * (Work.Spaces.DzIter m F y θ * Work.Elliptic.sinCos2 θ) := by
      funext y
      ring
    have hv : zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
          Work.Elliptic.sinCos2 θ
        = zetaR n θ *
          (Work.Spaces.pz (Work.Spaces.DzIter m F) x θ * Work.Elliptic.sinCos2 θ) := by ring
    rw [heq, hv]
    exact h2
  exact Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0
    (g := fun x θ => zetaR n θ * Work.Spaces.DzIter m F x θ * Work.Elliptic.sinCos2 θ)
    (g' := fun x θ => zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) x θ *
      Work.Elliptic.sinCos2 θ)
    hV hzV hVpos hg hg' hint hbnd2 hdiff

/-! ## The main result -/

/-- The induction: `D_z^m` applied to `z ↦ lam n F z` equals the angular integral of
`D_z^m F` against the cutoff. -/
theorem lamDzDeriv_aux {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ m : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ => lam n F z) z 0
        = ∫ θ in Work.Spaces.Iθ,
            zetaR n θ * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ := by
  intro m
  induction m with
  | zero => intro z _; rfl
  | succ m ih =>
    intro z hz
    have hstep : HasDerivAt (fun y => Work.Spaces.DzIter m (fun z _ => lam n F z) y 0)
        (∫ θ in Work.Spaces.Iθ,
          zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ *
            Work.Elliptic.sinCos2 θ) z :=
      (hasDerivAt_lamSlice hsm hn m hz).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
        exact ih y hy)
    have hL : Work.Spaces.DzIter (m + 1) (fun z _ => lam n F z) z 0
        = z * deriv (fun y => Work.Spaces.DzIter m (fun z _ => lam n F z) y 0) z := rfl
    have hDz : ∀ θ : ℝ, Work.Spaces.DzIter (m + 1) F z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter m F) z θ := fun θ => rfl
    rw [hL, hstep.deriv]
    rw [← MeasureTheory.integral_const_mul]
    congr 1 with θ
    simp only [hDz]
    ring

theorem lamDzDeriv {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F) (k n : ℕ)
    (hn : 1 ≤ n) :
    ∀ m : ℕ, m ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter m (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0
        = MeasureTheory.integral
            (MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iθ)
            (fun θ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ
              * Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ) := by
  intro m _ z hz
  exact lamDzDeriv_aux hsm hn m z hz

end Work.FTS.PhiStar.Honesty.CptApp
