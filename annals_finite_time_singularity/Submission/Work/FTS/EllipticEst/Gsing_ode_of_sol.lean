import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Fstar_contDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

/-! ## Auxiliary facts

This module proves `Work.FTS.EllipticEst.Gsing_ode_of_sol`: for a smooth solution `Ψ` of the
axi-symmetric Biot–Savart law (PolarBSL) with source `F ∈ ℋ^k`, the angular moment `F_*` and
the singular term `Gsing α F` are smooth on `(0,∞)`, and `Gsing` solves the Euler-type ODE
`α²z²G'' + α(5+α)zG' = (15/4)F_*`.

The three analytic ingredients are

* `F_*` is smooth, because `Work.Elliptic.PsiStar_ode` exhibits it as
  `-(α²z²(Ψ_*)'' + α(5+α)z(Ψ_*)')` with `Ψ_*` smooth (`Fstar_contDiffOn`);
* `|F_*(z)| ≤ √(π/2)·(z²/(1+z)²)·√(∫_θ HkIntegrand α k F z θ)`, by Cauchy–Schwarz on the
  angular slice, using only the `D_z⁰`-summand of the `H^k`-integrand;
* consequently `F_*/z` is integrable on every tail and `z^{(5-α)/α}F_*` is integrable near
  `0`, so that the tail integral `L₁₂` and the primitive occurring in `Ḡ` are smooth.
-/

/-- A statement holding on the open angular interval holds a.e. on `Iθ`. -/
private theorem ae_restrict_Iθ_of_Ioo_aux {p : ℝ → Prop} (h : ∀ θ, 0 < θ → θ < π / 2 → p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [Work.Spaces.Iθ, ← Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => h θ hθ.1 hθ.2)

/-- **`bslOp α Ψ` is smooth on the open quadrant.**  The only delicate term is
`∂_θ(tan θ · Ψ)`, whose smoothness comes from `Real.contDiffAt_tan` and `cos θ ≠ 0` on
`(0,π/2)`. -/
private theorem contDiffOn_uncurry_bslOp_aux (α : ℝ) (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) with hQ
  have hQopen : IsOpen Q := isOpen_Ioi.prod isOpen_Ioo
  have hsub : Q ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨by simp only [Set.mem_Ioi] at hz ⊢; linarith,
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hsmQ : ContDiffOn ℝ ⊤ (Function.uncurry Ψ) Q := hsm.mono hsub
  have hpz : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz Ψ)) Q :=
    Work.Spaces.contDiffOn_uncurry_pz hQopen hsmQ
  have hpz2 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Q := by
    simpa [Work.Spaces.pzIter_succ] using Work.Spaces.contDiffOn_uncurry_pz hQopen hpz
  have hpth : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pth Ψ)) Q :=
    Work.Spaces.contDiffOn_uncurry_pth hQopen hsmQ
  have hpth2 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Q := by
    simpa [Work.Spaces.pthIter_succ] using Work.Spaces.contDiffOn_uncurry_pth hQopen hpth
  have htan : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.tan p.2) Q := by
    intro p hp
    simp only [hQ, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
    have hcos : Real.cos p.2 ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
    exact ((Real.contDiffAt_tan.mpr hcos).comp p contDiffAt_snd).contDiffWithinAt
  have htanPsi : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => Real.tan θ * Ψ z θ)) Q := by
    refine (htan.mul hsmQ).congr ?_
    intro p hp
    rfl
  have hpthtan : ContDiffOn ℝ ⊤
      (Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ))) Q :=
    Work.Spaces.contDiffOn_uncurry_pth hQopen htanPsi
  have hLzero : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Elliptic.Lzero Ψ)) Q := by
    have h6 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => (6 : ℝ) * Function.uncurry Ψ p) Q :=
      contDiffOn_const.mul hsmQ
    refine (((hpth2.neg).add hpthtan).sub h6).congr ?_
    intro p hp
    rfl
  have h1 : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 Ψ) p) Q :=
    ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).neg).mul hpz2
  have h2 : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => -(α * (5 + α) * p.1) * Function.uncurry (Work.Spaces.pz Ψ) p) Q :=
    ((contDiffOn_const.mul contDiffOn_fst).neg).mul hpz
  refine ((h1.add h2).add hLzero).congr ?_
  intro p hp
  simp only [Function.uncurry, Work.Elliptic.bslOp_apply]
  ring

/-- **Smoothness of the angular moment `F_*` of a solution of (PolarBSL).**
`Work.Elliptic.PsiStar_ode` writes `F_* = -(α²z²(Ψ_*)'' + α(5+α)z(Ψ_*)')` on `(0,∞)`, and
`Work.FTS.EllipticEst.Fstar_contDiffOn` says `Ψ_*` is smooth on `(-1,∞)`. -/
private theorem fstar_contDiffOn_of_bsl_aux (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  have hEq : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Fstar F z
        = (fun z => -(α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)) z := by
    intro z hz
    show Work.Elliptic.Fstar F z
      = -(α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)
    rw [show α ^ 2 * z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
        = -(Work.Elliptic.Fstar F z) from Work.Elliptic.PsiStar_ode α F Ψ z hα hz hsm hsol]
    ring
  intro m
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ioi (-1) := by
    intro z hz; simp only [Set.mem_Ioi] at hz ⊢; linarith
  have hd1 : ContDiffOn ℝ (m + 1)
      (fun z => deriv (fun z' => Work.Elliptic.Fstar Ψ z') z) (Set.Ioi 0) :=
    ContDiffOn.deriv_of_isOpen ((Work.FTS.EllipticEst.Fstar_contDiffOn Ψ hsm (m + 2)).mono hsub)
      isOpen_Ioi (by push_cast; exact le_rfl)
  have hd2 : ContDiffOn ℝ m
      (fun z => deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z) (Set.Ioi 0) :=
    ContDiffOn.deriv_of_isOpen hd1 isOpen_Ioi (by push_cast; exact le_rfl)
  refine ContDiffOn.congr ?_ hEq
  refine ContDiffOn.neg ?_
  refine ContDiffOn.add ?_ ?_
  · exact ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hd2)
  · exact (((contDiffOn_const.mul contDiffOn_const).mul contDiffOn_id).mul (hd1.of_le (by simp)))

/-- Cauchy–Schwarz for a `√h`-type factor: if `0 ≤ h`, `h ∈ L¹` and `ρ² ∈ L¹` on `s`, then
`√h · ρ ∈ L¹` on `s`.  (The AM–GM inequality `2√h|ρ| ≤ h + ρ²`.) -/
private theorem integrableOn_sqrt_mul_aux {h ρ : ℝ → ℝ} {s : Set ℝ}
    (hh : IntegrableOn h s) (hhnn : ∀ x, 0 ≤ h x)
    (hρm : AEStronglyMeasurable ρ (volume.restrict s))
    (hρ : IntegrableOn (fun x => (ρ x) ^ 2) s) :
    IntegrableOn (fun x => Real.sqrt (h x) * ρ x) s := by
  have h1 : AEStronglyMeasurable (fun x => Real.sqrt (h x)) (volume.restrict s) :=
    (hh.aemeasurable.sqrt).aestronglyMeasurable
  have h2 : AEStronglyMeasurable ρ (volume.restrict s) := hρm
  refine Integrable.mono' ((hh.add hρ).const_mul (1 / 2)) (h1.mul h2) ?_
  refine Eventually.of_forall fun x => ?_
  have hx := hhnn x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2' : Real.sqrt (h x) * |ρ x| ≤ (h x + (ρ x) ^ 2) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (h x) - |ρ x|), Real.sq_sqrt hx, sq_abs (ρ x),
      Real.sqrt_nonneg (h x)]
  calc Real.sqrt (h x) * |ρ x| ≤ (h x + (ρ x) ^ 2) / 2 := h2'
    _ = (1 / 2) * (h x + (ρ x) ^ 2) := by ring

/-- **The bound on the angular moment.**  For `F` with `HkMem α k F` (and, to identify the
slice of `F` with the continuous slice of the elliptic operator, `F = bslOp α Ψ` on the open
quadrant with `Ψ` smooth),

`|F_*(z)| ≤ √(π/2)·z²/(1+z)²·√(∫_θ HkIntegrand α k F z θ)`  for `z > 0`.

The whole content is the `D_z⁰`-summand `(F·w/sin(2θ)^{η/2})²` of the `H^k`-integrand and
Cauchy–Schwarz on the angular slice; the constant is uniform in `α`, `k`. -/
private theorem fstar_abs_le_hk_aux (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hmem : Work.Spaces.HkMem α k F) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.Fstar F z| ≤ C * (z ^ 2 / (1 + z) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  refine ⟨Real.sqrt (π / 2), Real.sqrt_pos.mpr (by positivity), fun z hz => ?_⟩
  have hz0 : 0 < z := hz
  have hzI : z ∈ Work.Spaces.Iz := by simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hHnn : ∀ θ, 0 ≤ Work.Spaces.HkIntegrand α k F z θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  have hHint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k F z θ) Work.Spaces.Iθ :=
    hmem.1 z hzI
  -- pointwise domination of `F(z,·)²` by the `H^k`-integrand, on the open angle interval
  have hpt : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k F z θ / (Work.Spaces.w z) ^ 2 := by
    intro θ h0 h1
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
    have hS : 0 < S := Real.rpow_pos_of_pos hsin _
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α k F z θ 0 (Nat.zero_le k)
    simp only [Work.Spaces.DzIter_zero] at hkey
    have hrewrite : (F z θ) ^ 2
        = (F z θ * (Work.Spaces.w z / S)) ^ 2 * (S / Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, div_pow, div_pow]
      field_simp
    have hSsq : S ^ 2 ≤ (1 : ℝ) := by
      have h2 : S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [hSdef, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hsin)]
        norm_num
      calc S ^ 2 = (Real.sin (2 * θ)) ^ Work.Spaces.eta := h2
        _ ≤ 1 := Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _)
            (le_of_lt Work.Spaces.eta_pos)
    have hSw : (S / Work.Spaces.w z) ^ 2 ≤ 1 / (Work.Spaces.w z) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hSsq, pow_pos hwpos 2]
    rw [hrewrite]
    refine le_trans (mul_le_mul_of_nonneg_right hkey (sq_nonneg _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hSw (hHnn θ)) ?_
    rw [one_div, div_eq_mul_inv]
  -- a.e. strong measurability of the angular slice of `F`
  have hslice : AEStronglyMeasurable (fun θ => F z θ) (volume.restrict Work.Spaces.Iθ) := by
    have hQ := contDiffOn_uncurry_bslOp_aux α Ψ hsm
    have h1 : AEStronglyMeasurable (fun θ => Work.Elliptic.bslOp α Ψ z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry (Work.Elliptic.bslOp α Ψ))
        hQ.continuousOn hz0
    refine h1.congr ?_
    exact ae_restrict_Iθ_of_Ioo_aux (fun θ h0 h1 => hsol.1 z hz0 θ h0 h1)
  -- integrability of `F(z,·)²`
  have hF2 : IntegrableOn (fun θ => (F z θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (hHint.div_const ((Work.Spaces.w z) ^ 2)) (hslice.pow 2) ?_
    filter_upwards [ae_restrict_Iθ_of_Ioo_aux (fun θ h0 h1 => hpt θ h0 h1)] with θ hθ
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  -- Cauchy–Schwarz for the angular moment
  have hCS := Work.Elliptic.Fstar_sq_le F z hF2
  have hInt : ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) / (Work.Spaces.w z) ^ 2 := by
    have h1 := integral_mono_ae hF2 (hHint.div_const ((Work.Spaces.w z) ^ 2))
      (ae_restrict_Iθ_of_Ioo_aux (fun θ h0 h1 => hpt θ h0 h1))
    rwa [integral_div] at h1
  have hmain : (Work.Elliptic.Fstar F z) ^ 2 ≤ (π / 2) *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) / (Work.Spaces.w z) ^ 2) := by
    refine hCS.trans (mul_le_mul_of_nonneg_left hInt (by positivity))
  have hsqrt := Real.sqrt_le_sqrt hmain
  rw [Real.sqrt_sq_eq_abs] at hsqrt
  have hRHS : Real.sqrt ((π / 2) *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) / (Work.Spaces.w z) ^ 2))
      = Real.sqrt (π / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          / Work.Spaces.w z := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (integral_nonneg hHnn),
      Real.sqrt_sq_eq_abs, abs_of_pos hwpos]
    ring
  rw [hRHS] at hsqrt
  calc |Work.Elliptic.Fstar F z|
      ≤ Real.sqrt (π / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
          / Work.Spaces.w z := hsqrt
    _ = Real.sqrt (π / 2) * (z ^ 2 / (1 + z) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
        rw [Work.Spaces.w]
        field_simp

/-- **Integrability of `F_*(r)/r` on tails.**  From the bound `|F_*(r)| ≤ C·r²/(1+r)²·√h(r)`
and `h ∈ L¹`, since `√h·(1/(1+r)) ∈ L¹` (AM–GM against `h + (1+r)^{-2}`). -/
private theorem integrableOn_fstar_div_aux (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hbd : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.Fstar F z| ≤ C * (z ^ 2 / (1 + z) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ))
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ a ∈ Set.Ioi (0 : ℝ), IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi a) := by
  intro a ha
  obtain ⟨C, hCpos, hCbd⟩ := hbd
  have ha0 : 0 < a := ha
  have hh_int : IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
      (Set.Ioi a) :=
    hmem.2.mono_set (fun x hx => by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt (lt_trans ha0 hx))
  have h1r_int : IntegrableOn (fun r : ℝ => 1 / (1 + r) ^ 2) (Set.Ioi a) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := (-(2 : ℝ))) (c := a)
      (by norm_num) ha0) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_trans ha0 hx
        positivity
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : 0 < r := lt_trans ha0 hr
      have hrpow : (r : ℝ) ^ (-(2 : ℝ)) = (r ^ 2)⁻¹ := by
        rw [Real.rpow_neg hr0.le]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrpow]
      rw [one_div, inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
  have hprod : IntegrableOn (fun r => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F r θ) * (1 / (1 + r))) (Set.Ioi a) :=
    integrableOn_sqrt_mul_aux hh_int
      (fun x => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F x θ)
      (by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        refine ContinuousOn.div continuousOn_const ?_ ?_
        · exact continuousOn_const.add continuousOn_id
        · intro x hx
          have hx0 : (0 : ℝ) < x := lt_trans ha0 hx
          positivity)
      (by simpa [one_div, inv_pow] using h1r_int)
  -- the target is dominated by `C` times this product
  refine Integrable.mono' (hprod.const_mul C) ?_ ?_
  · have hdiv : ContinuousOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) :=
      hcont.div continuousOn_id (fun x hx => ne_of_gt hx)
    exact (hdiv.mono (fun x hx => lt_trans ha0 hx)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 < r := lt_trans ha0 hr
    have hb := hCbd r (lt_trans ha0 hr)
    have hsqrt_nn : 0 ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) := Real.sqrt_nonneg _
    have hw : r / (1 + r) ^ 2 ≤ 1 / (1 + r) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hstep : |Work.Elliptic.Fstar F r| / r ≤ C * (r / (1 + r) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) := by
      rw [div_le_iff₀ hr0]
      have hsplit : r ^ 2 / (1 + r) ^ 2 = (r / (1 + r) ^ 2) * r := by ring_nf
      calc |Work.Elliptic.Fstar F r|
          ≤ C * (r ^ 2 / (1 + r) ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) := hb
        _ = (C * (r / (1 + r) ^ 2)
              * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)) * r := by
            rw [hsplit]; ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    calc |Work.Elliptic.Fstar F r| / r
        ≤ C * (r / (1 + r) ^ 2)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) := hstep
      _ ≤ C * (1 / (1 + r))
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hCpos.le) hsqrt_nn
      _ = C * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
            * (1 / (1 + r))) := by ring

/-- **Integrability of `s^{(5-α)/α}F_*(s)` near `0`.**  With `p = (5-α)/α ≥ 4` and the bound
`|F_*(s)| ≤ C·s²/(1+s)²·√h(s)`, on `(0,a]` the integrand is dominated by
`C·s^{p+2}√h(s) ≤ (C/2)(s^{2p+4} + h(s))`, both terms integrable. -/
private theorem integrableOn_weight_mul_fstar_aux (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hbd : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.Fstar F z| ≤ C * (z ^ 2 / (1 + z) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ))
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ a ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioc 0 a) := by
  intro a ha
  obtain ⟨C, hCpos, hCbd⟩ := hbd
  have ha0 : 0 < a := ha
  set p : ℝ := (5 - α) / α with hpdef
  have hp4 : 4 ≤ p := by
    rw [hpdef, le_div_iff₀ hα]
    linarith
  have hp0 : 0 ≤ p := by linarith
  have hp20 : 0 ≤ p + 2 := by linarith
  have hh_int : IntegrableOn (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F s θ)
      (Set.Ioc 0 a) :=
    hmem.2.mono_set (fun x hx => by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      exact le_of_lt hx.1)
  -- the weight `(C·s^{p+2})²` is bounded on `(0,a]`
  have hρ_int : IntegrableOn (fun s => (C * s ^ (p + 2)) ^ 2) (Set.Ioc 0 a) := by
    refine Integrable.mono' (integrableOn_const (s := Set.Ioc (0:ℝ) a)
      (C := (C * a ^ (p + 2)) ^ 2) ?_) ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact ((continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun s hs => Or.inr hp20))).pow 2)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
      have hs0 : 0 < s := hs.1
      have hsa : s ≤ a := hs.2
      have hle : s ^ (p + 2) ≤ a ^ (p + 2) := Real.rpow_le_rpow hs0.le hsa hp20
      have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg hs0.le _) hle 2) hC2
  have hprod : IntegrableOn (fun s => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F s θ) * (C * s ^ (p + 2))) (Set.Ioc 0 a) :=
    integrableOn_sqrt_mul_aux hh_int
      (fun x => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F x θ)
      (by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
          (fun s hs => Or.inr hp20))))
      hρ_int
  refine Integrable.mono' hprod ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine (ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inr hp0)).mul ?_
    exact hcont.mono (fun x hx => hx.1)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
    have hs0 : 0 < s := hs.1
    have hs1 : (1:ℝ) ≤ (1 + s) ^ 2 := by nlinarith
    have hb := hCbd s hs0
    have hsqrt_nn : 0 ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F s θ) := Real.sqrt_nonneg _
    have hfactor : s ^ 2 / (1 + s) ^ 2 ≤ s ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hrpow : s ^ p * s ^ 2 = s ^ (p + 2) := by
      rw [← Real.rpow_natCast s 2]
      rw [← Real.rpow_add hs0]
      norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le p)]
    calc s ^ p * |Work.Elliptic.Fstar F s|
        ≤ s ^ p * (C * (s ^ 2 / (1 + s) ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F s θ)) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hs0.le p)
      _ ≤ s ^ p * (C * s ^ 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F s θ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hs0.le p)
          refine mul_le_mul_of_nonneg_right ?_ hsqrt_nn
          refine mul_le_mul_of_nonneg_left hfactor hCpos.le
      _ = C * (s ^ p * s ^ 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F s θ) := by ring
      _ = C * s ^ (p + 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k F s θ) := by rw [hrpow]
      _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F s θ)
            * (C * s ^ (p + 2)) := by ring

/-- **The tail integral of a smooth, tail-integrable function is smooth**, and its derivative
is minus the integrand.  On `(a,∞)` the tail integral is `const - ∫_a^· g`, a primitive of a
smooth function. -/
private theorem tailIntegral_contDiffOn_aux {g : ℝ → ℝ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0))
    (hint : ∀ a : ℝ, 0 < a → MeasureTheory.IntegrableOn g (Set.Ioi a)) :
    (∀ m : ℕ, ContDiffOn ℝ m (fun z => ∫ r in Set.Ioi z, g r) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => ∫ r in Set.Ioi z, g r) (-(g z)) z := by
  set Φ : ℝ → ℝ := fun z => ∫ r in Set.Ioi z, g r with hΦdef
  have hgcont : ContinuousOn g (Set.Ioi 0) := (hg 1).continuousOn
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Φ (-(g z)) z := by
    intro z hz
    have hz0 : 0 < z := hz
    set a : ℝ := z / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have haz : a < z := by rw [ha]; linarith
    have hinta : MeasureTheory.IntegrableOn g (Set.Ioi a) := hint a ha0
    have hcont_z : ContinuousAt g z := hgcont.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hint_az : IntervalIntegrable g volume a z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le haz.le]
      exact hinta.mono_set Set.Ioc_subset_Ioi_self
    have hmeas : StronglyMeasurableAtFilter g (𝓝 z) volume :=
      ⟨Set.Ioi a, Ioi_mem_nhds haz, hinta.aestronglyMeasurable⟩
    have hprim : HasDerivAt (fun u => ∫ x in a..u, g x) (g z) z :=
      intervalIntegral.integral_hasDerivAt_right hint_az hmeas hcont_z
    have hev : (fun u => (∫ r in Set.Ioi a, g r) - ∫ x in a..u, g x) =ᶠ[𝓝 z] Φ := by
      filter_upwards [Ioi_mem_nhds haz] with u hu
      have hau : a < u := hu
      have h1 : MeasureTheory.IntegrableOn g (Set.Ioi u) := hint u (by linarith)
      have hadd := intervalIntegral.integral_interval_add_Ioi (f := g) (a := a) (b := u) hinta h1
      show (∫ r in Set.Ioi a, g r) - ∫ x in a..u, g x = ∫ r in Set.Ioi u, g r
      linarith [hadd]
    simpa using (hprim.const_sub (∫ r in Set.Ioi a, g r)).congr_of_eventuallyEq hev.symm
  have hderiv_eq : ∀ x ∈ Set.Ioi (0 : ℝ), deriv Φ x = -(g x) := fun x hx => (hderiv x hx).deriv
  have hPhi : ContDiffOn ℝ ∞ Φ (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact ((contDiffOn_infty.mpr (fun n => hg n)).neg).congr (fun x hx => hderiv_eq x hx)
  exact ⟨fun m => contDiffOn_infty.mp hPhi m, hderiv⟩

/-- **The primitive of a smooth function is smooth.**  On `(c,∞)` with `c > 0` it is the
interval integral `∫_c^· φ` of a smooth function. -/
private theorem primitive_contDiffOn_aux {φ : ℝ → ℝ}
    (hφ : ∀ m : ℕ, ContDiffOn ℝ m φ (Set.Ioi 0))
    (hint : ∀ a : ℝ, 0 < a → MeasureTheory.IntegrableOn φ (Set.Ioc 0 a)) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun z => ∫ s in (0 : ℝ)..z, φ s) (Set.Ioi 0) := by
  set P : ℝ → ℝ := fun z => ∫ s in (0 : ℝ)..z, φ s with hPdef
  have hφcont : ContinuousOn φ (Set.Ioi 0) := (hφ 1).continuousOn
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt P (φ z) z := by
    intro z hz
    have hz0 : 0 < z := hz
    have hcont_z : ContinuousAt φ z := hφcont.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hint_z : IntervalIntegrable φ volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz0.le]
      exact hint z hz0
    have hmeas : StronglyMeasurableAtFilter φ (𝓝 z) volume :=
      ⟨Set.Ioi 0, Ioi_mem_nhds hz, hφcont.aestronglyMeasurable measurableSet_Ioi⟩
    exact intervalIntegral.integral_hasDerivAt_right hint_z hmeas hcont_z
  have hP : ContDiffOn ℝ ∞ P (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_⟩
    exact (contDiffOn_infty.mpr (fun n => hφ n)).congr (fun x hx => (hderiv x hx).deriv)
  exact fun m => contDiffOn_infty.mp hP m

/-! ## The main theorem -/

theorem Gsing_ode_of_sol (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    (hmem : Work.Spaces.HkMem α k F) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0)) ∧
      (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  have hFstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    fstar_contDiffOn_of_bsl_aux α F Ψ hα hsm hsol
  have hcontF : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi 0) := (hFstar 1).continuousOn
  have hbd : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.Fstar F z| ≤ C * (z ^ 2 / (1 + z) ^ 2)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
    fstar_abs_le_hk_aux α k F Ψ hsm hsol hmem
  have hdiv_int : ∀ a ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi a) :=
    integrableOn_fstar_div_aux α k F hcontF hbd hmem
  have hdiv_smooth : ∀ m : ℕ,
      ContDiffOn ℝ m (fun r => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := fun m =>
    (hFstar m).div contDiffOn_id
      (fun x hx => by simp only [Set.mem_Ioi] at hx; exact ne_of_gt hx)
  have htail := tailIntegral_contDiffOn_aux hdiv_smooth hdiv_int
  -- `G_*`
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    have h1 : ContDiffOn ℝ m
        (fun z => -(1 / (4 * α)) * (3 * ∫ r in Set.Ioi z, Work.Elliptic.Fstar F r / r))
        (Set.Ioi 0) :=
      contDiffOn_const.mul (contDiffOn_const.mul (htail.1 m))
    refine h1.congr fun z hz => ?_
    simp only [Work.Elliptic.Gstar, Work.Elliptic.L12_eq_radial, Work.Elliptic.L12rad]
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z')
        (-(3 * Work.Elliptic.Fstar F z / z)) z := by
    intro z hz
    have h := htail.2 z hz
    have h3 : HasDerivAt (fun z' => 3 * Work.Elliptic.L12rad F z')
        (3 * -(Work.Elliptic.Fstar F z / z)) z := h.const_mul 3
    have hev : (fun z' => 3 * Work.Elliptic.L12rad F z')
        =ᶠ[𝓝 z] (fun z' => Work.Elliptic.L12 F z') := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      rw [Work.Elliptic.L12_eq_radial]
    have h4 := h3.congr_of_eventuallyEq hev.symm
    have hval : 3 * -(Work.Elliptic.Fstar F z / z) = -(3 * Work.Elliptic.Fstar F z / z) := by
      ring
    rw [hval] at h4
    exact h4
  -- `Ḡ`
  have hweight_int : ∀ a ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioc 0 a) :=
    integrableOn_weight_mul_fstar_aux α k F hα hα1 hcontF hbd hmem
  have hweight_smooth : ∀ m : ℕ,
      ContDiffOn ℝ m (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0) := by
    intro m
    refine (ContDiffOn.rpow_const_of_ne contDiffOn_id
      (fun x hx => by simp only [Set.mem_Ioi] at hx; exact ne_of_gt hx)).mul (hFstar m)
  have hprim := primitive_contDiffOn_aux hweight_smooth hweight_int
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have h1 : ContDiffOn ℝ m
        (fun z => -(3 / (4 * α)) * z ^ (-(5 / α)) * (∫ s in (0 : ℝ)..z,
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)) (Set.Ioi 0) := by
      refine ContDiffOn.mul (ContDiffOn.mul contDiffOn_const ?_) (hprim m)
      exact ContDiffOn.rpow_const_of_ne contDiffOn_id
        (fun x hx => by simp only [Set.mem_Ioi] at hx; exact ne_of_gt hx)
    exact h1.congr fun z hz => rfl
  have hGsing : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0) := fun m =>
    (hGstar m).add (hGbar m)
  -- the three HasDerivAt hypotheses of `Work.Elliptic.Gsing_ode`
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    have hd : DifferentiableAt ℝ (Work.Elliptic.Fstar F) z :=
      ((hFstar 1).differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
    exact hd.hasDerivAt
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z',
          s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    have hz0 : 0 < z := hz
    have hint_z : IntervalIntegrable
        (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) volume 0 z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz0.le]
      exact hweight_int z hz0
    have hcont_z : ContinuousAt
        (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) z :=
      (hweight_smooth 1).continuousOn.continuousAt (isOpen_Ioi.mem_nhds hz)
    have hmeas : StronglyMeasurableAtFilter
        (fun s => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (𝓝 z) volume :=
      ⟨Set.Ioi 0, Ioi_mem_nhds hz,
        (hweight_smooth 1).continuousOn.aestronglyMeasurable measurableSet_Ioi⟩
    exact intervalIntegral.integral_hasDerivAt_right hint_z hmeas hcont_z
  exact ⟨hFstar, hGsing, fun z hz => Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ z hz⟩

end Work.FTS.EllipticEst
