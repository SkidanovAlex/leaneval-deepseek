/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/PZeroAux/hkNorm_Pz_le.lean` — `P₀` is bounded on `ℋᵏ`

The projection `Work.FTS.StrongEps.Pz` of the lead's design (`PZero.lean`),

  `P₀ f = f − (L₁₂ f 0 / L₁₂(bump)(0)) • bump`,

is *bounded* in the weighted `ℋᵏ`-norm:

  `∃ A > 0, ∀ α ∈ (0,1], ∀ k ≤ 6, ∀ f, SmoothOpen f → HkMem α 6 f →
      ‖P₀ f‖_{ℋᵏ} ≤ A ‖f‖_{ℋ⁶}`.

## Proof

`P₀ f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`, so the two ingredients are

* **subadditivity** of the weighted norm on the open quadrant,
  `HkNorm_add_fts`: `‖g₁ + g₂‖_{ℋᵏ} ≤ √2 (‖g₁‖_{ℋᵏ} + ‖g₂‖_{ℋᵏ})`, for `SmoothOpen` data in `ℋᵏ`
  (no membership of the sum is needed);
* **absolute homogeneity**, `HkNorm_const_mul`: `‖c • bump‖_{ℋᵏ} = |c| ‖bump‖_{ℋᵏ}`;
* the **zero-mode bound** `OpenPkg.l12zero_field` (proved, constant `3`),
  `|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}`, together with the monotonicity `|f|_{ℋ⁴} ≤ |f|_{ℋ⁶}`
  (`StrongLWP.HkNorm_mono_of_mem`) and `pzNorm > 0` (`PZeroAux.pzNorm_pos`, proved in this
  directory), which gives the coefficient bound `|c| ≤ (3/pzNorm) |f|_{ℋ⁶}`;
* a **uniform bound for the correction profile**, `exists_HkNorm_bump_le` below:
  `‖bump‖_{ℋᵏ} ≤ B` for every `α ∈ (0,1]` and `k ≤ 6` — the support of `bump` is the box
  `[1/2,1] × [π/4,3π/8]`, compactly contained in the open quadrant and away from the singular
  lines `z = 0`, `sin(2θ) = 0`, so every weight occurring in `HkIntegrand` is uniformly bounded
  there.

Everything is assembled with `Work.Spaces.HkNorm α k = √(HkSq α k)`, ending with
`A = √2 (1 + 3 B / pzNorm)`.  Every declaration in this file is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.MolClassC
import Submission.Work.FTS.EllipticEst.HkNorm_add_fts
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.Spaces.SmoothCompact_HkInf
import Submission.Work.FTS.Galerkin.Hilbert.HkMem_const_mul
import Submission.Work.FTS.GalLimit.Closure.phi_HQo
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Uniform bounds for the correction profile `bump`

The only `α`-dependence of `Work.Spaces.HkIntegrand α k f` is through the angular weight
`Wt α z θ = w z · sin(2θ)^{-γ(α)/2}`, with `γ(α) = 1 + α/10` increasing in `α`.  On `Iθ` the
base `sin(2θ)` lies in `[0,1]`, where `x ↦ x^{p}` is *antitone*, so the weight is increasing in
`α`: this is the first lemma.  It upgrades the per-`α` bounds of `BumpDefs.lean`
(`exists_bound_HkIntegrand_bump`) to a single bound valid for all `α ∈ (0,1]` and `k ≤ 6`. -/

/-- **Monotonicity of the `ℋ^k`-integrand in the parameter `α`.**  For `0 < α ≤ β`, on the
angular interval `Iθ = [0,π/2]` the weight `Wt α z θ` grows with `α` (the exponent `γ(α)/2`
grows and the base `sin(2θ) ∈ [0,1]`), so every summand of `HkIntegrand` grows termwise. -/
theorem HkIntegrand_gam_mono {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (k : ℕ)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand β k f z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hga : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hgb : 0 < Work.Spaces.gam β := Work.Spaces.gam_pos hβ0
  have hexp : -(Work.Spaces.gam β / 2) ≤ -(Work.Spaces.gam α / 2) := by
    have h : Work.Spaces.gam α ≤ Work.Spaces.gam β := by
      rw [Work.Spaces.gam, Work.Spaces.gam]; linarith
    linarith
  have hrpow : Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))
      ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)) := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h, Real.zero_rpow (by intro hc; linarith [hga]),
        Real.zero_rpow (by intro hc; linarith [hgb])]
    · exact Real.rpow_le_rpow_of_exponent_ge h hs1 hexp
  have hw0 : 0 ≤ Work.Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hterm : ∀ a : ℝ,
      (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        ≤ (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)))) ^ 2 := by
    intro a
    have hA0 : 0 ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) :=
      mul_nonneg hw0 (Real.rpow_nonneg hs0 _)
    have hAB : Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))
        ≤ Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)) :=
      mul_le_mul_of_nonneg_left hrpow hw0
    have hsq : (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        ≤ (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2))) ^ 2 :=
      pow_le_pow_left₀ hA0 hAB 2
    calc (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = a ^ 2 * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
          ring
      _ ≤ a ^ 2 * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      _ = (a * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam β / 2)))) ^ 2 := by
          ring
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add (le_refl _) ?_
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · rw [if_pos hc, if_pos hc]
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact hterm _
  · rw [if_neg hc, if_neg hc]

/-- The correction profile `bump` lies in `ℋᵏ` for every parameter `α` and every order `k`: its
support is the box `[1/2,1] × [π/8, 3π/8]`, strictly inside the open quadrant, and `bump` is
`C^∞` on the whole plane (`Work.FTS.GalLimit.Closure.hkMem_of_suppIn`). -/
theorem hkMem_bump (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := by
  refine Work.FTS.GalLimit.Closure.hkMem_of_suppIn α k (a := 1 / 2) (b := 1)
    (δ := Real.pi / 8) (by norm_num) (by norm_num) (by linarith [Real.pi_pos]) ?_ ?_
  · exact contDiffOn_iff_forall_nat_le.mpr
      (fun m _ => (Work.FTS.StrongEps.contDiff_bump m).contDiffOn)
  · intro z θ h
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    rcases h with h | h
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact Or.inl (le_of_lt h)
      · exact Or.inr (Or.inl (le_of_lt h))
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl (by linarith [h, Real.pi_pos])))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))

/-- **The correction profile is uniformly bounded in `ℋᵏ`.**  There is a single constant `B`
with `‖bump‖_{ℋᵏ} ≤ B` for every `α ∈ (0,1]` and every `k ≤ 6`.

The `ℋᵏ`-integrand of `bump` vanishes off the box `[1/2,1] × [π/4,3π/8]`
(`HkIntegrand_bump_eq_zero_of_not_mem`), and on that box it is bounded by the `α`-independent
constant supplied by `exists_bound_HkIntegrand_bump` at `α = 1`, `k = 6`, by the monotonicity in
`k` (`OpenPkg.HkIntegrand_mono_le`) and in `α` (`HkIntegrand_gam_mono`).  The squared norm is
then bounded with `HkSq_le_of_bound` (the `z`-support ends at `R = 1`). -/
theorem exists_HkNorm_bump_le :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 →
      Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := by
  obtain ⟨M, hMnn, hM⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump 1 6
  refine ⟨max 1 (Real.sqrt (M * (Real.pi / 2) * (1 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α hα k hk
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ ≤ M := by
    intro z hz θ hθ
    refine le_trans (le_trans ?_ (Work.FTS.OpenPkg.HkIntegrand_mono_le 1 hk _ z θ)) (hM z θ)
    exact HkIntegrand_gam_mono hα0 hα1 k _ hθ
  have hfg : ∀ z θ : ℝ, 1 < z → Work.FTS.StrongEps.bump z θ = 0 := by
    intro z θ hz
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    exact Or.inr (Or.inl (le_of_lt hz))
  have hsq := Work.Spaces.HkSq_le_of_bound α k Work.FTS.StrongEps.bump 1 M
    (by norm_num) hMnn hfg hbound
  rw [Work.Spaces.HkNorm]
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_max_right _ _)

/-! ## Two elementary closure properties used by the assembly -/

/-- `ℋᵏ` is closed under multiplication by a constant, with no smoothness hypothesis: the
integrand is homogeneous of degree two (`Galerkin.Hilbert.HkIntegrand_const_mul`), and the
integral is linear for constants. -/
theorem HkMem_const_mul_gen {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hm
  constructor
  · intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
          funext fun θ => Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α k c f z θ]
      rw [MeasureTheory.integral_const_mul]
    rw [hfun]
    exact h2.const_mul _

/-- Scalar multiples of a `SmoothOpen` function are `SmoothOpen` (the open-quadrant class is
closed under `C^∞`-multiplication and contains the constants). -/
theorem smoothOpen_const_mul_gen (c : ℝ) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * F z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => c * F z θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => c * F p.1 p.2)
    Work.FTS.EllipticEst.Q0
  have hF' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => F p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hF
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hF'

/-! ## The bound -/

/-- **`P₀` is bounded on `ℋᵏ`, uniformly in the parameter `α` and the order `k ≤ 6`.**

`P₀ f = f + (−c) • bump` with `c = L₁₂ f 0 / pzNorm`; the subadditivity of the norm on the open
quadrant (`HkNorm_add_fts`), its absolute homogeneity (`HkNorm_const_mul`), the proven zero-mode
bound `|L₁₂ f 0| ≤ 3 |f|_{ℋ⁴}` (`OpenPkg.l12zero_field`), the monotonicity `|f|_{ℋ⁴} ≤ |f|_{ℋ⁶}`
and the uniform bound `‖bump‖_{ℋᵏ} ≤ B` give the constant
`A = √2 (1 + 3 B / pzNorm)`. -/
theorem hkNorm_Pz_le :
    ∃ A : ℝ, 0 < A ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkNorm α k (Work.FTS.StrongEps.Pz f) ≤ A * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨B, hBpos, hB⟩ := exists_HkNorm_bump_le
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := pzNorm_pos
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm), ?_, ?_⟩
  · have h1 : 0 < C₁ * B / Work.FTS.StrongEps.pzNorm :=
      div_pos (mul_pos hC₁pos hBpos) hpzpos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  · intro α hα k hk f hfsm hm6
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hmemk : Work.Spaces.HkMem α k f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm k hk hm6
    have hmem4 : Work.Spaces.HkMem α 4 f :=
      Work.FTS.OpenPkg.HkMem_mono_open hfsm 4 (by norm_num) hm6
    -- the zero-mode bound and the descent `ℋ⁶ → ℋ⁴`
    have hl12 : |Work.Construction.L12 f 0| ≤ C₁ * Work.Spaces.HkNorm α 4 f := by
      simpa only [Work.FTS.Nonlin.Xn] using hC₁ α hα0 hα1 f ⟨hfsm, hmem4⟩
    have hnorm46 : Work.Spaces.HkNorm α 4 f ≤ Work.Spaces.HkNorm α 6 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hm6
    have hnormk6 : Work.Spaces.HkNorm α k f ≤ Work.Spaces.HkNorm α 6 f :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := k) hk hm6
    have hcoefnn : 0 ≤ C₁ / Work.FTS.StrongEps.pzNorm := div_nonneg hC₁nn hpzpos.le
    -- the correction coefficient is controlled by the `ℋ⁶`-norm
    have hc_bound : |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
        ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f := by
      rw [abs_div, abs_of_pos hpzpos]
      calc |Work.Construction.L12 f 0| / Work.FTS.StrongEps.pzNorm
          ≤ (C₁ * Work.Spaces.HkNorm α 4 f) / Work.FTS.StrongEps.pzNorm :=
            div_le_div_of_nonneg_right hl12 hpzpos.le
        _ = (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 f := by ring
        _ ≤ (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_left hnorm46 hcoefnn
    -- the correction profile
    have hbmem : Work.Spaces.HkMem α k Work.FTS.StrongEps.bump := hkMem_bump α k
    have hbnorm : Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := hB α hα k hk
    have hgbump : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry Work.FTS.StrongEps.bump)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => Work.FTS.StrongEps.smoothOpen_bump.forall n
    have hgsm : ∀ n : ℕ, ContDiffOn ℝ (↑n)
        (Function.uncurry (fun z θ => (-(Work.Construction.L12 f 0
          / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun n => (smoothOpen_const_mul_gen (-(Work.Construction.L12 f 0
        / Work.FTS.StrongEps.pzNorm)) Work.FTS.StrongEps.smoothOpen_bump).forall n
    have hgmem : Work.Spaces.HkMem α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ) :=
      HkMem_const_mul_gen _ hbmem
    -- `Pz f` in the additive shape needed by the subadditivity lemma
    have hPz : Work.FTS.StrongEps.Pz f
        = fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ := by
      funext z θ
      rw [Work.FTS.StrongEps.Pz_apply]
      ring
    rw [hPz]
    have hadd := Work.FTS.EllipticEst.HkNorm_add_fts α k
      (fun n => hfsm.forall n) hgsm hmemk hgmem
    have hcm : Work.Spaces.HkNorm α k
        (fun z θ => (-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm))
          * Work.FTS.StrongEps.bump z θ)
        = |-(Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)|
          * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump :=
      Work.FTS.EllipticEst.HkNorm_const_mul α k _ hgbump
    rw [hcm, abs_neg] at hadd
    calc Work.Spaces.HkNorm α k (fun z θ => f z θ + (-(Work.Construction.L12 f 0
            / Work.FTS.StrongEps.pzNorm)) * Work.FTS.StrongEps.bump z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f
            + |Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm|
              * Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump) := hadd
      _ ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 6 f
            + (C₁ / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 6 f * B) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hnormk6 ?_) (Real.sqrt_nonneg 2)
          exact mul_le_mul hc_bound hbnorm (Work.Spaces.HkNorm_nonneg _ _ _)
            (mul_nonneg hcoefnn (Work.Spaces.HkNorm_nonneg _ _ _))
      _ = Real.sqrt 2 * (1 + C₁ * B / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.HkNorm α 6 f := by ring

end Work.FTS.StrongEps.PZeroAux
