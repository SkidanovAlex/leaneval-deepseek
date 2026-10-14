import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFamSupAux.ug_bound
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_paramC2
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassC.RadGreenModeEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "w" => Work.Spaces.w
local notation "a" => Work.FTS.PhiStar.Radial.radGreen

/-- **The sharp weighted `L²` per-mode bound for `radGreen`.** -/
theorem radGreen_modeEnergy {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ}
    (hcont : ContinuousOn c (Set.Ioi 0))
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (hvy : ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    (hg0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hg0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hginf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1))
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (a α m c) (deriv (a α m c) z) z)
    (hderiv2 : ∀ z : ℝ, 0 < z → HasDerivAt (deriv (a α m c)) (deriv (deriv (a α m c)) z) z)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => (z * deriv (a α m c) z) ^ 2 * (w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => (a α m c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
      (fun z => c z * a α m c z * (w z) ^ 2) (Set.Ioi 0))
    (hint4 : MeasureTheory.IntegrableOn
      (fun z => (c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0)) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (a α m c z) ^ 2 * (w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (w z) ^ 2 := by
  -- the mode ODE, in the orientation of `modeWeightedEnergy_sq`
  have hode : ∀ z : ℝ, 0 < z →
      α ^ 2 * z ^ 2 * deriv (deriv (a α m c)) z + α * (5 + α) * z * deriv (a α m c) z
        = Work.FTS.PhiStar.Radial.lamR m * a α m c z - c z := by
    intro z hz
    have h := Work.FTS.PhiStar.Radial.radGreen_solves hα m hcont hg0 hg0' hginf z hz
    linarith
  have hac : ContinuousOn (a α m c) (Set.Ioi 0) := fun z hz =>
    (hderiv z hz).continuousAt.continuousWithinAt
  -- the two flux boundary conditions
  have hnear := radGreen_near_limits hα hα4 m hm hcont hvy hg0 hg0' hginf hderiv
  have hfar := radGreen_far_limits hα hα4 m hcont hdec hg0 hg0' hginf hderiv
  have hflux0 : ContinuousWithinAt (flux α (a α m c)) (Set.Ici 0) 0 :=
    flux_radGreen_zero m hnear.1 hnear.2
  have hfluxinf : Filter.Tendsto (flux α (a α m c)) Filter.atTop (nhds 0) :=
    flux_radGreen_atTop hα m hfar.1 hfar.2
  have hmu : 0 < Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Work.FTS.PhiStar.Radial.lamR]
    nlinarith [sq_nonneg α, hα.le, hα4, hm1]
  exact modeWeightedEnergy_sq (α := α) (lam := Work.FTS.PhiStar.Radial.lamR m) hα hac hderiv
    hderiv2 hode hint1 hint2 hint3 hint4 hflux0 hfluxinf hmu

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Lop_iter_sin_sq_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The coefficient functions `gfun` attached to `L^i (sin(2θ)²)`

`L = Work.Spaces.Lop` is the one-dimensional angular operator `L u θ = sin(2θ) u'(θ)`, whose
iterates are `LopIter i u = (L^[i]) u`.  The operator is a derivation (`Work.Spaces.Lop_mul`),
so `L(s·h) = L(s)·h + s·L(h)`; since `deriv (sin(2θ)²) = 4 sin(2θ) cos(2θ)` the identity
`L(sin(2θ)²·h) = sin(2θ)²·(4 cos(2θ)·h + sin(2θ)·h')` holds wherever `h` is differentiable.
Iterating it, `L^i (sin(2θ)²)` is divisible by `sin(2θ)²`, with quotient the coefficient
function `gfun i` of `LopIterSinSqDefs`. -/

/-- `deriv (fun θ => sin(2θ)²) θ = 4 sin(2θ) cos(2θ)`. -/
theorem lopSq_deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => (Real.sin (2 * t)) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : deriv (fun t : ℝ => Real.sin (2 * t)) θ = 2 * Real.cos (2 * θ) := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
    simpa [Function.comp_def, mul_comm] using h.deriv
  have hfun : (fun t : ℝ => (Real.sin (2 * t)) ^ 2)
      = (fun t : ℝ => Real.sin (2 * t)) ^ 2 := rfl
  rw [hfun, deriv_pow (by fun_prop), h1]
  ring

/-- The one-step recursion `L(sin(2θ)² · h) = sin(2θ)² · (4 cos(2θ) h + sin(2θ) h')`, at every
point where `h` is differentiable. -/
theorem lopSq_Lop_sin_sq_mul (h : ℝ → ℝ) (θ : ℝ) (hh : DifferentiableAt ℝ h θ) :
    Work.Spaces.Lop (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * h θ) θ
      = (Real.sin (2 * θ)) ^ 2 * (4 * Real.cos (2 * θ) * h θ
          + Real.sin (2 * θ) * deriv h θ) := by
  have hsin : DifferentiableAt ℝ (fun t : ℝ => (Real.sin (2 * t)) ^ 2) θ := by fun_prop
  have hfun : (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * h θ)
      = (fun t : ℝ => (Real.sin (2 * t)) ^ 2) * h := rfl
  rw [hfun, Work.Spaces.Lop_mul _ _ θ hsin hh]
  simp only [Work.Spaces.Lop]
  rw [lopSq_deriv_sin_two_sq]
  ring

/-- The iterates of `sin(2θ)²` under `L = sin(2θ) ∂_θ` are `sin(2θ)²` times the coefficient
functions of the recursion:  `L^i (sin(2θ)²) = fun θ => sin(2θ)² · gfun i θ`. -/
theorem lopSq_factor (i : ℕ) :
    LopIter i (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2)
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ 2 * gfun i θ := by
  induction i with
  | zero => simp [LopIter]
  | succ n ih =>
      rw [LopIter_succ, ih, gfun_succ]
      funext θ
      have hd : DifferentiableAt ℝ (gfun n) θ :=
        ((GfunContDiff n).differentiable (by simp)).differentiableAt
      simpa only [Pi.mul_apply] using lopSq_Lop_sin_sq_mul (gfun n) θ hd

/-- A common bound for the finitely many coefficient functions `gfun i`, `i ≤ K`, on the
compact interval `Iθ = [0, π/2]` (each `gfun i` is continuous there by `GfunContDiff`). -/
theorem lopSq_exists_bound_gfun (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ, |gfun i θ| ≤ C := by
  induction K with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      intro i hi θ _
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0
      simp
  | succ K ih =>
      obtain ⟨C, hCpos, hC⟩ := ih
      obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (f := gfun (K + 1)) ((GfunContDiff (K + 1)).continuous.continuousOn)
      refine ⟨max C (D + 1), lt_max_of_lt_left hCpos, ?_⟩
      intro i hi θ hθ
      rcases Nat.lt_or_eq_of_le hi with hlt | heq
      · exact le_trans (hC i (Nat.lt_succ_iff.mp hlt) θ hθ) (le_max_left _ _)
      · subst heq
        have hDθ := hD θ hθ
        rw [Real.norm_eq_abs] at hDθ
        exact le_trans hDθ
          (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _))

/-- Every iterate `L^i (sin(2θ)²)` of `L = sin(2θ) ∂_θ` is `O(sin(2θ)²)` on `Iθ = [0,π/2]`
(these are concrete coefficient functions occurring in the proof of `slice_f_bound`).

Recommended route (much simpler than a derivative ladder): by induction on `i` one has
`L^i (sin²) = fun θ => sin(2θ)^2 * g i θ` with `g : ℕ → ℝ → ℝ` the recursively defined
`g 0 = 1`, `g (i+1) = fun θ => 2 * cos (2θ) * g i θ + sin (2θ) * deriv (g i) θ`
(use `L(f·h) = sin(2θ)·deriv (f·h)` and the product rule: `L(sin²·h) = sin²·(2·deriv(sin²)/sin·h + sin·h')`,
i.e. `deriv (sin(2θ)^2) = 4 sin(2θ) cos(2θ)`, so `g (i+1) = 4cos(2θ)·g i + sin(2θ)·deriv (g i)`).
Each `g i` is `C^∞` on `ℝ` (induction on `i`, using `ContDiff.deriv`), so each is continuous,
hence bounded on the compact `Iθ`; taking the maximum over the finitely many `i ≤ K` gives
`C > 0` with `|g i θ| ≤ C` for `i ≤ K`, `θ ∈ Iθ`, and then
`|L^i (sin²) θ| = sin(2θ)^2 · |g i θ| ≤ C · sin(2θ)^2` (using `sin(2θ) ≥ 0` on `Iθ`).
At `θ = 0, π/2` this is `0 ≤ 0`. -/
theorem Lop_iter_sin_sq_bound (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => (Real.sin (2 * θ)) ^ 2) θ|
      ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := lopSq_exists_bound_gfun K
  refine ⟨C, hCpos, ?_⟩
  intro i hi θ hθ
  rw [lopSq_factor i]
  have hs : 0 ≤ (Real.sin (2 * θ)) ^ 2 := sq_nonneg _
  rw [abs_mul, abs_of_nonneg hs]
  calc (Real.sin (2 * θ)) ^ 2 * |gfun i θ|
        ≤ (Real.sin (2 * θ)) ^ 2 * C := mul_le_mul_of_nonneg_left (hC i hi θ hθ) hs
    _ = C * (Real.sin (2 * θ)) ^ 2 := mul_comm _ _

end Work.FTS.EllipticEst
end
end
-- ===== merged: Submission.Work.FTS.H2.DivQ.Wide_le_Dom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.DivQ

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise estimates -/

/-- **Diagonal domination.** -/
private lemma wide_le_diag {α : ℝ} {h : ℝ → ℝ} {j : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h j x
      ≤ (aCoeff j j x * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
  have hxpos : (0:ℝ) < x := hx.1
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hk0 : (2 * kappa x) ≠ 0 := by positivity
  have hA : (2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)) = (2 * kappa x) ^ (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, one_div, mul_assoc,
      mul_inv_cancel₀ hk0, mul_one]
  have hB : (x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (j : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hxpos j (-(Work.Spaces.gam α))
    rwa [show 2 * (j : ℝ) + (-(Work.Spaces.gam α)) = 2 * (j : ℝ) - Work.Spaces.gam α by ring]
      at h
  have key : ((2 * kappa x) ^ (j + 1) * (x ^ j * iteratedDeriv (j + 1) (sliceX h) x)) ^ 2
        * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      = (2 * kappa x) ^ (2 * j + 1)
        * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by
    set g : ℝ := iteratedDeriv (j + 1) (sliceX h) x
    have h1 : ((2 * kappa x) ^ (j + 1)) ^ 2 = (2 * kappa x) ^ (2 * j + 2) := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring]
    have h2 : (x ^ j * g) ^ 2 = (x ^ j) ^ 2 * g ^ 2 := mul_pow (x ^ j) g 2
    have h3 : ((2 * kappa x) ^ (j + 1) * (x ^ j * g)) ^ 2
        = ((2 * kappa x) ^ (j + 1)) ^ 2 * (x ^ j * g) ^ 2 :=
      mul_pow ((2 * kappa x) ^ (j + 1)) (x ^ j * g) 2
    have h4 : (2 * kappa x) ^ (2 * j + 2) * ((x ^ j) ^ 2 * g ^ 2)
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = ((2 * kappa x) ^ (2 * j + 2) * (1 / (2 * kappa x)))
          * ((x ^ j) ^ 2 * x ^ (-(Work.Spaces.gam α))) * g ^ 2 := by ring
    rw [h3, h1, h2, h4, hA, hB]
    ring
  have hadiag : aCoeff j j x = (2 * kappa x) ^ (j + 1) := by rw [aCoeff_diag]
  rw [hadiag, key, Wide]
  have hnn : (0:ℝ) ≤ x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
      * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)
  have h2' : (1:ℝ) ≤ (2 * kappa x) ^ (2 * j + 1) := one_le_pow₀ hk1
  calc x ^ (2 * (j : ℝ) - Work.Spaces.gam α) * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2
      = 1 * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
          * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) := by ring
    _ ≤ (2 * kappa x) ^ (2 * j + 1)
          * (x ^ (2 * (j : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (j + 1) (sliceX h) x) ^ 2) :=
        mul_le_mul_of_nonneg_right h2' hnn

/-- The `m ≥ 1` summand of `Restn`: the weight `x^{-γ}` combines with `x^{2m}` into `Wide m`. -/
private lemma rest_term_eq {α : ℝ} {h : ℝ → ℝ} {l m : ℕ} {x : ℝ} (hx : 0 < x) :
    (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x)) := by
  have hB : (x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α))
      = x ^ (2 * (m : ℝ) - Work.Spaces.gam α) := by
    have h := pow_sq_mul_rpow hx m (-(Work.Spaces.gam α))
    rwa [show 2 * (m : ℝ) + (-(Work.Spaces.gam α)) = 2 * (m : ℝ) - Work.Spaces.gam α by ring]
      at h
  have h3 : (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      = (aCoeff l m x) ^ 2
        * ((x ^ m) ^ 2 * (iteratedDeriv (m + 1) (sliceX h) x) ^ 2) := by
    rw [mul_pow (aCoeff l m x) (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) 2,
      mul_pow (x ^ m) (iteratedDeriv (m + 1) (sliceX h) x) 2]
  rw [h3, Wide]
  set g : ℝ := iteratedDeriv (m + 1) (sliceX h) x
  rw [show (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * g ^ 2)
        * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
      = (aCoeff l m x) ^ 2 * ((x ^ m) ^ 2 * x ^ (-(Work.Spaces.gam α)))
        * g ^ 2 * (1 / (2 * kappa x)) by ring]
  rw [hB]
  ring

/-- **The off-diagonal remainder.** -/
private lemma rest_le {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) {l : ℕ}
    (hl : 1 ≤ l)
    (hCb : ∀ m ≤ l, ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0:ℝ) xNear, |aCoeff l 0 x| ≤ Cm * x ^ 2)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hWle : ∀ m, 1 ≤ m → m < l → ∀ x ∈ Set.Ioo (0:ℝ) xNear, Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by
  have hxpos : (0:ℝ) < x := hx.1
  have hxIcc : x ∈ Set.Icc (0:ℝ) xNear := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hxle1 : x ≤ 1 := by linarith [hx.2, xNear_lt]
  have hk1 : (1:ℝ) ≤ 2 * kappa x := two_kappa_ge_one hxIcc
  have hkpos : (0:ℝ) < 2 * kappa x := lt_of_lt_of_le one_pos hk1
  have hknn : (0:ℝ) ≤ 1 / (2 * kappa x) := by positivity
  have hlnn : (0:ℝ) ≤ (l : ℝ) := by positivity
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range l)
    (f := fun m => aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x))
  have hCS : (∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2 := by
    simpa using hcs
  have hterm : ∀ m ∈ Finset.range l,
      (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
        ≤ Cm ^ 2 * Dom α h Cm m x := by
    intro m hm
    have hml : m ≤ l := by have := Finset.mem_range.mp hm; omega
    have hmlt : m < l := Finset.mem_range.mp hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      have h4η : x ^ (4 - Work.Spaces.gam α) ≤ x ^ (-(Work.Spaces.eta)) :=
        Real.rpow_le_rpow_of_exponent_ge hxpos hxle1 (by have := gam_lt_four hα1; linarith)
      have hsub : x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2 ≤ SubEta h x :=
        etaPiece_le_subEta hsm hx
      have h1 : (aCoeff l 0 x) ^ 2 ≤ Cm ^ 2 * x ^ 4 := by
        have hle : |aCoeff l 0 x| ≤ Cm * x ^ 2 := hC0 x hxIcc
        rw [show (aCoeff l 0 x) ^ 2 = |aCoeff l 0 x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l 0 x| ^ 2 ≤ (Cm * x ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 * x ^ 4 := by ring
      have hx4 : x ^ 4 * x ^ (-(Work.Spaces.gam α)) = x ^ (4 - Work.Spaces.gam α) := by
        have hh := (Real.rpow_add hxpos (4:ℝ) (-(Work.Spaces.gam α))).symm
        rw [← Real.rpow_natCast x 4]
        exact hh.trans (congrArg (fun e => x ^ e)
          (by ring : (4:ℝ) + (-(Work.Spaces.gam α)) = 4 - Work.Spaces.gam α))
      have hkey : x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
          ≤ x ^ (-(Work.Spaces.eta)) := by
        calc x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
            = x ^ (4 - Work.Spaces.gam α) * (1 / (2 * kappa x)) := by rw [hx4]
          _ ≤ x ^ (4 - Work.Spaces.gam α) * 1 :=
              mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
          _ = x ^ (4 - Work.Spaces.gam α) := by ring
          _ ≤ x ^ (-(Work.Spaces.eta)) := h4η
      simp only [pow_zero, one_mul, Nat.zero_add, iteratedDeriv_one]
      calc (aCoeff l 0 x * deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)))
          = (aCoeff l 0 x) ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ (Cm ^ 2 * x ^ 4) * (deriv (sliceX h) x) ^ 2
              * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
            · exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
        _ = Cm ^ 2 * (deriv (sliceX h) x) ^ 2
              * (x ^ 4 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by ring
        _ ≤ Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta)) := by
            refine mul_le_mul_of_nonneg_left hkey (mul_nonneg (sq_nonneg Cm) (sq_nonneg _))
        _ ≤ Cm ^ 2 * SubEta h x := by
            have hh := mul_le_mul_of_nonneg_left hsub (sq_nonneg Cm)
            rw [show Cm ^ 2 * (deriv (sliceX h) x) ^ 2 * x ^ (-(Work.Spaces.eta))
              = Cm ^ 2 * (x ^ (-(Work.Spaces.eta)) * (deriv (sliceX h) x) ^ 2) by ring]
            exact hh
        _ = Cm ^ 2 * Dom α h Cm 0 x := by rw [Dom_zero]
    · have h1 : (aCoeff l m x) ^ 2 ≤ Cm ^ 2 := by
        have hle : |aCoeff l m x| ≤ Cm := hCb m hml x hxIcc
        rw [show (aCoeff l m x) ^ 2 = |aCoeff l m x| ^ 2 from (sq_abs _).symm]
        calc |aCoeff l m x| ^ 2 ≤ Cm ^ 2 := by
              simpa using pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = Cm ^ 2 := rfl
      have hinv : 1 / (2 * kappa x) ≤ 1 := by rw [div_le_one hkpos]; linarith
      rw [rest_term_eq (α := α) (h := h) (x := x) hxpos]
      calc (aCoeff l m x) ^ 2 * Wide α h m x * (1 / (2 * kappa x))
          ≤ Cm ^ 2 * Wide α h m x * 1 := by
            have hp : (0:ℝ) < 1 / (2 * kappa x) := div_pos one_pos hkpos
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (Wide_nonneg α h m hxpos.le))
              hinv (le_of_lt hp) (mul_nonneg (sq_nonneg Cm) (Wide_nonneg α h m hxpos.le))
        _ ≤ Cm ^ 2 * Dom α h Cm m x := by
            have h3 := hWle m hmpos hmlt x hx
            nlinarith [h3, sq_nonneg Cm]
  have hstep1 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    have hz : (0:ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _) hknn
    have h0 : (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (Restn h l x) ^ 2 * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
      ring
    have hS : Restn h l x = ∑ m ∈ Finset.range l,
        aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x) := rfl
    rw [hS]
    rw [show (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
        = (∑ m ∈ Finset.range l, aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
          * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) by ring]
    refine (mul_le_mul_of_nonneg_right hCS hz).trans (le_of_eq ?_)
    rw [mul_assoc, Finset.sum_mul]
  calc (Restn h l x) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l,
          (aCoeff l m x * (x ^ m * iteratedDeriv (m + 1) (sliceX h) x)) ^ 2
            * (x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := hstep1
    _ ≤ ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hlnn
    _ = ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x := by
        have h1 : ((l : ℝ)) * ∑ m ∈ Finset.range l, Cm ^ 2 * Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) := by
          simp only [Finset.mul_sum]
        rw [show ((l : ℝ)) * Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x
            = ((l : ℝ)) * (Cm ^ 2 * ∑ m ∈ Finset.range l, Dom α h Cm m x) by ring]
        exact h1
    _ = ((l : ℝ)) * Cm ^ 2 * AccDom α h Cm l x := by rw [accDom_eq_sum]

/-- The pointwise Young step at level `k+1`. -/
private lemma wide_le_dom_succ {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCm : 0 ≤ Cm) (hα1 : α ≤ 1) (hk : k + 1 ≤ 4)
    (hCb : ∀ m ≤ k + 1, ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) m x| ≤ Cm)
    (hC0 : ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff (k + 1) 0 x| ≤ Cm * x ^ 2)
    (hWle : ∀ m, 1 ≤ m → m ≤ k → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h (k + 1) x ≤ Dom α h Cm (k + 1) x := by
  have hxpos : (0 : ℝ) < x := hx.1
  have hkpos : (0 : ℝ) < 2 * kappa x :=
    lt_of_lt_of_le one_pos (two_kappa_ge_one ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hknn : (0 : ℝ) ≤ x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) :=
    mul_nonneg (Real.rpow_nonneg hxpos.le _) (le_of_lt (div_pos one_pos hkpos))
  set A : ℝ := aCoeff (k + 1) (k + 1) x
    * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x) with hA
  set R : ℝ := Restn h (k + 1) x with hR
  have hExp : Work.Elliptic.Dth1Iter (k + 1) (deriv h) (thetaOf x) = Expn h (k + 1) x :=
    Dth1Iter_deriv_expansion (k + 1) hsm hx
  have hR' : (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
      * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x)) = R := by
    rw [hR]; rfl
  have hsplit : Expn h (k + 1) x = A + R := by
    have hE : Expn h (k + 1) x
        = (∑ l ∈ Finset.range (k + 1), aCoeff (k + 1) l x
            * (x ^ l * iteratedDeriv (l + 1) (sliceX h) x))
          + (aCoeff (k + 1) (k + 1) x
            * (x ^ (k + 1) * iteratedDeriv ((k + 1) + 1) (sliceX h) x)) := by
      simp only [Expn]
      rw [Finset.sum_range_succ]
    rw [hE, hR', ← hA, add_comm]
  have hHon : HonGam α h (k + 1) x
      = (A + R) ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    simp only [HonGam]
    rw [← hsplit, ← hExp]
  have hdiag : Wide α h (k + 1) x
      ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := by
    rw [hA]; exact wide_le_diag hx
  have hY2 : A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := by
    have := mul_le_mul_of_nonneg_right (young A R) hknn
    simpa only [mul_assoc] using this
  have h2 : (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
        * (1 / (2 * kappa x))
      = 2 * HonGam α h (k + 1) x
        + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := by
    rw [hHon]; ring
  have h3 : R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))
      ≤ (((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x := by
    rw [hR]
    exact rest_le (α := α) (h := h) (Cm := Cm) hCm hα1 (by omega) hCb hC0 hsm
      (fun m hm1 hmk => hWle m hm1 (by omega)) hx
  calc Wide α h (k + 1) x ≤ A ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x)) := hdiag
    _ ≤ (2 * (A + R) ^ 2 + 2 * R ^ 2) * x ^ (-(Work.Spaces.gam α))
          * (1 / (2 * kappa x)) := hY2
    _ = 2 * HonGam α h (k + 1) x
          + 2 * (R ^ 2 * x ^ (-(Work.Spaces.gam α)) * (1 / (2 * kappa x))) := h2
    _ ≤ 2 * HonGam α h (k + 1) x
          + 2 * ((((k + 1 : ℕ) : ℝ)) * Cm ^ 2 * AccDom α h Cm (k + 1) x) := by
        linarith [h3]
    _ = Dom α h Cm (k + 1) x := by rw [Dom_succ_eq]; ring

/-- **`Wide ≤ Dom`.**  The `x`-weighted square of the `(l+1)`-st slice derivative is dominated
by the level-`l` member of the inversion recursion, for `1 ≤ l ≤ 4`. -/
theorem Wide_le_Dom {α : ℝ} {h : ℝ → ℝ} {Cm : ℝ}
    (hα1 : α ≤ 1) (hCm : 0 ≤ Cm)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)))
    (hCb : ∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm)
    (hC0 : ∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
      ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2)
    {l : ℕ} (hl1 : 1 ≤ l) (hl4 : l ≤ 4) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) xNear) :
    Wide α h l x ≤ Dom α h Cm l x := by
  have key : ∀ k ≤ 3, ∀ m, 1 ≤ m → m ≤ k + 1 → ∀ x ∈ Set.Ioo (0 : ℝ) xNear,
      Wide α h m x ≤ Dom α h Cm m x := by
    intro k hk
    induction k with
    | zero =>
        intro m hm1 hm2 x hx
        obtain rfl : m = 1 := by omega
        exact wide_le_dom_succ hsm hCm hα1 (by omega)
          (fun m hm x hx => hCb 1 m le_rfl (by norm_num) hm x hx)
          (fun x hx => hC0 1 le_rfl (by norm_num) x hx)
          (fun m hm1 hm2 => by omega) hx
    | succ k ih =>
        intro m hm1 hm2 x hx
        rcases Nat.lt_or_ge m (k + 2) with hlt | hge
        · exact ih (by omega) m hm1 (by omega) x hx
        · obtain rfl : m = k + 2 := by omega
          refine wide_le_dom_succ hsm hCm hα1 (by omega)
            (fun m hm x hx => hCb (k + 2) m (by omega) (by omega) hm x hx)
            (fun x hx => hC0 (k + 2) (by omega) (by omega) x hx) ?_ hx
          intro r hr1 hr2
          exact ih (by omega) r hr1 (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  exact key k (by omega) (k + 1) (by omega) le_rfl x hx

end Work.FTS.H2.DivQ
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOde =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

/-! ## 7. The target -/

theorem SeriesOde (c d : ℕ → ℝ)
    (hcd : ∀ m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.lam m = d m)
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    ContDiffOn ℝ 2 (fun θ : ℝ => ∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ
          = ∑' m : ℕ, d m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  refine ⟨contDiffOn_series hc hd hcd, fun θ hθ => ?_⟩
  obtain ⟨h0, h1⟩ := hθ
  set ε : ℝ := min θ (Real.pi / 2 - θ) / 2 with hεdef
  have hpi : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  have hε : 0 < ε := by
    rw [hεdef]
    have h2 : (0 : ℝ) < min θ (Real.pi / 2 - θ) := lt_min h0 hpi
    linarith
  have hmem : θ ∈ Set.Ioo ε (Real.pi / 2 - ε) := by
    rw [hεdef]
    constructor
    · have h := min_le_left θ (Real.pi / 2 - θ); linarith
    · have h := min_le_right θ (Real.pi / 2 - θ); linarith
  exact lzero_series hcd hc hd hε hmem

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.eFam_growth_clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng

set_option maxHeartbeats 1000000

open scoped Real
open Work.FTS.PhiStar.Gegenbauer (eFam gC)

/-! ## 7. The two base cases of the induction -/

/-- **The `θ`-derivative of `eFam m`.**  The radial energy bound `ene m ≤ (Npsi m)²` of
`Series.eFamSupDefs` gives `|(ug m)' x| ≤ Npsi m`, and `ug_bound` gives
`|ug m x| ≤ √(Npsi m)·√(1-x²)`.  Since `(eFam m)' θ = (ug m)'(sin θ) + sin θ·(ug m)(sin θ)/cos²θ`
the two combine into `|(eFam m)' θ| ≤ Npsi m + √(Npsi m)/cos θ`. -/
lemma abs_deriv_eFam_le (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |deriv (eFam m) θ| ≤ Work.FTS.PhiStar.Series.Npsi m
      + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hsinI : Real.sin θ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hθ.1) (by linarith [Real.pi_pos, hθ.2]),
      Real.sin_le_one θ⟩
  have hNpos : 0 < Work.FTS.PhiStar.Series.Npsi m := Work.FTS.PhiStar.Series.Npsi_pos m
  -- `|(ug m)'| ≤ Npsi m`
  have hdu : |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
      ≤ Work.FTS.PhiStar.Series.Npsi m := by
    have hle := Work.FTS.PhiStar.Series.ene_le m hsinI
    have hnn : 0 ≤ Work.FTS.PhiStar.Series.Npsi m *
        ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
          * gC (2 * m + 1) (Real.sin θ))) := by
      have h1 : 0 ≤ 1 - (Real.sin θ) ^ 2 := by nlinarith [Real.sin_sq_le_one θ]
      have h2 : 0 ≤ gC (2 * m + 1) (Real.sin θ) * gC (2 * m + 1) (Real.sin θ) :=
        mul_self_nonneg _
      exact mul_nonneg (le_of_lt hNpos) (mul_nonneg h1 h2)
    have hsq : (deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)) ^ 2
        ≤ Work.FTS.PhiStar.Series.Npsi m * Work.FTS.PhiStar.Series.Npsi m := by
      have hen : Work.FTS.PhiStar.Series.ene m (Real.sin θ)
          = deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
              * deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
            + Work.FTS.PhiStar.Series.Npsi m *
              ((1 - (Real.sin θ) ^ 2) * (gC (2 * m + 1) (Real.sin θ)
                * gC (2 * m + 1) (Real.sin θ))) := rfl
      rw [hen] at hle
      nlinarith [hle, hnn, sq_nonneg (deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ))]
    calc |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        = Real.sqrt ((deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Work.FTS.PhiStar.Series.Npsi m * Work.FTS.PhiStar.Series.Npsi m) :=
          Real.sqrt_le_sqrt hsq
      _ = Work.FTS.PhiStar.Series.Npsi m := Real.sqrt_mul_self (le_of_lt hNpos)
  -- `|ug m (sin θ)| ≤ √(Npsi m)·cos θ`
  have hgu : |Work.FTS.PhiStar.Series.ug m (Real.sin θ)|
      ≤ Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ := by
    have h := Work.FTS.PhiStar.Series.eFamSupAux.ug_bound m hsinI
    have h1 : (Work.FTS.PhiStar.Series.ug m (Real.sin θ)) ^ 2
        ≤ (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hNpos)]
      have hs : 1 - (Real.sin θ) ^ 2 = (Real.cos θ) ^ 2 := by
        have h2 := Real.sin_sq_add_cos_sq θ
        linarith
      rw [hs] at h
      linarith [h]
    calc |Work.FTS.PhiStar.Series.ug m (Real.sin θ)|
        = Real.sqrt ((Work.FTS.PhiStar.Series.ug m (Real.sin θ)) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = |Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ| := Real.sqrt_sq_eq_abs _
      _ = Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ :=
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hcos))
  -- the derivative identity
  have hderiv : deriv (eFam m) θ
      = deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
        + Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2 := by
    have hq : HasDerivAt (gC (2 * m + 1)) (deriv (gC (2 * m + 1)) (Real.sin θ)) (Real.sin θ) :=
      (Work.FTS.PhiStar.Series.differentiable_gC (2 * m + 1)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => gC (2 * m + 1) (Real.sin t))
        (deriv (gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) θ :=
      hq.comp θ (Real.hasDerivAt_sin θ)
    have hprod : HasDerivAt (fun t : ℝ => Real.cos t * gC (2 * m + 1) (Real.sin t))
        (-Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + Real.cos θ * (deriv (gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)) θ :=
      (Real.hasDerivAt_cos θ).mul hcomp
    rw [show eFam m = fun t : ℝ => Real.cos t * gC (2 * m + 1) (Real.sin t) from rfl,
      hprod.deriv, Work.FTS.PhiStar.Series.deriv_ug m (Real.sin θ),
      show Work.FTS.PhiStar.Series.ug m (Real.sin θ)
          = (1 - (Real.sin θ) ^ 2) * gC (2 * m + 1) (Real.sin θ) from rfl]
    have hs : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
      have h2 := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hs]
    field_simp
    ring
  have hmid : |Real.sin θ| * |Work.FTS.PhiStar.Series.ug m (Real.sin θ)| / (Real.cos θ) ^ 2
      ≤ 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ)
          / (Real.cos θ) ^ 2 := by
    refine div_le_div_of_nonneg_right (mul_le_mul (Real.abs_sin_le_one θ) hgu (abs_nonneg _)
      (by norm_num)) (by positivity)
  have hfin : 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ)
        / (Real.cos θ) ^ 2
      = Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by
    field_simp
  rw [hderiv]
  calc |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)
        + Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2|
      ≤ |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        + |Real.sin θ * Work.FTS.PhiStar.Series.ug m (Real.sin θ) / Real.cos θ ^ 2| :=
        abs_add_le _ _
    _ = |deriv (Work.FTS.PhiStar.Series.ug m) (Real.sin θ)|
        + |Real.sin θ| * |Work.FTS.PhiStar.Series.ug m (Real.sin θ)| / (Real.cos θ) ^ 2 := by
        rw [abs_div, abs_mul, abs_of_pos (pow_pos hcos 2)]
    _ ≤ Work.FTS.PhiStar.Series.Npsi m
        + 1 * (Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) * Real.cos θ) / (Real.cos θ) ^ 2 :=
        add_le_add hdu hmid
    _ = Work.FTS.PhiStar.Series.Npsi m
        + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := by rw [hfin]

/-- Level `0`: `|eFam m θ| ≤ 3 (m+1)`. -/
lemma growth_zero {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ 0, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := by
  refine ⟨3, by norm_num, ?_⟩
  intro m i hi θ hθ
  have hi0 : i = 0 := by omega
  subst hi0
  have hθI : θ ∈ Work.Spaces.Iθ :=
    ⟨le_of_lt (lt_of_lt_of_le hA hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hB)⟩
  have h1 := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθI
  have h2 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) ≤ 3 * ((m : ℝ) + 1) := sqrt_Npsi_le m
  rw [iteratedDeriv_zero, pow_one]
  linarith [h1, h2]

/-- Levels `0` and `1`: `|eFam m θ| ≤ K (m+1)` and `|(eFam m)' θ| ≤ K (m+1)²`. -/
lemma growth_one {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2) (hAB : A ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ 1, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := by
  have hBpos : 0 < B := lt_of_lt_of_le hA hAB
  have hcosB : 0 < Real.cos B := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hB⟩
  refine ⟨max 3 (6 + 3 / Real.cos B),
    le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left _ _), ?_⟩
  intro m i hi θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hA hθ.1, lt_of_le_of_lt hθ.2 hB⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hI.1, le_of_lt hI.2⟩
  have hp1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp0 : (0 : ℝ) < (m : ℝ) + 1 := lt_of_lt_of_le one_pos hp1
  have hcosge : Real.cos B ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt hI.1) (by linarith [Real.pi_pos, hI.2]) hθ.2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi0 | hi1
  · subst hi0
    rw [iteratedDeriv_zero, pow_one]
    have h1 := Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθI
    have h2 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) ≤ 3 * ((m : ℝ) + 1) :=
      sqrt_Npsi_le m
    have h3 : (3 : ℝ) ≤ max 3 (6 + 3 / Real.cos B) := le_max_left _ _
    have hthis : 3 * ((m : ℝ) + 1) ≤ max 3 (6 + 3 / Real.cos B) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hp0)
    linarith [h1, h2, hthis]
  · subst hi1
    rw [iteratedDeriv_one, show (1 : ℕ) + 1 = 2 from rfl]
    have h1 := abs_deriv_eFam_le m hI
    have hcospos : 0 < Real.cos θ := lt_of_lt_of_le hcosB hcosge
    have hrec : 1 / Real.cos θ ≤ 1 / Real.cos B := one_div_le_one_div_of_le hcosB hcosge
    have hN : Work.FTS.PhiStar.Series.Npsi m = (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) := rfl
    have hstep1 : Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ
        ≤ (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
      rw [hN, div_eq_mul_one_div]
      calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) * (1 / Real.cos θ)
          ≤ (3 * ((m : ℝ) + 1)) * (1 / Real.cos B) :=
            mul_le_mul (sqrt_Npsi_le m) hrec (le_of_lt (one_div_pos.mpr hcospos))
              (by positivity)
        _ ≤ (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
            have h1 : 3 * ((m : ℝ) + 1) ≤ 3 * ((m : ℝ) + 1) ^ 2 := by nlinarith [hp1]
            have h2 : 3 * ((m : ℝ) + 1) * (1 / Real.cos B)
                = 3 * ((m : ℝ) + 1) / Real.cos B := by ring
            have h3 : (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2
                = 3 * ((m : ℝ) + 1) ^ 2 / Real.cos B := by ring
            rw [h2, h3]
            exact div_le_div_of_nonneg_right h1 (le_of_lt hcosB)
    have hkey : Work.FTS.PhiStar.Series.Npsi m
          + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ
        ≤ (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by
      have hdist : (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2
          = 6 * ((m : ℝ) + 1) ^ 2 + (3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := by ring
      linarith [Npsi_le_six m, hstep1, hdist]
    calc |deriv (eFam m) θ| ≤ Work.FTS.PhiStar.Series.Npsi m
            + Real.sqrt (Work.FTS.PhiStar.Series.Npsi m) / Real.cos θ := h1
      _ ≤ (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 := hkey
      _ ≤ max 3 (6 + 3 / Real.cos B) * ((m : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ## 8. The induction step -/

/-- One step of the induction: from bounds for the derivatives of order `≤ k` the bounds for
order `≤ k+1` follow by differentiating the Sturm–Liouville equation once more. -/
lemma growth_step {A B : ℝ} (hA : 0 < A) (hB : B < Real.pi / 2)
    (Tb Sb : ℕ → ℝ) (hTb0 : ∀ i, 0 ≤ Tb i) (hSb0 : ∀ i, 0 ≤ Sb i)
    (hTb : ∀ i θ, θ ∈ Set.Icc A B →
      |iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| ≤ Tb i)
    (hSb : ∀ i θ, θ ∈ Set.Icc A B →
      |iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| ≤ Sb i)
    {k : ℕ} (hk : 1 ≤ k) {K : ℝ} (hK : 0 ≤ K)
    (hIH : ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ m : ℕ, ∀ i ≤ k + 1, ∀ θ ∈ Set.Icc A B,
      |iteratedDeriv i (eFam m) θ| ≤ K' * ((m : ℝ) + 1) ^ (i + 1) := by
  set Cs : ℝ := ∑ i ∈ Finset.range (k - 1 + 1), ((k - 1).choose i : ℝ) * (Tb i + Sb i) with hCs
  have hCs0 : 0 ≤ Cs := by
    rw [hCs]
    exact Finset.sum_nonneg
      (fun i _ => mul_nonneg (by positivity) (add_nonneg (hTb0 i) (hSb0 i)))
  refine ⟨max K (K * (2 * Cs + 7)), le_trans hK (le_max_left _ _), ?_⟩
  intro m i hi θ hθ
  have hI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨lt_of_lt_of_le hA hθ.1, lt_of_le_of_lt hθ.2 hB⟩
  have hp1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp0 : (0 : ℝ) < (m : ℝ) + 1 := lt_of_lt_of_le one_pos hp1
  rcases Nat.eq_or_lt_of_le hi with hik | hik
  · -- `i = k + 1`: the main case, from the differentiated equation
    subst hik
    rw [show k + 1 + 1 = k + 2 by ring]
    have key := eFam_iteratedDeriv_ode m (k - 1) hI
    rw [show k - 1 + 2 = k + 1 by omega] at key
    have hb1 : |tanSum (k - 1) (eFam m) θ| ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      rw [tanSum, hCs, Finset.sum_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
      have hC0 : (0 : ℝ) ≤ ((k - 1).choose i : ℝ) := by positivity
      have hu : |iteratedDeriv (k - 1 + 1 - i) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (k + 2) :=
        le_trans (hIH m (k - 1 + 1 - i) (by omega) θ hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by omega)) hK)
      calc |((k - 1).choose i : ℝ) *
            (iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ * iteratedDeriv (k - 1 + 1 - i) (eFam m) θ)|
          = ((k - 1).choose i : ℝ) *
            (|iteratedDeriv i (fun θ : ℝ => Real.tan θ) θ| * |iteratedDeriv (k - 1 + 1 - i) (eFam m) θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC0]
        _ ≤ ((k - 1).choose i : ℝ) * (Tb i * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hTb i θ hθ) hu (abs_nonneg _) (hTb0 i)) hC0
        _ ≤ ((k - 1).choose i : ℝ) * ((Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right (hSb0 i))
              (mul_nonneg hK (pow_nonneg (le_of_lt hp0) _))) hC0
        _ = ((k - 1).choose i : ℝ) * (Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
    have hb2 : |secSum (k - 1) (eFam m) θ| ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      rw [secSum, hCs, Finset.sum_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
      have hC0 : (0 : ℝ) ≤ ((k - 1).choose i : ℝ) := by positivity
      have hu : |iteratedDeriv (k - 1 - i) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (k + 2) :=
        le_trans (hIH m (k - 1 - i) (by omega) θ hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp1 (by omega)) hK)
      calc |((k - 1).choose i : ℝ) *
            (iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ * iteratedDeriv (k - 1 - i) (eFam m) θ)|
          = ((k - 1).choose i : ℝ) *
            (|iteratedDeriv i (fun θ : ℝ => 1 / (Real.cos θ) ^ 2) θ| * |iteratedDeriv (k - 1 - i) (eFam m) θ|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hC0]
        _ ≤ ((k - 1).choose i : ℝ) * (Sb i * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hSb i θ hθ) hu (abs_nonneg _) (hSb0 i)) hC0
        _ ≤ ((k - 1).choose i : ℝ) * ((Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (hTb0 i))
              (mul_nonneg hK (pow_nonneg (le_of_lt hp0) _))) hC0
        _ = ((k - 1).choose i : ℝ) * (Tb i + Sb i) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
    have hb3 : |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
      have hfi : |iteratedDeriv (k - 1) (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ k := by
        have h := hIH m (k - 1) (by omega) θ hθ
        rwa [show k - 1 + 1 = k by omega] at h
      have hmul : Work.FTS.PhiStar.Series.eM m * |iteratedDeriv (k - 1) (eFam m) θ|
          ≤ (6 * ((m : ℝ) + 1) ^ 2) * (K * ((m : ℝ) + 1) ^ k) :=
        mul_le_mul (eM_le_six m) hfi (abs_nonneg _) (by positivity)
      have hpow : (6 * ((m : ℝ) + 1) ^ 2) * (K * ((m : ℝ) + 1) ^ k)
          = 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by
        rw [show k + 2 = 2 + k by omega, pow_add]
        ring
      rw [abs_mul, abs_of_nonneg (eM_nonneg m)]
      exact le_trans hmul (le_of_eq hpow)
    have htri : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
          - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ |tanSum (k - 1) (eFam m) θ| + |secSum (k - 1) (eFam m) θ|
          + |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ| := by
      have h1 : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
            - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
          ≤ |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ|
            + |Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le (tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ)
            (-(Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ))
      have h2 : |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ|
          ≤ |tanSum (k - 1) (eFam m) θ| + |secSum (k - 1) (eFam m) θ| := abs_add_le _ _
      linarith
    rw [key]
    calc |tanSum (k - 1) (eFam m) θ + secSum (k - 1) (eFam m) θ
          - Work.FTS.PhiStar.Series.eM m * iteratedDeriv (k - 1) (eFam m) θ|
        ≤ Cs * (K * ((m : ℝ) + 1) ^ (k + 2)) + Cs * (K * ((m : ℝ) + 1) ^ (k + 2))
            + 6 * (K * ((m : ℝ) + 1) ^ (k + 2)) := by linarith
      _ = (2 * Cs + 6) * (K * ((m : ℝ) + 1) ^ (k + 2)) := by ring
      _ ≤ max K (K * (2 * Cs + 7)) * ((m : ℝ) + 1) ^ (k + 2) := by
        have h1 : (2 * Cs + 6) * (K * ((m : ℝ) + 1) ^ (k + 2))
            ≤ K * (2 * Cs + 7) * ((m : ℝ) + 1) ^ (k + 2) := by
          nlinarith [hCs0, hK, mul_nonneg hK (pow_nonneg (le_of_lt hp0) (k + 2))]
        exact le_trans h1
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (le_of_lt hp0) _))
  · -- `i < k + 1`, hence `i ≤ k`: monotonicity of the constant
    have hikle : i ≤ k := by omega
    refine le_trans (hIH m i hikle θ hθ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (le_of_lt hp0) _)

/-! ## 9. The theorem -/

theorem eFam_iteratedDeriv_growth (j : ℕ) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h₂ : θ₂ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Icc θ₁ θ₂ →
      |iteratedDeriv j (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ C * ((m : ℝ) + 1) ^ (j + 1) := by
  by_cases hle : θ₁ ≤ θ₂
  · choose Tb hTb using exists_bound_iteratedDeriv_tan h₁ h₂
    choose Sb hSb using exists_bound_iteratedDeriv_secsq h₁ h₂
    have hstep : ∀ k : ℕ, (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc θ₁ θ₂,
          |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) →
        (∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k + 1, ∀ θ ∈ Set.Icc θ₁ θ₂,
          |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1)) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨K, hK0, hK⟩ := growth_one h₁ h₂ hle
        exact ⟨K, hK0, fun m i hi θ hθ => hK m i (by omega) θ hθ⟩
      · obtain ⟨K, hK0, hK⟩ := hk
        exact growth_step h₁ h₂ Tb Sb (fun i => (hTb i).1) (fun i => (hSb i).1)
          (fun i θ hθ => (hTb i).2 θ hθ) (fun i θ hθ => (hSb i).2 θ hθ) hkpos hK0 hK
    have hmain : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ i ≤ k, ∀ θ ∈ Set.Icc θ₁ θ₂,
        |iteratedDeriv i (eFam m) θ| ≤ K * ((m : ℝ) + 1) ^ (i + 1) := fun k =>
      Nat.rec (growth_zero h₁ h₂) (fun k hk => hstep k hk) k
    obtain ⟨C, hC0, hC⟩ := hmain j
    exact ⟨C, hC0, fun m θ hθ => hC m j le_rfl θ hθ⟩
  · exact ⟨0, le_refl 0, fun m θ hθ => absurd (le_trans hθ.1 hθ.2) hle⟩

end Work.FTS.PhiStar.Honesty.CptQSmooth.CleanAng
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero` — the moment conjunct `F_*(Ψ) ≡ 0`

`EllWeakPos α k F Ψ` (and every consumer in the `MixHon`/`Ae` chain) needs the angular moment
`F_*(Ψ) z = ∫_θ Ψ z θ · sinθcos²θ dθ` of the modal solution to vanish, i.e.

  `F_*(psiSeries α F) z = 0` for `z > 0`, from the source's moment `F_*(F) ≡ 0` on `z > 0`.

## The hypothesis `0 < z` is necessary (a review-gate catch)

The statement *without* the hypothesis `0 < z` is **FALSE**: `F_*(psiSeries α F) z` reduces
(`Fstar_psiSeries_eq_tsum`, `eFam_orthogonal`) to `acoeff α 0 F z · 3∫_0^{π/2} sin²θcos³θ dθ`,
and `acoeff α 0 F z = radGreen α 0 (cmode 0 F) z` integrates `cmode 0 F` — a multiple of `F_*(F)`
— over `(z, ∞)`; for `z < 0` that interval contains the negative half-line, about which the
source hypothesis says nothing.  A machine-checked witness is
`Work.FTS.PhiStar.Honesty.Fstar_psiSeries_counterexample`
(`Submission/Work/FTS/PhiStar/Honesty/Fstar_psiSeries_counterexample.lean`, `sorry`-free):
`α = 1`, `z = -1`, `F(t,θ) = 1_{(-1,-1/2)}(t)·(3 sinθcosθ)`.

With `0 < z` — exactly the form in which the node's hypothesis is stated
(`bslOp_sol_exists`: `(∀ z, 0 < z → F_*(F) z = 0)`) — the statement is true, and it is proved
below from the honest forms collected in `Fstar_psiSeries_eq_zero_corrected.lean`
(`Fstar_psiSeries_eq_zero_of_pos`, and the all-`z` variants
`…_of_moment_all`, `…_of_left_support` for sources vanishing on `z ≤ 0`).
-/

namespace Work.FTS.PhiStar.Honesty

/-- **The angular moment of the modal series vanishes at every `z > 0`**, from the vanishing of
the source's moment on the positive half-line (`acoeff α 0 F z = 0`, since the Green function
`radGreen α 0` only sees `z' > 0` when `z > 0`) and the weighted summability of the coefficients
(the zeroth-slot `hcoef` of the honesty capstones). -/
theorem Fstar_psiSeries_eq_zero {α : ℝ} {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsum : Summable (fun m : ℕ => ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hF : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  Fstar_psiSeries_eq_zero_of_pos hz hsum hF

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

set_option autoImplicit false

set_option maxHeartbeats 1000000


end Work.FTS.PhiStar.Honesty
end
end
