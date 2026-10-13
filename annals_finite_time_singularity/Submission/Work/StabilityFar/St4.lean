/-
# `Work.StabilityFar.St4` — the far-field `α`-Hölder bound (`St4`)

**The core calculation of the Stability layer.**  The paper's own self-similar solution has
`ω ~ |x|^{-α}` at infinity, hence `∂ₜω ~ |x|^{-2α}` and `∂ₜu = BS(∂ₜω) ~ |x|^{1-2α}` is
*unbounded* for `α < 1/2`: the paper's solution does **not** satisfy the *joint* `C^{1,α}` clause
of `theorem_1`.  The remedy used here is a compactly supported vorticity: if `ω(·,t)` is supported
in the fixed ball `B(0,R)` on `[0,T]`, then

* `∂ₜω(·,t)` is supported in the *same* ball (`slicesSupported_timeDeriv`: outside the ball the
  slice is identically zero on a neighbourhood of `t`);
* consequently `u = BS(ω)` and `∂ₜu = BS(∂ₜω)` are `O(‖x‖^{-2})` outside `B(0,2R)`, with
  derivatives `O(‖x‖^{-3})` (`Work.StabilityFar.Decay`);
* the two blocks of `fderiv u.uncurry` — the spatial derivative `D_xu` and the time derivative
  `∂ₜu` — are therefore **bounded and `α`-Hölder on the whole far region**:
  *bounded* by the decay estimates, and *Lipschitz* (hence `α`-Hölder, for `α ≤ 1`) because
  either their `x`-derivative or their `x`-Lipschitz constant is uniformly small there, while
  their `t`-variation is controlled by the a priori estimates `TimeHolderOnBall` (for the
  vorticity and for `∂ₜω`) and by `FarDerivLipschitz`.

The conclusion is `IsContDiffHolderOn ℝ α u.uncurry (farRegion (2R+5) ×ˢ Icc 0 T)` — the
far-field half of the joint `C^{1,α}` clause.  The half over the *core* is supplied by the
construction (`St0`–`St3`) and glued in `Work.StabilityFar.Assembly`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.StabilityFar.Decay
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply
import Submission.Work.StabilityFar.Holder.holderOnWith_of_norm_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- The far radius used in `St4`: `2R + 5`.  The slack of `5` makes the `Lipschitz`-on-a-ball
form of the Biot–Savart estimates (`ball x (‖x‖/4)`) and the segment bounds available at every
point of the far region, and keeps the far region inside `{2R < ‖x‖}` where the decay estimates
hold. -/
def st4Radius (R : ℝ) : ℝ := 2 * R + 5

/-! ## `fderiv u.uncurry` on the far region is the block derivative -/

/-- The derivative of `u.uncurry` at a point of the far region is `blockDeriv`; equivalently, the
two blocks of the joint derivative are the spatial and the time derivative. -/
theorem fderiv_uncurry_eq_blockDeriv {u : R3 → ℝ → R3}
    {L : (R3 × ℝ) →L[ℝ] R3} {x : R3} {t : ℝ}
    (h : HasFDerivAt (Function.uncurry u) L (x, t)) : L = blockDeriv u (x, t) := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  obtain ⟨v, s⟩ := w
  rw [Deriv.hasFDerivAt_uncurry_apply h v s, blockDeriv_apply]

/-- `fderivWithin` of `u.uncurry` over the far strip is the block derivative: at a point of the
far region the strip is inside a neighbourhood of the point in the spatial directions (the far
region is open) and in the time directions except at the endpoints of `Icc 0 T`, where
`UniqueDiffWithinAt` still holds (`uniqueDiffWithinAt_convex`). -/
theorem fderivWithin_farStrip_eq_blockDeriv {u : R3 → ℝ → R3} {R T : ℝ} (hT : 0 < T)
    (hsmooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo (-1) (T + 1)))
    {p : R3 × ℝ} (hp : p ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T) :
    fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) p = blockDeriv u p := by
  obtain ⟨x, t⟩ := p
  obtain ⟨hx, ht⟩ := hp
  have hmem : (x, t) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) (T + 1) :=
    ⟨trivial, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hn : Set.univ ×ˢ Set.Ioo (-1 : ℝ) (T + 1) ∈ 𝓝 (x, t) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds hmem
  have hcd : ContDiffAt ℝ 1 (Function.uncurry u) (x, t) := hsmooth.contDiffAt hn
  have hd : HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (x, t)) (x, t) :=
    (hcd.differentiableAt (by norm_num)).hasFDerivAt
  have hu : UniqueDiffWithinAt ℝ (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) (x, t) :=
    UniqueDiffWithinAt.prod ((isOpen_farRegion _).uniqueDiffWithinAt hx)
      (uniqueDiffWithinAt_Icc hT ht)
  have h1 : fderivWithin ℝ (Function.uncurry u) (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) (x, t)
      = fderiv ℝ (Function.uncurry u) (x, t) := (hd.hasFDerivWithinAt).fderivWithin hu
  rw [h1]
  exact fderiv_uncurry_eq_blockDeriv hd

/-! ## `α`-Hölder from a local `α`-Hölder bound and a global bound -/

/-- **A function that is `α`-Hölder on scales `≤ 1` and bounded is `α`-Hölder.**  This is the form
of the interpolation actually produced by the far-field estimates: the blocks of
`fderiv u.uncurry` satisfy an `α`-power estimate at small scales (their `t`-variation is
`α`-Hölder, with exponent `α`, not Lipschitz), and the decay estimates bound them globally. -/
theorem holderOnWith_of_local_holder_bounded {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] {α : NNReal} {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    {f : X → Y} {s : Set X}
    (hlocal : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1 → ‖f x - f y‖ ≤ L * dist x y ^ (α : ℝ))
    (hbdd : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ 2 * B) :
    HolderOnWith (Real.toNNReal (max L (2 * B))) α f s := by
  refine Holder.holderOnWith_of_norm_le (C := Real.toNNReal (max L (2 * B))) (fun x hx y hy => ?_)
  have hC : ((Real.toNNReal (max L (2 * B)) : NNReal) : ℝ) = max L (2 * B) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hC]
  rcases lt_or_ge (dist x y) 1 with hd | hd
  · exact le_trans (hlocal x hx y hy hd.le)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  · have h1 : (1 : ℝ) ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow hd α.coe_nonneg
    have h2 : 0 ≤ max L (2 * B) := by positivity
    calc ‖f x - f y‖ ≤ 2 * B := hbdd x hx y hy
      _ ≤ max L (2 * B) := le_max_right _ _
      _ = max L (2 * B) * 1 := by ring
      _ ≤ max L (2 * B) * dist x y ^ (α : ℝ) := mul_le_mul_of_nonneg_left h1 h2

/-! ## The main theorem -/

/-- **`St4`: the far-field joint `C^{1,α}` bound.**

Let `u = BS(ω)` slicewise, let `∂ₜu = BS(∂ₜω)` (the Biot–Savart reconstruction commutes with the
time derivative), let `ω` be supported in `B(0,R)` and bounded by `M` on the two-sided window,
let `∂ₜω` be supported in `B(0,R)` too (`Work.StabilityFar.slicesSupported_timeDeriv`) and
bounded by `M₁`, and let `ω`, `∂ₜω` be `α`-Hölder in time on the support ball with constants
`H`, `H₁`.

Then `u.uncurry` is jointly `C^{1,α}` on the far region `{2R+5 < ‖x‖} × [0,T]`.

The hypotheses `hlip`, `hAt`, `hAtu` are the *a priori* far-field estimates for the two blocks:
`D_xu` is Lipschitz in `x` (with the constant `A`, from the second-order Biot–Savart estimate
`Work.StabilityFar.farField_fderiv_sub_le`), and each block is `α`-Hölder in `t` at fixed far `x`
(constants `At`, `Atu`; these follow from the time-Hölder regularity of `ω`, `∂ₜω` on the ball
together with the Biot–Savart linearity `BS(g₁) - BS(g₂) = BS(g₁ - g₂)`). -/
theorem st4_farField_holder
    {α : NNReal} {ω u : R3 → ℝ → R3} {T R M M₁ H H₁ A At Atu : ℝ}
    (hT : 0 < T) (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) ≤ 1)
    (hR : 0 < R) (hM : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁)
    (hA : 0 ≤ A) (hAt : 0 ≤ At) (hAtu : 0 ≤ Atu)
    (hsmooth : ContDiffOn ℝ 1 u.uncurry (Set.univ ×ˢ Set.Ioo (-1) (T + 1)))
    (hbs : IsBiotSavartSlice u ω T) (hbsDt : IsTimeBiotSavartSlice u ω T)
    (hsupp : SlicesSupported ω R T) (hbdd : SlicesBounded ω M T)
    (hbddDt : SlicesBounded (timeDeriv ω) M₁ T) (hmeasDt : SlicesMeasurable (timeDeriv ω) T)
    (hth : TimeHolderOnBall (α : ℝ) ω R T H)
    (hthDt : TimeHolderOnBall (α : ℝ) (timeDeriv ω) R T H₁)
    (hlip : FarDerivLipschitz A (2 * R) T u)
    (hAt : ∀ x : R3, 2 * R < ‖x‖ → ∀ t ∈ window T, ∀ τ ∈ window T,
      ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) x‖ ≤ At * |t - τ| ^ (α : ℝ))
    (hAtu : ∀ x : R3, 2 * R < ‖x‖ → ∀ t ∈ window T, ∀ τ ∈ window T,
      ‖timeDeriv u x t - timeDeriv u x τ‖ ≤ Atu * |t - τ| ^ (α : ℝ)) :
    IsContDiffHolderOn ℝ α u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) := by
  have hT0 : (0 : ℝ) ≤ T := hT.le
  -- the three decay/regularity inputs, in the exact shapes used below
  have hDx : ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (u · t) x‖ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 :=
    fderiv_decay hR hM hbs hbdd hsupp
  have hDt : ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖timeDeriv u x t‖ ≤ (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2 :=
    velocity_decay_timeDeriv hR.le hM₁ hbsDt hbddDt hsupp
  have hLx : ∀ t ∈ Set.Icc 0 T, ∀ x y : R3, 2 * R + 5 < ‖x‖ → ‖x - y‖ ≤ 1 →
      ‖timeDeriv u x t - timeDeriv u y t‖ ≤ 2 ^ 17 * M₁ * ‖x - y‖ :=
    timeDeriv_lipschitz_x hR hM₁ hbsDt hbddDt hmeasDt hsupp
  -- the pointwise bound on the block derivative in the far region
  have hB : ∀ p ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T,
      ‖blockDeriv u p‖ ≤ 2 ^ 17 * M + 1 / 3 * M₁ * R := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hx2 : 2 * R < ‖x‖ := by simp only [st4Radius, mem_farRegion] at hx; linarith
    have hxR : 2 * R ≤ ‖x‖ := hx2.le
    have hxpos : 0 < ‖x‖ := by linarith
    have h1 : 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 ≤ 2 ^ 17 * M := by
      have hxx : (2 * R) ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (by linarith) hxR 3
      have h8 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
      rw [div_le_iff₀ (pow_pos hxpos 3)]
      have hstep : 2 ^ 17 * M * (8 * R ^ 3) ≤ 2 ^ 17 * M * ‖x‖ ^ 3 :=
        mul_le_mul_of_nonneg_left (by rw [← h8]; exact hxx) (by positivity)
      have hpow : (2 : ℝ) ^ 20 = 2 ^ 17 * 8 := by norm_num
      nlinarith [hstep, hpow]
    have h2 : (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2 ≤ 1 / 3 * M₁ * R := by
      have hxx : (2 * R) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by linarith) hxR 2
      have h4 : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
      rw [div_le_iff₀ (pow_pos hxpos 2)]
      have hstep : (1 / 3 * M₁ * R) * (4 * R ^ 2) ≤ (1 / 3 * M₁ * R) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (by rw [← h4]; exact hxx) (by positivity)
      nlinarith [hstep]
    calc ‖blockDeriv u (x, t)‖
        ≤ ‖fderiv ℝ (u · t) x‖ + ‖timeDeriv u x t‖ := norm_blockDeriv_le u x t
      _ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 + (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2 :=
          add_le_add (hDx t ht x hxR) (hDt t ht x hxR)
      _ ≤ 2 ^ 17 * M + 1 / 3 * M₁ * R := add_le_add h1 h2
  -- the pointwise difference bound for the block derivative on close far points
  have hLip : ∀ p ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T,
      ∀ q ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T, dist p q ≤ 1 →
      ‖fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) p
        - fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) q‖
        ≤ (A + 2 ^ 17 * M₁ + At + Atu) * dist p q ^ (α : ℝ) := by
    intro p hp q hq hpq
    obtain ⟨x, t⟩ := p
    obtain ⟨y, τ⟩ := q
    obtain ⟨hx, ht⟩ := hp
    obtain ⟨hy, hτ⟩ := hq
    have hp' : fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) (x, t)
        = blockDeriv u (x, t) :=
      fderivWithin_farStrip_eq_blockDeriv hT hsmooth (p := (x, t)) ⟨hx, ht⟩
    have hq' : fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) (y, τ)
        = blockDeriv u (y, τ) :=
      fderivWithin_farStrip_eq_blockDeriv hT hsmooth (p := (y, τ)) ⟨hy, hτ⟩
    rw [hp', hq']
    have hx2 : 2 * R < ‖x‖ := by simp only [st4Radius, mem_farRegion] at hx; linarith
    have hy2 : 2 * R < ‖y‖ := by simp only [st4Radius, mem_farRegion] at hy; linarith
    have hx25 : 2 * R + 5 < ‖x‖ := hx
    have htw : t ∈ window T := window_of_Icc ht
    have hτw : τ ∈ window T := window_of_Icc hτ
    -- the geometry of the product distance
    have hdist1 : ‖x - y‖ ≤ dist (x, t) (y, τ) := by
      rw [Prod.dist_eq, dist_eq_norm]
      exact le_max_left _ _
    have hdist2 : |t - τ| ≤ dist (x, t) (y, τ) := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_right _ _
    have hxy1 : ‖x - y‖ ≤ 1 := le_trans hdist1 hpq
    have hdist_le : dist (x, t) (y, τ) ≤ dist (x, t) (y, τ) ^ (α : ℝ) :=
      Real.self_le_rpow_of_le_one dist_nonneg hpq hα1
    have hrpow : |t - τ| ^ (α : ℝ) ≤ dist (x, t) (y, τ) ^ (α : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hdist2 hα.le
    have hxyle : ‖x - y‖ ≤ dist (x, t) (y, τ) ^ (α : ℝ) := le_trans hdist1 hdist_le
    -- the two blocks
    have hDxdiff : ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖
        ≤ A * ‖x - y‖ + At * |t - τ| ^ (α : ℝ) := by
      have h1 : ‖fderiv ℝ (u · t) x - fderiv ℝ (u · t) y‖ ≤ A * ‖x - y‖ :=
        hlip t htw x y hx2 hy2
      have h2 : ‖fderiv ℝ (u · t) y - fderiv ℝ (u · τ) y‖ ≤ At * |t - τ| ^ (α : ℝ) :=
        hAt y hy2 t htw τ hτw
      calc ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖
          = ‖(fderiv ℝ (u · t) x - fderiv ℝ (u · t) y)
              + (fderiv ℝ (u · t) y - fderiv ℝ (u · τ) y)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add h1 h2
    have hDtdiff : ‖timeDeriv u x t - timeDeriv u y τ‖
        ≤ 2 ^ 17 * M₁ * ‖x - y‖ + Atu * |t - τ| ^ (α : ℝ) := by
      have h1 : ‖timeDeriv u x t - timeDeriv u y t‖ ≤ 2 ^ 17 * M₁ * ‖x - y‖ :=
        hLx t ht x y hx25 hxy1
      have h2 : ‖timeDeriv u y t - timeDeriv u y τ‖ ≤ Atu * |t - τ| ^ (α : ℝ) :=
        hAtu y hy2 t htw τ hτw
      calc ‖timeDeriv u x t - timeDeriv u y τ‖
          = ‖(timeDeriv u x t - timeDeriv u y t) + (timeDeriv u y t - timeDeriv u y τ)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add h1 h2
    -- combine
    have hcoef1 : 0 ≤ A + 2 ^ 17 * M₁ := by linarith
    have hcoef2 : 0 ≤ At + Atu := by linarith
    calc ‖blockDeriv u (x, t) - blockDeriv u (y, τ)‖
        ≤ ‖fderiv ℝ (u · t) x - fderiv ℝ (u · τ) y‖
            + ‖timeDeriv u x t - timeDeriv u y τ‖ := norm_blockDeriv_sub_le u x y t τ
      _ ≤ (A * ‖x - y‖ + At * |t - τ| ^ (α : ℝ))
            + (2 ^ 17 * M₁ * ‖x - y‖ + Atu * |t - τ| ^ (α : ℝ)) :=
          add_le_add hDxdiff hDtdiff
      _ = (A + 2 ^ 17 * M₁) * ‖x - y‖ + (At + Atu) * |t - τ| ^ (α : ℝ) := by ring
      _ ≤ (A + 2 ^ 17 * M₁) * dist (x, t) (y, τ) ^ (α : ℝ)
            + (At + Atu) * dist (x, t) (y, τ) ^ (α : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hxyle hcoef1)
            (mul_le_mul_of_nonneg_left hrpow hcoef2)
      _ = (A + 2 ^ 17 * M₁ + At + Atu) * dist (x, t) (y, τ) ^ (α : ℝ) := by ring

  refine ⟨?_, ?_, ?_⟩
  · -- `ContDiffOn`
    refine hsmooth.mono (fun p hp => ⟨trivial, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩)
  · -- boundedness of the within-derivative
    rw [IsBoundedFunOn, isBounded_iff_forall_norm_le]
    refine ⟨2 ^ 17 * M + 1 / 3 * M₁ * R, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [fderivWithin_farStrip_eq_blockDeriv hT hsmooth hp]
    exact hB p hp
  · -- the Hölder bound
    have hlip' : ∀ p ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T,
        ∀ q ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T, dist p q ≤ 1 →
        ‖fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) p
          - fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) q‖
          ≤ (A + 2 ^ 17 * M₁ + At + Atu) * dist p q ^ (α : ℝ) := hLip
    have hbdd' : ∀ p ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T,
        ∀ q ∈ farRegion (st4Radius R) ×ˢ Set.Icc 0 T,
        ‖fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) p
          - fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) q‖
          ≤ 2 * (2 ^ 17 * M + 1 / 3 * M₁ * R) := by
      intro p hp q hq
      rw [fderivWithin_farStrip_eq_blockDeriv hT hsmooth hp,
        fderivWithin_farStrip_eq_blockDeriv hT hsmooth hq]
      calc ‖blockDeriv u p - blockDeriv u q‖
          ≤ ‖blockDeriv u p‖ + ‖blockDeriv u q‖ := norm_sub_le _ _
        _ ≤ 2 ^ 17 * M + 1 / 3 * M₁ * R + (2 ^ 17 * M + 1 / 3 * M₁ * R) :=
            add_le_add (hB p hp) (hB q hq)
        _ = 2 * (2 ^ 17 * M + 1 / 3 * M₁ * R) := by ring
    refine ⟨Real.toNNReal (max (A + 2 ^ 17 * M₁ + At + Atu)
      (2 * (2 ^ 17 * M + 1 / 3 * M₁ * R))), ?_⟩
    exact holderOnWith_of_local_holder_bounded (f := fun p =>
        fderivWithin ℝ u.uncurry (farRegion (st4Radius R) ×ˢ Set.Icc 0 T) p)
      (by linarith) (by positivity) hlip' hbdd'

end Work.StabilityFar
