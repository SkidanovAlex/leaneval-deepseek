/-
Copyright: work module for the Elgindi finite-time singularity project.

# `C²` for the first entry of a `D_z`/`D_θ`-tower of continuous functions

The operators of the elliptic estimates of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ`.  The extraction of the limit of a sequence of
solutions produces, on the open quadrant `Q0 = (0,∞) × (0,π/2)`, a family
`F : ℕ → ℕ → ℝ → ℝ → ℝ` of continuous functions (`F c d` for `c + d ≤ 2`) together with the
two *tower relations*

  `∂_z (F c d) = F (c+1) d / z`,   `∂_θ (F c d) = F c (d+1) / sin (2θ)`  (`c + d ≤ 1`),

i.e. `D_z (F c d) = F (c+1) d` and `D_θ (F c d) = F c (d+1)`.

This file proves that under these hypotheses `F 0 0` is `C²` on `Q0` — the regularity input
that the `LimTower` chain of the `EllLimOK` area needs.

The proof goes through the global coordinates `u = log z`, `v = log tan θ`, in which
`D_z = ∂_u` and `D_θ = 2 ∂_v`.  After rescaling the `d`-th `θ`-derivative by `2^{-d}` the
family becomes an honest *partial*-derivative tower on all of `ℝ²`, to which the elementary
lemma `contDiffOn_two_of_partial_tower` below applies; composing back with the smooth map
`(z,θ) ↦ (log z, log tan θ)` gives `C²` on `Q0`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.LocAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The Fréchet derivative from continuous slice derivatives -/

/-- The continuous linear map `ℝ × ℝ →L[ℝ] ℝ` which is the Fréchet derivative of a function
whose slice derivatives are `x` (in the first variable) and `y` (in the second). -/
def cop (x y : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).coprod (ContinuousLinearMap.toSpanSingleton ℝ y)

theorem cop_apply (x y : ℝ) (v : ℝ × ℝ) : cop x y v = v.1 * x + v.2 * y := by
  simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]

/-- The map `c ↦ x ↦ x • c` is continuous. -/
theorem continuous_toSpanSingleton :
    Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ)) := by
  have h : (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c : ℝ → (ℝ →L[ℝ] ℝ))
      = ⇑(ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)) := by
    funext c
    simp [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous

/-- **Slice derivatives give the Fréchet derivative.**  If the two one-variable slices of `φ`
have derivative `a z θ` resp. `b z θ` at every point of the open set `U`, and these slice
derivative functions are continuous on `U`, then `Function.uncurry φ` is differentiable on `U`
with `fderivWithin ℝ (Function.uncurry φ) U p = cop (a p.1 p.2) (b p.1 p.2)`. -/
theorem diffOn_uncurry_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    DifferentiableOn ℝ (Function.uncurry φ) U ∧
      EqOn (fderivWithin ℝ (Function.uncurry φ) U)
        (fun p => cop (a p.1 p.2) (b p.1 p.2)) U := by
  have key : ∀ p ∈ U, HasFDerivAt (Function.uncurry φ) (cop (a p.1 p.2) (b p.1 p.2)) p := by
    intro p hp
    have hmem : U ∈ 𝓝 p := hU.mem_nhds hp
    have h1 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ x v.2)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ)) v) v.1 := by
      filter_upwards [hmem] with v hv
      exact (ha v.1 v.2 hv).hasFDerivAt
    have h2 : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => φ v.1 x)
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) v) v.2 := by
      filter_upwards [hmem] with v hv
      exact (hb v.1 v.2 hv).hasFDerivAt
    have c1 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hca.continuousAt hmem)
    have c2 : ContinuousAt
        (Function.uncurry (fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ))) p :=
      continuous_toSpanSingleton.continuousAt.comp (hcb.continuousAt hmem)
    have h := hasStrictFDerivAt_uncurry_coprod (u := p) (f := φ)
      (f₁ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (a z θ))
      (f₂ := fun z θ => ContinuousLinearMap.toSpanSingleton ℝ (b z θ)) h1 h2 c1 c2
    exact h.hasFDerivAt
  constructor
  · intro p hp; exact (key p hp).differentiableAt.differentiableWithinAt
  · intro p hp
    exact ((key p hp).hasFDerivWithinAt).fderivWithin (hU.uniqueDiffOn p hp)

/-- **Continuous slice derivatives give `C¹`.** -/
theorem contDiffOn_one_of_slices {φ : ℝ → ℝ → ℝ} {a b : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U)
    (ha : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun z' => φ z' θ) (a z θ) z)
    (hb : ∀ z θ, (z, θ) ∈ U → HasDerivAt (fun θ' => φ z θ') (b z θ) θ)
    (hca : ContinuousOn (Function.uncurry a) U) (hcb : ContinuousOn (Function.uncurry b) U) :
    ContDiffOn ℝ 1 (Function.uncurry φ) U := by
  have h := diffOn_uncurry_of_slices hU ha hb hca hcb
  refine contDiffOn_succ_of_fderiv_apply (n := 0) h.1 (fun hω => absurd hω (by simp))
    (fun y => ?_)
  rw [contDiffOn_zero]
  have hcontfun : ContinuousOn
      (fun x : ℝ × ℝ => y.1 * a x.1 x.2 + y.2 * b x.1 x.2) U :=
    (continuousOn_const.mul hca).add (continuousOn_const.mul hcb)
  exact hcontfun.congr fun x hx => by rw [h.2 hx, cop_apply]

/-- **The derivative function `p ↦ cop (a p) (b p)` of two `C^n` functions is `C^n`.** -/
theorem contDiffOn_cop {n : WithTop ℕ∞} {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ → ℝ}
    (ha : ContDiffOn ℝ n a U) (hb : ContDiffOn ℝ n b U) :
    ContDiffOn ℝ n (fun p => cop (a p) (b p)) U := by
  have heq : (fun q : ℝ × ℝ => cop q.1 q.2)
      = fun q : ℝ × ℝ =>
        q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + q.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext q
    apply ContinuousLinearMap.ext
    intro v
    rw [show cop q.1 q.2 v = v.1 * q.1 + v.2 * q.2 from by
      simp [cop, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul]]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) v = v.1 from rfl,
        show (ContinuousLinearMap.snd ℝ ℝ ℝ) v = v.2 from rfl]
    ring
  have hc : ContDiff ℝ n (fun q : ℝ × ℝ => cop q.1 q.2) := by
    rw [heq]
    exact ((contDiff_fst (𝕜 := ℝ)).smul_const _).add ((contDiff_snd (𝕜 := ℝ)).smul_const _)
  have h := hc.comp_contDiffOn (ha.prodMk hb)
  simpa [Function.comp_def] using h

/-! ## The second-order partial tower on an open subset of `ℝ²` -/

/-- **`C²` from a continuous second-order partial tower.**  If `D : ℕ → ℕ → ℝ → ℝ → ℝ` is a
partial-derivative tower on the open set `U` — all `D a b` with `a + b ≤ 2` continuous on `U`
and the slices of `D a b` differentiating to `D (a+1) b` resp. `D a (b+1)` for `a + b ≤ 1` —
then the first entry `D 0 0` is `C²` on `U`. -/
theorem contDiffOn_two_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) :
    ContDiffOn ℝ 2 (Function.uncurry φ) U := by
  have hC1_10 : ContDiffOn ℝ 1 (Function.uncurry (D 1 0)) U :=
    contDiffOn_one_of_slices hU (hsz 1 0 (by norm_num)) (hth 1 0 (by norm_num))
      (hcont 2 0 (by norm_num)) (hcont 1 1 (by norm_num))
  have hC1_01 : ContDiffOn ℝ 1 (Function.uncurry (D 0 1)) U :=
    contDiffOn_one_of_slices hU (hsz 0 1 (by norm_num)) (hth 0 1 (by norm_num))
      (hcont 1 1 (by norm_num)) (hcont 0 2 (by norm_num))
  have hcop : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => cop (D 1 0 p.1 p.2) (D 0 1 p.1 p.2)) U :=
    contDiffOn_cop hC1_10 hC1_01
  have hdiff := diffOn_uncurry_of_slices hU (hsz 0 0 (by norm_num)) (hth 0 0 (by norm_num))
    (hcont 1 0 (by norm_num)) (hcont 0 1 (by norm_num))
  have hstep : ContDiffOn ℝ (1 + 1) (Function.uncurry (D 0 0)) U := by
    refine contDiffOn_succ_of_fderiv_apply (n := 1) hdiff.1 (fun hω => absurd hω (by simp))
      (fun y => ?_)
    refine (hcop.clm_apply (contDiffOn_const (c := y))).congr fun x hx => ?_
    rw [hdiff.2 hx]
  have hφD : Function.uncurry φ = Function.uncurry (D 0 0) := by
    funext p; exact hφ p.1 p.2
  rw [hφD]
  exact hstep

/-! ## The tower in the coordinates `u = log z`, `v = log tan θ` -/

/-- In the coordinates `u = log z`, `v = log tan θ` the operator `D_z` becomes `∂_u` and
`D_θ` becomes `2 ∂_v`; the extra factor `2^{-d}` below turns the `d`-fold `θ`-derivative into
the honest `∂_v^d`. -/
def T (F : ℕ → ℕ → ℝ → ℝ → ℝ) (c d : ℕ) (u v : ℝ) : ℝ :=
  F c d (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ d

/-- The transfer back to the original coordinates: on the open quadrant the tower entry
`T F 0 0` composed with `(z,θ) ↦ (log z, log tan θ)` is `F 0 0`. -/
theorem comp_logLog_T00 (F : ℕ → ℕ → ℝ → ℝ → ℝ) {p : ℝ × ℝ}
    (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Function.uncurry (F 0 0) p
      = ((Function.uncurry (fun u v => T F 0 0 u v)) ∘
          (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2)))) p := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have htanpos : 0 < Real.tan p.2 := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hθπ : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  simp only [Function.comp_apply, Function.uncurry, T]
  rw [Real.exp_log hz, Real.exp_log htanpos, Real.arctan_tan hθπ.1 hθπ.2, pow_zero, div_one]

/-! ## The target lemma -/

theorem LimTower_c2 {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hcont : ∀ (c d : ℕ), c + d ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ContDiffOn ℝ 2 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 := by
  -- the map `(u,v) ↦ (exp u, arctan (exp v))` lands in the open quadrant
  have hmemQ : ∀ p : ℝ × ℝ,
      (Real.exp p.1, Real.arctan (Real.exp p.2)) ∈ Work.FTS.EllipticEst.Q0 := by
    intro p
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
    · rw [Real.arctan_pos]; exact Real.exp_pos p.2
    · exact Real.arctan_lt_pi_div_two _
  have hΦcont : Continuous fun p : ℝ × ℝ => (Real.exp p.1, Real.arctan (Real.exp p.2)) := by
    fun_prop
  -- continuity of every tower entry in the `(u,v)`-coordinates
  have hcontT : ∀ a b : ℕ, a + b ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => T F a b p.1 p.2) Set.univ := by
    intro a b hab
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
      (hcont a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
    simpa only [T] using h1.div_const (2 ^ b)
  -- the `u`-derivative relation
  have hszT : ∀ a b : ℕ, a + b ≤ 1 → ∀ u v : ℝ,
      HasDerivAt (fun u' : ℝ => T F a b u' v) (T F (a + 1) b u v) u := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := hdz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp u (Real.hasDerivAt_exp u)
    have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
        * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    simpa only [T, Function.comp_apply] using h2
  -- the `v`-derivative relation
  have hthT : ∀ a b : ℕ, a + b ≤ 1 → ∀ u v : ℝ,
      HasDerivAt (fun v' : ℝ => T F a b u v') (T F a (b + 1) u v) v := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := hdth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp v (Work.FTS.StrongEps.LocUnif.hasDerivAt_arctan_exp v)
    have hsin : Real.sin (2 * Real.arctan (Real.exp v)) ≠ 0 := by
      rw [show Real.sin (2 * Real.arctan (Real.exp v))
            = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
        have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
        rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
        rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
              * (1 / √(1 + (Real.exp v) ^ 2))
            = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
        rw [Real.sq_sqrt hS.le]]
      positivity
    have hval : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v))
          / Real.sin (2 * Real.arctan (Real.exp v))
          * (Real.sin (2 * Real.arctan (Real.exp v)) / 2)
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
      rw [pow_succ]; ring
    rw [hval2] at h2
    simpa only [T, Function.comp_apply] using h2
  -- the partial tower on `ℝ²` and the transfer back through the smooth coordinate change
  have h2 := contDiffOn_two_of_partial_tower (φ := fun u v => T F 0 0 u v) (D := T F)
    isOpen_univ (fun u v => rfl) hcontT (fun a b hab z θ _ => hszT a b hab z θ)
    (fun a b hab z θ _ => hthT a b hab z θ)
  have hcomp := h2.comp (Work.FTS.StrongEps.LocUnif.contDiffOn_logLog_Q0 2)
    (fun p _ => Set.mem_univ _)
  exact hcomp.congr fun p hp => comp_logLog_T00 F hp

end Work.FTS_EllLimOK
