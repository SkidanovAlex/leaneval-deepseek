/-
Copyright: work module for the Elgindi finite-time singularity project.

# `pthU_slot_alg` — the slot algebra for `∂_θ(Uop α V)`

Target (statement unchanged, see below):

```
∀ k ≥ 2, ∃ C > 0, ∀ α > 0, ∀ V smooth to order k+1 on the open quadrant,
  HkMem α k (∂_θV) → HkMem α k (α D_z∂_θV) →
  HkSq α k (∂_θ(Uop α V)) ≤ C (HkSq α k (∂_θV) + HkSq α k (α D_z∂_θV)).
```

## The mathematics

`Uop α V = -3 V - α z ∂_zV` has coefficients constant in `θ`, so on the open quadrant
`∂_θ(Uop α V) = -3 ∂_θV - α D_z∂_θV` (using Clairaut for the mixed second derivative).
Writing `f := ∂_θV`, `g := D_z∂_θV` and `E := -3f - αg = ∂_θ(Uop α V)`, the whole content is
the *slotwise* estimate

  `(D_z^j D_θ^i E)² ≤ 18 (D_z^j D_θ^i f)² + 2α² (D_z^j D_θ^i g)²`   for `i + j ≤ k`.

This is the elementary `(a+b)² ≤ 2a²+2b²` applied to `D_z^jD_θ^i E = -3 D_z^jD_θ^i f
- α D_z^jD_θ^i g` — **except** that the totalised derivatives of `f` (only `C^k`, since
`V` is only `C^{k+1}`) and of `g` (only `C^{k-1}`) are *junk* at the top orders: the identity
above can genuinely fail there.  What makes the statement true is that the failure is
harmless: at a point where the junk value of `D^n g` is `0` (the function is not
differentiable there), the value of `D^n E` is `0` as well, so the left-hand side is `0`
and the inequality holds trivially.  The precise mechanism (proved below, in the
one-variable form that both the `z`- and the `θ`-direction reduce to):

* at levels `≤ n-1` the exact identity holds as an identity of *functions* (honest
  linearity of the totalised iterate — this only needs `C^i`-smoothness);
* at level `n` one differentiates once more: if the `g`-piece is differentiable at the point,
  the identity holds at the point and AM–GM finishes; if it is not, then (because the
  `f`-piece *is* differentiable, as `f` has more smoothness) the sum is not differentiable
  either, so both junk values are `0` and `0 ≤ 18 (D^n f)²`.

The same one-variable lemma, with the coefficient function `ω = id` and `U = (0,∞)`, gives
the `D_z`-slots; with `ω = sin(2·)` and `U = (0,π/2)`, applied to the `θ`-slices, it gives the
`D_θ`-slots.  The mixed slots `D_z^j D_θ^i` are obtained by applying the `z`-version with
coefficient `id` to the `z`-slices of `D_θ^i f`, `D_θ^i g`, `D_θ^i E` (the level-`i`
`θ`-identity, available for `i ≤ k-1`, provides the pointwise relation of the slices).

Integrating the integrand inequality (the dominating integrand is honest by the two
`HkMem` hypotheses) gives the statement with `C = 18`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS.LocData.HkIntegrand_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkNorm_add_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RegQ

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Part 1 — the one-variable operator `D_ω u = ω · u'` -/

/-- `C^m` for every `m ≤ n` (helper making the `ℕ → WithTop ℕ∞` coercions explicit). -/
theorem contDiffOn_of_le_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {U : Set E} {m n : ℕ}
    (h : ContDiffOn ℝ n f U) (hmn : m ≤ n) : ContDiffOn ℝ m f U :=
  h.of_le (by exact_mod_cast hmn)

namespace SliceD

/-- The one-variable operator `D_ω u = ω · u'` (totalised derivative).  The two instances used
below are `ω = id` (the `z`-direction, `D_z` on slices) and `ω = sin (2·)` (the `θ`-direction,
`D_θ` on slices). -/
def Dop (ω u : ℝ → ℝ) : ℝ → ℝ := fun x => ω x * deriv u x

/-- Iterated `D_ω`. -/
def DopIter (ω : ℝ → ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, u => u
  | n + 1, u => Dop ω (DopIter ω n u)

@[simp] theorem DopIter_zero (ω u : ℝ → ℝ) : DopIter ω 0 u = u := rfl

@[simp] theorem DopIter_succ (ω u : ℝ → ℝ) (n : ℕ) :
    DopIter ω (n + 1) u = Dop ω (DopIter ω n u) := rfl

theorem DopIter_succ_apply (ω u : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    DopIter ω (n + 1) u x = ω x * deriv (DopIter ω n u) x := rfl

/-- Locality of `D_ω^i`: functions agreeing on an open set have the same iterates there. -/
theorem dopIter_congr {ω : ℝ → ℝ} {u v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ x ∈ U, u x = v x) : ∀ m : ℕ, ∀ x ∈ U, DopIter ω m u x = DopIter ω m v x := by
  intro m
  induction m with
  | zero => intro x hx; exact h x hx
  | succ m ih =>
    intro x hx
    rw [DopIter_succ_apply, DopIter_succ_apply]
    congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih y hy)

/-- `D_ω` drops one order of differentiability. -/
theorem contDiffOn_dop {ω u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hω : ContDiffOn ℝ n ω U) (hu : ContDiffOn ℝ (n + 1 : ℕ) u U) :
    ContDiffOn ℝ n (Dop ω u) U := by
  have hderivWithin : ContDiffOn ℝ n (derivWithin u U) U :=
    hu.derivWithin hU.uniqueDiffOn (m := (n : WithTop ℕ∞)) (by simp)
  have hderiv : ContDiffOn ℝ n (deriv u) U :=
    hderivWithin.congr (fun x hx => (derivWithin_of_isOpen hU hx).symm)
  refine (hω.mul hderiv).congr (fun x _ => ?_)
  rfl

/-- `D_ω^i` drops `i` orders of differentiability. -/
theorem contDiffOn_dopIter {ω u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hω : ContDiffOn ℝ n ω U) (hu : ContDiffOn ℝ n u U) :
    ∀ m ≤ n, ContDiffOn ℝ (n - m : ℕ) (DopIter ω m u) U := by
  intro m
  induction m with
  | zero => intro _; simpa using hu
  | succ m ih =>
    intro hm
    have hm' : m ≤ n := by omega
    have h1 : ContDiffOn ℝ (n - m : ℕ) (DopIter ω m u) U := ih hm'
    have h2 : ContDiffOn ℝ (n - m - 1 + 1 : ℕ) (DopIter ω m u) U := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n - m)]; exact h1
    have h3 : ContDiffOn ℝ (n - m - 1 : ℕ) (Dop ω (DopIter ω m u)) U :=
      contDiffOn_dop hU (contDiffOn_of_le_nat hω (by omega)) h2
    have heq : n - (m + 1) = n - m - 1 := by omega
    rw [heq, DopIter_succ]
    exact h3

/-- Differentiability form of `contDiffOn_dopIter`: for `m < n` the iterate `D_ω^m u` is
differentiable on `U`. -/
theorem differentiableOn_dopIter {ω u : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hω : ContDiffOn ℝ n ω U) (hu : ContDiffOn ℝ n u U) {m : ℕ} (hm : m < n) :
    DifferentiableOn ℝ (DopIter ω m u) U :=
  (contDiffOn_of_le_nat (contDiffOn_dopIter hU hω hu m (le_of_lt hm))
    (by omega : 1 ≤ n - m)).differentiableOn (by simp)

/-- **Honest linearity of `D_ω^i`.**  On an open set `U`, if `u` and `w` are `C^m` then the
totalised iterate `D_ω^i` of a linear combination is the corresponding linear combination of
the iterates, for every `i ≤ m`. -/
theorem dopIter_lin {ω u w : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {m : ℕ}
    (hω : ContDiffOn ℝ m ω U) (hu : ContDiffOn ℝ m u U) (hw : ContDiffOn ℝ m w U)
    (a b : ℝ) :
    ∀ i ≤ m, ∀ x ∈ U,
      DopIter ω i (fun x => a * u x + b * w x) x
        = a * DopIter ω i u x + b * DopIter ω i w x := by
  intro i
  induction i with
  | zero => intro _ x hx; simp
  | succ i ih =>
    intro hi x hx
    have hi' : i ≤ m := by omega
    have hident : ∀ y ∈ U, DopIter ω i (fun x => a * u x + b * w x) y
        = a * DopIter ω i u y + b * DopIter ω i w y := ih hi'
    have hUi : ContDiffOn ℝ 1 (DopIter ω i u) U :=
      contDiffOn_of_le_nat (contDiffOn_dopIter hU hω hu i (by omega : i ≤ m))
        (by omega : 1 ≤ m - i)
    have hWi : ContDiffOn ℝ 1 (DopIter ω i w) U :=
      contDiffOn_of_le_nat (contDiffOn_dopIter hU hω hw i (by omega : i ≤ m))
        (by omega : 1 ≤ m - i)
    have hud : DifferentiableAt ℝ (DopIter ω i u) x :=
      (hUi.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hwd : DifferentiableAt ℝ (DopIter ω i w) x :=
      (hWi.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    rw [DopIter_succ_apply, DopIter_succ_apply, DopIter_succ_apply]
    have hcongr : deriv (DopIter ω i (fun x => a * u x + b * w x)) x
        = deriv (fun y => a * DopIter ω i u y + b * DopIter ω i w y) x := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hident y hy
    rw [hcongr]
    have hsplit : (fun y : ℝ => a * DopIter ω i u y + b * DopIter ω i w y)
        = (fun y : ℝ => a * DopIter ω i u y) + (fun y : ℝ => b * DopIter ω i w y) := by
      funext y; rfl
    rw [hsplit, deriv_add (hud.const_mul a) (hwd.const_mul b),
      deriv_const_mul a hud, deriv_const_mul b hwd]
    ring

/-- **The slot inequality in one variable.**  If `v = a·u + b·w` on the open set `U`, `u` is
`C^n` and `w` is `C^{n-1}`, then for every `i ≤ n`

  `(D_ω^i v x)² ≤ 2a² (D_ω^i u x)² + 2b² (D_ω^i w x)²`   on `U`.

This is the `(a+b)² ≤ 2a²+2b²` estimate for the *totalised* iterates, and it is the reason the
statement is true although the iterated derivatives of `w` are junk at the top order: where
`D_ω^{n-1}w` is not differentiable the junk value `D_ω^n w = 0` and, since `D_ω^{n-1}u` *is*
differentiable (one more order of smoothness of `u`), also `D_ω^n v = 0`. -/
theorem dopIter_sq_le {ω u w v : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {n : ℕ}
    (hω : ContDiffOn ℝ n ω U) (hu : ContDiffOn ℝ n u U) (hw : ContDiffOn ℝ (n - 1 : ℕ) w U)
    (a b : ℝ) (hv : ∀ x ∈ U, v x = a * u x + b * w x) :
    ∀ i ≤ n, ∀ x ∈ U,
      (DopIter ω i v x) ^ 2 ≤ 2 * a ^ 2 * (DopIter ω i u x) ^ 2
        + 2 * b ^ 2 * (DopIter ω i w x) ^ 2 := by
  intro i hi x hx
  rcases lt_or_eq_of_le hi with hlt | heq
  · -- `i ≤ n - 1`: the exact identity holds at this level
    have hu' : ContDiffOn ℝ (n - 1 : ℕ) u U := contDiffOn_of_le_nat hu (by omega)
    have hω' : ContDiffOn ℝ (n - 1 : ℕ) ω U := contDiffOn_of_le_nat hω (by omega)
    have hcongr : DopIter ω i v x
        = DopIter ω i (fun x => a * u x + b * w x) x :=
      dopIter_congr hU hv i x hx
    have hlin := dopIter_lin hU hω' hu' hw a b i (by omega : i ≤ n - 1) x hx
    rw [hcongr, hlin]
    nlinarith [sq_nonneg (a * DopIter ω i u x - b * DopIter ω i w x)]
  · -- `i = n`
    rw [heq]
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`: the level-`0` inequality is exactly `hv` and AM–GM
      rw [hn0]
      simp only [DopIter_zero]
      rw [hv x hx]
      nlinarith [sq_nonneg (a * u x - b * w x)]
    · -- top level: differentiate once more and split on differentiability of the `w`-piece
      have hident : ∀ y ∈ U, DopIter ω (n - 1) v y
          = a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y := by
        intro y hy
        have hc : DopIter ω (n - 1) v y
            = DopIter ω (n - 1) (fun x => a * u x + b * w x) y :=
          dopIter_congr hU hv (n - 1) y hy
        have hl := dopIter_lin hU (contDiffOn_of_le_nat hω (by omega : n - 1 ≤ n))
          (contDiffOn_of_le_nat hu (by omega : n - 1 ≤ n)) hw a b (n - 1) le_rfl y hy
        rw [hc, hl]
      have hsm : (fun y => DopIter ω (n - 1) v y) =ᶠ[𝓝 x]
          (fun y => a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hident y hy
      have hud : DifferentiableAt ℝ (DopIter ω (n - 1) u) x :=
        (differentiableOn_dopIter hU hω hu (by omega : n - 1 < n) x hx).differentiableAt
          (hU.mem_nhds hx)
      by_cases hb0 : b = 0
      · -- `b = 0`: `v = a·u` on `U`, so the claim is immediate
        have hlin0 : DopIter ω n v x = a * DopIter ω n u x := by
          have h1 : DopIter ω n v x
              = DopIter ω n (fun x => a * u x) x :=
            dopIter_congr hU (fun y hy => by rw [hv y hy, hb0]; ring) n x hx
          have h2 : DopIter ω n (fun x => a * u x) x = a * DopIter ω n u x := by
            have h3 : (fun x : ℝ => a * u x) = fun x : ℝ => a * u x + (0 : ℝ) * u x := by
              funext x; ring
            rw [h3, dopIter_lin hU hω hu hu a 0 n le_rfl x hx]
            ring
          rw [h1, h2]
        rw [hlin0]
        nlinarith [sq_nonneg (DopIter ω n u x)]
      by_cases hwd : DifferentiableAt ℝ (DopIter ω (n - 1) w) x
      · -- honest case: the identity holds at the point
        have hderiv : deriv (DopIter ω (n - 1) v) x
            = a * deriv (DopIter ω (n - 1) u) x + b * deriv (DopIter ω (n - 1) w) x := by
          rw [Filter.EventuallyEq.deriv_eq hsm]
          have hsplit : (fun y : ℝ => a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y)
              = (fun y : ℝ => a * DopIter ω (n - 1) u y)
                + fun y : ℝ => b * DopIter ω (n - 1) w y := by
            funext y; rfl
          rw [hsplit, deriv_add (hud.const_mul a) (hwd.const_mul b),
            deriv_const_mul a hud, deriv_const_mul b hwd]
        have hvt : DopIter ω n v x = ω x * deriv (DopIter ω (n - 1) v) x := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega]
          rw [DopIter_succ_apply]
        have hut : DopIter ω n u x = ω x * deriv (DopIter ω (n - 1) u) x := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega]
          rw [DopIter_succ_apply]
        have hwt : DopIter ω n w x = ω x * deriv (DopIter ω (n - 1) w) x := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega]
          rw [DopIter_succ_apply]
        rw [hvt, hut, hwt, hderiv]
        nlinarith [sq_nonneg (a * (ω x * deriv (DopIter ω (n - 1) u) x)
          - b * (ω x * deriv (DopIter ω (n - 1) w) x))]
      · -- junk case: both top values vanish
        have hsum : ¬ DifferentiableAt ℝ
            (fun y => a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y) x := by
          intro hcon
          have hdiff : DifferentiableAt ℝ
              ((fun y : ℝ => a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y)
                - fun y : ℝ => a * DopIter ω (n - 1) u y) x :=
            hcon.sub (hud.const_mul a)
          have hEq : ((fun y : ℝ => a * DopIter ω (n - 1) u y + b * DopIter ω (n - 1) w y)
                - fun y : ℝ => a * DopIter ω (n - 1) u y)
              = fun y : ℝ => b * DopIter ω (n - 1) w y := by
            funext y; simp only [Pi.sub_apply]; ring
          rw [hEq] at hdiff
          have h3 := hdiff.const_mul b⁻¹
          have h4 : (fun y : ℝ => b⁻¹ * (b * DopIter ω (n - 1) w y))
              = DopIter ω (n - 1) w := by
            funext y; rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
          rw [h4] at h3
          exact hwd h3
        have hnotv : ¬ DifferentiableAt ℝ (fun y => DopIter ω (n - 1) v y) x := by
          intro hcon
          exact hsum ((Filter.EventuallyEq.differentiableAt_iff hsm).mp hcon)
        have hv0 : DopIter ω n v x = 0 := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega]
          rw [DopIter_succ_apply, deriv_zero_of_not_differentiableAt hnotv, mul_zero]
        have hw0 : DopIter ω n w x = 0 := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega]
          rw [DopIter_succ_apply, deriv_zero_of_not_differentiableAt hwd, mul_zero]
        rw [hv0, hw0]
        nlinarith [sq_nonneg (DopIter ω n u x)]

end SliceD

/-! ## Part 2 — the two-variable calculus on the open quadrant -/

namespace Q2

/-- The open quadrant `(0,∞) × (0,π/2)`, the domain of the smoothness hypothesis. -/
abbrev Qd : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

theorem isOpen_Qd : IsOpen Qd := Work.FTS.EllipticEst.isOpen_Q0

/-- The coefficient of the `z`-direction operator on `z`-slices. -/
def wZ : ℝ → ℝ := fun z => z

/-- The coefficient of the `θ`-direction operator on `θ`-slices. -/
def wT : ℝ → ℝ := fun θ => Real.sin (2 * θ)

theorem contDiffOn_wZ {U : Set ℝ} (n : ℕ) : ContDiffOn ℝ n wZ U := by
  have h : wZ = fun z : ℝ => z := rfl
  rw [h]
  exact contDiffOn_id

theorem contDiffOn_wT {U : Set ℝ} (n : ℕ) : ContDiffOn ℝ n wT U := by
  have h : wT = fun θ : ℝ => Real.sin (2 * θ) := rfl
  rw [h]
  exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn.of_le le_top

/-! ### Finite-order smoothness of the partial derivatives -/

/-- `∂_θ` drops one order of differentiability. -/
theorem contDiffOn_pth_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) U := by
  have hchain : ∀ p ∈ U, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hU.uniqueDiffOn (by simp)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hU hp).symm)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) U := by
    simpa using hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  simpa only [Function.uncurry] using hchain p hp

/-- `∂_z` drops one order of differentiability. -/
theorem contDiffOn_pz_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) U := by
  have hchain : ∀ p ∈ U, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) U := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hU.uniqueDiffOn (by simp)
    exact h'.congr (fun p hp => (fderivWithin_of_isOpen hU hp).symm)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) U := by
    simpa using hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  simpa only [Function.uncurry] using hchain p hp

/-- `D_z = z ∂_z` drops one order of differentiability. -/
theorem contDiffOn_Dz_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) U := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (contDiffOn_fst.mul (contDiffOn_pz_fin hU h)).congr (fun p _ => rfl)

/-- `D_θ = sin 2θ · ∂_θ` drops one order of differentiability. -/
theorem contDiffOn_Dth_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) U := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) U :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn.of_le le_top
  exact (hsin.mul (contDiffOn_pth_fin hU h)).congr (fun p _ => rfl)

/-- `D_θ^i` drops `i` orders of differentiability. -/
theorem contDiffOn_DthIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) U) :
    ∀ i ≤ n, ContDiffOn ℝ (n - i : ℕ) (Function.uncurry (Work.Spaces.DthIter i G)) U := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := by omega
    have h1 : ContDiffOn ℝ (n - i : ℕ) (Function.uncurry (Work.Spaces.DthIter i G)) U := ih hi'
    have h2 : ContDiffOn ℝ (n - i - 1 + 1 : ℕ)
        (Function.uncurry (Work.Spaces.DthIter i G)) U := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n - i)]; exact h1
    have h3 : ContDiffOn ℝ (n - i - 1 : ℕ)
        (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DthIter i G))) U :=
      contDiffOn_Dth_fin hU h2
    have heq : n - (i + 1) = n - i - 1 := by omega
    rw [heq, Work.Spaces.DthIter_succ]
    exact h3

/-- `D_z^j` drops `j` orders of differentiability. -/
theorem contDiffOn_DzIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry G) U) :
    ∀ j ≤ n, ContDiffOn ℝ (n - j : ℕ) (Function.uncurry (Work.Spaces.DzIter j G)) U := by
  intro j
  induction j with
  | zero => intro _; simpa using h
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := by omega
    have h1 : ContDiffOn ℝ (n - j : ℕ) (Function.uncurry (Work.Spaces.DzIter j G)) U := ih hj'
    have h2 : ContDiffOn ℝ (n - j - 1 + 1 : ℕ)
        (Function.uncurry (Work.Spaces.DzIter j G)) U := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n - j)]; exact h1
    have h3 : ContDiffOn ℝ (n - j - 1 : ℕ)
        (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter j G))) U :=
      contDiffOn_Dz_fin hU h2
    have heq : n - (j + 1) = n - j - 1 := by omega
    rw [heq, Work.Spaces.DzIter_succ]
    exact h3

/-! ### Slices -/

/-- The `z`-slice of a function smooth to finite order on a product of sets. -/
theorem contDiffOn_slice_z_fin {G : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {θ : ℝ} (hθ : θ ∈ t) :
    ContDiffOn ℝ n (fun z => G z θ) s :=
  (hG.comp (((contDiffOn_id : ContDiffOn ℝ n (fun z : ℝ => z) s)).prodMk
    (contDiffOn_const (c := θ))) (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)

/-- The `θ`-slice of a function smooth to finite order on a product of sets. -/
theorem contDiffOn_slice_θ_fin {G : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (hG : ContDiffOn ℝ n (Function.uncurry G) (s ×ˢ t)) {z : ℝ} (hz : z ∈ s) :
    ContDiffOn ℝ n (fun θ => G z θ) t :=
  (hG.comp ((contDiffOn_const (c := z)).prodMk
    ((contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) t))) (fun θ hθ => ⟨hz, hθ⟩)).congr
    (fun θ _ => rfl)

/-! ### The `D`-iterates on slices -/

/-- The `D_z`-iterates act on the `z`-slices through the one-variable operator `SliceD.Dop wZ`. -/
theorem DzIter_slice_eq (X : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter j X z θ = SliceD.DopIter wZ j (fun z' => X z' θ) z := by
  induction j generalizing z with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, SliceD.DopIter_succ]
      simp only [Work.Spaces.Dz, Work.Spaces.pz, SliceD.Dop, wZ]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun z' => ih z')

/-- The `D_θ`-iterates act on the `θ`-slices through the one-variable operator `SliceD.Dop wT`. -/
theorem DthIter_slice_eq (X : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i X z θ = SliceD.DopIter wT i (fun θ' => X z θ') θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, SliceD.DopIter_succ]
      simp only [Work.Spaces.Dth, Work.Spaces.pth, SliceD.Dop, wT]
      congr 1
      exact Filter.EventuallyEq.deriv_eq (Eventually.of_forall fun θ' => ih θ')

/-! ### The `θ`-identity at levels `≤ k-1` -/

/-- **The `θ`-identity on the open quadrant.**  For `i ≤ k-1`,

  `D_θ^i E = -3 D_θ^i f - α D_θ^i g`   on `(0,∞) × (0,π/2)`,

where `E = -3f - αg` pointwise.  It is the honest linearity of `D_θ^i` for `C^i` data, applied
to the `θ`-slices. -/
theorem DthIter_lin_slice {E f g : ℝ → ℝ → ℝ} {k : ℕ} {α : ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = -3 * f z θ - α * g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) Qd)
    (hg : ContDiffOn ℝ (k - 1 : ℕ) (Function.uncurry g) Qd)
    {i : ℕ} (hi : i ≤ k - 1) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i E z θ
        = -3 * Work.Spaces.DthIter i f z θ - α * Work.Spaces.DthIter i g z θ := by
  intro z θ hz hθ0 hθ1
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
  have huf : ContDiffOn ℝ i (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_of_le_nat (contDiffOn_slice_θ_fin hf hzmem) (by omega)
  have hug : ContDiffOn ℝ i (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_of_le_nat (contDiffOn_slice_θ_fin hg hzmem) (by omega)
  have hv : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      E z θ' = (-3 : ℝ) * f z θ' + (-α) * g z θ' := by
    intro θ' hθ'
    rw [hE z θ' hz hθ'.1 hθ'.2]; ring
  rw [DthIter_slice_eq E i z θ, DthIter_slice_eq f i z θ, DthIter_slice_eq g i z θ]
  rw [SliceD.dopIter_congr hU hv i θ hmem]
  rw [SliceD.dopIter_lin hU (contDiffOn_wT i) huf hug (-3) (-α) i le_rfl θ hmem]
  ring

/-! ### The slot inequality -/

/-- **The pointwise slot estimate.**  For `i + j ≤ k` and `(z,θ)` in the open quadrant,

  `(D_z^j D_θ^i E)² ≤ 18 (D_z^j D_θ^i f)² + 2α² (D_z^j D_θ^i g)²`.

For `j = 0` this is the one-variable slot lemma in the `θ`-direction (`ω = sin 2·`), applied to
the `θ`-slices; for `j ≥ 1` (so that `i ≤ k-1` and the `θ`-identity is available) it is the same
lemma in the `z`-direction (`ω = id`) applied to the `z`-slices of the `D_θ^i`'s. -/
theorem slot_sq_le {E f g : ℝ → ℝ → ℝ} {k : ℕ} {α : ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = -3 * f z θ - α * g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) Qd)
    (hg : ContDiffOn ℝ (k - 1 : ℕ) (Function.uncurry g) Qd)
    {i j : ℕ} (hij : i + j ≤ k) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ) ^ 2
      ≤ 18 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ) ^ 2
        + 2 * α ^ 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- `j = 0`: the `θ`-direction
    rw [hj0]
    simp only [Work.Spaces.DzIter_zero]
    have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
    have huf : ContDiffOn ℝ i (fun θ' => f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_of_le_nat (contDiffOn_slice_θ_fin hf hzmem) (by omega)
    have hug : ContDiffOn ℝ (i - 1 : ℕ) (fun θ' => g z θ') (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_of_le_nat (contDiffOn_slice_θ_fin hg hzmem) (by omega)
    have hv : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        E z θ' = (-3 : ℝ) * f z θ' + (-α) * g z θ' := by
      intro θ' hθ'
      rw [hE z θ' hz hθ'.1 hθ'.2]; ring
    have key := SliceD.dopIter_sq_le (ω := wT) (U := Set.Ioo (0 : ℝ) (Real.pi / 2)) hU
      (contDiffOn_wT i) huf hug (-3) (-α) hv i le_rfl θ hmem
    rw [← DthIter_slice_eq E i z θ, ← DthIter_slice_eq f i z θ,
      ← DthIter_slice_eq g i z θ] at key
    nlinarith [key]
  · -- `j ≥ 1`, hence `i ≤ k - 1` and the `θ`-identity is available
    have hi : i ≤ k - 1 := by omega
    have hid := DthIter_lin_slice hE hf hg hi
    have hU : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
    have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have huf : ContDiffOn ℝ j (fun z' => Work.Spaces.DthIter i f z' θ) (Set.Ioi 0) :=
      contDiffOn_of_le_nat
        (contDiffOn_slice_z_fin (contDiffOn_DthIter_fin isOpen_Qd hf i (by omega)) hθmem)
        (by omega)
    have hug : ContDiffOn ℝ (j - 1 : ℕ)
        (fun z' => Work.Spaces.DthIter i g z' θ) (Set.Ioi 0) :=
      contDiffOn_of_le_nat
        (contDiffOn_slice_z_fin (contDiffOn_DthIter_fin isOpen_Qd hg i (by omega)) hθmem)
        (by omega)
    have hv : ∀ z' ∈ Set.Ioi (0 : ℝ),
        Work.Spaces.DthIter i E z' θ = (-3 : ℝ) * Work.Spaces.DthIter i f z' θ
          + (-α) * Work.Spaces.DthIter i g z' θ := by
      intro z' hz'
      rw [hid z' θ hz' hθ0 hθ1]; ring
    have key := SliceD.dopIter_sq_le (ω := wZ) (U := Set.Ioi (0 : ℝ)) hU
      (contDiffOn_wZ j) huf hug (-3) (-α) hv j le_rfl z hzmem
    rw [← DzIter_slice_eq (Work.Spaces.DthIter i E) j z θ,
      ← DzIter_slice_eq (Work.Spaces.DthIter i f) j z θ,
      ← DzIter_slice_eq (Work.Spaces.DthIter i g) j z θ] at key
    nlinarith [key]

end Q2

/-! ## Part 3 — the integrand estimate and the assembly -/

/-- Constants: `deriv` is homogeneous under multiplication by a constant, unconditionally
(no differentiability is needed: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, and both sides are `0`). -/
theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-- **The linearity of the iterated operators.**  Every operator of the `ℋ^k`-calculus
(`D_z^i`, `D_θ^i`, `D_z^jD_θ^i`) commutes with multiplication by a constant, unconditionally. -/
theorem DzIter_const_mul (j : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.DzIter j X z θ := by
  induction j with
  | zero => funext z θ; simp
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => c * Work.Spaces.DzIter j X z' θ) z
        = c * (z * deriv (fun z' => Work.Spaces.DzIter j X z' θ) z)
      rw [deriv_const_mul_uncond]
      ring

theorem DthIter_const_mul (i : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.DthIter i X z θ := by
  induction i with
  | zero => funext z θ; simp
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => c * Work.Spaces.DthIter i X z θ') θ
        = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i X z θ') θ)
      rw [deriv_const_mul_uncond]
      ring

theorem mixed_const_mul (j i : ℕ) (c : ℝ) (X : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * X z θ)
      = fun z θ => c * Work.Spaces.mixed j i X z θ := by
  funext z θ
  simp only [Work.Spaces.mixed]
  rw [DthIter_const_mul i c X]
  exact congrFun (congrFun (DzIter_const_mul j c (Work.Spaces.DthIter i X)) z) θ

/-- The sum identity `∑ (c·f + d·g) = c·∑f + d·∑g`. -/
theorem sum_mul_add {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (c d : ℝ) :
    (∑ i ∈ s, (c * f i + d * g i)) = c * (∑ i ∈ s, f i) + d * (∑ i ∈ s, g i) := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The iterated version of `sum_mul_add`. -/
theorem sum_sum_mul_add {ι : Type*} (s : Finset ι) (f g : ι → ι → ℝ) (c d : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (c * f i j + d * g i j))
      = c * (∑ i ∈ s, ∑ j ∈ s, f i j) + d * (∑ i ∈ s, ∑ j ∈ s, g i j) := by
  have h1 : ∀ i, (∑ j ∈ s, (c * f i j + d * g i j))
      = c * (∑ j ∈ s, f i j) + d * (∑ j ∈ s, g i j) := fun i => sum_mul_add s (f i) (g i) c d
  simp only [h1]
  exact sum_mul_add s (fun i => ∑ j ∈ s, f i j) (fun i => ∑ j ∈ s, g i j) c d

/-- At `z = 0` the weighted `ℋ^k`-integrand vanishes (the radial weight is `0`). -/
theorem HkIntegrand_zero_z_fts (α : ℝ) (k : ℕ) (X : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k X 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i X 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show Work.Spaces.w 0 = 0 from by simp [Work.Spaces.w], zero_div, mul_zero,
      zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i X 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with _hc
    · rw [show Work.Spaces.Wt α 0 θ = 0 from by simp [Work.Spaces.Wt, Work.Spaces.w],
        mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- At `sin (2θ) = 0` the weighted `ℋ^k`-integrand vanishes. -/
theorem HkIntegrand_zero_sin_fts (α : ℝ) (k : ℕ) (X : ℝ → ℝ → ℝ) {θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) (z : ℝ) :
    Work.Spaces.HkIntegrand α k X z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i X z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i X z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · have hm : Work.Spaces.mixed j i X z θ = 0 := by
        rw [Work.Spaces.mixed]
        exact Work.Spaces.DzIter_eq_zero_of_slice_zero
          (Work.Spaces.DthIter_eq_zero_of_sin hs i hc.1) j z
      rw [hm, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- **The pointwise integrand estimate.**  For `E = -3f - αg` pointwise on the open quadrant,
`f` of class `C^k` and `g` of class `C^{k-1}` there,

  `HkIntegrand α k E ≤ 18 HkIntegrand α k f + 2 HkIntegrand α k (α • g)`

on `Iz × Iθ`.  This is the slot estimate `slot_sq_le` assembled over the finitely many slots of
the integrand. -/
theorem HkIntegrand_slot_le (α : ℝ) (k : ℕ) {E f g : ℝ → ℝ → ℝ}
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = -3 * f z θ - α * g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) Q2.Qd)
    (hg : ContDiffOn ℝ (k - 1 : ℕ) (Function.uncurry g) Q2.Qd) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k E z θ
        ≤ 18 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k (fun z θ => α * g z θ) z θ := by
  intro z hz θ hθ
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_zero_z_fts, HkIntegrand_zero_z_fts, HkIntegrand_zero_z_fts]
    norm_num
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_zero_sin_fts α k E hs z, HkIntegrand_zero_sin_fts α k f hs z,
      HkIntegrand_zero_sin_fts α k (fun z θ => α * g z θ) hs z]
    norm_num
  · have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := Set.mem_Icc.mp hθ
    have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h' | h'
      · exact absurd (by rw [← h']; simp) hs
      · exact h'
    have hθ1 : θ < Real.pi / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h' | h'
      · exact h'
      · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
          Real.sin_pi]) hs
    -- the slot estimate on the individual slots
    have hslot : ∀ i j : ℕ, i + j ≤ k →
        (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ) ^ 2
          ≤ 18 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ) ^ 2
            + 2 * (Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => α * g z θ))
                z θ) ^ 2 := by
      intro i j hij
      have hb := Q2.slot_sq_le (α := α) (k := k) hE hf hg hij hzpos hθ0 hθ1
      have hcm : Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => α * g z θ)) z θ
          = α * Work.Spaces.DzIter j (Work.Spaces.DthIter i g) z θ := by
        rw [DthIter_const_mul i α g]
        exact congrFun (congrFun (DzIter_const_mul j α (Work.Spaces.DthIter i g)) z) θ
      rw [hcm]
      nlinarith [hb]
    simp only [Work.Spaces.HkIntegrand, Work.Spaces.mixed]
    set ρ : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hρdef
    set Wtα : ℝ := Work.Spaces.Wt α z θ with hWtdef
    have hZle : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i E z θ * ρ) ^ 2)
        ≤ 18 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i (fun z θ => α * g z θ) z θ * ρ) ^ 2) := by
      calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i E z θ * ρ) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1),
              (18 * (Work.Spaces.DzIter i f z θ * ρ) ^ 2
                + 2 * (Work.Spaces.DzIter i (fun z θ => α * g z θ) z θ * ρ) ^ 2) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hb := hslot 0 i (by omega)
            simp only [Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero, Nat.zero_add] at hb
            rw [mul_pow, mul_pow, mul_pow]
            nlinarith [hb, sq_nonneg ρ]
        _ = 18 * (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * ρ) ^ 2)
              + 2 * (∑ i ∈ Finset.range (k + 1),
                  (Work.Spaces.DzIter i (fun z θ => α * g z θ) z θ * ρ) ^ 2) :=
            sum_mul_add _ _ _ 18 2
    have hMle : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ * Wtα) ^ 2 else 0))
        ≤ 18 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j
                (Work.Spaces.DthIter i (fun z θ => α * g z θ)) z θ * Wtα) ^ 2 else 0)) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.DzIter j (Work.Spaces.DthIter i E) z θ * Wtα) ^ 2 else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (18 * (if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2
                  else 0)
                + 2 * (if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.DzIter j
                    (Work.Spaces.DthIter i (fun z θ => α * g z θ)) z θ * Wtα) ^ 2
                  else 0)) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos hc, if_pos hc, if_pos hc]
              have hb := hslot i j hc.2
              nlinarith [hb, sq_nonneg Wtα]
            · rw [if_neg hc, if_neg hc, if_neg hc]; norm_num
        _ = 18 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ * Wtα) ^ 2 else 0))
            + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.DzIter j
                  (Work.Spaces.DthIter i (fun z θ => α * g z θ)) z θ * Wtα) ^ 2 else 0)) :=
            sum_sum_mul_add _ _ _ 18 2
    linarith [hZle, hMle]

/-- **The `HkSq` estimate.**  Integrating the pointwise integrand estimate against the honest
`HkMem` certificates of the two summands. -/
theorem HkSq_slot_le (α : ℝ) (k : ℕ) {E f g : ℝ → ℝ → ℝ} (hα : 0 ≤ α)
    (hE : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → E z θ = -3 * f z θ - α * g z θ)
    (hf : ContDiffOn ℝ k (Function.uncurry f) Q2.Qd)
    (hg : ContDiffOn ℝ (k - 1 : ℕ) (Function.uncurry g) Q2.Qd)
    (hmf : Work.Spaces.HkMem α k f)
    (hmG : Work.Spaces.HkMem α k (fun z θ => α * g z θ)) :
    Work.Spaces.HkSq α k E ≤ 18 * Work.Spaces.HkSq α k f
      + 2 * Work.Spaces.HkSq α k (fun z θ => α * g z θ) := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k E z θ)
        ≤ 18 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (fun z θ => α * g z θ) z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k E z θ)
      (g := fun θ => 18 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k (fun z θ => α * g z θ) z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k E z θ)
      (((hmf.1 z hz).const_mul 18).add ((hmG.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        fun θ hθ => HkIntegrand_slot_le α k hE hf hg z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 18)
          ((hmG.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k E z θ)
    (g := fun z => 18 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => α * g z θ) z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k E z θ)
    ((hmf.2.const_mul 18).add (hmG.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  refine houter.trans_eq ?_
  rw [MeasureTheory.integral_add (hmf.2.const_mul 18) (hmG.2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The pointwise identity `∂_θ(Uop α V) = -3 ∂_θV - α D_z∂_θV` on the open quadrant. -/
theorem pth_Uop_eq (α : ℝ) {V : ℝ → ℝ → ℝ}
    (hV2 : ContDiffOn ℝ 2 (Function.uncurry V) Q2.Qd) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.FTS.EllipticEst.Uop α V) z θ
        = -3 * Work.Spaces.pth V z θ - α * Work.Spaces.Dz (Work.Spaces.pth V) z θ := by
  intro z θ hz hθ0 hθ1
  have hmem : (z, θ) ∈ Q2.Qd := ⟨hz, hθ0, hθ1⟩
  have hct : ContDiffAt ℝ 2 (Function.uncurry V) (z, θ) :=
    hV2.contDiffAt (Q2.isOpen_Qd.mem_nhds hmem)
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hzmem : z ∈ Set.Ioi (0 : ℝ) := hz
  have hslice : DifferentiableAt ℝ (fun θ' => V z θ') θ :=
    ((Q2.contDiffOn_slice_θ_fin hV2 hzmem).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθmem)
  have hslicepz : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz V z θ') θ :=
    ((Q2.contDiffOn_slice_θ_fin (Q2.contDiffOn_pz_fin Q2.isOpen_Qd hV2) hzmem).differentiableOn
      (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθmem)
  have hUop : Work.Spaces.pth (Work.FTS.EllipticEst.Uop α V) z θ
      = -3 * Work.Spaces.pth V z θ - α * z * Work.Spaces.pth (Work.Spaces.pz V) z θ := by
    change deriv (fun θ' => -3 * V z θ' - α * z * Work.Spaces.pz V z θ') θ
      = -3 * Work.Spaces.pth V z θ - α * z * Work.Spaces.pth (Work.Spaces.pz V) z θ
    rw [show (fun θ' => -3 * V z θ' - α * z * Work.Spaces.pz V z θ')
        = (fun θ' => (-3) * V z θ') + (fun θ' => (-(α * z)) * Work.Spaces.pz V z θ') from by
          funext θ'; simp only [Pi.add_apply]; ring]
    rw [deriv_add (hslice.const_mul (-3)) (hslicepz.const_mul (-(α * z))),
      deriv_const_mul (-3) hslice, deriv_const_mul (-(α * z)) hslicepz]
    simp only [Work.Spaces.pth]
    ring
  rw [hUop, ← Work.Spaces.pz_pth_comm (f := V) hct]
  simp only [Work.Spaces.Dz]
  ring

theorem pthU_slot_alg : ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, n ≤ k + 1 → ContDiffOn ℝ n (Function.uncurry V)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) →
      Work.Spaces.HkMem α k (Work.Spaces.pth V) →
      Work.Spaces.HkMem α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) →
      Work.Spaces.HkSq α k (Work.Spaces.pth (Work.FTS.EllipticEst.Uop α V))
        ≤ C * (Work.Spaces.HkSq α k (Work.Spaces.pth V)
            + Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)) := by
  intro k hk
  refine ⟨18, by norm_num, ?_⟩
  intro α V hα hV hmf hmG
  have hα0 : 0 ≤ α := le_of_lt hα
  -- smoothness on the open quadrant
  have hVk1 : ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry V) Q2.Qd := by
    simpa only [Q2.Qd, Work.FTS.EllipticEst.Q0] using hV (k + 1) le_rfl
  have hV2 : ContDiffOn ℝ 2 (Function.uncurry V) Q2.Qd :=
    contDiffOn_of_le_nat hVk1 (Nat.le_succ_of_le hk)
  have hf : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.pth V)) Q2.Qd :=
    Q2.contDiffOn_pth_fin Q2.isOpen_Qd hVk1
  have hg : ContDiffOn ℝ (k - 1 : ℕ)
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth V))) Q2.Qd := by
    refine (contDiffOn_fst.mul (Q2.contDiffOn_pz_fin Q2.isOpen_Qd ?_)).congr (fun p _ => rfl)
    exact contDiffOn_of_le_nat hf (by omega : (k - 1) + 1 ≤ k)
  -- the pointwise identity
  have hE := pth_Uop_eq α hV2
  -- the `HkSq` estimate
  have hsq := HkSq_slot_le α k hα0 hE hf hg hmf hmG
  calc Work.Spaces.HkSq α k (Work.Spaces.pth (Work.FTS.EllipticEst.Uop α V))
      ≤ 18 * Work.Spaces.HkSq α k (Work.Spaces.pth V)
        + 2 * Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) :=
        hsq
    _ ≤ 18 * (Work.Spaces.HkSq α k (Work.Spaces.pth V)
          + Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)) := by
        have hnn := Work.Spaces.HkSq_nonneg α k
          (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        linarith

end Work.FTS.EllipticEst.RegQ
