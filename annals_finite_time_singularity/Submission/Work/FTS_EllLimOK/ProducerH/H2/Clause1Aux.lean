/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.H2.Clause1Aux` — vocabulary for the box-`C²` clause

The supporting vocabulary of the chapter `H2/clause1`: the closed-box `C²`-regularity of the
stream function `E g` from the endpoint data `BoxData`.

* `Bf L0 L1 Ψ` — the boundary-corrected θ-slope of `Ψ`: `∂_θΨ` in the open strip, the one-sided
  limit `L0 z` (resp. `L1 z`) at `θ = 0` (resp. `θ = π/2`);
* `Mf N0 N1 Ψ` — the boundary-corrected mixed slope `∂_θ∂_zΨ`, with the one-sided limits
  `N0 z`, `N1 z` at the two endpoints;
* `B2f Ψ` — the boundary-corrected `∂_θ²Ψ`, vanishing at both endpoints;
* `LimitsAt Ψ X C a b L0 N0 L1 N1` — the `Limits` data of `Data.lean` with the witnesses and the
  rate constant frozen, one angular endpoint at a time.

The generic analysis lemmas (`interior_lipschitz_of_deriv_bound`, `theta_modulus_of_data`,
`continuousOn_zslice_of_smoothOpen`, `hasDerivWithinAt_Icc_left/right`,
`continuousWithinAt_Icc_left/right`, `continuousOn_thetaSlice_of_traces`) are the elementary
one-variable facts that convert the rates of `BoxData` into a uniform angular modulus and the
within-derivatives at the endpoints.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The boundary-corrected slope functions -/

/-- The boundary-corrected θ-slope: `∂_θΨ` in the open strip and the one-sided limits at the
two angular endpoints. -/
def Bf (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ = 0 then L0 z else if θ = π / 2 then L1 z else Work.Spaces.pth Ψ z θ

/-- The boundary-corrected mixed slope `∂_θ∂_zΨ`, with the one-sided limits at the two angular
endpoints. -/
def Mf (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    if θ = 0 then N0 z else if θ = π / 2 then N1 z else Work.Spaces.pth (Work.Spaces.pz Ψ) z θ

/-- The boundary-corrected `∂_θ²Ψ`, vanishing at both angular endpoints. -/
def B2f (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ = 0 then 0 else if θ = π / 2 then 0 else Work.Spaces.pth (Work.Spaces.pth Ψ) z θ

@[simp] theorem Bf_zero (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Bf L0 L1 Ψ z 0 = L0 z := by
  simp [Bf]

theorem Bf_pi (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Bf L0 L1 Ψ z (π / 2) = L1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Bf, h0]

theorem Bf_of_mem_Ioo {L0 L1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Bf L0 L1 Ψ z θ = Work.Spaces.pth Ψ z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Bf, if_neg h0, if_neg h1]

@[simp] theorem Mf_zero (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z 0 = N0 z := by
  simp [Mf]

theorem Mf_pi (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z (π / 2) = N1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Mf, h0]

theorem Mf_of_mem_Ioo {N0 N1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Mf N0 N1 Ψ z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Mf, if_neg h0, if_neg h1]

@[simp] theorem B2f_zero (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : B2f Ψ z 0 = 0 := by
  simp [B2f]

theorem B2f_pi (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : B2f Ψ z (π / 2) = 0 := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [B2f, h0]

theorem B2f_of_mem_Ioo {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    B2f Ψ z θ = Work.Spaces.pth (Work.Spaces.pth Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [B2f, if_neg h0, if_neg h1]

/-! ## The frozen `Limits` data -/

/-- The `Limits` data of `Data.lean` with the witnesses and the rate constant frozen: the two
one-sided angular limits of `∂_θΨ` and of `∂_z∂_θΨ`, their linear rates, continuity in `z` and
the identification of the `z`-derivative of the limit. -/
def LimitsAt (Ψ : ℝ → ℝ → ℝ) (X C a b : ℝ) (L0 N0 L1 N1 : ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth Ψ z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (L0 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ - L0 z| ≤ C * X * θ) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - N0 z| ≤ C * X * θ) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth Ψ z θ)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (L1 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ - L1 z| ≤ C * X * (π / 2 - θ)) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - N1 z| ≤ C * X * (π / 2 - θ)) ∧
  ContinuousOn L0 (Set.Icc a b) ∧ ContinuousOn N0 (Set.Icc a b) ∧
  ContinuousOn L1 (Set.Icc a b) ∧ ContinuousOn N1 (Set.Icc a b) ∧
  (∀ z ∈ Set.Icc a b, HasDerivWithinAt L0 (N0 z) (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, HasDerivWithinAt L1 (N1 z) (Set.Icc a b) z)

/-- The `Limits` component of `BoxData`, with the witnesses and the constant still existential
(inside the `∀ g`). -/
theorem limitsAt_of_boxData {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} {a b : ℝ}
    (h : BoxData α Ce E a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
      ∃ L0 N0 L1 N1 : ℝ → ℝ,
        LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b L0 N0 L1 N1 :=
  h.limits

/-! ## Generic one-variable analysis lemmas -/

/-- **Continuity of the `z`-slice of a function `C^∞` on the open quadrant.** -/
theorem continuousOn_zslice_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {a b θ : ℝ} (ha : 0 < a)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun z => F z θ) (Set.Icc a b) :=
  ((hF.curry_z hθ).continuousOn).mono (fun z hz => lt_of_lt_of_le ha hz.1)

/-- **The interior Lipschitz modulus of the angular slice from a bound on its derivative.** -/
theorem interior_lipschitz_of_deriv_bound {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hdiff : ∀ z : ℝ, ∀ θ ∈ Set.Ioo 0 (π / 2), DifferentiableAt ℝ (fun θ' => F z θ') θ)
    (hbd : ∀ z : ℝ, ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv (fun θ' => F z θ') θ| ≤ C) :
    ∀ z : ℝ, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| := by
  intro z θ hθ θ' hθ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun θ' => F z θ')
    (s := Set.Ioo 0 (π / 2)) (x := θ') (y := θ) (C := C)
    (fun x hx => hdiff z x hx)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbd z x hx)
    (convex_Ioo 0 (π / 2)) hθ' hθ
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **The interior Lipschitz modulus of one angular slice from a bound on its derivative** (the
`z`-restricted form of `interior_lipschitz_of_deriv_bound`, which is the usable one: the
θ-slices of `E g` are only known to be differentiable for `z > 0`). -/
theorem interior_lipschitz_at {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (hdiff : ∀ θ ∈ Set.Ioo 0 (π / 2), DifferentiableAt ℝ (fun θ' => F z θ') θ)
    (hbd : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv (fun θ' => F z θ') θ| ≤ C) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| := by
  intro θ hθ θ' hθ'
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun θ' => F z θ')
    (s := Set.Ioo 0 (π / 2)) (x := θ') (y := θ) (C := C)
    (fun x hx => hdiff x hx)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx)
    (convex_Ioo 0 (π / 2)) hθ' hθ
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **The uniform angular modulus on the box from the interior modulus and the endpoint rates**
(the `z ∈ [a,b]`-restricted form of `theta_modulus_of_data`). -/
theorem theta_modulus_on {F : ℝ → ℝ → ℝ} {C β a b : ℝ} (hβ : 0 < β)
    (hint : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (h0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), |F z θ - F z 0| ≤ C * θ ^ β)
    (hpi : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      |F z θ - F z (π / 2)| ≤ C * (π / 2 - θ) ^ β) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β := by
  intro z hz θ hθ θ' hθ'
  have h0' : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |t - 0| ^ β = t ^ β :=
    fun t ht => by rw [sub_zero, abs_of_nonneg ht.1]
  have hpi' : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |(π : ℝ) / 2 - t| ^ β = ((π : ℝ) / 2 - t) ^ β :=
    fun t ht => by rw [abs_of_nonneg (show (0 : ℝ) ≤ π / 2 - t by linarith [ht.2])]
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    rw [abs_sub_comm (0 : ℝ) θ', h0' θ' hθ', abs_sub_comm (F z 0) (F z θ')]
    exact h0 z hz θ' hθ'
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    rw [hpi' θ' hθ', abs_sub_comm (F z (π / 2)) (F z θ')]
    exact hpi z hz θ' hθ'
  rcases eq_or_lt_of_le hθ'.1 with h' | h'
  · subst h'
    rw [h0' θ hθ]
    exact h0 z hz θ hθ
  rcases eq_or_lt_of_le hθ'.2 with hp' | hp'
  · subst hp'
    rw [abs_sub_comm θ ((π : ℝ) / 2), hpi' θ hθ]
    exact hpi z hz θ hθ
  exact hint z hz θ ⟨h, hp⟩ θ' ⟨h', hp'⟩

/-- **The min-rate dominates `θ ^ β`** on `[0,π/2]` for `0 < β ≤ 1`. -/
theorem min_le_rpow_theta {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) : min θ (π / 2 - θ) ≤ θ ^ β := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [sub_zero, min_eq_left (show (0 : ℝ) ≤ π / 2 by positivity), Real.zero_rpow hβ.ne']
  · rcases lt_or_ge θ 1 with h1 | h1
    · have h2 := Real.rpow_le_rpow_of_exponent_ge h0 h1.le hβ1
      rw [Real.rpow_one] at h2
      exact (min_le_left _ _).trans h2
    · have hge : (1 : ℝ) ≤ θ ^ β := Real.one_le_rpow h1 hβ.le
      have hlt : π / 2 - θ < 1 := by linarith [hθ.2, Real.pi_lt_four]
      exact (min_le_right _ _).trans (hlt.le.trans hge)

/-- **The min-rate dominates `(π/2 - θ) ^ β`** on `[0,π/2]` for `0 < β ≤ 1`. -/
theorem min_le_rpow_pi_sub {β θ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) : min θ (π / 2 - θ) ≤ (π / 2 - θ) ^ β := by
  have h' : (π / 2 - θ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have h := min_le_rpow_theta (θ := π / 2 - θ) hβ hβ1 h'
  have h2 : (π / 2 - (π / 2 - θ)) = θ := by ring
  rw [h2, min_comm] at h
  exact h

/-- **The uniform Lipschitz angular modulus on `[a,b]` from the interior modulus and the two
one-sided endpoint rates** (the endpoint values being *different*: the case `(0,π/2)` is settled
by passing through `π/4`). -/
theorem theta_modulus_Icc_of_endpoints {F : ℝ → ℝ → ℝ} {C a b : ℝ}
    (hint : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'|)
    (h0 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2), |F z θ - F z 0| ≤ C * θ)
    (hpi : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z (π / 2)| ≤ C * (π / 2 - θ)) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| := by
  have hq : (π / 4 : ℝ) ∈ Set.Ioo 0 (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hhalf : (0 : ℝ) < π / 2 := by positivity
  intro z hz
  have h0' : |F z 0 - F z (π / 2)| ≤ C * |(0 : ℝ) - π / 2| := by
    have h1 := h0 z hz (π / 4) hq
    have h2 : |F z (π / 4) - F z (π / 2)| ≤ C * (π / 4) := by
      have h2' := hpi z hz (π / 4) hq
      rwa [show (π : ℝ) / 2 - π / 4 = π / 4 from by ring] at h2'
    have h3 : |F z 0 - F z (π / 4)| ≤ C * (π / 4) := by
      rw [abs_sub_comm]; exact h1
    calc |F z 0 - F z (π / 2)|
        ≤ |F z 0 - F z (π / 4)| + |F z (π / 4) - F z (π / 2)| := by
          rw [show F z 0 - F z (π / 2)
            = (F z 0 - F z (π / 4)) + (F z (π / 4) - F z (π / 2)) from by ring]
          exact abs_add_le _ _
      _ ≤ C * (π / 4) + C * (π / 4) := add_le_add h3 h2
      _ = C * |(0 : ℝ) - π / 2| := by
          rw [zero_sub, abs_neg, abs_of_pos hhalf]; ring
  intro θ hθ θ' hθ'
  rcases eq_or_lt_of_le hθ.1 with h0θ | h0θ
  · subst h0θ
    rcases eq_or_lt_of_le hθ'.2 with hpi' | hpi'
    · subst hpi'
      exact h0'
    · rcases eq_or_lt_of_le hθ'.1 with h0' | h0'
      · subst h0'
        have h1 : |F z 0 - F z 0| = 0 := by rw [sub_self, abs_zero]
        have h2 : C * |(0 : ℝ) - 0| = 0 := by rw [sub_self, abs_zero, mul_zero]
        exact le_of_eq (by rw [h1, h2])
      · have h1 := h0 z hz θ' ⟨h0', hpi'⟩
        have h2 : |F z 0 - F z θ'| = |F z θ' - F z 0| := abs_sub_comm _ _
        have h3 : |(0 : ℝ) - θ'| = θ' := by rw [zero_sub, abs_neg, abs_of_pos h0']
        rw [h2, h3]
        exact h1
  · rcases eq_or_lt_of_le hθ.2 with hpiθ | hpiθ
    · subst hpiθ
      rcases eq_or_lt_of_le hθ'.1 with h0' | h0'
      · subst h0'
        have h1 : |F z (π / 2) - F z 0| = |F z 0 - F z (π / 2)| := abs_sub_comm _ _
        have h2 : |(π : ℝ) / 2 - 0| = |(0 : ℝ) - π / 2| := by
          rw [sub_zero, abs_sub_comm, sub_zero]
        rw [h1, h2]
        exact h0'
      · rcases eq_or_lt_of_le hθ'.2 with hpi' | hpi'
        · subst hpi'
          have h1 : |F z (π / 2) - F z (π / 2)| = 0 := by rw [sub_self, abs_zero]
          have h2 : C * |(π : ℝ) / 2 - π / 2| = 0 := by rw [sub_self, abs_zero, mul_zero]
          exact le_of_eq (by rw [h1, h2])
        · have h1 := hpi z hz θ' ⟨h0', hpi'⟩
          have h2 : |F z (π / 2) - F z θ'| = |F z θ' - F z (π / 2)| := abs_sub_comm _ _
          have h3 : |(π : ℝ) / 2 - θ'| = π / 2 - θ' := abs_of_nonneg (by linarith [hθ'.2])
          rw [h2, h3]
          exact h1
    · rcases eq_or_lt_of_le hθ'.1 with h0' | h0'
      · subst h0'
        have h1 := h0 z hz θ ⟨h0θ, hpiθ⟩
        have h3 : |θ - (0 : ℝ)| = θ := by rw [sub_zero, abs_of_nonneg hθ.1]
        rw [h3]
        exact h1
      · rcases eq_or_lt_of_le hθ'.2 with hpi' | hpi'
        · subst hpi'
          have h1 := hpi z hz θ ⟨h0θ, hpiθ⟩
          have h3 : |θ - (π : ℝ) / 2| = π / 2 - θ := by
            rw [abs_of_nonpos (by linarith [hθ.2]), neg_sub]
          rw [h3]
          exact h1
        · exact hint z hz θ ⟨h0θ, hpiθ⟩ θ' ⟨h0', hpi'⟩

/-- **The uniform angular modulus from the interior modulus and the endpoint rates.** -/
theorem theta_modulus_of_data {F : ℝ → ℝ → ℝ} {C β : ℝ} (hβ : 0 < β)
    (hint : ∀ z : ℝ, ∀ θ ∈ Set.Ioo 0 (π / 2), ∀ θ' ∈ Set.Ioo 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (h0 : ∀ z : ℝ, ∀ θ ∈ Set.Icc 0 (π / 2), |F z θ - F z 0| ≤ C * θ ^ β)
    (hpi : ∀ z : ℝ, ∀ θ ∈ Set.Icc 0 (π / 2), |F z θ - F z (π / 2)| ≤ C * (π / 2 - θ) ^ β) :
    ∀ z : ℝ, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β := by
  intro z θ hθ θ' hθ'
  have h0' : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |t - 0| ^ β = t ^ β :=
    fun t ht => by rw [sub_zero, abs_of_nonneg ht.1]
  have hpi' : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |(π : ℝ) / 2 - t| ^ β = ((π : ℝ) / 2 - t) ^ β :=
    fun t ht => by rw [abs_of_nonneg (show (0 : ℝ) ≤ π / 2 - t by linarith [ht.2])]
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    rw [abs_sub_comm (0 : ℝ) θ', h0' θ' hθ', abs_sub_comm (F z 0) (F z θ')]
    exact h0 z θ' hθ'
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    rw [hpi' θ' hθ', abs_sub_comm (F z (π / 2)) (F z θ')]
    exact hpi z θ' hθ'
  rcases eq_or_lt_of_le hθ'.1 with h' | h'
  · subst h'
    rw [h0' θ hθ]
    exact h0 z θ hθ
  rcases eq_or_lt_of_le hθ'.2 with hp' | hp'
  · subst hp'
    rw [abs_sub_comm θ ((π : ℝ) / 2), hpi' θ hθ]
    exact hpi z θ hθ
  exact hint z θ ⟨h, hp⟩ θ' ⟨h', hp'⟩

/-- **Right-continuity on `[0,T]` from the right limit and the value at `0`.** -/
theorem continuousWithinAt_Icc_left {f : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (h : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) (h0 : f 0 = L) :
    ContinuousWithinAt f (Set.Icc 0 T) 0 := by
  rw [ContinuousWithinAt, h0, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) ε hε
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    rw [h0]
    simpa using hε
  · exact hδ' hx0 hxd

/-- **Left-continuity on `[0,T]` from the left limit and the value at `T`.** -/
theorem continuousWithinAt_Icc_right {f : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (h : Filter.Tendsto f (nhdsWithin T (Set.Iio T)) (nhds L)) (hT' : f T = L) :
    ContinuousWithinAt f (Set.Icc 0 T) T := by
  rw [ContinuousWithinAt, hT', Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) ε hε
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  rcases eq_or_lt_of_le hx.2 with hx0 | hx0
  · subst hx0
    rw [hT']
    simpa using hε
  · exact hδ' hx0 hxd

/-- **Within-derivative at the left endpoint from the one-sided limit of the derivative.** -/
theorem hasDerivWithinAt_Icc_left {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcont0 : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin 0 (Set.Ioi 0) := Ioo_mem_nhdsGT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont0 hmem hd').mono
    (fun x hx => hx.1)

/-- **Within-derivative at the right endpoint from the one-sided limit of the derivative.** -/
theorem hasDerivWithinAt_Icc_right {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin T (Set.Iio T)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) T := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcontT : ContinuousWithinAt f (Set.Ioo 0 T) T :=
    (hcont.continuousWithinAt (Set.right_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin T (Set.Iio T) := Ioo_mem_nhdsLT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin T (Set.Iio T)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontT hmem hd').mono
    (fun x hx => hx.2)

/-- **Continuity of an angular slice on the closed interval** from continuity on the open
interval and the two traces (the general form, not requiring a `SmoothOpen` ambient function). -/
theorem continuousOn_thetaSlice_of_interior {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hint : ∀ θ ∈ Set.Ioo 0 T, ContinuousAt f θ)
    (h0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)))
    (hT' : Filter.Tendsto f (nhdsWithin T (Set.Iio T)) (nhds (f T))) :
    ContinuousOn f (Set.Icc 0 T) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    exact continuousWithinAt_Icc_left hT h0 rfl
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    exact continuousWithinAt_Icc_right hT hT' rfl
  · exact (hint θ ⟨h, hp⟩).continuousWithinAt

/-- **`θ ^ β → 0` at `0⁺`, squeezed form.** -/
theorem tendsto_zero_of_abs_le_rpow {f : ℝ → ℝ} {C β : ℝ} (hβ : 0 < β)
    (h : ∀ θ : ℝ, 0 < θ → |f θ| ≤ C * θ ^ β) :
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  by_cases hC : C ≤ 0
  · refine ⟨1, one_pos, fun θ hθ _ => ?_⟩
    have h1 : |f θ| ≤ 0 :=
      le_trans (h θ hθ) (mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hθ.le _))
    have h2 : f θ = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    rw [h2, Real.dist_eq, sub_zero, abs_zero]
    exact hε
  · have hCpos : 0 < C := not_le.mp hC
    have hbase : 0 < (ε / 2) / C := by positivity
    refine ⟨min 1 (((ε / 2) / C) ^ (1 / β)), lt_min one_pos (Real.rpow_pos_of_pos hbase _),
      fun θ hθ hδ => ?_⟩
    have hθpos : (0 : ℝ) < θ := hθ
    have hlt : θ < min 1 (((ε / 2) / C) ^ (1 / β)) := by
      have h1 := hδ
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos] at h1
      exact h1
    have hδ' : θ ≤ (((ε / 2) / C) ^ (1 / β)) := (lt_min_iff.mp hlt).2.le
    have hpow : θ ^ β ≤ (ε / 2) / C := by
      calc θ ^ β ≤ ((((ε / 2) / C) ^ (1 / β))) ^ β :=
            Real.rpow_le_rpow hθpos.le hδ' hβ.le
        _ = (ε / 2) / C := by
            rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hβ.ne', Real.rpow_one]
    have h1 : |f θ| ≤ C * ((ε / 2) / C) :=
      le_trans (h θ hθpos) (mul_le_mul_of_nonneg_left hpow hCpos.le)
    have h2 : C * ((ε / 2) / C) = ε / 2 := by field_simp
    rw [Real.dist_eq, sub_zero]
    linarith [h1, h2]

/-- **`(π/2 - θ) ^ β → 0` at `(π/2)⁻`, squeezed form.** -/
theorem tendsto_zero_of_abs_le_rpow_pi_sub {f : ℝ → ℝ} {C β : ℝ} (hβ : 0 < β)
    (h : ∀ θ : ℝ, θ < π / 2 → |f θ| ≤ C * (π / 2 - θ) ^ β) :
    Filter.Tendsto f (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hT : (0 : ℝ) < π / 2 := by positivity
  have hcomp : Filter.Tendsto (fun θ : ℝ => f (π / 2 - θ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_abs_le_rpow hβ (C := C) (fun t ht => ?_)
    have h1 : |f (π / 2 - t)| ≤ C * (π / 2 - (π / 2 - t)) ^ β := h (π / 2 - t) (by linarith)
    have h2 : (π / 2 - (π / 2 - t)) = t := by ring
    simpa [h2] using h1
  have hshift : Filter.Tendsto (fun θ : ℝ => π / 2 - θ) (nhdsWithin (π / 2) (Set.Iio (π / 2)))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Filter.Tendsto (fun θ : ℝ => π / 2 - θ) (nhdsWithin (π / 2) (Set.Iio (π / 2)))
          (nhds (π / 2 - π / 2)) :=
        (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
      simpa using h1
    · filter_upwards [Ioo_mem_nhdsLT hT] with θ hθ
      exact sub_pos.mpr hθ.2
  have h1 : Filter.Tendsto (fun θ : ℝ => f (π / 2 - (π / 2 - θ)))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := hcomp.comp hshift
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall ?_) h1
  intro θ
  congr 1
  ring

/-- **Continuity of the angular slice on the closed interval** from the two traces. -/
theorem continuousOn_thetaSlice_of_traces {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => F z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (F z 0)))
    (hπ : Filter.Tendsto (fun θ => F z θ) (nhdsWithin (π / 2) (Set.Iio (π / 2)))
      (nhds (F z (π / 2)))) :
    ContinuousOn (fun θ => F z θ) (Set.Icc 0 (π / 2)) :=
  continuousOn_thetaSlice_of_interior (by positivity)
    (fun θ hθ => ((hsm.curry_θ hz).contDiffAt (isOpen_Ioo.mem_nhds hθ)).continuousAt)
    h0 hπ

end Work.FTS_EllLimOK.ProducerH.H2
