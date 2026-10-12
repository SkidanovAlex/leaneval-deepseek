import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-218 — the box-momentum representation, Step-1: the Neumann basis

(Work-in-progress module; Session-218.  Follows `SmallBoxBogolubovKinetic`
(Session-217): the 𝒯_B quadratic form needs a momentum representation over
the centred box.  The natural basis for the box `[−ℓ/2, ℓ/2]³` with the
CONSTANT condensate orbital (the `Q = 1 − P` excited projection removes the
constant) is the **Neumann cosine basis**: in 1-D the modes
`u_k(x) := cos(kπ(x + ℓ/2)/ℓ)`, `k ∈ ℕ₀` (the shift by `ℓ/2` makes the
derivative vanish at BOTH endpoints `±ℓ/2` — the true Neumann eigenmodes of
the centred interval), with the constant mode `u₀ ≡ 1` (the condensate
orbital direction).

Step-1 here: define the 1-D mode and prove its FIRST orthogonality fact —
the constant is orthogonal to every `k ≥ 1` mode:

    ∫_{−ℓ/2}^{ℓ/2} u_k(x) dx = 0   (k ≥ 1)

(so the condensate constant is orthogonal to all excited Neumann modes), and
the mode normalizations `∫ u₀² = ℓ` and `∫ u_k² = ℓ/2` for `k ≥ 1` (from
`cos²θ = (1+cos 2θ)/2` and orthogonality at `2k`).  These are the primitive
facts the 𝒯_B-layer estimates (and
the `bogolubov_sharp_bound_target` of `SmallBoxBogolubovTarget`) build on;
the 3-D product basis and the `χ_B`-localized momentum weights attach in the
following steps.
-/

open scoped Real
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Submission.BoseGases

/-- the 1-D Neumann mode of the centred interval `[−ℓ/2, ℓ/2]` at wave-number
`k ∈ ℕ₀`: `u_k(x) := cos(kπ(x + ℓ/2)/ℓ)` (`u₀ ≡ 1`; the `+ℓ/2`-shift makes
`u_k'` vanish at both endpoints — the Neumann boundary condition). -/
def boxNeumann (ℓ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))

/-- the constant mode is `u₀ ≡ 1` on the centred interval. -/
lemma boxNeumann_zero (ℓ : ℝ) (x : ℝ) : boxNeumann ℓ 0 x = 1 := by
  dsimp [boxNeumann]
  norm_num

/-- **First orthogonality**: the constant is orthogonal to every `k ≥ 1`
Neumann mode over the centred interval: `∫_{−ℓ/2}^{ℓ/2} u_k = 0`. -/
lemma boxNeumann_const_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x) = 0 := by
  let A : ℝ := (k : ℝ) * Real.pi / ℓ
  have hAne : A ≠ 0 := by
    dsimp [A]
    exact div_ne_zero
      (mul_ne_zero (by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hk))) Real.pi_ne_zero)
      (ne_of_gt hℓ)
  have hpt : (fun x : ℝ => boxNeumann ℓ k x)
      = fun x : ℝ => Real.cos (A * (x + ℓ / 2)) := by
    funext x
    dsimp [boxNeumann, A]
  have hshift : (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x)
      = ∫ t in 0..ℓ, Real.cos (A * t) := by
    rw [hpt]
    change (∫ x in (-(ℓ / 2))..(ℓ / 2),
        (fun y : ℝ => Real.cos (A * y)) (x + ℓ / 2))
        = ∫ t in 0..ℓ, Real.cos (A * t)
    have h := intervalIntegral.integral_comp_add_right
      (f := fun y : ℝ => Real.cos (A * y)) (a := -(ℓ / 2)) (b := ℓ / 2) (d := ℓ / 2)
    rw [h]
    have hb1 : -(ℓ / 2) + ℓ / 2 = 0 := by ring
    have hb2 : ℓ / 2 + ℓ / 2 = ℓ := by ring
    rw [hb1, hb2]
  have hmul : (∫ t in 0..ℓ, Real.cos (A * t))
      = A⁻¹ * (∫ s in 0..A * ℓ, Real.cos s) := by
    have h := intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := 0) (b := ℓ) (c := A) hAne
    simpa using h
  calc
    (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x)
        = ∫ t in 0..ℓ, Real.cos (A * t) := hshift
    _ = A⁻¹ * (∫ s in 0..A * ℓ, Real.cos s) := hmul
    _ = A⁻¹ * (Real.sin (A * ℓ) - Real.sin 0) := by
        congr 1
        rw [integral_cos]
    _ = 0 := by
        have hAℓ : A * ℓ = (k : ℝ) * Real.pi := by
          dsimp [A]
          field_simp [ne_of_gt hℓ]
        rw [hAℓ, Real.sin_nat_mul_pi k]
        simp


/-- **Mode normalization (k = 0)**: `∫_{−ℓ/2}^{ℓ/2} u₀² = ℓ` (`u₀ ≡ 1`). -/
lemma boxNeumann_sq_norm_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ 0 x) ^ 2) = ℓ := by
  have hc : (∫ x in (-(ℓ / 2))..(ℓ / 2), (1 : ℝ)) = ℓ := by
    have hcc := intervalIntegral.integral_const (a := -(ℓ / 2)) (b := ℓ / 2) (c := (1 : ℝ))
    have hba : ℓ / 2 - (-(ℓ / 2)) = ℓ := by ring
    simp [hba, hcc]
  calc
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ 0 x) ^ 2)
        = ∫ x in (-(ℓ / 2))..(ℓ / 2), (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change (boxNeumann ℓ 0 x) ^ 2 = 1
            rw [boxNeumann_zero]
            norm_num
    _ = ℓ := hc


/-- **Mode normalization (k ≥ 1)**: `∫_{−ℓ/2}^{ℓ/2} u_k² = ℓ/2` — from
`cos²θ = (1 + cos 2θ)/2` and `boxNeumann_const_orthogonal` at wave-number
`2k` (which kills the oscillatory term). -/
lemma boxNeumann_sq_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : 1 ≤ k) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ k x) ^ 2) = ℓ / 2 := by
  have hcos (t : ℝ) : (Real.cos t) ^ 2 = (1 + Real.cos (2 * t)) / 2 := by
    have hcm := Real.cos_two_mul t
    have hcs := Real.cos_sq_add_sin_sq t
    nlinarith
  have hk2 : 1 ≤ 2 * k := by nlinarith [hk]
  have hcos2 : (∫ x in (-(ℓ / 2))..(ℓ / 2), Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) = 0 := by
    have hpt : (fun x : ℝ => Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))))
        = fun x : ℝ => boxNeumann ℓ (2 * k) x := by
      funext x
      dsimp [boxNeumann]
      congr 1
      rw [Nat.cast_mul]
      ring_nf
    rw [hpt]
    exact boxNeumann_const_orthogonal hℓ hk2
  have hpt : (fun x : ℝ => (boxNeumann ℓ k x) ^ 2)
      = fun x : ℝ => (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) / 2 := by
    funext x
    change (Real.cos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2
        = (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) / 2
    rw [hcos (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))]
  calc
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ k x) ^ 2)
        = ∫ x in (-(ℓ / 2))..(ℓ / 2), (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) / 2 := by
            rw [hpt]
    _ = (1 / 2) * (∫ x in (-(ℓ / 2))..(ℓ / 2), (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2))))) := by
            have hpt' : (fun x : ℝ => (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) / 2)
                = fun x : ℝ => (1 / 2) * (1 + Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) := by
              funext x
              ring
            rw [hpt']
            rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2) * (ℓ + 0) := by
            congr 1
            have hI1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-(ℓ / 2)) (ℓ / 2) :=
              intervalIntegrable_const (a := -(ℓ / 2)) (b := ℓ / 2) (μ := volume) (c := (1 : ℝ))
            have hI2 : IntervalIntegrable
                (fun x : ℝ => Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))) volume (-(ℓ / 2)) (ℓ / 2) := by
              exact (by fun_prop : Continuous fun x : ℝ =>
                Real.cos (2 * (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)))).intervalIntegrable _ _
            rw [intervalIntegral.integral_add hI1 hI2]
            have h1 : (∫ x in (-(ℓ / 2))..(ℓ / 2), (1 : ℝ)) = ℓ := by
              have hcc := intervalIntegral.integral_const (a := -(ℓ / 2)) (b := ℓ / 2) (c := (1 : ℝ))
              have hba : ℓ / 2 - (-(ℓ / 2)) = ℓ := by ring
              simp [hba, hcc]
            rw [h1, hcos2]
    _ = ℓ / 2 := by ring


/-- **the 3-D Neumann product mode** over the coordinate functions
`z : Fin 3 → ℝ` (each coordinate the 1-D `boxNeumann` at its wave-number):
`u_k(z) := ∏_j boxNeumann ℓ (k j) (z j)` — the product basis of the centred
box `[−ℓ/2,ℓ/2]³` (constant mode `k ≡ 0` is `u₀ ≡ 1`, the condensate
direction). -/
def boxNeumann3 (ℓ : ℝ) (k : Fin 3 → ℕ) (z : Fin 3 → ℝ) : ℝ :=
  ∏ j : Fin 3, boxNeumann ℓ (k j) (z j)

/-- **separable triple-factorization** (the Fubini fact the 3-D box
orthogonality reduces to): for continuous `f, g, h` over a common interval,

    ∫x₀∫x₁∫x₂ (f x₀·g x₁·h x₂) = (∫f)·(∫g)·(∫h). -/
lemma triple_separable_intervalIntegral {a b : ℝ} (f g h : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    (∫ x₀ in a..b, ∫ x₁ in a..b, ∫ x₂ in a..b, f x₀ * g x₁ * h x₂)
      = (∫ x₀ in a..b, f x₀) * (∫ x₁ in a..b, g x₁) * (∫ x₂ in a..b, h x₂) := by
  -- innermost: pull (f x₀·g x₁) out of the x₂-integral
  have hstep2 : ∀ x₀ x₁ : ℝ,
      (∫ x₂ in a..b, f x₀ * g x₁ * h x₂) = (f x₀ * g x₁) * (∫ x₂ in a..b, h x₂) := by
    intro x₀ x₁
    have hpt : (fun x₂ : ℝ => f x₀ * g x₁ * h x₂)
        = fun x₂ : ℝ => (f x₀ * g x₁) * h x₂ := by
      funext x₂
      ring
    rw [hpt]
    rw [intervalIntegral.integral_const_mul]
  -- next: pull (f x₀ · ∫h) out of the x₁-integral
  have hstep1 : ∀ x₀ : ℝ,
      (∫ x₁ in a..b, ∫ x₂ in a..b, f x₀ * g x₁ * h x₂)
        = f x₀ * (∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁) := by
    intro x₀
    calc
      (∫ x₁ in a..b, ∫ x₂ in a..b, f x₀ * g x₁ * h x₂)
          = ∫ x₁ in a..b, (f x₀ * g x₁) * (∫ x₂ in a..b, h x₂) := by
              apply intervalIntegral.integral_congr
              intro x₁ hx
              exact hstep2 x₀ x₁
      _ = f x₀ * (∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁) := by
              -- pull (f x₀·∫h) out of the x₁-integral
              have hpt : (fun x₁ : ℝ => (f x₀ * g x₁) * (∫ x₂ in a..b, h x₂))
                  = fun x₁ : ℝ => (f x₀ * (∫ x₂ in a..b, h x₂)) * g x₁ := by
                funext x₁
                ring
              rw [hpt]
              rw [intervalIntegral.integral_const_mul]
  calc
    (∫ x₀ in a..b, ∫ x₁ in a..b, ∫ x₂ in a..b, f x₀ * g x₁ * h x₂)
        = ∫ x₀ in a..b, f x₀ * (∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁) := by
            apply intervalIntegral.integral_congr
            intro x₀ hx₀
            exact hstep1 x₀
    _ = (∫ x₀ in a..b, f x₀) * (∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁) := by
            have hpt : (fun x₀ : ℝ => f x₀ * (∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁))
                = fun x₀ : ℝ => ((∫ x₂ in a..b, h x₂) * (∫ x₁ in a..b, g x₁)) * f x₀ := by
              funext x₀
              ring
            rw [hpt]
            rw [intervalIntegral.integral_const_mul]
            ring
    _ = (∫ x₀ in a..b, f x₀) * (∫ x₁ in a..b, g x₁) * (∫ x₂ in a..b, h x₂) := by ring


/-- **first 3-D orthogonality**: a product Neumann mode with its coordinate-0
wave-number excited (`1 ≤ k₀`) integrates to zero over the centred box
(separable factorization `triple_separable_intervalIntegral` + the 1-D
orthogonality of coordinate 0). -/
lemma boxNeumann3_orthogonal_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {k₀ k₁ k₂ : ℕ} (hk : 1 ≤ k₀) :
    (∫ x₀ in (-(ℓ / 2))..(ℓ / 2), ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
      ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
        boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂) = 0 := by
  have hfac := triple_separable_intervalIntegral (a := -(ℓ / 2)) (b := ℓ / 2)
    (boxNeumann ℓ k₀) (boxNeumann ℓ k₁) (boxNeumann ℓ k₂)
    (by unfold boxNeumann; fun_prop) (by unfold boxNeumann; fun_prop)
    (by unfold boxNeumann; fun_prop)
  rw [hfac]
  have h0 := boxNeumann_const_orthogonal hℓ hk
  rw [h0]
  ring


/-- **single product-mode normalization (general form)**: the box integral of
the squared 3-D mode factors into the product of the three 1-D
normalizations:

    ∫x₀∫x₁∫x₂ (u_{k₀}x₀·u_{k₁}x₁·u_{k₂}x₂)²
        = (∫u_{k₀}²)·(∫u_{k₁}²)·(∫u_{k₂}²). -/
lemma boxNeumann3_sq_norm {ℓ : ℝ} (hℓ : 0 < ℓ) (k₀ k₁ k₂ : ℕ) :
    (∫ x₀ in (-(ℓ / 2))..(ℓ / 2), ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
      ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
        (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂) ^ 2)
      = (∫ x₀ in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ k₀ x₀) ^ 2)
          * (∫ x₁ in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ k₁ x₁) ^ 2)
          * (∫ x₂ in (-(ℓ / 2))..(ℓ / 2), (boxNeumann ℓ k₂ x₂) ^ 2) := by
  have hpt : (fun x₀ : ℝ => ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
        ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
          (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂) ^ 2)
      = fun x₀ : ℝ => ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
          ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
            (boxNeumann ℓ k₀ x₀) ^ 2 * (boxNeumann ℓ k₁ x₁) ^ 2 * (boxNeumann ℓ k₂ x₂) ^ 2 := by
    funext x₀
    apply intervalIntegral.integral_congr
    intro x₁ hx₁
    apply intervalIntegral.integral_congr
    intro x₂ hx₂
    ring
  rw [hpt]
  exact triple_separable_intervalIntegral (a := -(ℓ / 2)) (b := ℓ / 2)
    (fun x => (boxNeumann ℓ k₀ x) ^ 2) (fun x => (boxNeumann ℓ k₁ x) ^ 2)
    (fun x => (boxNeumann ℓ k₂ x) ^ 2)
    (by unfold boxNeumann; fun_prop) (by unfold boxNeumann; fun_prop)
    (by unfold boxNeumann; fun_prop)

/-- **single product-mode normalization (all coordinates excited)**: for
`1 ≤ k₀,k₁,k₂`, the box integral of the squared 3-D mode is `(ℓ/2)³`. -/
lemma boxNeumann3_sq_norm_all {ℓ : ℝ} (hℓ : 0 < ℓ) {k₀ k₁ k₂ : ℕ}
    (hk₀ : 1 ≤ k₀) (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) :
    (∫ x₀ in (-(ℓ / 2))..(ℓ / 2), ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
      ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
        (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂) ^ 2)
      = (ℓ / 2) * (ℓ / 2) * (ℓ / 2) := by
  rw [boxNeumann3_sq_norm hℓ k₀ k₁ k₂]
  rw [boxNeumann_sq_norm hℓ hk₀, boxNeumann_sq_norm hℓ hk₁, boxNeumann_sq_norm hℓ hk₂]


/-- **1-D product-to-sum**: for `m ≤ k`,
`2·u_k·u_m = u_{k−m} + u_{k+m}` pointwise (`2cosAcosB = cos(A−B)+cos(A+B)`
with the wave-number algebra `↑(k−m) = ↑k−↑m`, `↑(k+m) = ↑k+↑m`). -/
lemma boxNeumann_mul_of_le {ℓ : ℝ} {k m : ℕ} (hmk : m ≤ k) (x : ℝ) :
    2 * boxNeumann ℓ k x * boxNeumann ℓ m x
      = boxNeumann ℓ (k - m) x + boxNeumann ℓ (k + m) x := by
  let th : ℝ := x + ℓ / 2
  have hpt : 2 * boxNeumann ℓ k x * boxNeumann ℓ m x
      = 2 * Real.cos (((k : ℝ) * Real.pi / ℓ) * th)
          * Real.cos (((m : ℝ) * Real.pi / ℓ) * th) := by
    dsimp [boxNeumann, th]
  have h2 := Real.two_mul_cos_mul_cos (((k : ℝ) * Real.pi / ℓ) * th)
    (((m : ℝ) * Real.pi / ℓ) * th)
  have hargs1 : ((k : ℝ) * Real.pi / ℓ) * th - ((m : ℝ) * Real.pi / ℓ) * th
      = ((k - m : ℕ) : ℝ) * Real.pi / ℓ * th := by
    rw [Nat.cast_sub hmk]
    ring
  have hargs2 : ((k : ℝ) * Real.pi / ℓ) * th + ((m : ℝ) * Real.pi / ℓ) * th
      = ((k + m : ℕ) : ℝ) * Real.pi / ℓ * th := by
    rw [Nat.cast_add]
    ring
  calc
    2 * boxNeumann ℓ k x * boxNeumann ℓ m x
        = 2 * Real.cos (((k : ℝ) * Real.pi / ℓ) * th)
            * Real.cos (((m : ℝ) * Real.pi / ℓ) * th) := hpt
    _ = Real.cos (((k : ℝ) * Real.pi / ℓ) * th - ((m : ℝ) * Real.pi / ℓ) * th)
        + Real.cos (((k : ℝ) * Real.pi / ℓ) * th + ((m : ℝ) * Real.pi / ℓ) * th) := by
            rw [h2]
    _ = Real.cos (((k - m : ℕ) : ℝ) * Real.pi / ℓ * th)
        + Real.cos (((k + m : ℕ) : ℝ) * Real.pi / ℓ * th) := by
            rw [hargs1, hargs2]
    _ = boxNeumann ℓ (k - m) x + boxNeumann ℓ (k + m) x := by
            dsimp [boxNeumann, th]

/-- **1-D distinct-mode orthogonality (helper, `m ≤ k`)**: `∫ u_k·u_m = 0`
when `1 ≤ k−m` (product-to-sum + constant-orthogonality at `k−m` and
`k+m`). -/
lemma boxNeumann_mul_integral_of_le {ℓ : ℝ} (hℓ : 0 < ℓ) {k m : ℕ}
    (hmk : m ≤ k) (hpos : 1 ≤ k - m) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x * boxNeumann ℓ m x) = 0 := by
  have hkpm : 1 ≤ k + m := by omega
  have hpmul : ∀ x : ℝ, boxNeumann ℓ k x * boxNeumann ℓ m x
      = (1 / 2) * (boxNeumann ℓ (k - m) x + boxNeumann ℓ (k + m) x) := by
    intro x
    have h := boxNeumann_mul_of_le (ℓ := ℓ) hmk x
    nlinarith
  have hI1 : IntervalIntegrable (fun x : ℝ => boxNeumann ℓ (k - m) x) volume
      (-(ℓ / 2)) (ℓ / 2) := by
    exact (by unfold boxNeumann; fun_prop : Continuous fun x : ℝ =>
      boxNeumann ℓ (k - m) x).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun x : ℝ => boxNeumann ℓ (k + m) x) volume
      (-(ℓ / 2)) (ℓ / 2) := by
    exact (by unfold boxNeumann; fun_prop : Continuous fun x : ℝ =>
      boxNeumann ℓ (k + m) x).intervalIntegrable _ _
  calc
    (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x * boxNeumann ℓ m x)
        = ∫ x in (-(ℓ / 2))..(ℓ / 2),
            (1 / 2) * (boxNeumann ℓ (k - m) x + boxNeumann ℓ (k + m) x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hpmul x
    _ = (1 / 2) * (∫ x in (-(ℓ / 2))..(ℓ / 2),
            boxNeumann ℓ (k - m) x + boxNeumann ℓ (k + m) x) := by
            rw [intervalIntegral.integral_const_mul]
    _ = 0 := by
            rw [intervalIntegral.integral_add hI1 hI2]
            rw [boxNeumann_const_orthogonal hℓ hpos]
            rw [boxNeumann_const_orthogonal hℓ hkpm]
            norm_num

/-- **1-D distinct-mode orthogonality**: `∫_{−ℓ/2}^{ℓ/2} u_k·u_m = 0` for
`k ≠ m`. -/
lemma boxNeumann_distinct_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) {k m : ℕ} (hkm : k ≠ m) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x * boxNeumann ℓ m x) = 0 := by
  by_cases hmk : m ≤ k
  · have hmklt : m < k := lt_of_le_of_ne hmk (Ne.symm hkm)
    exact boxNeumann_mul_integral_of_le hℓ hmk (by omega)
  · have hkmle : k ≤ m := le_of_not_ge hmk
    have hkmlt : k < m := lt_of_le_of_ne hkmle hkm
    have hswap : (∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ k x * boxNeumann ℓ m x)
        = ∫ x in (-(ℓ / 2))..(ℓ / 2), boxNeumann ℓ m x * boxNeumann ℓ k x := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [hswap]
    exact boxNeumann_mul_integral_of_le hℓ hkmle (by omega)


/-- **3-D distinct-mode orthogonality (first coordinate differs)**: if the
two product modes differ in their coordinate-0 wave-numbers (`k₀ ≠ m₀`),
their product integrates to zero over the centred box (separability +
the 1-D `boxNeumann_distinct_orthogonal` at coordinate 0). -/
lemma boxNeumann3_orthogonal_first {ℓ : ℝ} (hℓ : 0 < ℓ)
    {k₀ k₁ k₂ m₀ m₁ m₂ : ℕ} (h : k₀ ≠ m₀) :
    (∫ x₀ in (-(ℓ / 2))..(ℓ / 2), ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
      ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
        (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂)
          * (boxNeumann ℓ m₀ x₀ * boxNeumann ℓ m₁ x₁ * boxNeumann ℓ m₂ x₂))
      = 0 := by
  -- pointwise rearrange the double product into the separable form
  have hpt : (fun x₀ : ℝ => ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
        ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
          (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ k₁ x₁ * boxNeumann ℓ k₂ x₂)
            * (boxNeumann ℓ m₀ x₀ * boxNeumann ℓ m₁ x₁ * boxNeumann ℓ m₂ x₂))
      = fun x₀ : ℝ => ∫ x₁ in (-(ℓ / 2))..(ℓ / 2),
          ∫ x₂ in (-(ℓ / 2))..(ℓ / 2),
            (boxNeumann ℓ k₀ x₀ * boxNeumann ℓ m₀ x₀)
              * (boxNeumann ℓ k₁ x₁ * boxNeumann ℓ m₁ x₁)
              * (boxNeumann ℓ k₂ x₂ * boxNeumann ℓ m₂ x₂) := by
    funext x₀
    apply intervalIntegral.integral_congr
    intro x₁ hx₁
    apply intervalIntegral.integral_congr
    intro x₂ hx₂
    ring
  have hfac := triple_separable_intervalIntegral (a := -(ℓ / 2)) (b := ℓ / 2)
    (fun x => boxNeumann ℓ k₀ x * boxNeumann ℓ m₀ x)
    (fun x => boxNeumann ℓ k₁ x * boxNeumann ℓ m₁ x)
    (fun x => boxNeumann ℓ k₂ x * boxNeumann ℓ m₂ x)
    (by unfold boxNeumann; fun_prop) (by unfold boxNeumann; fun_prop)
    (by unfold boxNeumann; fun_prop)
  rw [hpt]
  rw [hfac]
  rw [boxNeumann_distinct_orthogonal hℓ h]
  ring





/-- first derivative of the 1-D Neumann mode:
`(u_k)'(x) = -sin(A·(x+ℓ/2))·A`, `A := kπ/ℓ`. -/
lemma boxNeumann_hasDerivAt (ℓ : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (boxNeumann ℓ k)
      (-Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) * ((k : ℝ) * Real.pi / ℓ)) x := by
  let A : ℝ := (k : ℝ) * Real.pi / ℓ
  have hlin : HasDerivAt (fun y : ℝ => A * (y + ℓ / 2)) A x := by
    simpa using (((hasDerivAt_id x).add_const (ℓ / 2)).const_mul A)
  have hcos : HasDerivAt (Real.cos ∘ fun y : ℝ => A * (y + ℓ / 2))
      (A • (-Real.sin (A * (x + ℓ / 2)))) x := by
    simpa using (Real.hasDerivAt_cos (A * (x + ℓ / 2))).scomp x hlin
  have hfun : Real.cos ∘ (fun y : ℝ => A * (y + ℓ / 2)) = boxNeumann ℓ k := by
    funext y
    dsimp [boxNeumann, A]
  rw [hfun] at hcos
  have hval : A • (-Real.sin (A * (x + ℓ / 2)))
      = -Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) * ((k : ℝ) * Real.pi / ℓ) := by
    dsimp [A]
    ring
  rwa [hval] at hcos

/-- pointwise derivative expression -/
lemma boxNeumann_deriv (ℓ : ℝ) (k : ℕ) (x : ℝ) :
    deriv (boxNeumann ℓ k) x =
      -Real.sin (((k : ℝ) * Real.pi / ℓ) * (x + ℓ / 2)) * ((k : ℝ) * Real.pi / ℓ) :=
  (boxNeumann_hasDerivAt ℓ k x).deriv

/-- **eigen-bridge**: the second derivative of the 1-D Neumann mode is the
eigenidentity `(u_k)'' = -(kπ/ℓ)²·u_k` — the content the `fsKinCoeff` weight
acts on (`√−Δ` acts on `u_k` by `kπ/ℓ`). -/
lemma boxNeumann_deriv_two (ℓ : ℝ) (k : ℕ) (x : ℝ) :
    deriv (deriv (boxNeumann ℓ k)) x =
      - (((k : ℝ) * Real.pi / ℓ) ^ 2) * boxNeumann ℓ k x := by
  let A : ℝ := (k : ℝ) * Real.pi / ℓ
  have hder (y : ℝ) : deriv (boxNeumann ℓ k) y
      = -Real.sin (A * (y + ℓ / 2)) * A := by
    simpa [A] using (boxNeumann_hasDerivAt ℓ k y).deriv
  have hlin : HasDerivAt (fun y : ℝ => A * (y + ℓ / 2)) A x := by
    simpa using (((hasDerivAt_id x).add_const (ℓ / 2)).const_mul A)
  have hsinneg : HasDerivAt (fun y : ℝ => -Real.sin (A * (y + ℓ / 2)))
      (-(A • Real.cos (A * (x + ℓ / 2)))) x := by
    exact ((Real.hasDerivAt_sin (A * (x + ℓ / 2))).scomp x hlin).neg
  have houter : HasDerivAt (fun y : ℝ => -Real.sin (A * (y + ℓ / 2)) * A)
      ((-(A • Real.cos (A * (x + ℓ / 2)))) * A) x := by
    exact hsinneg.mul_const A
  have hfun : (fun y : ℝ => -Real.sin (A * (y + ℓ / 2)) * A)
      = fun y : ℝ => deriv (boxNeumann ℓ k) y := by
    funext y
    rw [hder y]
  rw [hfun] at houter
  change deriv (fun y : ℝ => deriv (boxNeumann ℓ k) y) x
      = - (((k : ℝ) * Real.pi / ℓ) ^ 2) * boxNeumann ℓ k x
  rw [houter.deriv]
  dsimp [A, boxNeumann]
  ring

/-- **Neumann boundary condition (left endpoint)**: the derivative of the
1-D mode vanishes at `−ℓ/2`. -/
lemma boxNeumann_deriv_endpoint_neg (ℓ : ℝ) (k : ℕ) :
    deriv (boxNeumann ℓ k) (-(ℓ / 2)) = 0 := by
  rw [boxNeumann_deriv]
  have h : -Real.sin (((k : ℝ) * Real.pi / ℓ) * (-(ℓ / 2) + ℓ / 2)) * ((k : ℝ) * Real.pi / ℓ) = 0 := by
    have harg : ((k : ℝ) * Real.pi / ℓ) * (-(ℓ / 2) + ℓ / 2) = 0 := by ring
    rw [harg, Real.sin_zero]
    ring
  exact h

/-- **Neumann boundary condition (right endpoint)**: the derivative of the
1-D mode vanishes at `ℓ/2`. -/
lemma boxNeumann_deriv_endpoint_pos {ℓ : ℝ} (hℓ : ℓ ≠ 0) (k : ℕ) :
    deriv (boxNeumann ℓ k) (ℓ / 2) = 0 := by
  rw [boxNeumann_deriv]
  have hA : ((k : ℝ) * Real.pi / ℓ) * (ℓ / 2 + ℓ / 2) = (k : ℝ) * Real.pi := by
    field_simp [hℓ]
    ring
  rw [hA, Real.sin_nat_mul_pi]
  ring



end Submission.BoseGases
