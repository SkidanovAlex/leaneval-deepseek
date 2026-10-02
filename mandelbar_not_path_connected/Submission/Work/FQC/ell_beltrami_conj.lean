/-
# `Work.FQC.ell_beltrami_conj`

The MNS twist `ℓ_t (x + iy) = x + i(y + t · saw x)` of the Écalle cylinder
(`Work.FQC.ell`, `Submission/Work/FQC/Defs.lean`) commutes with the reflection

  `σ w = conj w + 1/2`

of the cylinder, because the triangle wave is antiperiodic: `saw (x + 1/2) = -saw x`
(`Work.FQC.saw_add_half`).  This file upgrades that commutation to the level of complex
dilatations:

  `μ_{ℓ_t} (σ w) = conj (μ_{ℓ_t} w)   for almost every `w`,

which is what makes the invariant Beltrami coefficient `μ_Q` (`Work.FQC.muQC`) compatible
with the antiholomorphic symmetry `T_c(z) = z̄² + c`: it says that the coefficient pulled
back from the cylinder by an *antiholomorphic* Fatou coordinate is invariant under the
reflection `σ` that the symmetry induces on the cylinder.

## The two ingredients

*Commutativity of the differential.*  `ℓ_t ∘ σ = σ ∘ ℓ_t` as functions, and `σ` is an
antiholomorphic isometry with `∂σ = 0`, `∂̄σ = 1`.  The Wirtinger chain rules
(`Work.MRMT.Wirtinger.dz_comp`, `dzbar_comp`) applied to both sides of

  `∂(ℓ∘σ) = ∂(σ∘ℓ)`,  `∂̄(ℓ∘σ) = ∂̄(σ∘ℓ)`

give `∂ℓ (σ w) = conj (∂ℓ w)` and `∂̄ℓ (σ w) = conj (∂̄ℓ w)` at every point where `ℓ_t` is
real differentiable at `w` and at `σ w`; the identity for `μ = ∂̄ℓ / ∂ℓ` follows because
conjugation is multiplicative.

*Almost everywhere differentiability.*  `ℓ_t` is Lipschitz (the triangle wave is
2-Lipschitz), so by Rademacher's theorem (`LipschitzWith.ae_differentiableAt`, a theorem of
Mathlib) it is real differentiable a.e.; composing with `σ` and its smooth inverse
`σ⁻¹ w = conj w - 1/2` transports this to a.e. differentiability at `σ w`.

Nothing here is specific to the twist: `beltramiOf_sigmaCyl_conj` proves the conjugation
identity for an arbitrary real differentiable map commuting with `σ`.
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.saw_add_half
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.FQC

open Work.MRMT.Wirtinger

/-! ## 1. The reflection `σ w = conj w + 1/2` of the Écalle cylinder -/

/-- The antiholomorphic involution (on the cylinder `ℂ/ℤ`) of the Écalle coordinate:
`σ w = conj w + 1/2`.  It reverses orientation and satisfies `σ (σ w) = w + 1`. -/
def sigmaCyl (w : ℂ) : ℂ := star w + 1/2

@[simp] theorem sigmaCyl_apply (w : ℂ) : sigmaCyl w = star w + 1/2 := rfl

theorem sigmaCyl_re (w : ℂ) : (sigmaCyl w).re = w.re + 1/2 := by
  simp [sigmaCyl]

theorem sigmaCyl_sigmaCyl (w : ℂ) : sigmaCyl (sigmaCyl w) = w + 1 := by
  simp only [sigmaCyl, star_add, star_star]
  rw [show star ((1 : ℂ)/2) = (1 : ℂ)/2 from by norm_num [Complex.star_def]]
  ring

theorem sigmaCyl_inv (w : ℂ) : sigmaCyl (star w - 1/2) = w := by
  simp [sigmaCyl]

/-! ## 2. The twist commutes with the reflection -/

/-- `ℓ_t ∘ σ = σ ∘ ℓ_t`: the twist commutes with the reflection of the cylinder, because
it only shifts the imaginary part, by a function of the real part which is antiperiodic. -/
theorem ell_sigmaCyl (t : ℝ) (w : ℂ) : ell t (sigmaCyl w) = sigmaCyl (ell t w) := by
  have h : saw (w.re + 1 / 2) = - (saw w.re) := saw_add_half w.re
  have hre : (sigmaCyl w).re = w.re + 1 / 2 := sigmaCyl_re w
  simp only [ell]
  rw [hre, h]
  simp only [sigmaCyl]
  simp
  ring

/-! ## 3. Lipschitz bounds -/

/-- The distance from `y` to the half-integers, `|fract y - 1/2|`, is bounded by the
distance from `y` to any half-integer `k + 1/2`. -/
theorem fract_abs_sub_half_le (y : ℝ) (k : ℤ) :
    |Int.fract y - 1/2| ≤ |y - ((k : ℝ) + 1/2)| := by
  have hle : |Int.fract y - 1/2| ≤ 1/2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [Int.fract_nonneg y, Int.fract_lt_one y]
  have hsplit : y - ((k : ℝ) + 1/2) =
      (Int.fract y - 1/2) + ((⌊y⌋ : ℝ) - (k : ℝ)) := by
    linarith [Int.fract_add_floor y]
  rcases eq_or_ne (⌊y⌋ : ℤ) k with hk | hk
  · subst hk
    rw [hsplit]; simp
  · have hd : (1 : ℝ) ≤ |(⌊y⌋ : ℝ) - (k : ℝ)| := by
      have hcast : (⌊y⌋ : ℝ) - (k : ℝ) = ((⌊y⌋ - k : ℤ) : ℝ) := by push_cast; ring
      rw [hcast, ← Int.cast_abs]
      have hne : ⌊y⌋ - k ≠ 0 := sub_ne_zero.mpr hk
      exact_mod_cast Int.one_le_abs hne
    rw [hsplit, add_comm]
    have h1 : |((⌊y⌋ : ℝ) - (k : ℝ))| - |-(Int.fract y - 1/2)| ≤
        |((⌊y⌋ : ℝ) - (k : ℝ)) - (-(Int.fract y - 1/2))| := abs_sub_abs_le_abs_sub _ _
    rw [abs_neg, sub_neg_eq_add] at h1
    linarith

/-- `y ↦ |fract y - 1/2|` is 1-Lipschitz: it is the distance to the set of half-integers. -/
theorem absFractHalf_lipschitz :
    LipschitzWith 1 (fun y : ℝ => |Int.fract y - 1/2|) := by
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  have hAa : |Int.fract a - 1/2| = |a - ((⌊a⌋ : ℝ) + 1/2)| := by
    congr 1; linarith [Int.fract_add_floor a]
  have hAb : |Int.fract b - 1/2| = |b - ((⌊b⌋ : ℝ) + 1/2)| := by
    congr 1; linarith [Int.fract_add_floor b]
  rw [abs_sub_le_iff]
  constructor
  · have hB := fract_abs_sub_half_le a ⌊b⌋
    calc |Int.fract a - 1/2| - |Int.fract b - 1/2|
        ≤ |a - ((⌊b⌋ : ℝ) + 1/2)| - |b - ((⌊b⌋ : ℝ) + 1/2)| := sub_le_sub hB hAb.ge
      _ ≤ |a - b| := by
          have h := abs_sub_abs_le_abs_sub (a - ((⌊b⌋ : ℝ) + 1/2)) (b - ((⌊b⌋ : ℝ) + 1/2))
          rw [show (a - ((⌊b⌋ : ℝ) + 1/2)) - (b - ((⌊b⌋ : ℝ) + 1/2)) = a - b by ring] at h
          exact h
  · have hB := fract_abs_sub_half_le b ⌊a⌋
    calc |Int.fract b - 1/2| - |Int.fract a - 1/2|
        ≤ |b - ((⌊a⌋ : ℝ) + 1/2)| - |a - ((⌊a⌋ : ℝ) + 1/2)| := sub_le_sub hB hAa.ge
      _ ≤ |b - a| := by
          have h := abs_sub_abs_le_abs_sub (b - ((⌊a⌋ : ℝ) + 1/2)) (a - ((⌊a⌋ : ℝ) + 1/2))
          rw [show (b - ((⌊a⌋ : ℝ) + 1/2)) - (a - ((⌊a⌋ : ℝ) + 1/2)) = b - a by ring] at h
          exact h
      _ = |a - b| := abs_sub_comm b a

/-- The triangle wave is 2-Lipschitz: it is `1/2 - 2 |fract (· + 1/4) - 1/2|`. -/
theorem saw_lipschitz_aux : LipschitzWith 2 (saw : ℝ → ℝ) := by
  have hdecomp : saw = (fun y : ℝ => 1/2 - 2*y) ∘
      ((fun y : ℝ => |Int.fract y - 1/2|) ∘ (fun x : ℝ => x + 1/4)) := by
    funext x
    simp only [Function.comp_apply, saw_apply]
  have h1 : LipschitzWith 1 (fun x : ℝ => x + 1/4) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show a + 1/4 - (b + 1/4) = a - b by ring]
  have h2 : LipschitzWith 2 (fun y : ℝ => 1/2 - 2*y) := by
    refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
    rw [show (1/2 - 2*a) - (1/2 - 2*b) = -(2*(a-b)) by ring, abs_neg, abs_mul]
    norm_num
  have hcomp : LipschitzWith (2 * (1 * 1)) ((fun y : ℝ => 1/2 - 2*y) ∘
      ((fun y : ℝ => |Int.fract y - 1/2|) ∘ (fun x : ℝ => x + 1/4))) :=
    LipschitzWith.comp h2 (LipschitzWith.comp absFractHalf_lipschitz h1)
  rw [hdecomp]
  simpa using hcomp

/-- The reflection `σ` of the cylinder is an isometry, hence 1-Lipschitz. -/
theorem lipschitzWith_sigmaCyl : LipschitzWith 1 sigmaCyl := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h : sigmaCyl x - sigmaCyl y = star (x - y) := by
    simp only [sigmaCyl, star_sub]
    ring
  rw [h, norm_star]

/-- The twist `ℓ_t` is Lipschitz, with constant `1 + 2|t|`. -/
theorem lipschitzWith_ell_twist (t : ℝ) :
    LipschitzWith (Real.toNNReal (1 + 2 * |t|)) (ell t) := by
  refine LipschitzWith.of_dist_le_mul (fun w w' => ?_)
  rw [dist_eq_norm, dist_eq_norm,
    Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 1 + 2 * |t|)]
  have hsub : ell t w - ell t w' =
      (w - w') + ((t * (saw w.re - saw w'.re) : ℝ) : ℂ) * Complex.I := by
    simp only [ell]; push_cast; ring
  rw [hsub]
  have hnorm : ‖(((t * (saw w.re - saw w'.re)) : ℝ) : ℂ)‖
      = |t * (saw w.re - saw w'.re)| := RCLike.norm_ofReal _
  have h' : |saw w.re - saw w'.re| ≤ 2 * |w.re - w'.re| := by
    have h := saw_lipschitz_aux.dist_le_mul w.re w'.re
    rw [Real.dist_eq, Real.dist_eq] at h
    simpa using h
  have hre : |w.re - w'.re| ≤ ‖w - w'‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  calc ‖(w - w') + ((t * (saw w.re - saw w'.re) : ℝ) : ℂ) * Complex.I‖
      ≤ ‖w - w'‖ + ‖((t * (saw w.re - saw w'.re) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖w - w'‖ + |t| * |saw w.re - saw w'.re| := by
        rw [norm_mul, Complex.norm_I, mul_one, hnorm, abs_mul]
    _ ≤ ‖w - w'‖ + |t| * (2 * |w.re - w'.re|) :=
        add_le_add_right (mul_le_mul_of_nonneg_left h' (abs_nonneg t)) ‖w - w'‖
    _ ≤ ‖w - w'‖ + |t| * (2 * ‖w - w'‖) :=
        add_le_add_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hre (by norm_num)) (abs_nonneg t)) ‖w - w'‖
    _ = (1 + 2 * |t|) * ‖w - w'‖ := by ring

/-! ## 4. Almost everywhere differentiability of the twist -/

/-- `ℓ_t` is real differentiable almost everywhere (Rademacher's theorem, since it is
Lipschitz). -/
theorem ae_differentiableAt_ell_twist (t : ℝ) :
    ∀ᵐ w ∂(volume : Measure ℂ), DifferentiableAt ℝ (ell t) w :=
  (lipschitzWith_ell_twist t).ae_differentiableAt

/-- `ℓ_t` is real differentiable a.e. also at the reflected point `σ w`.

Since `σ` is only an isometry up to a translation, this is not immediate from
`ae_differentiableAt_ell_twist`; instead we apply Rademacher to the composition
`ℓ_t ∘ σ` (also Lipschitz) and compose with the smooth inverse `σ⁻¹ w = conj w - 1/2`. -/
theorem ae_differentiableAt_ell_twist_sigmaCyl (t : ℝ) :
    ∀ᵐ w ∂(volume : Measure ℂ), DifferentiableAt ℝ (ell t) (sigmaCyl w) := by
  have hσ : ∀ᵐ w ∂(volume : Measure ℂ), DifferentiableAt ℝ ((ell t) ∘ sigmaCyl) w :=
    ((lipschitzWith_ell_twist t).comp lipschitzWith_sigmaCyl).ae_differentiableAt
  filter_upwards [hσ] with w hw
  have hψ : DifferentiableAt ℝ (fun y : ℂ => star y - 1/2) (sigmaCyl w) :=
    (differentiableAt_star (sigmaCyl w)).sub_const (1/2)
  have key : DifferentiableAt ℝ (((ell t) ∘ sigmaCyl) ∘ (fun y : ℂ => star y - 1/2))
      (sigmaCyl w) := by
    refine DifferentiableAt.comp (x := sigmaCyl w) ?_ hψ
    rw [show star (sigmaCyl w) - 1/2 = w from by simp [sigmaCyl]]
    exact hw
  have heq : ((ell t) ∘ sigmaCyl) ∘ (fun y : ℂ => star y - 1/2) = ell t := by
    funext y
    simp only [Function.comp_apply]
    rw [show sigmaCyl (star y - 1/2) = y from sigmaCyl_inv y]
  rwa [heq] at key

/-! ## 5. The Wirtinger derivatives of `σ` -/

theorem dz_translate_right (c z : ℂ) : Work.MRMT.dz (fun y : ℂ => y + c) z = 1 := by
  have h : fderiv ℝ (fun y : ℂ => y + c) z = 1 := by
    rw [fderiv_add_const c]; exact fderiv_id
  simp only [Work.MRMT.dz, h, one_apply_eq_self]
  rw [Complex.I_mul_I]; norm_num

theorem dz_translate_left (c z : ℂ) : Work.MRMT.dz (fun y : ℂ => c + y) z = 1 := by
  have h : fderiv ℝ (fun y : ℂ => c + y) z = 1 := by
    rw [fderiv_const_add c]; exact fderiv_id
  simp only [Work.MRMT.dz, h, one_apply_eq_self]
  rw [Complex.I_mul_I]; norm_num

theorem dzbar_translate_right (c z : ℂ) : Work.MRMT.dzbar (fun y : ℂ => y + c) z = 0 := by
  have h : fderiv ℝ (fun y : ℂ => y + c) z = 1 := by
    rw [fderiv_add_const c]; exact fderiv_id
  simp only [Work.MRMT.dzbar, h, one_apply_eq_self]
  rw [Complex.I_mul_I]; norm_num

theorem dzbar_translate_left (c z : ℂ) : Work.MRMT.dzbar (fun y : ℂ => c + y) z = 0 := by
  have h : fderiv ℝ (fun y : ℂ => c + y) z = 1 := by
    rw [fderiv_const_add c]; exact fderiv_id
  simp only [Work.MRMT.dzbar, h, one_apply_eq_self]
  rw [Complex.I_mul_I]; norm_num

theorem dz_sigmaCyl (z : ℂ) : Work.MRMT.dz sigmaCyl z = 0 := by
  have hcomp : sigmaCyl = (fun y : ℂ => y + 1/2) ∘ (star : ℂ → ℂ) := rfl
  rw [hcomp, Work.MRMT.Wirtinger.dz_comp]
  · simp only [Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star,
      dz_translate_right, dzbar_translate_right]
    simp
  · exact (differentiableAt_id (x := star z)).add_const (1/2 : ℂ)
  · exact differentiableAt_star z

theorem dzbar_sigmaCyl (z : ℂ) : Work.MRMT.dzbar sigmaCyl z = 1 := by
  have hcomp : sigmaCyl = (fun y : ℂ => y + 1/2) ∘ (star : ℂ → ℂ) := rfl
  rw [hcomp, Work.MRMT.Wirtinger.dzbar_comp]
  · simp only [Work.MRMT.Wirtinger.dz_star, Work.MRMT.Wirtinger.dzbar_star,
      dz_translate_right, dzbar_translate_right]
    simp
  · exact (differentiableAt_id (x := star z)).add_const (1/2 : ℂ)
  · exact differentiableAt_star z

theorem differentiableAt_sigmaCyl (z : ℂ) : DifferentiableAt ℝ sigmaCyl z := by
  have hcomp : sigmaCyl = (fun y : ℂ => y + 1/2) ∘ (star : ℂ → ℂ) := rfl
  rw [hcomp]
  exact ((differentiableAt_id (x := star z)).add_const (1/2 : ℂ)).comp z
    (differentiableAt_star z)

/-! ## 6. The conjugation identity for a map commuting with `σ` -/

/-- If a real differentiable map `F` commutes with the reflection `σ`, then its complex
dilatation is conjugated by `σ`: `μ_F (σ w) = conj (μ_F w)`.

This is the whole content of the commutation, and it is proved without knowing anything
about `F` beyond differentiability at `w` and at `σ w`: the Wirtinger chain rules applied
to the two sides of `F ∘ σ = σ ∘ F` give `∂F (σ w) = conj (∂F w)` and
`∂̄F (σ w) = conj (∂̄F w)`. -/
theorem beltramiOf_sigmaCyl_conj {F : ℂ → ℂ} {w : ℂ}
    (hw : DifferentiableAt ℝ F w) (hσw : DifferentiableAt ℝ F (sigmaCyl w))
    (hcomm : F ∘ sigmaCyl = sigmaCyl ∘ F) :
    Work.MRMT.beltramiOf F (sigmaCyl w) = star (Work.MRMT.beltramiOf F w) := by
  have h1 : Work.MRMT.dz (F ∘ sigmaCyl) w = Work.MRMT.dzbar F (sigmaCyl w) := by
    rw [Work.MRMT.Wirtinger.dz_comp hσw (differentiableAt_sigmaCyl w), dz_sigmaCyl,
      dzbar_sigmaCyl]
    simp
  have h2 : Work.MRMT.dzbar (F ∘ sigmaCyl) w = Work.MRMT.dz F (sigmaCyl w) := by
    rw [Work.MRMT.Wirtinger.dzbar_comp hσw (differentiableAt_sigmaCyl w), dz_sigmaCyl,
      dzbar_sigmaCyl]
    simp
  have h3 : Work.MRMT.dz (sigmaCyl ∘ F) w = star (Work.MRMT.dzbar F w) := by
    rw [Work.MRMT.Wirtinger.dz_comp (differentiableAt_sigmaCyl (F w)) hw, dz_sigmaCyl,
      dzbar_sigmaCyl]
    simp
  have h4 : Work.MRMT.dzbar (sigmaCyl ∘ F) w = star (Work.MRMT.dz F w) := by
    rw [Work.MRMT.Wirtinger.dzbar_comp (differentiableAt_sigmaCyl (F w)) hw, dz_sigmaCyl,
      dzbar_sigmaCyl]
    simp
  have e1 : Work.MRMT.dzbar F (sigmaCyl w) = star (Work.MRMT.dzbar F w) := by
    rw [← h1, hcomm]; exact h3
  have e2 : Work.MRMT.dz F (sigmaCyl w) = star (Work.MRMT.dz F w) := by
    rw [← h2, hcomm]; exact h4
  rw [Work.MRMT.beltramiOf, Work.MRMT.beltramiOf, e1, e2, Complex.star_def]
  exact (map_div₀ (starRingEnd ℂ) (Work.MRMT.dzbar F w) (Work.MRMT.dz F w)).symm

/-! ## 7. The target: `μ_{ℓ_t} (conj w + 1/2) = conj (μ_{ℓ_t} w)` a.e. -/

theorem ell_beltrami_conj (t : ℝ) : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Work.MRMT.beltramiOf (Work.FQC.ell t) (star w + 1 / 2) = star (Work.MRMT.beltramiOf (Work.FQC.ell t) w) := by
  have hcomm : (ell t) ∘ sigmaCyl = sigmaCyl ∘ (ell t) :=
    funext (ell_sigmaCyl t)
  filter_upwards [ae_differentiableAt_ell_twist t, ae_differentiableAt_ell_twist_sigmaCyl t]
    with w hw hσw
  exact beltramiOf_sigmaCyl_conj hw hσw hcomm

end Work.FQC

end
