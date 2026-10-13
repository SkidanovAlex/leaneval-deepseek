/-
# `row15_FstarRadial` — the radial profile bound of row 15

The iterated `D_z`-jets of the fundamental-model profile `F_* (z) = 2z/(1+z)²` are bounded by
`C·z/(1+z)²` on the whole half-line `z > 0`, up to order `4`:

  `|D_z^m (fun z _ => F_* z) (z,θ)| ≤ C z/(1+z)²`,   `m ≤ 4`, `z > 0`.

This is the radial input of row 15 of the nonlinear estimate table (§3.4 of the design): the
sibling `row15_PthFstarMixed` controls `mixed l m (∂_θ F_*)` by
`Γ(θ)/sin(2θ) · |(OpZ^[l]) F_* (z)|` (`OpZ = z∂_z`, the one-variable slice of `D_z`), so the
profile has to be small at *both* ends of the radial half-line.

## Route

`DzIter m (fun z _ => F_* z) z θ = (T1^[m]) F_* z`, where `T1 u z = z·u'(z)`
(`Work.FTS.LocData.DzIter_Fstar_eq_T1`), so the statement is about the iterates of a single
one-variable operator acting on `F_*`.

* **Far field** `z ≥ 1`.  The delivered `Work.FTS.LocData.DzIter_FM_Fstar_abs_le` (constant
  `1000`) gives `|(T1^[m]) F_* z| ≤ C/z` for `m ≤ 4`, and `1/z ≤ 4z/(1+z)²` for `z ≥ 1`.

* **Near field** `0 < z ≤ 1`.  The profile is *invariant under the inversion* `z ↦ 1/z`
  (`F_* (1/z) = F_* z`) and `T1` changes sign under it, `T1 (u ∘ inv) = -(T1 u) ∘ inv`, so

    `(T1^[m]) F_* z = (-1)^m (T1^[m]) F_* (1/z)`   for `z > 0`

  (`row15Fstar_T1_iter_symm`).  Applying the *far* estimate at `1/z ≥ 1` gives
  `|(T1^[m]) F_* z| ≤ C·z` for `0 < z ≤ 1`, and `z ≤ 4z/(1+z)²` there.

The symmetry is an induction on `m`, maintaining `C^∞`-regularity of `(T1^[m]) F_*` on the
open half-line `(0,∞)` (it is needed for the chain rule of `u ↦ u(1/z)`): `ContDiffOn ℝ ∞` is
preserved by `T1` because it is preserved by `deriv` on an open set
(`ContDiffOn.deriv_of_isOpen`) and by multiplication.  The sign identity itself is the
pointwise derivative of the inverse, `deriv (u ∘ inv) z = deriv u (1/z)·(-(z²)⁻¹)`
(`deriv_comp` + `deriv_inv`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-- The honest `C^∞` order for `ContDiffOn` (in this library the plain `⊤` is the *analytic*
order `ω`; the coercion of `⊤ : ℕ∞` is `C^∞`). -/
private abbrev SmO : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **Inversion invariance of the profile**: `F_* (1/z) = F_* z` for `z ≠ 0`
(at `z = 0` both sides are `0`). -/
theorem row15Fstar_one_div (z : ℝ) : Work.FM.Fstar (1 / z) = Work.FM.Fstar z := by
  unfold Work.FM.Fstar
  rcases eq_or_ne z 0 with rfl | hz
  · norm_num
  · field_simp
    ring

/-- `F_*` is `C^∞` on `(0,∞)`. -/
theorem row15Fstar_contDiffOn :
    ContDiffOn ℝ SmO (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
  rw [show (fun z : ℝ => Work.FM.Fstar z) = (fun z : ℝ => 2 * z / (1 + z) ^ 2) from by
    funext z; rw [Work.FM.Fstar]]
  apply ContDiffOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have : 0 < 1 + x := by linarith [Set.mem_Ioi.mp hx]
    positivity

/-- `C^∞`-functions on the open half-line have `C^∞` derivatives. -/
private theorem row15Fstar_deriv_contDiffOn {u : ℝ → ℝ}
    (h : ContDiffOn ℝ SmO u (Set.Ioi 0)) : ContDiffOn ℝ SmO (deriv u) (Set.Ioi 0) :=
  h.deriv_of_isOpen isOpen_Ioi (by simp [SmO])

/-- All the `T1`-iterates of the profile are `C^∞` on `(0,∞)`.  (`T1 u = z·u'` is `z` times
the derivative of `u`, so this is an immediate induction using
`row15Fstar_deriv_contDiffOn`.) -/
theorem row15Fstar_T1_iter_contDiffOn (m : ℕ) :
    ContDiffOn ℝ SmO ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) (Set.Ioi 0) := by
  induction m with
  | zero => simpa using row15Fstar_contDiffOn
  | succ m ih =>
      rw [Function.iterate_succ']
      show ContDiffOn ℝ SmO
        (fun z => z * deriv ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) z) (Set.Ioi 0)
      exact contDiffOn_id.mul (row15Fstar_deriv_contDiffOn ih)

/-- The chain rule for the inversion: `d/dz (u(1/z)) = u'(1/z)·(-(z²)⁻¹)`. -/
private theorem row15Fstar_deriv_comp_inv {u : ℝ → ℝ} {z : ℝ} (hz : z ≠ 0)
    (hd : DifferentiableAt ℝ u z⁻¹) :
    deriv (fun w => u (w⁻¹)) z = deriv u (z⁻¹) * (-(z ^ 2)⁻¹) := by
  have hinv : DifferentiableAt ℝ (fun w : ℝ => w⁻¹) z := differentiableAt_inv hz
  have h1 : (fun w : ℝ => u (w⁻¹)) = u ∘ (fun w : ℝ => w⁻¹) := rfl
  rw [h1, deriv_comp z hd hinv, deriv_inv]

/-- **The inversion symmetry of the `T1`-iterates**: for `z > 0`,
`(T1^[m]) F_* z = (-1)^m (T1^[m]) F_* (1/z)`.  It is the statement that `T1` intertwines the
inversion with a sign, `T1 (u ∘ inv) = -(T1 u) ∘ inv`, which holds because the inversion
reverses the orientation. -/
theorem row15Fstar_T1_iter_symm (m : ℕ) :
    Set.EqOn ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar)
      (fun z => (-1 : ℝ) ^ m * (Work.FTS.LocData.T1F^[m]) Work.FM.Fstar z⁻¹) (Set.Ioi 0) := by
  induction m with
  | zero =>
      intro z _
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
      rw [← one_div]
      exact (row15Fstar_one_div z).symm
  | succ m ih =>
      intro z hz
      have hzpos : 0 < z := Set.mem_Ioi.mp hz
      have hz0 : z ≠ 0 := ne_of_gt hzpos
      have hzI : z⁻¹ ∈ Set.Ioi (0 : ℝ) := by
        rw [Set.mem_Ioi]; exact inv_pos.mpr hzpos
      -- differentiate the induction hypothesis at `z`
      have hderiv : deriv ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) z
          = deriv (fun w => (-1 : ℝ) ^ m * (Work.FTS.LocData.T1F^[m]) Work.FM.Fstar w⁻¹) z :=
        ih.deriv isOpen_Ioi hz
      have hd_at : DifferentiableAt ℝ ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) z⁻¹ :=
        ((row15Fstar_T1_iter_contDiffOn m).differentiableOn (by simp [SmO])).differentiableAt
          (isOpen_Ioi.mem_nhds hzI)
      have hdiff : DifferentiableAt ℝ
          ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar ∘ fun w : ℝ => w⁻¹) z :=
        hd_at.comp z (differentiableAt_inv hz0)
      rw [Function.iterate_succ']
      show z * deriv ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) z
        = (-1 : ℝ) ^ (m + 1) * (z⁻¹ * deriv ((Work.FTS.LocData.T1F^[m]) Work.FM.Fstar) z⁻¹)
      rw [hderiv]
      have hc : deriv (fun w => (-1 : ℝ) ^ m * (Work.FTS.LocData.T1F^[m]) Work.FM.Fstar w⁻¹) z
          = (-1 : ℝ) ^ m
            * deriv (fun w => (Work.FTS.LocData.T1F^[m]) Work.FM.Fstar w⁻¹) z :=
        deriv_const_mul _ hdiff
      rw [hc, row15Fstar_deriv_comp_inv hz0 hd_at, pow_succ]
      field_simp
      ring

/-- **The near-field bound**: `|D_z^m (fun z _ => F_* z) (z,θ)| ≤ K·z` for `0 < z ≤ 1`, `m ≤ 4`.
This is the far-field estimate `Work.FTS.LocData.DzIter_FM_Fstar_abs_le` read through the
inversion symmetry: at `1/z ≥ 1` it gives `|(T1^[m]) F_* (1/z)| ≤ C/(1/z) = C·z`. -/
theorem row15Fstar_near_bound : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), m ≤ 4 → ∀ (z θ : ℝ), 0 < z →
    z ≤ 1 → |Work.Spaces.DzIter m (fun z (_ : ℝ) => Work.FM.Fstar z) z θ| ≤ K * z := by
  obtain ⟨C, hC⟩ := Work.FTS.LocData.DzIter_FM_Fstar_abs_le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro m hm z θ hz hz1
  have hzi : (1 : ℝ) ≤ z⁻¹ := (one_le_inv₀ hz).mpr hz1
  have hsym := row15Fstar_T1_iter_symm m hz
  rw [Work.FTS.LocData.DzIter_Fstar_eq_T1 m θ z, hsym, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  have hfar : |(Work.FTS.LocData.T1F^[m]) Work.FM.Fstar z⁻¹| ≤ C * z := by
    have h := hC m hm z⁻¹ hzi θ
    rw [Work.FTS.LocData.DzIter_Fstar_eq_T1 m θ z⁻¹, div_inv_eq_mul] at h
    exact h
  exact le_trans hfar (mul_le_mul_of_nonneg_right (le_max_left C 1) hz.le)

theorem row15_FstarRadial : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ 4 → ∀ (z θ : ℝ), 0 < z → |Work.Spaces.DzIter m (fun z (_ : ℝ) => Work.FM.Fstar z) z θ| ≤ C * z / (1 + z) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := row15Fstar_near_bound
  obtain ⟨Cf, hCf⟩ := Work.FTS.LocData.DzIter_FM_Fstar_abs_le
  refine ⟨max (4 * K) (4 * max Cf 1), lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro m hm z θ hz
  -- `1 + z > 0`, so both `z/(1+z)²` and the two comparison factors are nonnegative
  have hden : 0 < (1 + z) ^ 2 := by positivity
  have hzdiv : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz.le hden.le
  by_cases hle : z ≤ 1
  · -- near field: `z ≤ 1`, use `K·z ≤ 4K·z/(1+z)²` from `(1+z)² ≤ 4`
    have h1 := hK m hm z θ hz hle
    have h4 : (1 + z) ^ 2 ≤ 4 := by nlinarith
    have hd : z / 4 ≤ z / (1 + z) ^ 2 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hden]
      nlinarith
    rw [mul_div_assoc]
    calc |Work.Spaces.DzIter m (fun z (_ : ℝ) => Work.FM.Fstar z) z θ| ≤ K * z := h1
      _ = 4 * K * (z / 4) := by ring
      _ ≤ 4 * K * (z / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ max (4 * K) (4 * max Cf 1) * (z / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hzdiv
  · -- far field: `1 < z`, use `Cf/z ≤ 4Cf·z/(1+z)²` from `(1+z)² ≤ 4z²`
    have hz1 : (1 : ℝ) ≤ z := le_of_lt (not_le.mp hle)
    have h1 := hCf m hm z hz1 θ
    have hMn : (0 : ℝ) ≤ max Cf 1 := le_trans zero_le_one (le_max_right Cf 1)
    have hd : (1 : ℝ) / z ≤ 4 * z / (1 + z) ^ 2 := by
      rw [div_le_div_iff₀ hz hden]
      nlinarith
    rw [mul_div_assoc]
    calc |Work.Spaces.DzIter m (fun z (_ : ℝ) => Work.FM.Fstar z) z θ| ≤ Cf / z := h1
      _ ≤ max Cf 1 / z := div_le_div_of_nonneg_right (le_max_left Cf 1) hz.le
      _ = max Cf 1 * (1 / z) := by rw [mul_one_div]
      _ ≤ max Cf 1 * (4 * z / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hd hMn
      _ = 4 * max Cf 1 * (z / (1 + z) ^ 2) := by ring
      _ ≤ max (4 * K) (4 * max Cf 1) * (z / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hzdiv

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
