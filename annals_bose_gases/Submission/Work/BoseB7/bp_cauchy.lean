import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7.FockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.bp_cauchy` — Cauchy–Schwarz and Young for the Fock form

The Fock form `F.bp` of the `B4` interface (`Work.BoseB7.FockDefs`) is a
symmetric, positive semidefinite, definite bilinear form on `F.H`; every
estimate of FS §10 uses the resulting Cauchy–Schwarz inequality

  `2 ⟨f,g⟩ ≤ ε ⟨f,f⟩ + ε⁻¹ ⟨g,g⟩`  for all `ε > 0`

(`f = g = Φ` with `ε = 1` is the plain `2⟨Φ,Ψ⟩ ≤ ‖Φ‖² + ‖Ψ‖²` of the paper).

The proof has three independent steps, isolated as lemmas:

* `bp_cauchy_sq` — the *squared* Cauchy–Schwarz inequality
  `⟨f,g⟩² ≤ ⟨f,f⟩·⟨g,g⟩`.  It is the classical discriminant argument: the
  semidefiniteness `⟨u,u⟩ ≥ 0` applied to the trial vector
  `u = ⟨f,g⟩·f - ⟨f,f⟩·g` gives `⟨f,f⟩·(⟨f,f⟩⟨g,g⟩ - ⟨f,g⟩²) ≥ 0`, and either
  `⟨f,f⟩ > 0` (divide) or `⟨f,f⟩ = 0`, in which case definiteness gives `f = 0`
  and hence `⟨f,g⟩ = 0`.

* `bp_cauchy_abs` — the absolute-value form
  `|⟨f,g⟩| ≤ √⟨f,f⟩·√⟨g,g⟩`, from `bp_cauchy_sq` and `|x| = √(x²)`.

* `two_mul_le_eps_inv` — the arithmetic (Young) inequality
  `2XY ≤ εX² + ε⁻¹Y²` for `ε > 0`, whose content is
  `εX² + ε⁻¹Y² - 2XY = ε(X - Y/ε)² ≥ 0`.

The main theorem is then the composition of the last two, with
`X = √⟨f,f⟩`, `Y = √⟨g,g⟩` and `sq_sqrt`.

No structure of `Mode` beyond `AddCommGroup`/`Fintype` is used, and no
positivity of the `ccrK` kernel is needed: the statement is pure positivity of
the Fock form.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

/-- **Young's inequality with the complementary factor `ε⁻¹`**: for `ε > 0` and
all reals `X, Y`, `2XY ≤ εX² + ε⁻¹Y²`.  The difference of the two sides is
`ε(X - Y/ε)²` (up to reordering), so no hypothesis on the signs of `X, Y` is
needed.  This is the arithmetic half of `bp_cauchy`; it is applied there to
`X = √⟨f,f⟩`, `Y = √⟨g,g⟩`. -/
lemma two_mul_le_eps_inv {ε : ℝ} (hε : 0 < ε) (X Y : ℝ) :
    2 * X * Y ≤ ε * X^2 + ε⁻¹ * Y^2 := by
  have h : 0 ≤ ε * (X - Y / ε)^2 := mul_nonneg (le_of_lt hε) (sq_nonneg _)
  have hexp : ε * (X - Y / ε)^2 = ε * X^2 - 2 * X * Y + ε⁻¹ * Y^2 := by
    field_simp
    ring
  linarith [h, hexp]

/-- **Squared Cauchy–Schwarz for the Fock form**: `⟨f,g⟩² ≤ ⟨f,f⟩⟨g,g⟩`.

The quadratic form `⟨u,u⟩ ≥ 0` evaluated at `u = ⟨f,g⟩·f - ⟨f,f⟩·g` reads
`⟨f,f⟩·(⟨f,f⟩⟨g,g⟩ - ⟨f,g⟩²) ≥ 0` (bilinearity and symmetry of `bp`).  If
`⟨f,f⟩ = 0` then `f = 0` by definiteness, so `⟨f,g⟩ = 0`; otherwise divide by
the (positive) factor `⟨f,f⟩`. -/
lemma bp_cauchy_sq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (f g : F.H) :
    (F.bp f g)^2 ≤ F.bp f f * F.bp g g := by
  have hx : 0 ≤ F.bp f f := F.bp_nonneg f
  have hy : 0 ≤ F.bp g g := F.bp_nonneg g
  -- expansion of the form at the trial vector `u = ⟨f,g⟩·f - ⟨f,f⟩·g`
  have hexp :
      F.bp (F.bp f g • f + (-(F.bp f f)) • g) (F.bp f g • f + (-(F.bp f f)) • g)
        = (F.bp f g)^2 * F.bp f f + 2 * F.bp f g * (-(F.bp f f)) * F.bp f g
          + (-(F.bp f f))^2 * F.bp g g := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [F.bp_symm g f]
    ring
  have hkey : 0 ≤ F.bp f f * (F.bp f f * F.bp g g - (F.bp f g)^2) := by
    have h := F.bp_nonneg (F.bp f g • f + (-(F.bp f f)) • g)
    rw [hexp] at h
    nlinarith [h]
  by_cases h0 : F.bp f f = 0
  · -- `⟨f,f⟩ = 0` forces `f = 0`, hence `⟨f,g⟩ = 0`
    have hf : f = 0 := F.bp_def f h0
    simp [hf]
  · have hpos : 0 < F.bp f f := lt_of_le_of_ne hx (Ne.symm h0)
    have := (mul_nonneg_iff_of_pos_left hpos).mp hkey
    linarith

/-- **Cauchy–Schwarz for the Fock form, absolute-value form**:
`|⟨f,g⟩| ≤ √⟨f,f⟩ · √⟨g,g⟩`.  Immediate from `bp_cauchy_sq`, `|x| = √(x²)` and
`√(xy) = √x·√y` for `x, y ≥ 0`. -/
lemma bp_cauchy_abs {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (f g : F.H) :
    |F.bp f g| ≤ Real.sqrt (F.bp f f) * Real.sqrt (F.bp g g) := by
  have hx : 0 ≤ F.bp f f := F.bp_nonneg f
  calc |F.bp f g| = Real.sqrt ((F.bp f g)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (F.bp f f * F.bp g g) := Real.sqrt_le_sqrt (bp_cauchy_sq F f g)
    _ = Real.sqrt (F.bp f f) * Real.sqrt (F.bp g g) := Real.sqrt_mul hx (F.bp g g)

/-- **Cauchy–Schwarz with `ε`** (the form used throughout FS §10's estimates):
for `ε > 0` and all `f g` in the Fock space,
`2⟨f,g⟩ ≤ ε⟨f,f⟩ + ε⁻¹⟨g,g⟩`.

Combines `bp_cauchy_abs` (which bounds `⟨f,g⟩ ≤ |⟨f,g⟩| ≤ √⟨f,f⟩√⟨g,g⟩`) with
Young's inequality `two_mul_le_eps_inv` at `X = √⟨f,f⟩`, `Y = √⟨g,g⟩`, using
`(√x)² = x` for `x ≥ 0`. -/
theorem bp_cauchy {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) {ε : ℝ} (hε : 0 < ε) (f g : F.H) :
    2 * F.bp f g ≤ ε * F.bp f f + ε⁻¹ * F.bp g g := by
  have hx : 0 ≤ F.bp f f := F.bp_nonneg f
  have hy : 0 ≤ F.bp g g := F.bp_nonneg g
  have hcs : 2 * F.bp f g ≤ 2 * (Real.sqrt (F.bp f f) * Real.sqrt (F.bp g g)) := by
    have h1 : F.bp f g ≤ |F.bp f g| := le_abs_self _
    have h2 := bp_cauchy_abs F f g
    linarith
  have h2 := two_mul_le_eps_inv hε (Real.sqrt (F.bp f f)) (Real.sqrt (F.bp g g))
  rw [Real.sq_sqrt hx, Real.sq_sqrt hy] at h2
  linarith

end Work.BoseB7
