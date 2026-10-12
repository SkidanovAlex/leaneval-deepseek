import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1fun_bounds_ae.lean`

The **honest forms** of the row `Work.BoseB7AK.W1rows.W1fun_bounds`
(FS `eq:W1-g`, `final_v2.tex` line ~834), i.e. of the kernel sandwich

  `g₀ ≤ W₁ = g₀/(χ⋆χ)_ℓ ≤ 2 g₀`   on `‖x‖ ≤ R`

for `W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g0 v h)`.

## Why the pointwise row cannot be proved

The corpus knows `convScale ℓ x ∈ [1/2, 1]` on the ball `‖x‖ ≤ R`
(`Submission.BoseGases.convScale_ge_half_ball` and `conv3chi_le_one`), and
`W1fun v h ℓ x = g0 v h x / convScale ℓ x` by definition.  Consequently the
requested conjunction

  `g0 v h x ≤ W1fun v h ℓ x ∧ W1fun v h ℓ x ≤ 2 * g0 v h x`

is **equivalent** to `0 ≤ g0 v h x`:

* forward: multiplying the two inequalities by `0 < convScale ℓ x` gives
  `g·c ≤ g` and `g ≤ 2·g·c` with `g := g0 v h x`, `c := convScale ℓ x`; adding
  them gives `-g·c ≤ 0`, i.e. `0 ≤ g` (`nonneg_of_W1fun_bounds` below);
* backward: for `0 ≤ g` the two inequalities are `c ≤ 1` and `2c ≥ 1`
  (`W1fun_bounds_of_nonneg` below).

So the pointwise row is exactly the *pointwise* nonnegativity of
`g₀ = v·(1 − w₀)`, `w₀ = Classical.choose h`, on the ball of radius `R`.  The
workspace has this only almost everywhere:
`Submission.BoseGases.g0_nonneg_ae : ∀ᵐ x, 0 ≤ g0 v h x`, since every
scattering fact about the chosen solution is a.e.
(`scattering_bounds_ae`, `chosen_w0_bounds_ae`,
`chosen_scattering_av_exterior`, `canonicalProfile_eq_profile`).  This is not a
gap that can be closed: `BoseGases.IsScatteringSolution w v` is invariant under
changing `w` on a sphere `{x | ‖x‖ = r₀}` (locally-integrability, the weak
equation and the cocompact limit all see only a.e. data, and radiality is
preserved by a spherical modification), so a "spiked" witness with `w = 2` on a
sphere inside `ball 0 R` on which `v > 0` is an honest `ScatSol v` witness, and
`Classical.choose h` is constrained by `choose_spec` alone.  The corpus's own
general form of FS `eq:W1-g`, `Submission.BoseGases.wScaled_sandwich`, carries
exactly the missing hypothesis `hg : 0 ≤ g`; the a.e. form for `g₀` is
`Submission.Work.BoseB7AK.W1rows.W1fun_bounds_ae.W1fun_bounds_ae` below (cf. the
existing `FibreLocal.g0_le_wScaled_ae` for the lower bound alone).

The two statements delivered here are the correct replacements:

* `W1fun_bounds_of_nonneg` — the pointwise row *with* `0 ≤ g0 v h x` added
  (the missing hypothesis of the request);
* `W1fun_bounds_ae` — the a.e. row, from `g0_nonneg_ae`.

Both are `sorry`-free.
-/

namespace Work.BoseB7AK.W1rows

-- `ℝ³` is the *global* `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs`, which is in this file's import cone (via
-- `Submission.Work.BoseFixR.Defs`); redeclaring it locally makes the term
-- ambiguous.

open MeasureTheory

/-- **FS `eq:W1-g`, pointwise, with the missing nonnegativity hypothesis.**
On the ball `‖x‖ ≤ R` (`R ≤ ℓ·chiR0`) the normalisation `(χ⋆χ)(x/ℓ)` lies in
`[1/2,1]`, so `g x ≤ g x/(χ⋆χ)(x/ℓ)` and `g x/(χ⋆χ)(x/ℓ) ≤ 2·g x` as soon as
`0 ≤ g x`.

The hypothesis `hg0` is *not* redundant: see `nonneg_of_W1fun_bounds` below. -/
theorem W1fun_bounds_of_nonneg {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {x : ℝ³} (hx : ‖x‖ ≤ R) (hg0 : 0 ≤ Submission.BoseGases.g0 v h x) :
    Submission.BoseGases.g0 v h x ≤ Work.BoseFixR.W1fun v h ℓ x
      ∧ Work.BoseFixR.W1fun v h ℓ x ≤ 2 * Submission.BoseGases.g0 v h x := by
  have hchalf : 1 / 2 ≤ Submission.BoseGases.convScale ℓ x :=
    Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx
  have hcpos : 0 < Submission.BoseGases.convScale ℓ x :=
    lt_of_lt_of_le (by norm_num) hchalf
  have hcle : Submission.BoseGases.convScale ℓ x ≤ 1 := by
    simpa [Submission.BoseGases.convScale] using
      (Submission.BoseGases.conv3chi_le_one ((ℓ⁻¹) • x))
  rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]
  constructor
  · rw [le_div_iff₀ hcpos]
    nlinarith
  · rw [div_le_iff₀ hcpos]
    nlinarith

/-- **The requested row cannot be strengthened to a pointwise statement about
`g₀` without extra hypotheses**: the conjunction `g ≤ W₁ ≤ 2g` *forces*
`0 ≤ g₀ v h x` on the ball.  (Multiply by `0 < convScale ℓ x` and add
`g·c ≤ g` to `g ≤ 2·g·c`.) -/
theorem nonneg_of_W1fun_bounds {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {x : ℝ³} (hx : ‖x‖ ≤ R)
    (hconcl : Submission.BoseGases.g0 v h x ≤ Work.BoseFixR.W1fun v h ℓ x
      ∧ Work.BoseFixR.W1fun v h ℓ x ≤ 2 * Submission.BoseGases.g0 v h x) :
    0 ≤ Submission.BoseGases.g0 v h x := by
  have hcpos : 0 < Submission.BoseGases.convScale ℓ x :=
    lt_of_lt_of_le (by norm_num)
      (Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx)
  have h1 : Submission.BoseGases.g0 v h x * Submission.BoseGases.convScale ℓ x
      ≤ Submission.BoseGases.g0 v h x := by
    have hh := hconcl.1
    rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled] at hh
    exact (le_div_iff₀ hcpos).mp hh
  have h2 : Submission.BoseGases.g0 v h x
      ≤ 2 * Submission.BoseGases.g0 v h x * Submission.BoseGases.convScale ℓ x := by
    have hh := hconcl.2
    rw [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled] at hh
    exact (div_le_iff₀ hcpos).mp hh
  nlinarith [h1, h2, hcpos]

/-- **FS `eq:W1-g` in the form the workspace supports: almost everywhere.**
For a nonnegative radial `v` supported in `ball 0 R`, `ScatSol v`, and
`R ≤ ℓ·chiR0`, the sandwich `g₀ ≤ W₁ ≤ 2g₀` holds for almost every `x` with
`‖x‖ ≤ R`; the exceptional null set is the one of `g0_nonneg_ae`. -/
theorem W1fun_bounds_ae {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ᵐ x : ℝ³, ‖x‖ ≤ R →
      Submission.BoseGases.g0 v h x ≤ Work.BoseFixR.W1fun v h ℓ x
        ∧ Work.BoseFixR.W1fun v h ℓ x ≤ 2 * Submission.BoseGases.g0 v h x := by
  have hnn : ∀ᵐ x : ℝ³, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  filter_upwards [hnn] with x hx0 hx
  exact W1fun_bounds_of_nonneg hR hℓ h hRℓ hx hx0

end Work.BoseB7AK.W1rows
