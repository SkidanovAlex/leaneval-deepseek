import Mathlib
import Submission.Work.Diff.L.monotoneOn_Ico_of_hasDerivWithinAt_nonneg
import Submission.Work.Diff.L.antitoneOn_Ico_of_hasDerivWithinAt_nonpos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

/-- **Riccati comparison (one-sided Gronwall).**  If `x` satisfies `x' ≥ c * x²` on `[t₀, T)`,
`y` satisfies `y' = c * y²` there with `0 < y`, `c ≥ 0` and `y t₀ ≤ x t₀`, then `y ≤ x` on
`[t₀, T)`.

Route.  Put `W u = y u - x u` and `K u = c * (x u + y u)`.  Then
`W' u - K u * W u = c * x u ^ 2 - x' u ≤ 0` — this holds with *no* sign hypothesis on `W`, which
is the point: `K` is continuous (`x`, `y` are continuous on `Ico t₀ T`, hence on each
`Icc t₀ t ⊆ Ico t₀ T`), so with `F u = ∫_{t₀}^{u} K` the function `S u = W u * exp (-(F u))` has
`S' u = (W' u - K u * W u) * exp (-(F u)) ≤ 0`; `S t₀ = W t₀ ≤ 0` together with
`antitoneOn_of_hasDerivWithinAt_nonpos` gives `S ≤ 0`, hence `W ≤ 0`.
Alternatively (no integrals): on `[s, s+δ]` with `W s ≤ 0` the functions `x`, `y` are nonnegative
and nondecreasing there (their derivatives are `≥ 0`), so `K u ≤ B := c * (x (s+δ) + y (s+δ))` for
`u ∈ (s, s+δ)` and the integrating factor `exp (-(B * (u - s)))` gives `W ≤ 0` on `[s, s+δ]`;
then glue these local steps (the set `{t | ∀ u ∈ Icc t₀ t, y u ≤ x u}` is closed in `Icc t₀ T` by
continuity, and a maximal point of it below `T` is extended to the right).  The case `T ≤ t₀` is
vacuous.

PROOF.  The proof below takes the *logarithmic* route (no integrals at all).  Both `x` and `y`
are nondecreasing (their derivatives are `≥ 0`), and `x t₀ ≥ y t₀ > 0`, so `x` is strictly
positive on `[t₀, T)`.  On `[t₀, T)` the reciprocals therefore satisfy
`(1/x)' = -x'/x² ≤ -c x²/x² = -c` and `(1/y)' = -(c y²)/y² = -c`, so
`u := 1/x - 1/y` is continuous on `[t₀, T)` with `u' ≤ 0` there and `u t₀ ≤ 0`; hence `u ≤ 0`,
and since both reciprocals are positive, `inv_le_inv₀` turns `1/x ≤ 1/y` into `y ≤ x`.  The two
half-open-interval monotonicity lemmas are proved in
`Submission/Work/Diff/L/monotoneOn_Ico_of_hasDerivWithinAt_nonneg.lean` and
`Submission/Work/Diff/L/antitoneOn_Ico_of_hasDerivWithinAt_nonpos.lean`. -/
theorem riccati_le {c t₀ T : ℝ} (hc : 0 ≤ c) {x x' y : ℝ → ℝ}
    (hxc : ContinuousOn x (Set.Ico t₀ T)) (hyc : ContinuousOn y (Set.Ico t₀ T))
    (hx : ∀ t ∈ Set.Ico t₀ T, HasDerivWithinAt x (x' t) (Set.Ico t₀ T) t)
    (hxineq : ∀ t ∈ Set.Ico t₀ T, c * x t ^ 2 ≤ x' t)
    (hy : ∀ t ∈ Set.Ico t₀ T, HasDerivWithinAt y (c * y t ^ 2) (Set.Ico t₀ T) t)
    (hyp : ∀ t ∈ Set.Ico t₀ T, 0 < y t)
    (h0 : y t₀ ≤ x t₀) :
    ∀ t ∈ Set.Ico t₀ T, y t ≤ x t := by
  intro t ht
  have hT : t₀ < T := lt_of_le_of_lt ht.1 ht.2
  have ht₀ : t₀ ∈ Set.Ico t₀ T := ⟨le_rfl, hT⟩
  -- `x` is nondecreasing on `[t₀, T)`.
  have hxmono : MonotoneOn x (Set.Ico t₀ T) :=
    monotoneOn_Ico_of_hasDerivWithinAt_nonneg hxc hx fun u hu =>
      le_trans (mul_nonneg hc (sq_nonneg _)) (hxineq u hu)
  -- hence strictly positive there, because `x t₀ ≥ y t₀ > 0`.
  have hxt₀ : 0 < x t₀ := lt_of_lt_of_le (hyp t₀ ht₀) h0
  have hxpos : ∀ u ∈ Set.Ico t₀ T, 0 < x u := fun u hu =>
    lt_of_lt_of_le hxt₀ (hxmono ht₀ hu hu.1)
  -- `u = 1/x - 1/y` is continuous on `[t₀, T)` ...
  have hcont : ContinuousOn (fun u => (x u)⁻¹ - (y u)⁻¹) (Set.Ico t₀ T) := by
    refine ContinuousOn.sub ?_ ?_
    · exact ContinuousOn.inv₀ hxc fun u hu => ne_of_gt (hxpos u hu)
    · exact ContinuousOn.inv₀ hyc fun u hu => ne_of_gt (hyp u hu)
  -- ... has a derivative there, given by the reciprocal rule ...
  have hderiv : ∀ u ∈ Set.Ico t₀ T,
      HasDerivWithinAt (fun u => (x u)⁻¹ - (y u)⁻¹)
        ((-x' u) / (x u) ^ 2 - (-(c * y u ^ 2)) / (y u) ^ 2) (Set.Ico t₀ T) u := by
    intro u hu
    have hxne : x u ≠ 0 := ne_of_gt (hxpos u hu)
    have hyne : y u ≠ 0 := ne_of_gt (hyp u hu)
    exact (hx u hu).inv hxne |>.sub ((hy u hu).inv hyne)
  -- ... and that derivative is `≤ 0`, since `(c y²)/y² = c ≤ x'/x²`.
  have hsign : ∀ u ∈ Set.Ico t₀ T,
      ((-x' u) / (x u) ^ 2 - (-(c * y u ^ 2)) / (y u) ^ 2) ≤ 0 := by
    intro u hu
    have hxne : x u ≠ 0 := ne_of_gt (hxpos u hu)
    have hyne : y u ≠ 0 := ne_of_gt (hyp u hu)
    have hval : (-x' u) / (x u) ^ 2 - (-(c * y u ^ 2)) / (y u) ^ 2
        = (c * y u ^ 2) / (y u) ^ 2 - x' u / (x u) ^ 2 := by ring
    rw [hval]
    have h1 : (c * y u ^ 2) / (y u) ^ 2 = c := by field_simp
    have h2 : c ≤ x' u / (x u) ^ 2 := by
      have h := div_le_div_of_nonneg_right (hxineq u hu) (by positivity : (0:ℝ) ≤ (x u)^2)
      have h3 : (c * x u ^ 2) / (x u) ^ 2 = c := by field_simp
      rw [h3] at h
      exact h
    linarith
  have hanti := antitoneOn_Ico_of_hasDerivWithinAt_nonpos hcont hderiv hsign
  have hkey : (x t)⁻¹ ≤ (y t)⁻¹ := by
    have hle := hanti ht₀ ht ht.1
    have h0' : (x t₀)⁻¹ ≤ (y t₀)⁻¹ := (inv_le_inv₀ hxt₀ (hyp t₀ ht₀)).mpr h0
    linarith
  exact (inv_le_inv₀ (hxpos t ht) (hyp t ht)).mp hkey

end Work.Diff.L
