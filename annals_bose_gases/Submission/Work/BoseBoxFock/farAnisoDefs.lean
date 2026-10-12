import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.AliasDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.farAnisoDefs` — the far-image kernel and its spherical average

Vocabulary for the **anisotropy budget** of `FINDING_deficitAlias_far_image_le_ninth.md` §2.
Write `𝒢 = aliasKernel g`, `R₁ = kinFirst g`, and let the *far* lattice indices be
`F = {m : Fin 3 → ℤ | √2 ≤ ‖latVec m‖}` (the `‖m‖ = 1` touching images are excluded).

* `farEven ℓ u` is the **even (reflection-symmetrised) far-image kernel**

      (Φ_far)^even(u) = Σ_{m ∈ F} ½ (‖u − ℓ•latVec m‖⁻⁴ + ‖u + ℓ•latVec m‖⁻⁴) ,

  which is what the even kernel `𝒢` sees: `∫_u 𝒢(u)·farEven ℓ u = Σ_{m∈F} ∫_u 𝒢(u)‖u−ℓm‖⁻⁴`.
  (This is `π²·(π⁻²Σ_far)`, the left-hand side of the target up to `π²`.)

* `farAvg ℓ u` is the **spherical average** of `farEven ℓ ·` at `ρ = ‖u‖`,

      Φ̄_far(ρ) = Σ_{m ∈ F} ℓ⁻⁴ (‖m‖² − (ρ/ℓ)²)⁻² ,

  the value of `⨍_{S²}‖ρω − ℓm‖⁻⁴ dσ` by `Work.BoseBoxFock.sphere_average_inv_fourth`.

Both series are `tsum`s of nonnegative terms over the lattice; they are summable because
`Σ_{m≠0}‖m‖⁻⁴ < ∞` (cf. `Work.BoseK15.sum_inv_one_add_norm_le`).

The two statements this vocabulary serves are:

* the **unconditional radial bound** (FINDING §2, eq. (2)):
  `∫_u 𝒢(u)·farAvg ℓ u ≤ K₀π²(1/128 + μ/512 + μ²/4096)·R₁`
  (`K₀ = Σ_F‖m‖⁻⁴ = 10.5886`, `K_sharp = Σ_F(‖m‖²−1)⁻² = 22.2994`, `μ = (K_sharp−K₀)/K₀ = 1.10593`),
  i.e. `≤ 1.073375·R₁`; the statement `farImage_sphereAvg_le` files the rounded `1.073·R₁`;
* the **anisotropy budget** (FINDING §2, (ANISO)):
  `∫_u 𝒢(u)·(farEven ℓ u − farAvg ℓ u) ≤ 0.023·R₁`   (exact budget `π²/9 − 1.073375 = 0.023248`);

and (2) + (ANISO) gives `(1.073 + 0.023)·R₁ = 1.096 R₁ < π²R₁/9 = 1.0966227 R₁`, i.e. the target
`π⁻²Σ_far ≤ R₁/9`.  (The `1/1000`-rounding of the two constants is what makes the pair close with
a positive margin; both files' constants are pinned against the FINDING's arithmetic.)
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The even (reflection-symmetrised) far-image kernel
`Σ_{m ∈ F} ½(‖u − ℓm‖⁻⁴ + ‖u + ℓm‖⁻⁴)`, `0` on the touching indices `‖m‖ = 1`. -/
noncomputable def farEven (ℓ : ℝ) (u : E3) : ℝ :=
  ∑' m : Fin 3 → ℤ,
    if Real.sqrt 2 ≤ ‖latVec m‖ then
      (2 : ℝ)⁻¹ * ((‖u - ℓ • latVec m‖ ^ 4)⁻¹ + (‖u + ℓ • latVec m‖ ^ 4)⁻¹)
    else 0

/-- The spherical average of the far-image kernel at radius `‖u‖`:
`Σ_{m ∈ F} ℓ⁻⁴(‖m‖² − (‖u‖/ℓ)²)⁻²`. -/
noncomputable def farAvg (ℓ : ℝ) (u : E3) : ℝ :=
  ∑' m : Fin 3 → ℤ,
    if Real.sqrt 2 ≤ ‖latVec m‖ then
      (ℓ ^ 4 * (‖latVec m‖ ^ 2 - (‖u‖ / ℓ) ^ 2) ^ 2)⁻¹
    else 0

theorem farEven_nonneg (ℓ : ℝ) (u : E3) : 0 ≤ farEven ℓ u := by
  refine tsum_nonneg fun m => ?_
  split_ifs with h
  · positivity
  · exact le_refl 0

theorem farAvg_nonneg (ℓ : ℝ) (u : E3) : 0 ≤ farAvg ℓ u := by
  refine tsum_nonneg fun m => ?_
  split_ifs with h
  · positivity
  · exact le_refl 0

end Work.BoseBoxFock
