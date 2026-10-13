/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the angular slice of the "hard" part of `SpecialTransport`

`HardIntegrable` is the integrability input of the `SpecialTransport` argument: for a fixed
`z ∈ Iz = [0,∞)`, the angular slice

  `θ ↦ HardF α f g z θ = w(z)² · ( f z θ · ∂_θ(D_z⁴ g) z θ · D_z⁴ g z θ · sin(2θ)^{-η}
      + f z θ · (∑ ∂_θ(D_z^jD_θ^i g) z θ · D_z^jD_θ^i g z θ) · sin(2θ)^{-γ} )`

is integrable on `Iθ = [0,π/2]`, knowing only

* `f z ·` is a.e. strongly measurable on `Iθ` and `|f z θ| ≤ K sin(2θ)`, and
* `g` is smooth on a neighbourhood of the closed quadrant (`Spaces.SmoothNbhd g`).

The point is that every `g`-factor is bounded on `[0,z] × Iθ` (the `θ`-slices of the iterated
derivatives of a `SmoothNbhd` function are continuous on the compact `Iθ`), while the mixed
slots `D_z^jD_θ^i g` with `i ≥ 1` *vanish* like `sin(2θ)` (`Work.FTS.H2.mixed_sin_bound`).
Hence

  `|HardF α f g z θ| ≤ C · sin(2θ)^{1-η}`,

and `1 - η = 1/100 > -1`, so `intervalIntegrable_sin_rpow` / `intervalIntegrable_of_sin_bound`
finish.  The exponent bookkeeping is the content of `sin_two_mul_rpow_neg_eta`,
`sin_two_mul_mul_rpow_neg_gam` and `sin_two_rpow_cmp_gam` below; the numerical core is
`hardF_numeric`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.mixed_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary exponent identities on `Iθ`

All of them are instances of `Real.rpow_add'` (which, unlike `Real.rpow_add`, does not require
a *positive* base, only that the sum of the exponents be non-zero — this is what makes them
valid also at the two endpoints of `Iθ`, where `sin(2θ) = 0`). -/

/-- `sin(2θ) · sin(2θ)^{-η} = sin(2θ)^{1-η}` on `Iθ` (including at the endpoints). -/
theorem sin_two_mul_rpow_neg_eta {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hne : (1 : ℝ) + (-Work.Spaces.eta) ≠ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have h : (1 : ℝ) - Work.Spaces.eta = 1 + (-Work.Spaces.eta) := by ring
  rw [h, Real.rpow_add' hs hne, Real.rpow_one]

/-- `sin(2θ)² · sin(2θ)^{-γ} = sin(2θ)^{2-γ}` on `Iθ`, for `γ = 1 + α/10` with `0 < α ≤ 1`
(so that `1 - γ ≠ 0` and `2 - γ ≠ 0`). -/
theorem sin_two_mul_mul_rpow_neg_gam {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hγ1 : 1 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  have hne1 : (1 : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
    intro h; linarith
  have hne2 : (1 : ℝ) + (1 + (-(Work.Spaces.gam α))) ≠ 0 := by
    intro h; linarith
  have h : (2 : ℝ) - Work.Spaces.gam α = 1 + (1 + (-(Work.Spaces.gam α))) := by ring
  rw [h, Real.rpow_add' hs hne2, Real.rpow_add' hs hne1, Real.rpow_one]
  ring

/-- `sin(2θ)^{2-γ} ≤ sin(2θ)^{1-η}` on `Iθ` for `0 < α ≤ 1`: both exponents are positive and
`1 - η = 1/100 ≤ 1 - α/10 = 2 - γ`. -/
theorem sin_two_rpow_cmp_gam {α : ℝ} (_hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h2r : 2 - Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have h1q : 1 - Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  have hqr : 1 - Work.Spaces.eta ≤ 2 - Work.Spaces.gam α := by
    rw [Work.Spaces.eta, Work.Spaces.gam]; linarith
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h, Real.zero_rpow h2r, Real.zero_rpow h1q]
  · exact Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) hqr

/-! ## Small numerical lemmas -/

/-- `|a · b| ≤ A · B` from `|a| ≤ A` and `|b| ≤ B`. -/
theorem hardF_abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- The numerical core of the pointwise bound of `HardF`, with the three exponent facts left
as hypotheses. -/
theorem hardF_numeric {α W K S a A B N E : ℝ} (hW : 0 ≤ W) (hK : 0 ≤ K) (hS0 : 0 ≤ S)
    (_hS1 : S ≤ 1) (_hN : 0 ≤ N) (hE : 0 ≤ E) (ha : |a| ≤ K * S) (hA : |A| ≤ N)
    (hB : |B| ≤ E * S)
    (hid1 : S * S ^ (-Work.Spaces.eta) = S ^ (1 - Work.Spaces.eta))
    (hid2 : S * S * S ^ (-(Work.Spaces.gam α)) = S ^ (2 - Work.Spaces.gam α))
    (hcmp : S ^ (2 - Work.Spaces.gam α) ≤ S ^ (1 - Work.Spaces.eta)) :
    |W * (a * A * S ^ (-Work.Spaces.eta) + a * B * S ^ (-(Work.Spaces.gam α)))|
      ≤ W * K * (N + E) * S ^ (1 - Work.Spaces.eta) := by
  have hSη : 0 ≤ S ^ (-Work.Spaces.eta) := Real.rpow_nonneg hS0 _
  have hSγ : 0 ≤ S ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS0 _
  have hfirst : |a * A * S ^ (-Work.Spaces.eta)| ≤ K * N * S ^ (1 - Work.Spaces.eta) := by
    have h1 : |a * A| ≤ (K * S) * N := hardF_abs_mul_le ha hA
    have h2 : |a * A * S ^ (-Work.Spaces.eta)|
        ≤ ((K * S) * N) * S ^ (-Work.Spaces.eta) :=
      hardF_abs_mul_le h1 (le_of_eq (abs_of_nonneg hSη))
    calc |a * A * S ^ (-Work.Spaces.eta)| ≤ ((K * S) * N) * S ^ (-Work.Spaces.eta) := h2
      _ = K * N * (S * S ^ (-Work.Spaces.eta)) := by ring
      _ = K * N * S ^ (1 - Work.Spaces.eta) := by rw [hid1]
  have hsecond : |a * B * S ^ (-(Work.Spaces.gam α))| ≤ K * E * S ^ (1 - Work.Spaces.eta) := by
    have h1 : |a * B| ≤ (K * S) * (E * S) := hardF_abs_mul_le ha hB
    have h2 : |a * B * S ^ (-(Work.Spaces.gam α))|
        ≤ ((K * S) * (E * S)) * S ^ (-(Work.Spaces.gam α)) :=
      hardF_abs_mul_le h1 (le_of_eq (abs_of_nonneg hSγ))
    calc |a * B * S ^ (-(Work.Spaces.gam α))|
          ≤ ((K * S) * (E * S)) * S ^ (-(Work.Spaces.gam α)) := h2
      _ = K * E * (S * S * S ^ (-(Work.Spaces.gam α))) := by ring
      _ = K * E * S ^ (2 - Work.Spaces.gam α) := by rw [hid2]
      _ ≤ K * E * S ^ (1 - Work.Spaces.eta) :=
          mul_le_mul_of_nonneg_left hcmp (mul_nonneg hK hE)
  calc |W * (a * A * S ^ (-Work.Spaces.eta) + a * B * S ^ (-(Work.Spaces.gam α)))|
      = W * |a * A * S ^ (-Work.Spaces.eta) + a * B * S ^ (-(Work.Spaces.gam α))| := by
        rw [abs_mul, abs_of_nonneg hW]
    _ ≤ W * (|a * A * S ^ (-Work.Spaces.eta)| + |a * B * S ^ (-(Work.Spaces.gam α))|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hW
    _ ≤ W * (K * N * S ^ (1 - Work.Spaces.eta) + K * E * S ^ (1 - Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hW
    _ = W * K * (N + E) * S ^ (1 - Work.Spaces.eta) := by ring

/-! ## Slices of `SmoothNbhd` functions and their box bounds -/

/-- The `θ`-slice of a function which is smooth on a neighbourhood of the closed quadrant is
continuous on `Iθ` (for `z ∈ Iz`). -/
theorem continuousOn_slice_of_smoothNbhd {H : ℝ → ℝ → ℝ} (hH : Work.Spaces.SmoothNbhd H)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => H z θ) Work.Spaces.Iθ :=
  (hH : ContDiffOn ℝ ⊤ (Function.uncurry H) Work.Spaces.U).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun _ hθ => Work.Spaces.mem_U_of_dom hz hθ)

/-- On the box `[0,z] × Iθ` (with `z ∈ Iz`) the absolute value of a `SmoothNbhd` function is
bounded by its `boxSup`, which is nonnegative. -/
theorem smoothNbhd_slice_le_boxSup {H : ℝ → ℝ → ℝ} (hH : Work.Spaces.SmoothNbhd H)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    0 ≤ Work.Spaces.boxSup z H
      ∧ ∀ θ ∈ Work.Spaces.Iθ, |H z θ| ≤ Work.Spaces.boxSup z H := by
  have hb : BddAbove (Work.Spaces.boxSet z H) :=
    Work.Spaces.bddAbove_boxSup_of_continuousOn
      (Work.Spaces.continuousOn_box_of_contDiffOn hH)
  exact ⟨Work.Spaces.boxSup_nonneg hz hb,
    fun θ hθ => Work.Spaces.le_boxSup hb ⟨hz, le_refl z⟩ hθ⟩

/-! ## The pointwise bound of `HardF` -/

/-- `HardF` rewritten with the two pairs of factors grouped as they are bounded. -/
theorem hardF_eq_blocks (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HardF α f g z θ
      = (Work.Spaces.w z) ^ 2 *
          (f z θ * (Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
              * Work.Spaces.DzIter 4 g z θ) * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
            + f z θ * (Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
                  * Work.Spaces.mixed 3 1 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
                  * Work.Spaces.mixed 2 2 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
                  * Work.Spaces.mixed 1 3 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
                  * Work.Spaces.mixed 0 4 g z θ)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  rw [HardF]; ring

/-- Pointwise bound of the hard part, at fixed `z ∈ Iz`, with a constant which may depend on
`z`: the two groups of terms are dominated by `sin(2θ)^{1-η}` and `sin(2θ)^{2-γ}` respectively,
and `2 - γ ≥ 1 - η` (because `α ≤ 1`). -/
theorem hardF_pointwise_bound {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.Spaces.SmoothNbhd g) {K : ℝ} (hK : 0 ≤ K) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hf : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |HardF α f g z θ| ≤ C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
  -- boundedness of the smooth factors on the box `[0,z] × Iθ`
  obtain ⟨hB1nn, hB1⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DzIter hg 4)) hz
  obtain ⟨hB2nn, hB2⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.smoothNbhd_DzIter hg 4) hz
  obtain ⟨hM1nn, hM1⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 3 1)) hz
  obtain ⟨hM2nn, hM2⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 2 2)) hz
  obtain ⟨hM3nn, hM3⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 1 3)) hz
  obtain ⟨hM4nn, hM4⟩ := smoothNbhd_slice_le_boxSup
    (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 0 4)) hz
  -- angular vanishing of the mixed slots (`i ≥ 1`)
  obtain ⟨C1, hC1nn, hC1⟩ := mixed_sin_bound g hg z hz 3 1 (by norm_num)
  obtain ⟨C2, hC2nn, hC2⟩ := mixed_sin_bound g hg z hz 2 2 (by norm_num)
  obtain ⟨C3, hC3nn, hC3⟩ := mixed_sin_bound g hg z hz 1 3 (by norm_num)
  obtain ⟨C4, hC4nn, hC4⟩ := mixed_sin_bound g hg z hz 0 4 (by norm_num)
  refine ⟨(Work.Spaces.w z) ^ 2 * K *
      (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.DzIter 4 g))
          * Work.Spaces.boxSup z (Work.Spaces.DzIter 4 g)
        + (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g)) * C1
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g)) * C2
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g)) * C3
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g)) * C4)),
      mul_nonneg (mul_nonneg (sq_nonneg (Work.Spaces.w z)) hK)
        (add_nonneg (mul_nonneg hB1nn hB2nn)
          (add_nonneg
            (add_nonneg (add_nonneg (mul_nonneg hM1nn hC1nn) (mul_nonneg hM2nn hC2nn))
              (mul_nonneg hM3nn hC3nn))
            (mul_nonneg hM4nn hC4nn))), ?_⟩
  intro θ hθ
  have hS0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hS1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  -- the bounds on the two blocks
  have hA : |Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
      * Work.Spaces.DzIter 4 g z θ|
      ≤ Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.DzIter 4 g))
        * Work.Spaces.boxSup z (Work.Spaces.DzIter 4 g) :=
    hardF_abs_mul_le (hB1 θ hθ) (hB2 θ hθ)
  have ht1 : |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
      * Work.Spaces.mixed 3 1 g z θ|
      ≤ (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g)) * C1)
        * Real.sin (2 * θ) := by
    have h := hardF_abs_mul_le (hM1 θ hθ) (hC1 θ hθ)
    calc |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
          * Work.Spaces.mixed 3 1 g z θ|
        ≤ Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g))
            * (C1 * Real.sin (2 * θ)) := h
      _ = (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g)) * C1)
            * Real.sin (2 * θ) := by ring
  have ht2 : |Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
      * Work.Spaces.mixed 2 2 g z θ|
      ≤ (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g)) * C2)
        * Real.sin (2 * θ) := by
    have h := hardF_abs_mul_le (hM2 θ hθ) (hC2 θ hθ)
    calc |Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
          * Work.Spaces.mixed 2 2 g z θ|
        ≤ Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g))
            * (C2 * Real.sin (2 * θ)) := h
      _ = (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g)) * C2)
            * Real.sin (2 * θ) := by ring
  have ht3 : |Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
      * Work.Spaces.mixed 1 3 g z θ|
      ≤ (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g)) * C3)
        * Real.sin (2 * θ) := by
    have h := hardF_abs_mul_le (hM3 θ hθ) (hC3 θ hθ)
    calc |Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
          * Work.Spaces.mixed 1 3 g z θ|
        ≤ Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g))
            * (C3 * Real.sin (2 * θ)) := h
      _ = (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g)) * C3)
            * Real.sin (2 * θ) := by ring
  have ht4 : |Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
      * Work.Spaces.mixed 0 4 g z θ|
      ≤ (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g)) * C4)
        * Real.sin (2 * θ) := by
    have h := hardF_abs_mul_le (hM4 θ hθ) (hC4 θ hθ)
    calc |Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
          * Work.Spaces.mixed 0 4 g z θ|
        ≤ Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g))
            * (C4 * Real.sin (2 * θ)) := h
      _ = (Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g)) * C4)
            * Real.sin (2 * θ) := by ring
  have hB : |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
        * Work.Spaces.mixed 3 1 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
        * Work.Spaces.mixed 2 2 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
        * Work.Spaces.mixed 1 3 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
        * Work.Spaces.mixed 0 4 g z θ|
      ≤ ((Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g)) * C1
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g)) * C2
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g)) * C3
          + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g)) * C4))
        * Real.sin (2 * θ) := by
    have e1 : |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
          * Work.Spaces.mixed 3 1 g z θ
        + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
          * Work.Spaces.mixed 2 2 g z θ
        + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
          * Work.Spaces.mixed 1 3 g z θ
        + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
          * Work.Spaces.mixed 0 4 g z θ|
        ≤ |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
              * Work.Spaces.mixed 1 3 g z θ|
          + |Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
              * Work.Spaces.mixed 0 4 g z θ| := abs_add_le _ _
    have e2 : |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
              * Work.Spaces.mixed 1 3 g z θ|
        ≤ |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ|
          + |Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
              * Work.Spaces.mixed 1 3 g z θ| := abs_add_le _ _
    have e3 : |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ|
        ≤ |Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ|
          + |Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ| := abs_add_le _ _
    linarith [e1, e2, e3, ht1, ht2, ht3, ht4]
  rw [hardF_eq_blocks]
  exact hardF_numeric (W := (Work.Spaces.w z) ^ 2) (K := K) (S := Real.sin (2 * θ))
    (a := f z θ)
    (A := Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ * Work.Spaces.DzIter 4 g z θ)
    (B := Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ * Work.Spaces.mixed 3 1 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ * Work.Spaces.mixed 2 2 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ * Work.Spaces.mixed 1 3 g z θ
      + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ * Work.Spaces.mixed 0 4 g z θ)
    (N := Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.DzIter 4 g))
      * Work.Spaces.boxSup z (Work.Spaces.DzIter 4 g))
    (E := Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 3 1 g)) * C1
      + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 2 2 g)) * C2
      + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 1 3 g)) * C3
      + Work.Spaces.boxSup z (Work.Spaces.pth (Work.Spaces.mixed 0 4 g)) * C4)
    (sq_nonneg (Work.Spaces.w z)) hK hS0 hS1 (mul_nonneg hB1nn hB2nn)
    (add_nonneg
      (add_nonneg (add_nonneg (mul_nonneg hM1nn hC1nn) (mul_nonneg hM2nn hC2nn))
        (mul_nonneg hM3nn hC3nn))
      (mul_nonneg hM4nn hC4nn))
    (hf θ hθ) hA hB
    (sin_two_mul_rpow_neg_eta hθ) (sin_two_mul_mul_rpow_neg_gam hα hα1 hθ)
    (sin_two_rpow_cmp_gam hα hα1 hθ)

/-! ## A.e. strong measurability of the slice -/

/-- The angular slice of `HardF` is a.e. strongly measurable on `Iθ` as soon as the `f`-slice
is: every other factor is a continuous (`g`-derivative) or measurable (`sin(2θ)^{-η}`,
`sin(2θ)^{-γ}`) function of `θ`. -/
theorem hardF_aesm {α : ℝ} {f g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz)
    (hfm : MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.AEStronglyMeasurable (fun θ => HardF α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hslic : ∀ {H : ℝ → ℝ → ℝ}, Work.Spaces.SmoothNbhd H →
      MeasureTheory.AEStronglyMeasurable (fun θ => H z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun hH => (continuousOn_slice_of_smoothNbhd hH hz).aestronglyMeasurable measurableSet_Icc
  have hsin : ∀ p : ℝ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun p =>
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p).aestronglyMeasurable
  have hD4 := hslic (Work.Spaces.smoothNbhd_DzIter hg 4)
  have hpD4 := hslic (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_DzIter hg 4))
  have hm31 := hslic (Work.Spaces.smoothNbhd_mixed hg 3 1)
  have hm22 := hslic (Work.Spaces.smoothNbhd_mixed hg 2 2)
  have hm13 := hslic (Work.Spaces.smoothNbhd_mixed hg 1 3)
  have hm04 := hslic (Work.Spaces.smoothNbhd_mixed hg 0 4)
  have hp31 := hslic (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 3 1))
  have hp22 := hslic (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 2 2))
  have hp13 := hslic (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 1 3))
  have hp04 := hslic (Work.Spaces.SmoothNbhd.pth (Work.Spaces.smoothNbhd_mixed hg 0 4))
  have hsum : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
            * Work.Spaces.mixed 3 1 g z θ
          + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
            * Work.Spaces.mixed 2 2 g z θ
          + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
            * Work.Spaces.mixed 1 3 g z θ
          + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
            * Work.Spaces.mixed 0 4 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (((hp31.mul hm31).add (hp22.mul hm22)).add (hp13.mul hm13)).add (hp04.mul hm04)
  have hT1 : MeasureTheory.AEStronglyMeasurable
      (fun θ => f z θ * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
          * Work.Spaces.DzIter 4 g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hfm.mul hpD4).mul hD4).mul (hsin (-Work.Spaces.eta))
  have hT2 : MeasureTheory.AEStronglyMeasurable
      (fun θ => f z θ * (Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
              * Work.Spaces.mixed 3 1 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
              * Work.Spaces.mixed 2 2 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
              * Work.Spaces.mixed 1 3 g z θ
            + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
              * Work.Spaces.mixed 0 4 g z θ)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hfm.mul hsum).mul (hsin (-(Work.Spaces.gam α)))
  have key : (fun θ => HardF α f g z θ)
      = fun θ => (Work.Spaces.w z) ^ 2 *
          (f z θ * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
              * Work.Spaces.DzIter 4 g z θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
            + f z θ * (Work.Spaces.pth (Work.Spaces.mixed 3 1 g) z θ
                  * Work.Spaces.mixed 3 1 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 2 2 g) z θ
                  * Work.Spaces.mixed 2 2 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 1 3 g) z θ
                  * Work.Spaces.mixed 1 3 g z θ
                + Work.Spaces.pth (Work.Spaces.mixed 0 4 g) z θ
                  * Work.Spaces.mixed 0 4 g z θ)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    funext θ
    rw [HardF]
  rw [key]
  exact (aestronglyMeasurable_const (b := (Work.Spaces.w z) ^ 2)).mul (hT1.add hT2)

/-! ## The main statement -/

theorem HardIntegrable {α : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.Spaces.SmoothNbhd g) {K : ℝ} (hK : 0 ≤ K)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hfm : MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hf : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ)) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.HardF α f g z θ) Work.Spaces.Iθ := by
  obtain ⟨C, -, hb⟩ := hardF_pointwise_bound hα hα1 hg hK hz hf
  have hmeas := hardF_aesm (α := α) hg hz hfm
  have hη : (-1 : ℝ) < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hII : IntervalIntegrable (fun θ => HardF α f g z θ) volume 0 (π / 2) :=
    intervalIntegrable_of_sin_bound (f := fun θ => HardF α f g z θ) (C := C) hη hmeas hb
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])] at hII
  exact hII

end Work.FTS.H2
