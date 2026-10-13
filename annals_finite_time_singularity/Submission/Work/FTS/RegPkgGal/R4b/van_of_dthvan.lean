/-
# `Work.FTS.RegPkgGal.R4b.van_of_dthvan`

**The class lemma R4b**: on a strip `τ ∈ [0,S]`, a family `g` whose angular derivative satisfies
the `Γ`-bound `|D_θ g| = |sin(2θ)·∂_θ g| ≤ Cθ·z²·Γ(θ)` and which vanishes on the two angular
boundary lines (`VanishTheta`) is itself dominated by `Γ`:

  `|g z θ τ| ≤ Cv · Γ(θ)`  for `0 ≤ z ≤ 2`, `θ ∈ Iθ = [0,π/2]`, `τ ∈ [0,S]`.

This is the corrected counterpart of `R4/van_of_dthvan`, which is *false* for the hypotheses
there (`R4/van_of_dthvan_counterexample.lean`): the earlier statement only demanded `C¹` on the
**open** strip `(0,∞)×(0,π/2)` and `VanishTheta` (values at the two endpoints), which does not
connect the value at `θ = 0` with the limit `lim_{θ→0⁺} g`; the profile which is `1` in the
interior and redefined to `0` at `θ ∈ {0, π/2}` satisfies the hypotheses of R4 but not its
conclusion.  Here `hsm` is `C¹` on the *larger open* strip
`(-1,∞) × (-1, π/2+1)`, which contains the whole closed box `[0,2]×[0,π/2]` in its **interior**;
combined with `VanishTheta` this makes the two boundary values the *limits* of the slice, so the
fundamental theorem of calculus applies.

## Proof

Fix `τ` and `z ≥ 0`.  The angular slice `u = fun x => g z x τ` is `C¹` on the open interval
`(-1, π/2+1) ⊇ [0,π/2]`, and `u 0 = u (π/2) = 0` by `VanishTheta`.  Hence for `θ ∈ Iθ`

* `|g z θ τ| = |u θ - u 0| ≤ ∫_0^θ |∂_θ g|` and, dually, `= |u (π/2) - u θ| ≤ ∫_θ^{π/2} |∂_θ g|`.

On `(0,π/2)` we have `sin(2·) > 0`, so the hypothesis gives the pointwise bound
`|∂_θ g(z,·,τ)| ≤ Cθ·z²·Γ/sin(2·)`, and the two boundary rates of the density
`Γ(θ)/sin(2θ)` — `θ^{α-1}` at `0⁺` (`primBoundLeft`) and `(π/2-θ)^{2α-1}` at `(π/2)⁻`
(`primBoundRight`, the delegated companion files) — turn the two integrals into `Γ(θ)`:

* for `θ ≤ π/4`: `∫_0^θ Γ/sin(2·) ≤ M·θ^α/α ≤ (M/(α·(1/π)^α))·Γ(θ)`;
* for `θ ≥ π/4`: `∫_θ^{π/2} Γ/sin(2·) ≤ N·(π/2-θ)^{2α}/(2α) ≤ (N/(2α·c₂))·Γ(θ)`
  with `c₂ = (√2/2·(2/π)²)^α`,

using `Γ(θ) = (sinθ cos²θ)^α ≥ (1/π)^α θ^α` on `[0,π/4]` and
`Γ(θ) ≥ c₂ (π/2-θ)^{2α}` on `[π/4,π/2]` (`Gamma_left_lb`, `Gamma_right_lb`).  Finally `z ≤ 2`
gives `z² ≤ 4`, so `Cv = Cθ·4·max (M/(α·(1/π)^α)) (N/(2α·c₂))` works.

The slice step itself is `slice_ftc_abs_le`: it packages the fundamental theorem of calculus for
the `θ`-slices together with the integrability of the derivative (obtained from `measurable_deriv`
and the majorant) and the monotone comparison of the integrals.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R4b.primBoundLeft
import Submission.Work.FTS.RegPkgGal.R4b.primBoundRight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R4b

set_option autoImplicit false

/-! ## The slice calculus -/

/-- **The `θ`-derivative of a slice.**  If `G` is `C¹` on a product `s ×ˢ t` of open sets, then at
every point `(z,θ) ∈ s ×ˢ t` the angular slice `fun θ' => G z θ'` has derivative
`Work.Spaces.pth G z θ` at `θ` (which is how `pth` is defined, but here the differentiability
comes from the *uncurried* smoothness hypothesis). -/
theorem hasDerivAt_sliceTh {G : ℝ → ℝ → ℝ} {s t : Set ℝ} (hs : IsOpen s) (ht : IsOpen t)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) (s ×ˢ t)) {z θ : ℝ} (hz : z ∈ s) (hθ : θ ∈ t) :
    HasDerivAt (fun θ' => G z θ') (Work.Spaces.pth G z θ) θ := by
  have hp : (z, θ) ∈ s ×ˢ t := ⟨hz, hθ⟩
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    ((h.differentiableOn (by norm_num)).differentiableAt ((hs.prod ht).mem_nhds hp))
  have hcurve : HasDerivAt (fun x : ℝ => (z, x)) (0, 1) θ := by
    simpa using (hasDerivAt_const (x := θ) z).prodMk (hasDerivAt_id θ)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt θ hcurve
  rw [Work.Spaces.pth_eq_fderiv hd]
  simpa [Function.comp_def] using hcomp

/-- **FTC for a slice, with a majorant.**  If `G` is `C¹` on the product `s ×ˢ t` of open sets,
`z ∈ s`, `a ≤ b`, `[a,b] ⊆ t`, and `maj` is interval integrable on `[a,b]` and dominates the
norm of the slice derivative almost everywhere on `(a,b]`, then

  `|G z b - G z a| ≤ ∫_a^b maj`.

The derivative is only evaluated on the *open* interval (which is why the a.e. hypothesis
suffices), so this lemma is insensitive to the singularities of `maj` at the endpoints. -/
lemma slice_ftc_abs_le {G : ℝ → ℝ → ℝ} {s t : Set ℝ} (hs : IsOpen s) (ht : IsOpen t)
    (h : ContDiffOn ℝ 1 (Function.uncurry G) (s ×ˢ t))
    {z a b : ℝ} (hz : z ∈ s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ t)
    {maj : ℝ → ℝ} (hmaj_int : IntervalIntegrable maj volume a b)
    (hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), ‖deriv (fun θ => G z θ) x‖ ≤ maj x) :
    |G z b - G z a| ≤ ∫ x in a..b, maj x := by
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ (fun θ => G z θ) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_sliceTh hs ht h hz (hsub hx)).differentiableAt
  have hint : IntervalIntegrable (deriv (fun θ => G z θ)) volume a b := by
    refine IntervalIntegrable.mono_fun' hmaj_int ?_ ?_
    · exact (measurable_deriv _).aestronglyMeasurable
    · change ∀ᵐ x ∂(volume.restrict (Set.uIoc a b)), ‖deriv (fun θ => G z θ) x‖ ≤ maj x
      rw [Set.uIoc_of_le hab]
      exact hmaj
  have hftc : ∫ x in a..b, deriv (fun θ => G z θ) x = G z b - G z a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  have hle : ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ ≤ ∫ x in a..b, maj x := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
    · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint).norm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hmaj_int
    · exact hmaj
  have hnorm : |∫ x in a..b, deriv (fun θ => G z θ) x| ≤ ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ := by
    simpa [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (f := fun x => deriv (fun θ => G z θ) x) hab
  calc |G z b - G z a| = |∫ x in a..b, deriv (fun θ => G z θ) x| := by rw [hftc]
    _ ≤ ∫ x in a..b, ‖deriv (fun θ => G z θ) x‖ := hnorm
    _ ≤ ∫ x in a..b, maj x := hle

/-! ## The pointwise majorants of the derivative -/

/-- The left majorant: `|∂_θg| ≤ Cθ·z²·Γ/sin(2·) ≤ Cθ·z²·M·t^{α-1}` on `(0,π/4]`. -/
lemma pth_le_majorant {α Cθ M : ℝ} (hCθ : 0 ≤ Cθ) {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hdτ : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hM : ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1))
    {z x : ℝ} (hz : 0 ≤ z) (hx : 0 < x) (hxle : x ≤ Real.pi / 4) :
    |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
  have hxI : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx, by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have h1 := hdτ z x hz hxI
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin] at h1
  have hMs : Work.FTS.Regularity.Gamma α x ≤ M * x ^ (α - 1) * Real.sin (2 * x) := by
    have h := hM x hx hxle
    rw [div_le_iff₀ hsin] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hkey : |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
      ≤ (Cθ * z ^ 2 * M * x ^ (α - 1)) * Real.sin (2 * x) := by
    calc |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
        = Real.sin (2 * x) * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| := by ring
      _ ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α x := h1
      _ ≤ Cθ * z ^ 2 * (M * x ^ (α - 1) * Real.sin (2 * x)) :=
            mul_le_mul_of_nonneg_left hMs (by positivity)
      _ = (Cθ * z ^ 2 * M * x ^ (α - 1)) * Real.sin (2 * x) := by ring
  exact le_of_mul_le_mul_right hkey hsin

/-- The right majorant: `|∂_θg| ≤ Cθ·z²·N·(π/2-t)^{2α-1}` on `[π/4,π/2)`. -/
lemma pth_le_majorant_right {α Cθ N : ℝ} (hCθ : 0 ≤ Cθ) {g : ℝ → ℝ → ℝ → ℝ} {τ : ℝ}
    (hdτ : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hN : ∀ t : ℝ, Real.pi / 4 ≤ t → t < Real.pi / 2 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ N * (Real.pi / 2 - t) ^ (2 * α - 1))
    {z x : ℝ} (hz : 0 ≤ z) (hx : Real.pi / 4 ≤ x) (hxlt : x < Real.pi / 2) :
    |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x|
      ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
  have hx0 : 0 < x := by linarith [Real.pi_pos]
  have hxI : x ∈ Work.Spaces.Iθ := ⟨le_of_lt hx0, le_of_lt hxlt⟩
  have hsin : 0 < Real.sin (2 * x) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h1 := hdτ z x hz hxI
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin] at h1
  have hNs : Work.FTS.Regularity.Gamma α x
      ≤ N * (Real.pi / 2 - x) ^ (2 * α - 1) * Real.sin (2 * x) := by
    have h := hN x hx hxlt
    rw [div_le_iff₀ hsin] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hkey : |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
      ≤ (Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) * Real.sin (2 * x) := by
    calc |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| * Real.sin (2 * x)
        = Real.sin (2 * x) * |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z x| := by ring
      _ ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α x := h1
      _ ≤ Cθ * z ^ 2 * (N * (Real.pi / 2 - x) ^ (2 * α - 1) * Real.sin (2 * x)) :=
            mul_le_mul_of_nonneg_left hNs (by positivity)
      _ = (Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) * Real.sin (2 * x) := by ring
  exact le_of_mul_le_mul_right hkey hsin

/-! ## The two lower bounds for `Γ` -/

/-- `Γ(θ) ≥ (1/π)^α θ^α` on `[0,π/4]`: `Γ = sin^α·cos^{2α}` with `sinθ ≥ (2/π)θ` and
`cosθ ≥ √2/2`. -/
lemma Gamma_left_lb {α θ : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθle : θ ≤ Real.pi / 4) :
    (1 / Real.pi) ^ α * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
  have hcos2 : (0:ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos θ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hθ0
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hθle
    rwa [Real.cos_pi_div_four] at h
  have hcossq : (1/2 : ℝ) ≤ Real.cos θ ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hcos]
  have e1 : ((2 / Real.pi) * θ) ^ α ≤ Real.sin θ ^ α :=
    Real.rpow_le_rpow (by positivity) (Real.mul_le_sin hθ0 (by linarith [Real.pi_pos]))
      (le_of_lt hα)
  have e2 : ((1/2 : ℝ)) ^ α ≤ (Real.cos θ ^ 2) ^ α :=
    Real.rpow_le_rpow (by norm_num) hcossq (le_of_lt hα)
  have hmul := mul_le_mul e1 e2 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg hsin0 α)
  have hEq : (1 / Real.pi) ^ α * θ ^ α = (2 / Real.pi * θ) ^ α * (1/2 : ℝ) ^ α := by
    have A : (1 / Real.pi) ^ α * θ ^ α = ((1 / Real.pi) * θ) ^ α :=
      (Real.mul_rpow (by positivity) hθ0).symm
    have B : (2 / Real.pi * θ) ^ α * (1/2 : ℝ) ^ α = ((2 / Real.pi * θ) * (1/2)) ^ α :=
      (Real.mul_rpow (by positivity) (by norm_num)).symm
    rw [A, B]
    congr 1
    ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.mul_rpow hsin0 hcos2, hEq]
  exact hmul

/-- `Γ(θ) ≥ c₂·(π/2-θ)^{2α}` on `[π/4,π/2]`, `c₂ = (√2/2·(2/π)²)^α`: with `σ = π/2-θ` one has
`Γ(π/2-σ) = (cosσ·sin²σ)^α` and `cosσ ≥ √2/2`, `sinσ ≥ (2/π)σ`. -/
lemma Gamma_right_lb {α σ : ℝ} (hα : 0 < α) (hσ0 : 0 ≤ σ) (hσle : σ ≤ Real.pi / 4) :
    ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α * σ ^ (2 * α)
      ≤ Work.FTS.Regularity.Gamma α (Real.pi / 2 - σ) := by
  have hsinσ0 : 0 ≤ Real.sin σ := Real.sin_nonneg_of_mem_Icc ⟨hσ0, by linarith [Real.pi_pos]⟩
  have hb0 : 0 ≤ (2 / Real.pi) * σ := by positivity
  have hc : (2 / Real.pi) * σ ≤ Real.sin σ := Real.mul_le_sin hσ0 (by linarith [Real.pi_pos])
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos σ := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hσ0
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hσle
    rwa [Real.cos_pi_div_four] at h
  have hcos0 : (0:ℝ) ≤ Real.cos σ :=
    le_trans (div_nonneg (Real.sqrt_nonneg 2) (by norm_num)) hcos
  have hsq : ((2 / Real.pi) * σ) ^ 2 ≤ Real.sin σ ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hb0 hc
  have hc3 : (0:ℝ) ≤ (Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2 :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg 2) (by norm_num)) (sq_nonneg _)
  have hbase : ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2
      ≤ Real.cos σ * Real.sin σ ^ 2 := by
    have h1 : ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2
        = (Real.sqrt 2 / 2) * ((2 / Real.pi) * σ) ^ 2 := by ring
    rw [h1]
    exact mul_le_mul hcos hsq (sq_nonneg _) hcos0
  have hEq : (((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) * σ ^ 2) ^ α
      = ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α * σ ^ (2 * α) := by
    rw [Real.mul_rpow hc3 (sq_nonneg σ), ← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ0]
    norm_num
  have h := Real.rpow_le_rpow (mul_nonneg hc3 (sq_nonneg σ)) hbase (le_of_lt hα)
  rw [show (Real.cos σ * Real.sin σ ^ 2) ^ α = Work.FTS.Regularity.Gamma α (Real.pi / 2 - σ) from by
      rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.sin_pi_div_two_sub,
          Real.cos_pi_div_two_sub]] at h
  rwa [hEq] at h

/-! ## The target lemma -/

theorem van_of_dthvan {α S Cθ : ℝ} (hα : 0 < α) (hS : 0 < S) (hCθ : 0 ≤ Cθ)
    {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ)) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma α θ := by
  obtain ⟨M, hM0, hM⟩ := primBoundLeft hα
  obtain ⟨N, hN0, hN⟩ := primBoundRight hα
  set c1 : ℝ := (1 / Real.pi) ^ α with hc1
  set c2 : ℝ := ((Real.sqrt 2 / 2) * (2 / Real.pi) ^ 2) ^ α with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; exact Real.rpow_pos_of_pos (by positivity) _
  have hc2pos : 0 < c2 := by rw [hc2]; exact Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Cθ * 4 * max (M / (α * c1)) (N / (2 * α * c2)), ?_, ?_⟩
  · have hK0 : 0 ≤ max (M / (α * c1)) (N / (2 * α * c2)) :=
      le_trans (div_nonneg hM0 (by positivity)) (le_max_left _ _)
    exact mul_nonneg (by positivity) hK0
  · intro τ hτ z θ hz hz2 hθ
    have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
    rcases le_or_gt θ (Real.pi / 4) with hθle | hθgt
    · -- ## the left half: integrate from `0` up to `θ ≤ π/4`
      have hθ0 : 0 ≤ θ := hθ.1
      have hsub : Set.Icc (0:ℝ) θ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1], by linarith [hx.2, hθ.2, Real.pi_pos]⟩
      have hmaj_int : IntervalIntegrable (fun x : ℝ => Cθ * z ^ 2 * M * x ^ (α - 1)) volume 0 θ :=
        (intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < α - 1 by linarith)).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0:ℝ) θ)),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * M * x ^ (α - 1) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with x hx
        have hxle : x ≤ Real.pi / 4 := le_trans hx.2 hθle
        have h := pth_le_majorant hCθ (hd τ hτ) hM hz hx.1 hxle
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθ0 hsub hmaj_int hmaj
      have hval : ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1)
          = Cθ * z ^ 2 * M * (θ ^ α / α) := by
        rw [intervalIntegral.integral_const_mul,
            integral_rpow (Or.inl (show (-1:ℝ) < α - 1 by linarith)),
            show α - 1 + 1 = α by ring, Real.zero_rpow (ne_of_gt hα), sub_zero]
      have hGam : c1 * θ ^ α ≤ Work.FTS.Regularity.Gamma α θ := by
        rw [hc1]; exact Gamma_left_lb hα hθ0 hθle
      have hAc1 : θ ^ α * c1 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c1 (θ ^ α)]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : θ ^ α / α ≤ Work.FTS.Regularity.Gamma α θ / (α * c1) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < α),
            show Work.FTS.Regularity.Gamma α θ / (α * c1) * α
              = Work.FTS.Regularity.Gamma α θ * α / (α * c1) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < α * c1)]
        nlinarith [hAc1, hα, hc1pos]
      have hq0 : 0 ≤ θ ^ α / α := div_nonneg (Real.rpow_nonneg hθ0 α) (le_of_lt hα)
      have hz2le : z ^ 2 ≤ 4 := by nlinarith [hz, hz2]
      have hstep1 : Cθ * z ^ 2 * M * (θ ^ α / α) ≤ Cθ * 4 * (M * (θ ^ α / α)) := by
        have h1 : z ^ 2 * (M * (θ ^ α / α)) ≤ 4 * (M * (θ ^ α / α)) :=
          mul_le_mul_of_nonneg_right hz2le (mul_nonneg hM0 hq0)
        have h2 := mul_le_mul_of_nonneg_left h1 hCθ
        calc Cθ * z ^ 2 * M * (θ ^ α / α) = Cθ * (z ^ 2 * (M * (θ ^ α / α))) := by ring
          _ ≤ Cθ * (4 * (M * (θ ^ α / α))) := h2
          _ = Cθ * 4 * (M * (θ ^ α / α)) := by ring
      have hstep2 : M * (θ ^ α / α)
          ≤ (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hM0
        rwa [show M * (Work.FTS.Regularity.Gamma α θ / (α * c1))
              = (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (M / (α * c1)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hΓ0
      calc |g z θ τ| = |g z θ τ - g z 0 τ| := by
              rw [show g z 0 τ = 0 from (hvt τ hτ).1 z, sub_zero]
        _ ≤ ∫ x in (0:ℝ)..θ, Cθ * z ^ 2 * M * x ^ (α - 1) := hftc
        _ = Cθ * z ^ 2 * M * (θ ^ α / α) := hval
        _ ≤ Cθ * 4 * (M * (θ ^ α / α)) := hstep1
        _ ≤ Cθ * 4 * ((M / (α * c1)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ ≤ Cθ * 4 * (max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = Cθ * 4 * max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
              ring
    · -- ## the right half: integrate from `θ > π/4` up to `π/2`
      have hθpi2 : θ ≤ Real.pi / 2 := hθ.2
      have hsub : Set.Icc θ (Real.pi / 2) ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
        intro x hx
        exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
      have hbase : IntervalIntegrable (fun x : ℝ => x ^ (2 * α - 1)) volume 0 (Real.pi / 2 - θ) :=
        intervalIntegral.intervalIntegrable_rpow' (show (-1:ℝ) < 2 * α - 1 by linarith)
      have hcomp : IntervalIntegrable (fun x : ℝ => (Real.pi / 2 - x) ^ (2 * α - 1))
          volume (Real.pi / 2) θ := by
        have h' := hbase.comp_sub_left (Real.pi / 2)
        rw [sub_zero, show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h'
        exact h'
      have hmaj_int : IntervalIntegrable
          (fun x : ℝ => Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)) volume θ (Real.pi / 2) :=
        (hcomp.symm).const_mul _
      have hmaj : ∀ᵐ x ∂(volume.restrict (Set.Ioc θ (Real.pi / 2))),
          ‖deriv (fun θ' => g z θ' τ) x‖ ≤ Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := by
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
          rw [MeasureTheory.ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact MeasureTheory.measure_singleton _
        filter_upwards [hae] with x hx hxmem
        have hx1 : Real.pi / 4 ≤ x := le_trans (le_of_lt hθgt) hxmem.1.le
        have hx2 : x < Real.pi / 2 := lt_of_le_of_ne hxmem.2 hx
        have h := pth_le_majorant_right hCθ (hd τ hτ) hN hz hx1 hx2
        simpa [Work.Spaces.pth, Work.FTS.Regularity.gSlice, Real.norm_eq_abs] using h
      have hftc := slice_ftc_abs_le isOpen_Ioi isOpen_Ioo (hsm τ hτ) hzmem hθpi2 hsub hmaj_int hmaj
      have hval : ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1)
          = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s ^ (2 * α - 1)) (Real.pi / 2),
            show Real.pi / 2 - Real.pi / 2 = 0 by ring,
            integral_rpow (Or.inl (show (-1:ℝ) < 2 * α - 1 by linarith)),
            show 2 * α - 1 + 1 = 2 * α by ring,
            Real.zero_rpow (by linarith : 2 * α ≠ 0), sub_zero]
      have hσ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθpi2]
      have hσle : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith [hθgt]
      have hGam : c2 * (Real.pi / 2 - θ) ^ (2 * α) ≤ Work.FTS.Regularity.Gamma α θ := by
        have h := Gamma_right_lb hα hσ0 hσle
        rwa [show Real.pi / 2 - (Real.pi / 2 - θ) = θ by ring] at h
      have hAc2 : (Real.pi / 2 - θ) ^ (2 * α) * c2 ≤ Work.FTS.Regularity.Gamma α θ := by
        linarith [hGam, mul_comm c2 ((Real.pi / 2 - θ) ^ (2 * α))]
      have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
      have hquot : (Real.pi / 2 - θ) ^ (2 * α) / (2 * α)
          ≤ Work.FTS.Regularity.Gamma α θ / (2 * α * c2) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 2 * α),
            show Work.FTS.Regularity.Gamma α θ / (2 * α * c2) * (2 * α)
              = Work.FTS.Regularity.Gamma α θ * (2 * α) / (2 * α * c2) by ring,
            le_div_iff₀ (by positivity : (0:ℝ) < 2 * α * c2)]
        nlinarith [hAc2, hα, hc2pos]
      have hq0 : 0 ≤ (Real.pi / 2 - θ) ^ (2 * α) / (2 * α) :=
        div_nonneg (Real.rpow_nonneg hσ0 (2 * α)) (by linarith)
      have hz2le : z ^ 2 ≤ 4 := by nlinarith [hz, hz2]
      have hstep1 : Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
          ≤ Cθ * 4 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by
        have h1 : z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)))
            ≤ 4 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) :=
          mul_le_mul_of_nonneg_right hz2le (mul_nonneg hN0 hq0)
        have h2 := mul_le_mul_of_nonneg_left h1 hCθ
        calc Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
            = Cθ * (z ^ 2 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)))) := by ring
          _ ≤ Cθ * (4 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)))) := h2
          _ = Cθ * 4 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := by ring
      have hstep2 : N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))
          ≤ (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
        have h1 := mul_le_mul_of_nonneg_left hquot hN0
        rwa [show N * (Work.FTS.Regularity.Gamma α θ / (2 * α * c2))
              = (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ by ring] at h1
      have hstep3 : (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ
          ≤ max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hΓ0
      calc |g z θ τ| = |g z (Real.pi / 2) τ - g z θ τ| := by
              rw [show g z (Real.pi / 2) τ = 0 from (hvt τ hτ).2 z, zero_sub, abs_neg]
        _ ≤ ∫ x in θ..(Real.pi / 2), Cθ * z ^ 2 * N * (Real.pi / 2 - x) ^ (2 * α - 1) := hftc
        _ = Cθ * z ^ 2 * N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α)) := hval
        _ ≤ Cθ * 4 * (N * ((Real.pi / 2 - θ) ^ (2 * α) / (2 * α))) := hstep1
        _ ≤ Cθ * 4 * ((N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ ≤ Cθ * 4 * (max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = Cθ * 4 * max (M / (α * c1)) (N / (2 * α * c2)) * Work.FTS.Regularity.Gamma α θ := by
              ring

end Work.FTS.RegPkgGal.R4b
