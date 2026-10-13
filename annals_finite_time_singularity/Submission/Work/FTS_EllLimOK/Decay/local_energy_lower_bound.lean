/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Decay.local_energy_lower_bound`

A value `|Ψ z θ₀| ≥ ε` at a large `z` (with the jet of `Ψ` bounded by `C` on the open quadrant)
forces the *weighted angular energy* `∫_θ HkIntegrand α 0 Ψ z' θ` to stay `≥ c > 0` on the whole
window `[z, z+1]`, with a constant `c > 0` depending only on `α`, `C`, `ε` and `θ₀`.

The mechanism is elementary and uses the two Lipschitz bounds of `DecayTools`:
* in `θ`, `|∂_θΨ| ≤ C/sin(2θ) ≤ C/s` on a fixed window around `θ₀` (where `s > 0`), so the
  value `ε` at `θ₀` propagates to a whole `θ`-interval of length `~ ε/C`;
* in `z`, `|∂_zΨ| ≤ C/z ≤ ε/4` on the window `[z, z+1]` as soon as `z ≥ 4C/ε`.
Hence `|Ψ z' θ| ≥ 5ε/8` on that `θ`-interval, and since the `k = 0` integrand is the square
of `Ψ · (w(z)/sin(2θ)^{η/2})` with `w(z)/sin(2θ)^{η/2} ≥ 1` there, the angular integral is
`≥ (5ε/8)² · (length)`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.BoxReg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.Decay

set_option autoImplicit false

theorem local_energy_lower_bound {α C : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hbox : Work.FTS_EllLimOK.BoxReg Ψ)
    (hHk : Work.Spaces.HkMem α 0 Ψ)
    (hDz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 1 0 Ψ z θ| ≤ C)
    (hDth : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed 0 1 Ψ z θ| ≤ C)
    (hC : 0 < C) {ε : ℝ} (hε : 0 < ε) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, max 1 (4 * C / ε) ≤ z → ε ≤ |Ψ z θ₀| →
      ∀ z' ∈ Set.Icc z (z + 1),
        c ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z' θ := by
  /- ### Step 1: the geometric data attached to `θ₀` -/
  have hθ₀0 : 0 < θ₀ := hθ₀.1
  have hθ₀lt : θ₀ < Real.pi / 2 := hθ₀.2
  have hS2pos : 0 < Real.sin (2 * θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the base half-width `u` of the `θ`-window and the resulting lower bound `s` for `sin 2θ`
  set u : ℝ := min (θ₀ / 2) (min ((Real.pi / 2 - θ₀) / 2) (Real.sin (2 * θ₀) / 8)) with hu
  have hu_le1 : u ≤ θ₀ / 2 := hu.le.trans (min_le_left _ _)
  have hu_le2 : u ≤ min ((Real.pi / 2 - θ₀) / 2) (Real.sin (2 * θ₀) / 8) :=
    hu.le.trans (min_le_right _ _)
  have hu_le3 : u ≤ (Real.pi / 2 - θ₀) / 2 := hu_le2.trans (min_le_left _ _)
  have hu_le4 : u ≤ Real.sin (2 * θ₀) / 8 := hu_le2.trans (min_le_right _ _)
  have hu_pos : 0 < u := by
    rw [hu]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  set s : ℝ := 3 * Real.sin (2 * θ₀) / 4 with hs
  have hs_pos : 0 < s := by rw [hs]; linarith
  have hsne : s ≠ 0 := ne_of_gt hs_pos
  have hCne : C ≠ 0 := ne_of_gt hC
  -- `sin 2θ ≥ s` on the window `[θ₀ - u, θ₀ + u]`
  have hsin_ge : ∀ θ ∈ Set.Icc (θ₀ - u) (θ₀ + u), s ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have h1 : |θ - θ₀| ≤ u := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have h2 : |2 * θ - 2 * θ₀| ≤ 2 * u := by
      have hθ2 : 2 * θ - 2 * θ₀ = 2 * (θ - θ₀) := by ring
      rw [hθ2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h3 : |Real.sin (2 * θ) - Real.sin (2 * θ₀)| ≤ 2 * u :=
      le_trans (Real.abs_sin_sub_sin_le _ _) h2
    have h4 : 2 * u ≤ Real.sin (2 * θ₀) / 4 := by linarith [hu_le4]
    have h5 := (abs_le.mp h3).1
    rw [hs]
    linarith
  /- ### Step 2: the final window, shrunk so that the value at `θ₀` survives -/
  set δ : ℝ := min u (ε * s / (8 * C)) with hδ
  have hδ_le_u : δ ≤ u := hδ.le.trans (min_le_left _ _)
  have hδ_le_eps : δ ≤ ε * s / (8 * C) := hδ.le.trans (min_le_right _ _)
  have hδ_pos : 0 < δ := by
    rw [hδ]
    exact lt_min hu_pos (div_pos (mul_pos hε hs_pos) (by linarith))
  have ha_pos : 0 < θ₀ - δ := by linarith [hu_le1, hδ_le_u, hθ₀0]
  have hb_lt : θ₀ + δ < Real.pi / 2 := by linarith [hu_le3, hδ_le_u, hθ₀lt]
  have hab : θ₀ - δ ≤ θ₀ + δ := by linarith [hδ_pos]
  have hsub : Set.Ioc (θ₀ - δ) (θ₀ + δ) ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, hb_lt]⟩
  have hwin : ∀ θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ), θ ∈ Set.Icc (θ₀ - u) (θ₀ + u) :=
    fun θ hθ => ⟨by linarith [hδ_le_u, hθ.1], by linarith [hδ_le_u, hθ.2]⟩
  have hθ₀mem : θ₀ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ) :=
    ⟨by linarith [hδ_pos], by linarith [hδ_pos]⟩
  refine ⟨(5 * ε / 8) ^ 2 * (2 * δ),
    mul_pos (pow_pos (by linarith : 0 < 5 * ε / 8) 2) (by linarith), ?_⟩
  /- ### Step 3: the local energy bound on `[z, z+1]` -/
  intro z hz hΨz z' hz'
  have hz1 : 1 ≤ z := le_trans (le_max_left _ _) hz
  have hzC : 4 * C / ε ≤ z := le_trans (le_max_right _ _) hz
  have hzpos : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hz'1 : z ≤ z' := hz'.1
  have hz'le : z' ≤ z + 1 := hz'.2
  have hz'ge1 : 1 ≤ z' := le_trans hz1 hz'1
  have hz'pos : 0 < z' := lt_of_lt_of_le zero_lt_one hz'ge1
  have hz'mem : z' ∈ Work.Spaces.Iz := hz'pos.le
  have h4C : 4 * C ≤ ε * z := by
    have h := hzC
    rw [div_le_iff₀ hε] at h
    linarith
  have hCz : C / z ≤ ε / 4 := by
    rw [div_le_iff₀ hzpos]
    linarith
  have hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 Ψ z' θ)
      Work.Spaces.Iθ := hHk.1 z' hz'mem
  have hlow : ∀ θ ∈ Set.Icc (θ₀ - δ) (θ₀ + δ),
      (5 * ε / 8) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 Ψ z' θ := by
    intro θ hθmem
    have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ha_pos, hθmem.1], by linarith [hθmem.2, hb_lt]⟩
    -- the value at `θ₀` propagates to the window at the same `z`
    have hthZ : |Ψ z θ - Ψ z θ₀| ≤ C / s * |θ - θ₀| :=
      abs_slice_th_sub_le (a := θ₀ - δ) (b := θ₀ + δ) (z := z) (s := s)
        hbox hDth hC hzpos ha_pos hb_lt (fun t ht => hsin_ge t (hwin t ht)) hs_pos
        hθ₀mem hθmem
    have hθδ : |θ - θ₀| ≤ δ := abs_le.mpr ⟨by linarith [hθmem.1], by linarith [hθmem.2]⟩
    have hCs : 0 ≤ C / s := (div_pos hC hs_pos).le
    have hbound1 : C / s * |θ - θ₀| ≤ ε / 8 := by
      have h1 : C / s * |θ - θ₀| ≤ C / s * δ := mul_le_mul_of_nonneg_left hθδ hCs
      have h2 : C / s * δ ≤ C / s * (ε * s / (8 * C)) :=
        mul_le_mul_of_nonneg_left hδ_le_eps hCs
      have h3 : C / s * (ε * s / (8 * C)) = ε / 8 := by
        field_simp
      linarith
    have hΨzθ : 7 * ε / 8 ≤ |Ψ z θ| := by
      have hup : |Ψ z θ| - |Ψ z θ₀| ≤ ε / 8 :=
        le_trans (abs_sub_abs_le_abs_sub (Ψ z θ) (Ψ z θ₀)) (le_trans hthZ hbound1)
      have hdown : |Ψ z θ₀| - |Ψ z θ| ≤ ε / 8 := by
        have h3 : |Ψ z θ₀ - Ψ z θ| ≤ ε / 8 := by
          rw [abs_sub_comm]
          exact le_trans hthZ hbound1
        exact le_trans (abs_sub_abs_le_abs_sub (Ψ z θ₀) (Ψ z θ)) h3
      linarith
    -- and then across the window `[z, z+1]`
    have hzZ : |Ψ z' θ - Ψ z θ| ≤ ε / 4 := by
      have h1 : |Ψ z' θ - Ψ z θ| ≤ C / z * (z' - z) :=
        abs_slice_z_sub_le hbox hDz hC hzpos hz'1 hθIoo
      have h2 : C / z * (z' - z) ≤ C / z * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (div_pos hC hzpos).le
      have h3 : C / z * 1 ≤ ε / 4 := by rw [mul_one]; exact hCz
      linarith
    have hΨz'θ : 5 * ε / 8 ≤ |Ψ z' θ| := by
      have hup : |Ψ z' θ| - |Ψ z θ| ≤ ε / 4 :=
        le_trans (abs_sub_abs_le_abs_sub (Ψ z' θ) (Ψ z θ)) hzZ
      have hdown : |Ψ z θ| - |Ψ z' θ| ≤ ε / 4 := by
        have h3 : |Ψ z θ - Ψ z' θ| ≤ ε / 4 := by
          rw [abs_sub_comm]
          exact hzZ
        exact le_trans (abs_sub_abs_le_abs_sub (Ψ z θ) (Ψ z' θ)) h3
      linarith
    -- the integrand is a square with weight factor `≥ 1`
    rw [HkIntegrand_zero_eq]
    have hw : 1 ≤ Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      one_le_w_div_sin hz'ge1 hθIoo
    have hwpos : 0 < Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      lt_of_lt_of_le zero_lt_one hw
    have habs : |Ψ z' θ * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        = |Ψ z' θ| * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [abs_mul, abs_of_pos hwpos]
    have hge : 5 * ε / 8 ≤
        |Ψ z' θ * (Work.Spaces.w z' / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
      rw [habs]
      have := mul_le_mul hΨz'θ hw zero_le_one (abs_nonneg (Ψ z' θ))
      linarith
    rw [sq_le_sq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 5 * ε / 8)]
    exact hge
  have hfin := thetaIntegral_ge_of_lower_bound
    (f := fun θ => Work.Spaces.HkIntegrand α 0 Ψ z' θ)
    (a := θ₀ - δ) (b := θ₀ + δ) (c := (5 * ε / 8) ^ 2)
    hab hsub hint (fun θ => by rw [HkIntegrand_zero_eq]; exact sq_nonneg _) hlow
  have hlen : θ₀ + δ - (θ₀ - δ) = 2 * δ := by ring
  rw [hlen] at hfin
  exact hfin

end Work.FTS_EllLimOK.Decay
