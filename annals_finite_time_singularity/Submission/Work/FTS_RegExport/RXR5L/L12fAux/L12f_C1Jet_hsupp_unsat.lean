/-
# `L12f_C1Jet_hsupp_unsat` — the `hsupp` of the assigned `L12f_C1Jet` is **unsatisfiable**

Machine-checked companion of `L12f_C1Jet_hsupp_note`.  The main result is

`hsupp_pExp_unsatisfiable` : for `α > 0` and `S ≥ 0` there is **no** `Lf > 0` with
`profFull (pExp α) (gS α (tauExt g)) z θ τ = 0` for all `z ≥ Lf` — i.e. the hypothesis
`hsupp` of `Work.FTS_RegExport.RXR5L.L12f_C1Jet` has no model (the statement is vacuous).

The two ingredients:

* `profFull_pExp_forces_Fstar_eq` (`L12f_C1Jet_hsupp_note`): the hypothesis forces
  `Fstar (pExp (pExp α)) z θ = Fstar (pExp α) z θ` for every `θ ∉ Iθ`, because the else-branch of
  `gS` is definitionally `-Fstar (pExp α)`;
* `c_pos` : `0 < c β` for every `β > 0` (the integrand `Γ_β K` is bounded below by
  `(1/4)^{β/3}·(3/4)` on `Icc (π/6) (π/4)`, where `u = sinθcos²θ ∈ [1/4,1]`);

and the conclusion: at the two angles `3π/4` and `2π/3` (both outside `Iθ`, with
`u(3π/4) = √2/4 ≠ √3/8 = u(2π/3)`), the forced identity says `3·u(θ)^{2α}·c(3α) = c(9α)` —
impossible, since `u ↦ u^{2α}` is strictly increasing (`α > 0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_hsupp_note
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false

/-! ## §1 A uniform lower bound for the angular integrand of `c`, for every exponent `> 0` -/

theorem gamK_lower_pos {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ∈ Set.Icc (π / 6) (π / 4)) :
    (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ := by
  have hpi := Real.pi_pos
  have hθ1 : π / 6 ≤ θ := hθ.1
  have hθ2 : θ ≤ π / 4 := hθ.2
  have hmem1 : θ ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hmem2 : π / 6 ∈ Set.Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hsin1 : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 := Real.monotoneOn_sin hmem2 hmem1 hθ1
    rwa [Real.sin_pi_div_six] at h1
  have hmem3 : θ ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
  have hmem4 : π / 4 ∈ Set.Icc 0 π := ⟨by linarith, by linarith⟩
  have hcos1 : Real.cos (π / 4) ≤ Real.cos θ := Real.antitoneOn_cos hmem3 hmem4 hθ2
  rw [Real.cos_pi_div_four] at hcos1
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    have h2 : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have h3 : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos θ ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg 2]) hcos1
    linarith [h2, h3]
  have hu : (1 : ℝ) / 4 ≤ Real.sin θ * Real.cos θ ^ 2 := by nlinarith [hsin1, hcos2]
  have hsin0 : 0 ≤ Real.sin θ := by linarith
  have hcos20 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hGam : (1 / 4 : ℝ) ^ (β / 3) ≤ Work.Spaces.Gam β θ := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow (by norm_num) hu (by positivity)
  have hK : (3 / 4 : ℝ) ≤ Work.Spaces.K θ := by
    rw [Work.Spaces.K]
    nlinarith [hu, hsin0, hcos20]
  have hGam0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (β / 3) := Real.rpow_nonneg (by norm_num) _
  calc (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) ≤ (1 / 4 : ℝ) ^ (β / 3) * Work.Spaces.K θ :=
        mul_le_mul_of_nonneg_left hK hGam0
    _ ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ :=
        mul_le_mul_of_nonneg_right hGam (by rw [Work.Spaces.K]; positivity)

/-! ## §2 `c` is positive on `(0,∞)` -/

theorem c_pos {β : ℝ} (hβ0 : 0 < β) : 0 < Work.Spaces.c β := by
  have hpi := Real.pi_pos
  have h_int : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam β θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK β hβ0
  have h_nonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (0 : ℝ) ≤ Work.Spaces.Gam β θ * Work.Spaces.K θ := by
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun θ hθ => (Work.Spaces.gamK_bounds β θ hβ0 hθ).1
  have hvol : volume.real (Set.Icc (π / 6) (π / 4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsub : Set.Icc (π / 6) (π / 4) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hst : Set.Icc (π / 6) (π / 4) ≤ᵐ[volume] Work.Spaces.Iθ := by
    filter_upwards with θ hθ
    exact hsub hθ
  have hfin : volume (Set.Icc (π / 6) (π / 4)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hge : (1 / 4 : ℝ) ^ (β / 3) * (3 / 4) * volume.real (Set.Icc (π / 6) (π / 4))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam β θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
      (fun θ hθ => gamK_lower_pos hβ0 hθ) (h_int.mono_set hsub)
  have hle : ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam β θ * Work.Spaces.K θ
      ≤ Work.Spaces.c β := by
    rw [Work.Spaces.c]
    exact MeasureTheory.setIntegral_mono_set h_int h_nonneg hst
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ (β / 3) * (3 / 4)
      * volume.real (Set.Icc (π / 6) (π / 4)) := by
    rw [hvol]
    have h1 : (0 : ℝ) < (1 / 4 : ℝ) ^ (β / 3) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  linarith

/-! ## §3 The angular values `u = sinθcos²θ` at `3π/4` and `2π/3` -/

theorem sin_cos_sq_three_pi_div_four :
    Real.sin (3 * π / 4) * Real.cos (3 * π / 4) ^ 2 = Real.sqrt 2 / 4 := by
  have h1 : 3 * π / 4 = π - π / 4 := by ring
  rw [h1, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
  have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h2]

theorem sin_cos_sq_two_pi_div_three :
    Real.sin (2 * π / 3) * Real.cos (2 * π / 3) ^ 2 = Real.sqrt 3 / 8 := by
  have h1 : 2 * π / 3 = π - π / 3 := by ring
  rw [h1, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_pi_div_three, Real.cos_pi_div_three]
  have h2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h2]

theorem sqrt_two_div_four_ne_sqrt_three_div_eight :
    Real.sqrt 2 / 4 ≠ Real.sqrt 3 / 8 := by
  intro h
  have h2 : Real.sqrt 2 * 8 = Real.sqrt 3 * 4 := by
    field_simp at h
    linarith [h]
  have h3 : (Real.sqrt 2 * 8) ^ 2 = (Real.sqrt 3 * 4) ^ 2 := by rw [h2]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)] at h3
  norm_num at h3

/-! ## §4 The identity forced by `hsupp` implies a fixed ratio -/

theorem three_mul_rpow_mul_c_eq {α u z : ℝ} (hα : 0 < α) (hu : 0 < u) (hz : 0 < z)
    {θ : ℝ}
    (hGam9 : Work.Spaces.Gam (9 * α) θ = u ^ (2 * α) * u ^ α)
    (hGam3 : Work.Spaces.Gam (3 * α) θ = u ^ α)
    (h : Work.Construction.Fstar (9 * α) z θ = Work.Construction.Fstar (3 * α) z θ) :
    3 * u ^ (2 * α) * Work.Spaces.c (3 * α) = Work.Spaces.c (9 * α) := by
  have hc3 : Work.Spaces.c (3 * α) ≠ 0 := ne_of_gt (c_pos (by linarith))
  have hc9 : Work.Spaces.c (9 * α) ≠ 0 := ne_of_gt (c_pos (by linarith))
  have hF : Work.FM.Fstar z ≠ 0 := by
    rw [Work.FM.Fstar]
    have h1 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
    exact div_ne_zero (by positivity) (ne_of_gt h1)
  -- unfold the two profiles and cancel `F̂(z)`
  rw [Work.Construction.Fstar, Work.Construction.Fstar] at h
  rw [hGam9, hGam3] at h
  have hkey : 9 * α * ((u ^ (2 * α) * u ^ α) / Work.Spaces.c (9 * α))
      = 3 * α * (u ^ α / Work.Spaces.c (3 * α)) := mul_right_cancel₀ hF h
  -- put both sides over their denominator and cross-multiply
  rw [← mul_div_assoc, ← mul_div_assoc] at hkey
  have hmain := (div_eq_div_iff hc9 hc3).mp hkey
  -- cancel the common factor `3αu^α`
  have h2 : (3 * α * u ^ α) * (3 * u ^ (2 * α) * Work.Spaces.c (3 * α))
      = (3 * α * u ^ α) * Work.Spaces.c (9 * α) := by
    have h3 : (3 * α * u ^ α) * (3 * u ^ (2 * α) * Work.Spaces.c (3 * α))
        = 9 * α * (u ^ (2 * α) * u ^ α) * Work.Spaces.c (3 * α) := by ring
    rw [h3, hmain]
  exact mul_left_cancel₀ (by positivity) h2

/-! ## §5 The refutation -/

theorem hsupp_pExp_unsatisfiable {α S : ℝ} {g : Work.FTS.Galerkin.Fam} (hα : 0 < α)
    (hS : 0 ≤ S) :
    ¬ (∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0) := by
  rintro ⟨Lf, hLf, hvan⟩
  have hpi := Real.pi_pos
  have hτ0 : (0 : ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, hS⟩
  have hnot1 : ¬ (3 * π / 4 ∈ Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rintro ⟨-, h2⟩
    linarith
  have hnot2 : ¬ (2 * π / 3 ∈ Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    rintro ⟨-, h2⟩
    linarith
  have hc1 := profFull_pExp_forces_Fstar_eq (g := g) hLf hvan hτ0 le_rfl hnot1
  have hc2 := profFull_pExp_forces_Fstar_eq (g := g) hLf hvan hτ0 le_rfl hnot2
  have hu1 : (0 : ℝ) < Real.sqrt 2 / 4 := by positivity
  have hu2 : (0 : ℝ) < Real.sqrt 3 / 8 := by positivity
  have hpe : Work.FTS.Regularity.pExp (Work.FTS.Regularity.pExp α) = 9 * α := by
    rw [Work.FTS.Regularity.pExp_eq, Work.FTS.Regularity.pExp_eq]; ring
  have hpe3 : Work.FTS.Regularity.pExp α = 3 * α := by rw [Work.FTS.Regularity.pExp_eq]
  -- θ = 3π/4
  have hc1' : Work.Construction.Fstar (9 * α) Lf (3 * π / 4)
      = Work.Construction.Fstar (3 * α) Lf (3 * π / 4) := by
    rw [← hpe, ← hpe3]; exact hc1
  have hg1 : Work.Spaces.Gam (9 * α) (3 * π / 4)
      = (Real.sqrt 2 / 4) ^ (2 * α) * (Real.sqrt 2 / 4) ^ α := by
    rw [Work.Spaces.Gam, sin_cos_sq_three_pi_div_four,
      show (9 * α) / 3 = 2 * α + α by ring, Real.rpow_add hu1]
  have hg3_1 : Work.Spaces.Gam (3 * α) (3 * π / 4) = (Real.sqrt 2 / 4) ^ α := by
    rw [Work.Spaces.Gam, sin_cos_sq_three_pi_div_four, show (3 * α) / 3 = α by ring]
  have hr1 := three_mul_rpow_mul_c_eq hα hu1 hLf hg1 hg3_1 hc1'
  -- θ = 2π/3
  have hc2' : Work.Construction.Fstar (9 * α) Lf (2 * π / 3)
      = Work.Construction.Fstar (3 * α) Lf (2 * π / 3) := by
    rw [← hpe, ← hpe3]; exact hc2
  have hg2 : Work.Spaces.Gam (9 * α) (2 * π / 3)
      = (Real.sqrt 3 / 8) ^ (2 * α) * (Real.sqrt 3 / 8) ^ α := by
    rw [Work.Spaces.Gam, sin_cos_sq_two_pi_div_three,
      show (9 * α) / 3 = 2 * α + α by ring, Real.rpow_add hu2]
  have hg3_2 : Work.Spaces.Gam (3 * α) (2 * π / 3) = (Real.sqrt 3 / 8) ^ α := by
    rw [Work.Spaces.Gam, sin_cos_sq_two_pi_div_three, show (3 * α) / 3 = α by ring]
  have hr2 := three_mul_rpow_mul_c_eq hα hu2 hLf hg2 hg3_2 hc2'
  -- the two forced ratios cannot both hold
  have hc3 : Work.Spaces.c (3 * α) ≠ 0 := ne_of_gt (c_pos (by linarith))
  have hEq : (Real.sqrt 2 / 4) ^ (2 * α) = (Real.sqrt 3 / 8) ^ (2 * α) := by
    have hmid : (3 * Work.Spaces.c (3 * α)) * (Real.sqrt 2 / 4) ^ (2 * α)
        = (3 * Work.Spaces.c (3 * α)) * (Real.sqrt 3 / 8) ^ (2 * α) := by
      rw [show (3 * Work.Spaces.c (3 * α)) * (Real.sqrt 2 / 4) ^ (2 * α)
            = 3 * (Real.sqrt 2 / 4) ^ (2 * α) * Work.Spaces.c (3 * α) by ring,
        hr1,
        show Work.Spaces.c (9 * α)
            = 3 * (Real.sqrt 3 / 8) ^ (2 * α) * Work.Spaces.c (3 * α) from hr2.symm,
        show 3 * (Real.sqrt 3 / 8) ^ (2 * α) * Work.Spaces.c (3 * α)
            = (3 * Work.Spaces.c (3 * α)) * (Real.sqrt 3 / 8) ^ (2 * α) by ring]
    exact mul_left_cancel₀ (by positivity : (3 : ℝ) * Work.Spaces.c (3 * α) ≠ 0) hmid
  have hpos2 : (0 : ℝ) < 2 * α := by linarith
  rcases lt_trichotomy (Real.sqrt 2 / 4) (Real.sqrt 3 / 8) with hlt | heq | hgt
  · have h3 := Real.rpow_lt_rpow hu1.le hlt hpos2
    rw [hEq] at h3
    exact lt_irrefl _ h3
  · exact sqrt_two_div_four_ne_sqrt_three_div_eight heq
  · have h3 := Real.rpow_lt_rpow hu2.le hgt hpos2
    rw [hEq] at h3
    exact lt_irrefl _ h3

end Work.FTS_RegExport.RXR5L.L12fAux
