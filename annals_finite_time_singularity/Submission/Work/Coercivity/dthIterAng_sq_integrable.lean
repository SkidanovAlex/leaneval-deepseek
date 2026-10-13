/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of `(D_θ^i Γ)² sin(2θ)^{-γ}` and `(D_θ^i Γ)² sin(2θ)^{-η}` on `[0,π/2]`

The angular integrals `AngGam α i` and `AngEta α i` of `CTDefs` are the `θ`-integrals of
`(D_θ^i Γ)² sin(2θ)^{-γ}` resp. `(D_θ^i Γ)² sin(2θ)^{-η}`; this module proves that the
integrands are `IntegrableOn Iθ`, so that those integrals are the honest (finite) values of
integrable functions rather than junk.

Both statements follow from the single structural fact, established in
`Submission/Work/Spaces/Gamma_WlInf.lean`,

  `|D_θ^i Γ(θ)| ≤ C_i · Γ(θ)`   on `Iθ`   (`C_i` depending only on `i` and `α`),

together with `Γ(θ)² ≤ sin(2θ)^{2α/3}`.  Since `sin(2θ)^{-q}` is integrable on `Iθ` for
`q ∈ (0,1)`, the `γ`-integrand is dominated by `C_i² sin(2θ)^{2α/3 - γ}` with
`2α/3 - γ = -(1 - 17α/30) ∈ (-1,0)`, and the `η`-integrand by `C_i² sin(2θ)^{-η}` with
`η = 99/100 ∈ (0,1)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Coercivity.integral_sin_two_neg_rpow_le
import Submission.Work.Coercivity.gamDth_l2_bound
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

namespace CT

/-- `CT.DthIterAng i` is the `i`-fold iterate of the univariate operator `Spaces.dthU`
(`dthU φ = sin(2·) · φ'`); in particular `D_θ^i Γ = dthU^[i] Γ`. -/
lemma DthIterAng_eq_iterate (i : ℕ) (g : ℝ → ℝ) :
    DthIterAng i g = Spaces.dthU^[i] g := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [DthIterAng_succ, ih, Function.iterate_succ_apply']
      rfl

end CT

/-- `Γ(θ) = (sin θ cos²θ)^{α/3}` is continuous on the angular interval `Iθ`. -/
lemma dthIterAng_continuousOn_Gam (α : ℝ) (hα : 0 < α) :
    ContinuousOn (Spaces.Gam α) Spaces.Iθ := by
  change ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Spaces.Iθ
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Spaces.Iθ := by
    fun_prop
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  exact hbase.rpow_const (p := α / 3) (fun θ _ => Or.inr hα3)

/-- Every angular derivative `D_θ^i Γ` is continuous on `Iθ`.

For `i ≥ 1`, `D_θ^i Γ` agrees on `Iθ` with the everywhere smooth function
`α · Tfun (i-1) α · Γ`: the identity `dthU_iter_Gam` holds on the open interval
`(0,π/2)`, and at both endpoints the two sides vanish (`sin(2θ) = 0` kills the left-hand
side, and `Γ = 0` kills the right-hand side). -/
lemma dthIterAng_continuousOn (i : ℕ) (α : ℝ) (hα : 0 < α) :
    ContinuousOn (CT.DthIterAng i (Spaces.Gam α)) Spaces.Iθ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simpa using dthIterAng_continuousOn_Gam α hα
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have heq : ∀ θ ∈ Spaces.Iθ,
        CT.DthIterAng (k + 1) (Spaces.Gam α) θ = α * Spaces.Tfun k α θ * Spaces.Gam α θ := by
      intro θ hθ
      rw [CT.DthIterAng_eq_iterate]
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        rw [Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Spaces.Gam α t) (by omega)
          (by simp), Spaces.Gam_zero_left α (ne_of_gt hα)]
        ring
      rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Spaces.Gam α t) (by omega)
          (by rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]),
          Spaces.Gam_zero_right α (ne_of_gt hα)]
        ring
      · exact Spaces.dthU_iter_Gam k α hα ⟨h0, h1⟩
    have hcont : ContinuousOn (fun θ : ℝ => α * Spaces.Tfun k α θ * Spaces.Gam α θ) Spaces.Iθ :=
      ((continuous_const.mul (Spaces.Tfun_smooth k α).continuous).continuousOn).mul
        (dthIterAng_continuousOn_Gam α hα)
    exact hcont.congr (fun θ hθ => heq θ hθ)

/-- **A uniform bound `|D_θ^i Γ| ≤ C_i Γ` on `Iθ`.**  For `i = 0` one can take `C_0 = 1`
(since `0 ≤ Γ ≤ 1`), and for `i ≥ 1` the bound `Spaces.dthU_Gam_le` gives
`|D_θ^i Γ| ≤ α · tBound (i-1) 0 · Γ`. -/
lemma dthIterAng_le_Gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    refine ⟨1, zero_le_one, fun θ hθ => ?_⟩
    rw [CT.DthIterAng_zero]
    exact le_of_eq (by rw [one_mul, abs_of_nonneg (Spaces.Gam_bounds α θ hα hθ).1])
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    refine ⟨α * Spaces.tBound k 0, mul_nonneg (le_of_lt hα) (Spaces.tBound_nonneg k 0),
      fun θ hθ => ?_⟩
    rw [CT.DthIterAng_eq_iterate]
    simpa using Spaces.dthU_Gam_le (k + 1) (by omega) α hα hα1 θ hθ

/-- The `γ`-integrand `(D_θ^i Γ)² sin(2θ)^{-γ}` is dominated pointwise by
`C_i² sin(2θ)^{2α/3 - γ}` on `Iθ`. -/
lemma dthIterAng_sq_mul_le_gam {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C) {i : ℕ}
    (hbound : ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ) :
    ∀ θ ∈ Spaces.Iθ,
      (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by
  intro θ hθ
  have hG := Spaces.Gam_bounds α θ hα hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hne : 2 * α / 3 + -(Spaces.gam α) ≠ 0 := by
    have hlt : 2 * α / 3 < Spaces.gam α := by
      rw [Spaces.gam]
      nlinarith
    linarith
  have hsq : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    have h2 : |CT.DthIterAng i (Spaces.Gam α) θ| ≤ |C * Spaces.Gam α θ| := by
      rw [abs_of_nonneg (mul_nonneg hC hG.1)]
      exact hbound θ hθ
    have h1 : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := by
      calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
          = |CT.DthIterAng i (Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
        _ ≤ |C * Spaces.Gam α θ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = (C * Spaces.Gam α θ) ^ 2 := by rw [sq_abs]
    calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := h1
      _ = C ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) :=
          mul_le_mul_of_nonneg_left (Gam_sq_le_sin_two α hα θ hθ) (sq_nonneg C)
  calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
      ≤ (C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hsq hw0
    _ = C ^ 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) :=
        by ring
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 + -(Spaces.gam α)) := by
        rw [Real.rpow_add' hs0 hne]
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Spaces.gam α) := by ring_nf

/-- The `η`-integrand `(D_θ^i Γ)² sin(2θ)^{-η}` is dominated pointwise by
`C_i² sin(2θ)^{-η}` on `Iθ`. -/
lemma dthIterAng_sq_mul_le_eta {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {i : ℕ}
    (hbound : ∀ θ ∈ Spaces.Iθ, |CT.DthIterAng i (Spaces.Gam α) θ| ≤ C * Spaces.Gam α θ) :
    ∀ θ ∈ Spaces.Iθ,
      (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta)
        ≤ C ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  intro θ hθ
  have hG := Spaces.Gam_bounds α θ hα hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsq : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ C ^ 2 := by
    have h2 : |CT.DthIterAng i (Spaces.Gam α) θ| ≤ |C * Spaces.Gam α θ| := by
      rw [abs_of_nonneg (mul_nonneg hC hG.1)]
      exact hbound θ hθ
    have h1 : (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := by
      calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
          = |CT.DthIterAng i (Spaces.Gam α) θ| ^ 2 := by rw [sq_abs]
        _ ≤ |C * Spaces.Gam α θ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = (C * Spaces.Gam α θ) ^ 2 := by rw [sq_abs]
    calc (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2 ≤ (C * Spaces.Gam α θ) ^ 2 := h1
      _ = C ^ 2 * (Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ C ^ 2 * 1 ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          nlinarith [hG.1, hG.2]
      _ = C ^ 2 := by ring
  exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs0 _)

/-- The `γ`-weighted square of `D_θ^i Γ` is integrable on `Iθ`. -/
lemma dthIterAng_sq_integrable_gam (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    IntegrableOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) Spaces.Iθ := by
  obtain ⟨C, hC0, hbound⟩ := dthIterAng_le_Gam α hα hα1 i
  set q : ℝ := 1 - 17 * α / 30 with hqdef
  have hq0 : 0 < q := by simp only [hqdef]; linarith
  have hq1 : q < 1 := by simp only [hqdef]; linarith
  obtain ⟨hBint, -⟩ := integral_sin_two_neg_rpow_le q hq0 hq1
  have hmaj : IntegrableOn (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Spaces.Iθ :=
    hBint.const_mul _
  -- measurability: the integrand is continuous on the open interval, which differs from
  -- `Iθ` by the null set `{0, π/2}`
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · fun_prop
    · intro θ hθ
      have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  have hcont_f : ContinuousOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) (Set.Ioo 0 (π / 2)) :=
    (((dthIterAng_continuousOn i α hα).mono Set.Ioo_subset_Icc_self).pow 2).mul hcont_sin
  have hmeas : AEStronglyMeasurable (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) (volume.restrict Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact hcont_f.aestronglyMeasurable measurableSet_Ioo
  have hpoint := dthIterAng_sq_mul_le_gam hα hα1 hC0 hbound
  have hexp : 2 * α / 3 - Spaces.gam α = -q := by simp only [hqdef, Spaces.gam]; ring
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
  have h := hpoint θ hθ
  rw [hexp] at h
  exact h

/-- The `η`-weighted square of `D_θ^i Γ` is integrable on `Iθ`. -/
lemma dthIterAng_sq_integrable_eta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ) :
    IntegrableOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) Spaces.Iθ := by
  obtain ⟨C, hC0, hbound⟩ := dthIterAng_le_Gam α hα hα1 i
  obtain ⟨hBint, -⟩ := integral_sin_two_neg_rpow_le Spaces.eta Spaces.eta_pos Spaces.eta_lt_one
  have hmaj : IntegrableOn (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      Spaces.Iθ := hBint.const_mul _
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hcont_sin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Spaces.eta))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · fun_prop
    · intro θ hθ
      have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  have hcont_f : ContinuousOn (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (Set.Ioo 0 (π / 2)) :=
    (((dthIterAng_continuousOn i α hα).mono Set.Ioo_subset_Icc_self).pow 2).mul hcont_sin
  have hmeas : AEStronglyMeasurable (fun θ => (CT.DthIterAng i (Spaces.Gam α) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Spaces.eta)) (volume.restrict Spaces.Iθ) := by
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    exact hcont_f.aestronglyMeasurable measurableSet_Ioo
  have hpoint := dthIterAng_sq_mul_le_eta hα hC0 hbound
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))]
  exact hpoint θ hθ

theorem dthIterAng_sq_integrable (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ i : ℕ, MeasureTheory.IntegrableOn (fun θ => (Work.Coercivity.CT.DthIterAng i (Work.Spaces.Gam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ)
    ∧ (∀ i : ℕ, MeasureTheory.IntegrableOn (fun θ => (Work.Coercivity.CT.DthIterAng i (Work.Spaces.Gam α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :=
  ⟨fun i => dthIterAng_sq_integrable_gam α hα hα1 i,
   fun i => dthIterAng_sq_integrable_eta α hα hα1 i⟩

end Work.Coercivity
