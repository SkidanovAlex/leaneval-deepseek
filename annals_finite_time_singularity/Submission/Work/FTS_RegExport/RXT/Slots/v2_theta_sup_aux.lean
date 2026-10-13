/-
Copyright: work module for the Elgindi finite-time singularity project.

# `v2_theta_sup_uniform` — the *uniform* angular sup bound for a mixed slot

For `0 < α ≤ 1`, a datum `f` which is `C⁴` on the open quadrant and honestly in `ℋ⁴`, and a
mixed slot `D_z^b D_θ^a f` of order `a + b ≤ 3`, there is a constant `K = K(α) ≥ 0` — the
**same** for every `f` and every slot — with

  `(D_z^b D_θ^a f (s,θ) · w(s))² ≤ K · ∫_σ HkIntegrand α 4 f (s,σ) dσ`

for every `s > 0` and every `θ ∈ (0,π/2)`, where `w(s) = (1+s)²/s²`.

The point is that the radial weight `w` is a function of `s` alone, so it commutes with every
`θ`-derivative; the whole estimate is therefore *angular*, and the constant is independent of
the slot and of the datum.

## Route

1. **Pointwise slot bound.**  For `σ ∈ (0,π/2)` and `a + b ≤ 4`, the `w`-weighted square of the
   slot is a summand of `HkIntegrand α 4`, up to a factor `sin(2σ)^{±γ} ∈ (0,1]`
   (`slot_le_HkIntegrand_aux`, `slot_sin_le_HkIntegrand_aux`).
2. **Angular mean–variation bound** (`angular_meanVar_aux`, delegated as
   `Work.FTS_RegExport.RXT.Slots.angular_meanVar_open`).  For a function `g` of the open
   interval with derivative `g'`, continuous on the interior, the companion angle
   `θ₀ ∈ [π/8,3π/8]` minimising `g²` satisfies `g(θ₀)² ≤ (4/π) ∫_{Iθ} g²`, while
   Cauchy–Schwarz against the weight `sin(2θ)^{γ-2}` controls the variation:
   `(g θ - g θ₀)² ≤ (∫ sin^{γ-2}) (∫ g'² sin^{2-γ})`.  Hence
   `g θ² ≤ (8/π) ∫ g² + 2 (∫ sin^{γ-2}) (∫ g'² sin^{2-γ})`.
3. **Assembly.**  Multiply by `w(s)²`, use `D_θ = sin(2θ)·∂_θ` to turn `(g')² sin^{2-γ} w²`
   into the `Wt`-weighted slot of order `a+1`, and bound `∫ sin^{γ-2} ≤ 100/(γ-1)`.
-/

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integral_sin_rpow
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers on the weight `w` -/

theorem w_nonneg_aux (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos_aux {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem sq_mul_le_sq_mul_aux {a b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) :
    (a * b) ^ 2 ≤ (a * c) ^ 2 := by
  have h1 : b ^ 2 ≤ c ^ 2 := by nlinarith
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    _ ≤ a ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    _ = (a * c) ^ 2 := by ring

/-! ## The angular interval, its interior, and a.e. strong measurability -/

theorem restrict_Iθ_eq_Ioo_aux :
    MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := Real.pi / 2))).symm

theorem aesm_Iθ_of_continuousOn_Ioo_aux {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable u (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo_aux]
  exact hu.aestronglyMeasurable measurableSet_Ioo

/-! ## The `θ`-slice of a function continuous on the open quadrant -/

theorem continuousOn_slice_of_continuousOn_Q0_aux {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun θ => g s θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hlin : ContinuousOn (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hθ⟩
  exact (hg.comp hlin hmaps).congr (fun θ _ => rfl)

/-- The interior `θ`-slice of `∂_θ(D_z^bD_θ^af)` is continuous: on the open quadrant it equals
`(D_z^bD_θ^{a+1}f)/sin(2θ)` (`Dth_mixed_eq_C4`), and both factors are continuous there. -/
theorem continuousOn_pth_mixed_slice_aux {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ 4) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hm : ContinuousOn (fun σ => Work.Spaces.mixed b (a + 1) f s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    continuousOn_slice_of_continuousOn_Q0_aux
      ((Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b (a + 1) 0 (by omega)).continuousOn)
      hs
  have hsin : ContinuousOn (fun σ : ℝ => Real.sin (2 * σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hdiv := hm.div hsin (fun σ hσ => ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))
  refine hdiv.congr (fun σ hσ => ?_)
  have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a hab hs hσ
  rw [Work.Spaces.Dth] at hD
  simp only [Pi.div_apply]
  rw [eq_div_iff (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)), mul_comm]
  exact hD

/-! ## Pointwise domination of a slot by the `ℋ⁴`-integrand -/

/-- At an interior angle the `w`-weighted square of the slot `D_z^bD_θ^a f` (`a + b ≤ 4`) is
dominated by `HkIntegrand α 4 f`: for `a ≥ 1` the slot occurs in the mixed sum with the full
weight `W = w·sin(2θ)^{-γ/2}` (and `sin^γ ≤ 1`), for `a = 0` it occurs in the `D_z`-sum with
`w/sin^{η/2}` (and `sin^{η/2} ≤ 1`). -/
theorem slot_le_HkIntegrand_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (b a : ℕ)
    (hab : a + b ≤ 4) (s : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have hsinle : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 4 f s σ b (by omega))
    refine sq_mul_le_sq_mul_aux (w_nonneg_aux s) ?_
    have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
    have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hsin.le hsinle (by have := Work.Spaces.eta_pos; linarith)
    calc Work.Spaces.w s = Work.Spaces.w s * 1 := (mul_one _).symm
      _ ≤ Work.Spaces.w s * (1 / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) :=
          mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) (w_nonneg_aux s)
      _ = Work.Spaces.w s / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by ring
  · refine le_trans
      (Work.FTS_RegExport.RXA1w.mixed_slot_sq_w_le_HkIntegrand hα b a ha (by omega) s hσ) ?_
    have hsinγ : Real.sin (2 * σ) ^ (Work.Spaces.gam α) ≤ 1 :=
      Real.rpow_le_one hsin.le hsinle (Work.Spaces.gam_pos hα).le
    calc Real.sin (2 * σ) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f s σ
        ≤ 1 * Work.Spaces.HkIntegrand α 4 f s σ :=
          mul_le_mul_of_nonneg_right hsinγ (Work.Spaces.HkIntegrand_nonneg α 4 f s σ)
      _ = Work.Spaces.HkIntegrand α 4 f s σ := one_mul _

/-- The companion bound for the `θ`-derivative slot: `(D_z^bD_θ^{a+1}f · w)² sin(2θ)^{-γ}`
is the `Wt`-weighted mixed slot of order `a + 1`, hence dominated by `HkIntegrand α 4 f`. -/
theorem slot_sin_le_HkIntegrand_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (b a : ℕ)
    (hab : a + 1 + b ≤ 4) (s : ℝ) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f s σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s σ (a + 1) b (by omega) (by omega)
  have hid : (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.Wt α s σ) ^ 2
      = (Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    have hsq : ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [sq, ← Real.rpow_add hsin,
        show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hsq]
    ring
  rw [hid] at h1
  exact h1

/-! ## Integrability of the two angular integrands of the mean–variation bound -/

theorem integrable_slot_sq_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 3) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun σ => (Work.Spaces.mixed b a f s σ) ^ 2) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (aesm_Iθ_of_continuousOn_Ioo_aux
      (((Work.FTS_RegExport.RXA1w.contDiffOn_slice_mixed h4 b a 1 (by omega) hs).continuousOn).pow 2))
    ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hkey : (Work.Spaces.mixed b a f s σ) ^ 2
      = (Work.Spaces.mixed b a f s σ * Work.Spaces.w s) ^ 2 / (Work.Spaces.w s) ^ 2 := by
    rw [mul_pow, eq_div_iff (by have := w_pos_aux hs; positivity)]
  rw [hkey]
  exact div_le_div_of_nonneg_right
    (slot_le_HkIntegrand_aux hα b a (by omega) s hσ) (sq_nonneg _)

theorem integrable_pth_sq_sin_aux {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 3) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hsI : s ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hs.le
  have hcont : ContinuousOn
      (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) s σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuousOn_pth_mixed_slice_aux h4 b a (by omega) hs).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ))))
  refine (hmem.1 s hsI).div_const ((Work.Spaces.w s) ^ 2) |>.mono'
    (aesm_Iθ_of_continuousOn_Ioo_aux hcont) ?_
  filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))]
  have hpth : Work.Spaces.pth (Work.Spaces.mixed b a f) s σ
      = Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ) := by
    have hD := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 h4 b a (by omega) hs hσ
    rw [Work.Spaces.Dth] at hD
    rw [eq_div_iff (ne_of_gt hsin), mul_comm]
    exact hD
  rw [hpth]
  have hkey : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = ((Work.Spaces.mixed b (a + 1) f s σ * Work.Spaces.w s) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) / (Work.Spaces.w s) ^ 2 := by
    have h2 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
        Real.rpow_add hsin, Real.rpow_ofNat]
    have e1 : (Work.Spaces.mixed b (a + 1) f s σ / Real.sin (2 * σ)) ^ 2
        = (Work.Spaces.mixed b (a + 1) f s σ) ^ 2 / (Real.sin (2 * σ)) ^ 2 :=
      div_pow _ _ 2
    have hwne : Work.Spaces.w s ≠ 0 := ne_of_gt (w_pos_aux hs)
    rw [e1, h2]
    field_simp <;> ring_nf
  rw [hkey]
  exact div_le_div_of_nonneg_right
    (slot_sin_le_HkIntegrand_aux hα b a (by omega) s hσ) (sq_nonneg _)

/-! ## The angular mean–variation bound -/

/-- `(x^{p/2})² = x^p` for `x > 0`. -/
private theorem rpow_sq_aux {x p : ℝ} (hx : 0 < x) : (x ^ (p / 2)) ^ 2 = x ^ p := by
  rw [sq, ← Real.rpow_add hx, show p / 2 + p / 2 = p by ring]

/-- **Cauchy–Schwarz against the angular weight on `(a,b]`.**  For `0 < a`, `b < π/2` and
`a ≤ b`,

  `(∫_{(a,b]} g')² ≤ (∫_{(a,b]} g'² sin(2θ)^{2-γ}) (∫_{(a,b]} sin(2θ)^{γ-2})`.

On the closure of `(a,b]` the weight `sin(2·)` is bounded below by `sin(2a) > 0`, so both factors
`g' sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}` are continuous there and square integrable, and
`Work.Spaces.cs_integral` applies. -/
theorem cs_Ioc_aux {γ : ℝ} {g' : ℝ → ℝ}
    (hg'c : ContinuousOn g' (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    (∫ x in Set.Ioc a b, g' x) ^ 2
      ≤ (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hsubIθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  have hsinpos : ∀ x ∈ Set.Ioc a b, 0 < Real.sin (2 * x) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, ha])
      (by linarith [hx.2, hb, Real.pi_pos])
  have hsincont : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  set A : ℝ → ℝ := fun x => g' x * (Real.sin (2 * x)) ^ ((2 - γ) / 2) with hA
  set B : ℝ → ℝ := fun x => (Real.sin (2 * x)) ^ ((γ - 2) / 2) with hB
  have hAcont : ContinuousOn A (Set.Ioc a b) :=
    (hg'c.mono hsub).mul (hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx))))
  have hBcont : ContinuousOn B (Set.Ioc a b) :=
    hsincont.rpow_const (fun x hx => Or.inl (ne_of_gt (hsinpos x hx)))
  have hAesm : AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hAcont.aestronglyMeasurable measurableSet_Ioc
  have hBesm : AEStronglyMeasurable B (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hBcont.aestronglyMeasurable measurableSet_Ioc
  have hsqA : ∀ x ∈ Set.Ioc a b, A x ^ 2 = g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    simp only [hA]
    rw [mul_pow, rpow_sq_aux (hsinpos x hx)]
  have hsqB : ∀ x ∈ Set.Ioc a b, B x ^ 2 = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    simp only [hB]
    rw [rpow_sq_aux (hsinpos x hx)]
  have hprod : ∀ x ∈ Set.Ioc a b, A x * B x = g' x := by
    intro x hx
    simp only [hA, hB]
    rw [mul_assoc, ← Real.rpow_add (hsinpos x hx),
      show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  have hA2int : MeasureTheory.Integrable (fun x => A x ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hint2.mono_set hsubIθ).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (hsqA x hx).symm))
  have hB2int : MeasureTheory.Integrable (fun x => B x ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hGint.mono_set hsubIθ).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (hsqB x hx).symm))
  have hMemA : MeasureTheory.MemLp A 2 (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  have hMemB : MeasureTheory.MemLp B 2 (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBesm).mpr hB2int
  have hcs := Work.Spaces.cs_integral (u := A) (v := B) (s := Set.Ioc a b) hMemA hMemB
  have hleft : (∫ x in Set.Ioc a b, A x * B x) = ∫ x in Set.Ioc a b, g' x :=
    MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hprod)
  rw [← hleft]
  refine le_trans hcs (le_of_eq ?_)
  congr 1
  · exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hsqA x hx))
  · exact MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hsqB x hx))

/-- **Angular mean–variation (Agmon) bound on the open interval.**  If `g` has derivative `g'`
on `(0,π/2)`, `g'` is continuous there, and both `g²` and `g'² sin(2θ)^{2-γ}` are integrable
on `Iθ` (the latter being the case for `1 < γ ≤ 2`), then for every interior `θ`

  `g θ² ≤ (8/π) ∫_{Iθ} g² + 2 (∫_{Iθ} sin(2θ)^{γ-2}) (∫_{Iθ} g'² sin(2θ)^{2-γ})`.

The companion angle `θ₀` minimising `g²` on the fixed interval `[π/8,3π/8] ⊂ (0,π/2)` gives
`g(θ₀)² ≤ (4/π)∫_{Iθ} g²` (min ≤ average), and the fundamental theorem of calculus together
with Cauchy–Schwarz against the weight `sin(2θ)^{γ-2}` bounds the variation
`(g θ - g θ₀)² ≤ (∫_{Iθ} sin^{γ-2})(∫_{Iθ} g'² sin^{2-γ})`; combine with
`g θ² ≤ 2(g θ - g θ₀)² + 2g(θ₀)²`. -/
theorem angular_meanVar_aux {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hg'c : ContinuousOn g' (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint1 : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ)
    (hint2 : MeasureTheory.IntegrableOn (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g θ ^ 2 ≤ (8 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2)
        + 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2))
          * (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) := by
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (γ - 2) (by linarith) (by linarith)).1
  have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with θ hθ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ)) _
  -- the companion interval and the minimising angle
  set J : Set ℝ := Set.Icc (Real.pi / 8) (3 * Real.pi / 8) with hJ
  have hJsub : J ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [hJ] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hJsubIθ : J ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [hJ] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hJcont : ContinuousOn (fun σ => (g σ) ^ 2) J := fun x hx =>
    (((hg x (hJsub hx)).continuousAt).pow 2).continuousWithinAt
  obtain ⟨θ₀, hθ₀J, hθ₀min⟩ := IsCompact.exists_isMinOn isCompact_Icc
    ⟨Real.pi / 8, Set.left_mem_Icc.mpr (by linarith [Real.pi_pos])⟩ hJcont
  have hθ₀pos : 0 < θ₀ := by linarith [hθ₀J.1, Real.pi_pos]
  have hθ₀lt : θ₀ < Real.pi / 2 := by linarith [hθ₀J.2, Real.pi_pos]
  -- Step 1: the value at the companion angle is controlled by the average
  have hvolJ : (MeasureTheory.volume : MeasureTheory.Measure ℝ).real J = Real.pi / 4 := by
    rw [hJ, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hstep1 : (g θ₀) ^ 2 * (Real.pi / 4) ≤ ∫ σ in Work.Spaces.Iθ, (g σ) ^ 2 := by
    have hconstInt : (∫ σ in J, (g θ₀) ^ 2) = (g θ₀) ^ 2 * (Real.pi / 4) := by
      rw [MeasureTheory.setIntegral_const, hvolJ, smul_eq_mul, mul_comm]
    have hmono1 : (∫ σ in J, (g θ₀) ^ 2) ≤ ∫ σ in J, (g σ) ^ 2 :=
      MeasureTheory.setIntegral_mono_on
        (MeasureTheory.integrableOn_const
          (by rw [hJ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (hint1.mono_set hJsubIθ) measurableSet_Icc (fun σ hσ => hθ₀min hσ)
    have hmono2 : (∫ σ in J, (g σ) ^ 2) ≤ ∫ σ in Work.Spaces.Iθ, (g σ) ^ 2 :=
      MeasureTheory.setIntegral_mono_set hint1 (Eventually.of_forall fun σ => sq_nonneg _)
        (Filter.Eventually.of_forall hJsubIθ)
    rw [hconstInt] at hmono1
    linarith
  intro θ hθ
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < Real.pi / 2 := hθ.2
  -- Step 2: the variation, by the fundamental theorem of calculus and Cauchy–Schwarz
  have huIcc : ∀ x ∈ Set.uIcc θ₀ θ, x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le (lt_min hθ₀pos hθpos) (le_trans (min_le_left _ _) h1),
        lt_of_le_of_lt (le_trans h2 (le_max_right _ _)) (max_lt hθ₀lt hθlt)⟩
    · exact ⟨lt_of_lt_of_le (lt_min hθ₀pos hθpos) (le_trans (min_le_right _ _) h1),
        lt_of_le_of_lt (le_trans h2 (le_max_left _ _)) (max_lt hθ₀lt hθlt)⟩
  have hder_on : ∀ x ∈ Set.uIcc θ₀ θ, HasDerivAt g (g' x) x := fun x hx => hg x (huIcc x hx)
  have hcont_on : ContinuousOn g' (Set.uIcc θ₀ θ) := hg'c.mono huIcc
  have hftc : (∫ σ in θ₀..θ, g' σ) = g θ - g θ₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder_on hcont_on.intervalIntegrable
  have hapos : 0 < min θ₀ θ := lt_min hθ₀pos hθpos
  have hblt : max θ₀ θ < Real.pi / 2 := max_lt hθ₀lt hθlt
  have hcs := cs_Ioc_aux (γ := γ) hg'c hint2 hGint hapos hblt min_le_max
  have hconv : (∫ σ in θ₀..θ, g' σ) ^ 2
      = (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), g' σ) ^ 2 := by
    rcases lt_trichotomy θ₀ θ with h | h | h
    · rw [min_eq_left h.le, max_eq_right h.le, intervalIntegral.integral_of_le h.le]
    · subst h
      rw [min_self, max_self, Set.Ioc_self, MeasureTheory.setIntegral_empty,
        intervalIntegral.integral_same]
    · rw [min_eq_right h.le, max_eq_left h.le, intervalIntegral.integral_symm θ θ₀,
        intervalIntegral.integral_of_le h.le]
      ring
  have hnnG : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => (Real.sin (2 * σ)) ^ (γ - 2)) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _
  have hnnB : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun σ => g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
    filter_upwards [Work.FTS.H2.ae_mem_Ioo_Iθ] with σ hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (Work.FTS.H2.sin_two_pos_of_mem_Ioo hσ)) _)
  have hsub_ae : Set.Ioc (min θ₀ θ) (max θ₀ θ) ≤ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
    Filter.Eventually.of_forall fun x hx =>
      ⟨le_of_lt (lt_trans hapos hx.1), le_of_lt (lt_of_le_of_lt hx.2 hblt)⟩
  have hSin : ∀ x ∈ Set.Ioc (min θ₀ θ) (max θ₀ θ), 0 < Real.sin (2 * x) := fun x hx =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, hapos])
      (by linarith [hx.2, hblt, Real.pi_pos])
  have hB1 : (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2))
      ≤ ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2) :=
    MeasureTheory.setIntegral_mono_set hGint hnnG hsub_ae
  have hB2 : (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ),
          g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
      ≤ ∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) :=
    MeasureTheory.setIntegral_mono_set hint2 hnnB hsub_ae
  have hnn1 : 0 ≤ ∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Set.mem_Ioc] at hσ
    exact Real.rpow_nonneg (le_of_lt (hSin σ (Set.mem_Ioc.mpr hσ))) _
  have hnn2 : 0 ≤ ∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ),
      g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Set.mem_Ioc] at hσ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (hSin σ (Set.mem_Ioc.mpr hσ))) _)
  have hvariation : (g θ - g θ₀) ^ 2
      ≤ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
        * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
    rw [← hftc, hconv]
    refine le_trans hcs ?_
    calc (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (∫ σ in Set.Ioc (min θ₀ θ) (max θ₀ θ), (Real.sin (2 * σ)) ^ (γ - 2))
        ≤ (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ))
          * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2)) :=
          mul_le_mul hB2 hB1 hnn1 (MeasureTheory.integral_nonneg_of_ae hnnB)
      _ = (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
          * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by ring
  -- Step 3: combine the value at `θ₀` with the variation
  have hcomb : (g θ) ^ 2 ≤ 2 * (g θ - g θ₀) ^ 2 + 2 * (g θ₀) ^ 2 := by
    nlinarith [sq_nonneg (g θ - 2 * g θ₀)]
  have hcompañon : (g θ₀) ^ 2
      ≤ (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) := by
    have hπ4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
    have h1 : (g θ₀) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) / (Real.pi / 4) :=
      (le_div_iff₀ hπ4).mpr hstep1
    have h2 : (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) / (Real.pi / 4)
        = (4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2) := by
      field_simp <;> ring
    linarith [h1, h2]
  calc (g θ) ^ 2 ≤ 2 * (g θ - g θ₀) ^ 2 + 2 * (g θ₀) ^ 2 := hcomb
    _ ≤ 2 * ((∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
            * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)))
          + 2 * ((4 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2)) := by
        linarith [hvariation, hcompañon]
    _ = (8 / Real.pi) * (∫ σ in Work.Spaces.Iθ, (g σ) ^ 2)
          + 2 * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (γ - 2))
            * (∫ σ in Work.Spaces.Iθ, g' σ ^ 2 * (Real.sin (2 * σ)) ^ (2 - γ)) := by
        ring_nf

end Work.FTS_RegExport.RXT.Slots
