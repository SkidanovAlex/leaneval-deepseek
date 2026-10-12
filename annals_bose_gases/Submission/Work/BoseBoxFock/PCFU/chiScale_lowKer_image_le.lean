import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiScale_lowKer_image_le`

**The tied-cutoff (`κ = 1/(d²ℓ)`) lattice-image bound of the low-momentum kernel.**

    ‖ χ_ℓ(b) · ∑'_{e ≠ 0} Κ_κ(u - b + ℓ • latVec e) ‖ ≤ C · d^{2M}/ℓ³
        (0 < d, 0 < ℓ, κ = 1/(d²ℓ), u ∈ acube ℓ).

## Why it is true

The symbol of `Κ_κ` is `f(‖p‖/κ)`, so `Κ_κ` is the `κ`-dilate of `Κ_1`:
`Κ_κ(z) = κ³·Κ_1(κz)` (exact identity, `lowKer_smul_scale`).  At the tied cutoff `κ = 1/(d²ℓ)`
the dilation maps the box ratio `ℓ` to `κℓ = d^{-2}` — a *frozen* parameter — so the whole
statement reduces to the proved lattice-image bound `chiScale_imageSum_lowKer_le` at `κ = 1` and
box ratio `d^{-2}`:

    ‖ χ_{d^{-2}}(κb) · (d^{-2})³ · ∑'_{e ≠ 0} Κ_1(κu - κb + (d^{-2}) • latVec e) ‖ ≤ C / (d^{-2})^M,

i.e. `‖χ_ℓ(b) S₁‖ ≤ C d^{2M}/(κℓ)^{M+3}`, which after multiplication by `κ³` and the elementary
identity `κ³/(κℓ)^{M+3} = d^{2M}/ℓ³` (from `d²·(κℓ) = 1`) gives the claim.  The hypothesis
`u ∈ acube ℓ` is transported to the rescaled configuration `κu ∈ acube (κℓ)`, and the `χ`-factor
satisfies `χ_{κℓ}(κb) = χ_ℓ(b)` by definition.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

/-- **The exact scaling of the low-momentum kernel**: `Κ_κ(z) = κ³·Κ₁(κz)`
(the symbol `f(‖p‖/κ)` is the `κ`-dilate of `f(‖p‖)`). -/
private lemma lowKer_smul_scale (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (z : E3) :
    lowKer fc κ z = κ ^ 3 * lowKer fc 1 (κ • z) := by
  have hG : ∀ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z)
      = fc.f (‖q‖ / 1) * Real.cos (inner ℝ q (κ • z)) := by
    intro q
    have h1 : ‖κ • q‖ / κ = ‖q‖ / 1 := by
      rw [norm_smul, Real.norm_of_nonneg hκ.le, div_one]
      field_simp
    have h2 : inner ℝ (κ • q) z = inner ℝ q (κ • z) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [h1, h2]
  have hsub := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure E3))
    (f := fun p : E3 => fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z)) κ (hR := hκ.le)
  have hfin : Module.finrank ℝ E3 = 3 := by simp [EuclideanSpace]
  rw [hfin] at hsub
  rw [lowKer_apply, lowKer_apply]
  have hkey : (∫ p : E3, fc.f (‖p‖ / κ) * Real.cos (inner ℝ p z))
      = κ ^ 3 * ∫ q : E3, fc.f (‖κ • q‖ / κ) * Real.cos (inner ℝ (κ • q) z) := by
    rw [hsub, smul_eq_mul]
    have hne : κ ^ 3 ≠ 0 := pow_ne_zero _ (ne_of_gt hκ)
    field_simp
  rw [hkey, integral_congr_ae (Filter.Eventually.of_forall hG)]
  ring

/-- The `κ`-dilate of a centered cube is the centered cube of the rescaled side. -/
private lemma mem_acube_smul {κ ℓ : ℝ} (hκ : 0 < κ) {u : E3}
    (hu : u ∈ Submission.BoseGases.acube ℓ) : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := by
  rw [Submission.BoseGases.mem_acube_iff] at hu ⊢
  intro m
  have hm := hu m
  have hcomp : (κ • u).ofLp m = κ * u.ofLp m := by
    rw [WithLp.ofLp_smul]
    rfl
  rw [hcomp]
  constructor
  · nlinarith [hm.1, hκ]
  · nlinarith [hm.2, hκ]

theorem chiScale_lowKer_image_le (fc : Work.BoseBoxFix.LowCut) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ d ℓ : ℝ}, 0 < d → 0 < ℓ → κ = 1 / (d ^ 2 * ℓ) →
      ∀ (b u : EuclideanSpace ℝ (Fin 3)), u ∈ Submission.BoseGases.acube ℓ →
        ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
          * (∑' e : Fin 3 → ℤ, if e = 0 then 0
              else ((Work.BoseBoxFock.PCFU.lowKer fc κ
                (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
          ≤ C * d ^ (2 * M) / ℓ ^ 3 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le fc (κ := 1) one_pos M
  refine ⟨C₁, hC₁0, ?_⟩
  intro κ d ℓ hd hℓ hκeq b u hu
  have hκpos : 0 < κ := by rw [hκeq]; positivity
  have hκℓpos : 0 < κ * ℓ := mul_pos hκpos hℓ
  -- the `χ`-identity `χ_{κℓ}(κb) = χ_ℓ(b)`
  have hchi : Submission.BoseGases.chiScale (κ * ℓ) (κ • b)
      = Submission.BoseGases.chiScale ℓ b := by
    rw [Submission.BoseGases.chiScale, Submission.BoseGases.chiScale, smul_smul]
    congr 1
    field_simp
  -- the rescaled argument identity
  have harg : ∀ e : Fin 3 → ℤ,
      κ • (u - b + ℓ • Work.BoseBoxFock.latVec e)
        = κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e := by
    intro e
    rw [smul_add, smul_sub, smul_smul]
  -- the termwise scaling identity (complex-valued)
  have hterm : ∀ e : Fin 3 → ℤ,
      ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)
        = ((κ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) := by
    intro e
    have h := lowKer_smul_scale fc hκpos (u - b + ℓ • Work.BoseBoxFock.latVec e)
    rw [h, harg e]
    push_cast
    ring
  -- the two sums
  set S₁ : ℂ := ∑' e : Fin 3 → ℤ, if e = 0 then 0
      else ((Work.BoseBoxFock.PCFU.lowKer fc 1
        (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ) with hS₁
  have hS : (∑' e : Fin 3 → ℤ, if e = 0 then 0
        else ((Work.BoseBoxFock.PCFU.lowKer fc κ
          (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) = ((κ ^ 3 : ℝ) : ℂ) * S₁ := by
    have h1 : (∑' e : Fin 3 → ℤ, if e = 0 then 0
          else ((Work.BoseBoxFock.PCFU.lowKer fc κ
            (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))
        = ∑' e : Fin 3 → ℤ, ((κ ^ 3 : ℝ) : ℂ) * (if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc 1
              (κ • u - κ • b + (κ * ℓ) • Work.BoseBoxFock.latVec e) : ℝ) : ℂ)) := by
      refine tsum_congr (fun e => ?_)
      by_cases he : e = 0
      · subst he; simp
      · rw [if_neg he, if_neg he]
        exact hterm e
    rw [h1, tsum_mul_left, hS₁]
  -- the `κ = 1` lemma at `ℓ̃ = κℓ`, `b̃ = κb`, `ũ = κu`
  have hac : κ • u ∈ Submission.BoseGases.acube (κ * ℓ) := mem_acube_smul hκpos hu
  have hb := hC₁ hκℓpos (κ • b) (κ • u) hac
  -- extract `‖χ_{κℓ}(κb)·S₁‖` from the lemma's norm
  have hb' : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖
      ≤ C₁ / (κ * ℓ) ^ (M + 3) := by
    rw [← hS₁] at hb
    have hnorm : ‖((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
          * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁‖
        = (κ * ℓ) ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
      rw [← hchi]
      rw [show ((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ)
            * (((κ * ℓ) ^ 3 : ℝ) : ℂ) * S₁
          = (((κ * ℓ) ^ 3 : ℝ) : ℂ)
            * (((Submission.BoseGases.chiScale (κ * ℓ) (κ • b) : ℝ) : ℂ) * S₁) from by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnorm] at hb
    have hsplit : C₁ / (κ * ℓ) ^ M = (κ * ℓ) ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
      rw [pow_add]
      field_simp
    rw [hsplit] at hb
    exact le_of_mul_le_mul_left hb (by positivity)
  -- the arithmetic identity
  have hκℓ : κ * ℓ = (d ^ 2)⁻¹ := by
    rw [hκeq]; field_simp
  have harith : κ ^ 3 / (κ * ℓ) ^ (M + 3) = d ^ (2 * M) / ℓ ^ 3 := by
    rw [div_eq_div_iff (by positivity) (by positivity), ← mul_pow]
    rw [pow_add, pow_mul, ← mul_assoc, ← mul_pow]
    have hd2κℓ : d ^ 2 * (κ * ℓ) = 1 := by
      rw [hκℓ]; field_simp
    rw [hd2κℓ]
    simp
  -- assembly
  calc ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)
        * (∑' e : Fin 3 → ℤ, if e = 0 then 0
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ
              (u - b + ℓ • Work.BoseBoxFock.latVec e) : ℝ) : ℂ))‖
      = ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)‖ := by
        rw [hS]
      _ = κ ^ 3 * ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁‖ := by
        rw [show ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((κ ^ 3 : ℝ) : ℂ) * S₁)
            = (((κ ^ 3 : ℝ) : ℂ)) * (((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * S₁) from by
              ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3)) := by
        refine mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = C₁ * d ^ (2 * M) / ℓ ^ 3 := by
        rw [show κ ^ 3 * (C₁ / (κ * ℓ) ^ (M + 3))
              = C₁ * (κ ^ 3 / (κ * ℓ) ^ (M + 3)) from by ring, harith]
        ring

end Work.BoseBoxFock.PCFU
