import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs
import Submission.Work.Coercivity.Basic
import Submission.Work.Spaces.CAux.integrableOn_GamK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- For almost every `r > 0` the angular slice `θ ↦ K(θ) ∂_z f(r,θ)` is integrable on `Iθ`.
This is the a.e.-slice form of the joint integrability hypothesis `L12Hyp.hint` (Fubini on the
product `(0,∞) × Iθ`). -/
theorem ae_integrableOn_K_pz {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f r θ)
        Work.Spaces.Iθ := by
  have h := H.hint
  rw [MeasureTheory.IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict] at h
  filter_upwards [h.prod_right_ae] with r hr
  simpa [Work.Spaces.Iθ, MeasureTheory.IntegrableOn, Function.uncurry] using hr

/-- The angular normalisation: `∫_{Iθ} K(θ)Γ(θ) dθ = c(α)`. -/
theorem integral_K_Gam_eq_c (α : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ = Work.Spaces.c α := by
  simp only [Work.Spaces.c]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- Additivity of a set integral over a sum of four functions. -/
theorem setIntegral_add_four {s : Set ℝ} {a b c d : ℝ → ℝ}
    (ha : MeasureTheory.IntegrableOn a s) (hb : MeasureTheory.IntegrableOn b s)
    (hc : MeasureTheory.IntegrableOn c s) (hd : MeasureTheory.IntegrableOn d s) :
    (∫ x in s, (a x + b x + c x + d x))
      = (∫ x in s, a x) + (∫ x in s, b x) + (∫ x in s, c x) + (∫ x in s, d x) := by
  have h1 : (∫ x in s, a x) + (∫ x in s, b x) = (∫ x in s, a x + b x) :=
    (MeasureTheory.integral_add ha hb).symm
  have h2 : (∫ x in s, a x + b x) + (∫ x in s, c x) = (∫ x in s, a x + b x + c x) :=
    (MeasureTheory.integral_add (ha.add hb) hc).symm
  have h3 : (∫ x in s, a x + b x + c x) + (∫ x in s, d x)
      = (∫ x in s, a x + b x + c x + d x) :=
    (MeasureTheory.integral_add ((ha.add hb).add hc) hd).symm
  rw [← h3, ← h2, ← h1]

theorem ZM_density_ae {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.FTS.Apriori.ZeroMode.GOf α f r - Work.FTS.Apriori.ZeroMode.uOf f r
        = Work.FTS.Apriori.ZeroMode.mdOf f r
          - 2 * Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r)
          - 2 * Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 := by
  -- the normalisation constant does not vanish
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero H.hα H.hα1
  -- `K·Γ` is integrable on the angular interval (no integrability of `f` needed)
  have hGK : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    simpa only [mul_comm] using Work.Spaces.CAux.integrableOn_GamK α H.hα
  filter_upwards [ae_integrableOn_K_pz H,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hpz hr
  have hrpos : 0 < r := hr
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have h1r : (1 : ℝ) + r ≠ 0 := by positivity
  -- the four elementary pieces of the density of `𝓛_Γ f`
  set g1 : ℝ → ℝ := fun θ => Work.Spaces.K θ * f r θ / r with hg1
  set g2 : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.Spaces.pz f r θ with hg2
  set g3 : ℝ → ℝ := fun θ => (-2 / (1 + r)) * g1 θ with hg3
  set g4 : ℝ → ℝ :=
    fun θ => (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
      * (Work.Spaces.K θ * Work.Spaces.Gam α θ) with hg4
  have h1 : MeasureTheory.IntegrableOn g1 Work.Spaces.Iθ :=
    (hslice r hrpos).div_const r
  have h2 : MeasureTheory.IntegrableOn g2 Work.Spaces.Iθ := hpz
  have h3 : MeasureTheory.IntegrableOn g3 Work.Spaces.Iθ := by
    rw [hg3]; exact h1.const_mul _
  have h4 : MeasureTheory.IntegrableOn g4 Work.Spaces.Iθ := by
    rw [hg4]; exact hGK.const_mul _
  -- pointwise expansion of the density integrand
  have hpt : ∀ θ : ℝ,
      Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r = (g1 + g2 + g3 + g4) θ := by
    intro θ
    simp only [hg1, hg2, hg3, hg4, Pi.add_apply, Work.Coercivity.LGamma, Work.Coercivity.L,
      Work.Spaces.Dz, ROf_eq]
    field_simp
    ring
  -- `GOf α f r` is the integral of the four pieces
  have hG : Work.FTS.Apriori.ZeroMode.GOf α f r
      = ∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ := by
    rw [show Work.FTS.Apriori.ZeroMode.GOf α f r
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r
        from rfl]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- split the integral into the four pieces
  have hsplit : (∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ)
      = (∫ θ in Work.Spaces.Iθ, g1 θ) + (∫ θ in Work.Spaces.Iθ, g2 θ)
        + (∫ θ in Work.Spaces.Iθ, g3 θ) + (∫ θ in Work.Spaces.Iθ, g4 θ) :=
    setIntegral_add_four h1 h2 h3 h4
  -- value of each piece
  have hu1 : (∫ θ in Work.Spaces.Iθ, g1 θ) = Work.FTS.Apriori.ZeroMode.uOf f r := by
    rw [hg1]
    rfl
  have hu2 : (∫ θ in Work.Spaces.Iθ, g2 θ) = Work.FTS.Apriori.ZeroMode.mdOf f r := by
    rw [hg2]
    rfl
  have hu3 : (∫ θ in Work.Spaces.Iθ, g3 θ)
      = (-2 / (1 + r)) * Work.FTS.Apriori.ZeroMode.uOf f r := by
    have h3' : (∫ θ in Work.Spaces.Iθ, g3 θ)
        = (-2 / (1 + r)) * (∫ θ in Work.Spaces.Iθ, g1 θ) := by
      rw [hg3]; exact MeasureTheory.integral_const_mul _ _
    rw [h3', hu1]
  have hu4 : (∫ θ in Work.Spaces.Iθ, g4 θ)
      = (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
        * Work.Spaces.c α := by
    have h4' : (∫ θ in Work.Spaces.Iθ, g4 θ)
        = (-(2 * Work.FTS.Apriori.ZeroMode.ROf f r / (Work.Spaces.c α * (1 + r) ^ 2)))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      rw [hg4]; exact MeasureTheory.integral_const_mul _ _
    rw [h4', integral_K_Gam_eq_c]
  -- assemble
  have hmain : Work.FTS.Apriori.ZeroMode.GOf α f r
      = Work.FTS.Apriori.ZeroMode.uOf f r + Work.FTS.Apriori.ZeroMode.mdOf f r
        - 2 * Work.FTS.Apriori.ZeroMode.uOf f r / (1 + r)
        - 2 * Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r) ^ 2 := by
    rw [hG, hsplit, hu1, hu2, hu3, hu4]
    field_simp
    ring
  rw [hmain]
  ring

end Work.FTS.Apriori.ZeroMode
