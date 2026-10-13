import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS.StrongEps.continuousOn_integral_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `HintL`: the `L₁₂`-weighted `(z,θ)`-integrand is integrable

The radial factor of the angular data `K(θ)Γ(θ)` is bounded by `3` on `Iθ = [0,π/2]`
(lemma `integrableOn_GamK` records its integrability), while the radial factor

  `z ↦ L₁₂(f)(z) / (1+z)²`

is dominated by `C / (1+z)²` for `z > 0`, where `C = ∫_{Ioi 0} |L12dens f|` is the `L¹`-mass
of the density: by `Work.FM.L12` the operator `L₁₂(f)(z) = ∫_{s > z} L12dens f s ds` is the
tail integral of the density, whence `|L₁₂(f)(z)| ≤ ∫_{s > z} |L12dens f s| ≤ C` for `z > 0`.
Since `z ↦ 1/(1+z)²` is integrable on `(0,∞)`, the product is integrable on
`Ioi 0 ×ˢ Iθ`; the dominating function is produced from `MeasureTheory.Integrable.mul_prod`
(Fubini for the product measure), and the measurability of the integrand from the continuity
of the tail integral (`Work.FTS.StrongEps.continuousOn_integral_Ioi`).
-/

theorem HintL {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hintL2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  -- the `L¹`-mass of the density
  set C : ℝ := ∫ s in Set.Ioi 0, |Work.Construction.L12dens f s| with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun s => abs_nonneg (Work.Construction.L12dens f s)
  -- `L₁₂(f)` is the tail integral of the density, hence continuous on `[0,∞)` …
  have hcont0 : ContinuousOn (fun z : ℝ => ∫ s in Set.Ioi z, Work.Construction.L12dens f s)
      (Set.Ici 0) := Work.FTS.StrongEps.continuousOn_integral_Ioi hintL2
  have hcont : ContinuousOn (Work.Coercivity.L12f f) (Set.Ici 0) := hcont0
  have hfun : Work.Coercivity.L12f f
      = fun z : ℝ => ∫ s in Set.Ioi z, Work.Construction.L12dens f s := rfl
  -- … and bounded by `C` on `(0,∞)`.
  have hL12bd : ∀ z ∈ Set.Ioi (0:ℝ), |Work.Coercivity.L12f f z| ≤ C := by
    intro z hz
    have h1 : |∫ s in Set.Ioi z, Work.Construction.L12dens f s| ≤
        ∫ s in Set.Ioi z, |Work.Construction.L12dens f s| := by
      have := MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z)) (f := fun s => Work.Construction.L12dens f s)
      simpa only [Real.norm_eq_abs] using this
    have h2 : (∫ s in Set.Ioi z, |Work.Construction.L12dens f s|) ≤ C := by
      rw [hCdef]
      exact MeasureTheory.setIntegral_mono_set hintL2.abs
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hz.le))
    rw [hfun]
    exact le_trans h1 h2
  -- the angular factor is bounded by `3` on `Iθ`
  have hKG : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.K θ * Work.Spaces.Gam α θ| ≤ 3 := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin (by positivity)
    have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ), hsin]
    have hrp : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) ≤ 1 :=
      Real.rpow_le_one hb0 hb1 (by linarith)
    have hK0 : 0 ≤ Work.Spaces.K θ := by rw [Work.Spaces.K]; positivity
    have hK3 : Work.Spaces.K θ ≤ 3 := by rw [Work.Spaces.K]; nlinarith [hb1]
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := by rw [Work.Spaces.Gam]; exact Real.rpow_nonneg hb0 _
    rw [abs_of_nonneg (mul_nonneg hK0 hG0)]
    calc Work.Spaces.K θ * Work.Spaces.Gam α θ ≤ 3 * 1 := mul_le_mul hK3 hrp hG0 (by norm_num)
      _ = 3 := by norm_num
  -- continuity of the angular factor on `Iθ`, and of the two factors on the product set
  have hKGcont : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ)
      Work.Spaces.Iθ := by
    have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
    have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
    have h1 : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
        Work.Spaces.Iθ := hu.rpow_const (fun θ _ => Or.inr hα3)
    have hK : ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
    have h2 : ContinuousOn (fun θ : ℝ =>
        (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2))
        Work.Spaces.Iθ := h1.mul hK
    refine h2.congr (fun θ _ => ?_)
    simp only [Work.Spaces.K, Work.Spaces.Gam]
    ring
  have hKGprod : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    hKGcont.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hRadcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
    have hφ : ContinuousOn (fun z : ℝ => Work.Coercivity.L12f f z / (1 + z) ^ 2)
        (Set.Ioi 0) :=
      (hcont.mono Set.Ioi_subset_Ici_self).div
        (((continuous_const.add continuous_id).pow 2).continuousOn)
        (fun z hz => by
          have hz0 : (0:ℝ) < z := hz
          have h1 : (0:ℝ) < 1 + z := by linarith
          exact pow_ne_zero 2 (ne_of_gt h1))
    exact hφ.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :=
    (hKGprod.mul hRadcont).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Icc)
  -- the dominating function `(1/(1+z)²)·(3C)` is integrable (Fubini on the product measure)
  have hrad : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := (-2:ℝ)) (c := 0) (m := 1)
      (by norm_num) (by norm_num)
    refine h.congr_fun (fun z hz => ?_) measurableSet_Ioi
    show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
    rw [show (-2 : ℝ) = -(2:ℝ) by norm_num,
      Real.rpow_neg (by linarith [show (0:ℝ) < z from hz]), Real.rpow_two, inv_eq_one_div]
    ring
  have hIθfin : volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => 3 * C) (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integrableOn_const hIθfin
  have hmul := MeasureTheory.Integrable.mul_prod hrad hconst
  have hdom : MeasureTheory.Integrable (fun p : ℝ × ℝ => (1 / (1 + p.1) ^ 2) * (3 * C))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict] at hmul
    exact hmul
  -- the pointwise domination
  have hbound : ∀ᵐ p ∂(volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)),
      ‖Work.Spaces.K p.2 * Work.Spaces.Gam α p.2
        * (Work.Coercivity.L12f f p.1 / (1 + p.1) ^ 2)‖ ≤ (1 / (1 + p.1) ^ 2) * (3 * C) := by
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioi.prod measurableSet_Icc) (fun p hp => ?_)
    have hpz : (0:ℝ) < p.1 := hp.1
    have h1z : (0:ℝ) < 1 + p.1 := by linarith
    have hpos : (0:ℝ) < (1 + p.1) ^ 2 := pow_pos h1z 2
    have hb1 : |Work.Coercivity.L12f f p.1| / (1 + p.1) ^ 2 ≤ C / (1 + p.1) ^ 2 :=
      div_le_div_of_nonneg_right (hL12bd p.1 hp.1) hpos.le
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hpos]
    calc |Work.Spaces.K p.2 * Work.Spaces.Gam α p.2|
          * (|Work.Coercivity.L12f f p.1| / (1 + p.1) ^ 2)
        ≤ 3 * (C / (1 + p.1) ^ 2) :=
          mul_le_mul (hKG p.2 hp.2) hb1 (by positivity) (by norm_num)
      _ = (1 / (1 + p.1) ^ 2) * (3 * C) := by ring
  exact MeasureTheory.Integrable.mono' hdom haesm hbound

end Work.FTS.StrongEps.EpsZero.Bridge
