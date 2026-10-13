/-
Weighted Cauchy–Schwarz on the angular slice `Iθ = [0, π/2]`.

`cs_weighted` is the elementary inequality

`(∫_{a}^{b} |g'|)² ≤ (∫_{Iθ} g'² sin(2θ)^{2-γ}) · (∫_{Iθ} sin(2θ)^{γ-2})`

for `1 < γ`, `0 < a ≤ b < π/2`, i.e. Cauchy–Schwarz for the factorisation

`|g'| = (|g'| sin(2θ)^{(2-γ)/2}) · sin(2θ)^{(γ-2)/2}`

on `(a,b] ⊂ (0, π/2)`.  The two weight functions are continuous on the open interval
`(0, π/2)` (where `sin(2θ) > 0`), so the two squares `g'² sin(2θ)^{2-γ}` and
`sin(2θ)^{γ-2}` are honest `L²` functions there; the small interval `(a,b]` is used for the
left-hand side so that no integrability of `g'` itself is needed, and the two resulting
integrals over `(a,b]` are compared with the integrals over `Iθ` by monotonicity of the
integral of nonnegative functions (`setIntegral_mono_set`, integrability on `Iθ` being
exactly the hypotheses).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

set_option linter.unusedVariables false

namespace Work.FTS_RXTPieces.Angular

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_of_pos {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

theorem cs_weighted {γ : ℝ} (hγ : 1 < γ) {g' : ℝ → ℝ}
    (hmes : MeasureTheory.AEStronglyMeasurable g'
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hWv : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (γ - 2))
      MeasureTheory.volume 0 (Real.pi / 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    (∫ x in a..b, |g' x|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2)) := by
  -- Sine is positive on the open interval `(0, π/2)` and nonnegative on `[0, π/2]`.
  have hsinpos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsinIoc : ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The interval `(a,b]` sits inside `[0, π/2]` and inside the open interval.
  have hS_T : Set.Ioc a b ⊆ Set.Ioc (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha (le_of_lt hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  have hS_Ioo : Set.Ioc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha (le_of_lt hx.1), lt_of_le_of_lt hx.2 hb⟩
  have hS_Iθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt (lt_of_lt_of_le ha (le_of_lt hx.1)), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  -- `Iθ` and `(0, π/2]` differ by the null set `{0}`, so they carry the same measure.
  have hnull : MeasureTheory.volume ({(0:ℝ)} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hae0 : ∀ᵐ (x:ℝ), x ∉ ({(0:ℝ)} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hae : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioc (0:ℝ) (Real.pi / 2) := by
    filter_upwards [hae0] with x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioc]
    exact propext ⟨fun h => ⟨lt_of_le_of_ne h.1 (fun h0 => hx h0.symm), h.2⟩,
      fun h => ⟨le_of_lt h.1, h.2⟩⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hae
  -- `hint2` transported to the equivalent set `(0, π/2]`.
  have hint2r : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) (Set.Ioc (0:ℝ) (Real.pi / 2)) := by
    change MeasureTheory.Integrable (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2)))
    rw [← hms]
    exact hint2
  rw [hms]
  have hWvI : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (γ - 2))
      (Set.Ioc (0:ℝ) (Real.pi / 2)) := hWv.1
  -- Continuity of the two weights on the open interval, where `sin (2θ) ≠ 0`.
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - γ) / 2))
      (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hVcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((γ - 2) / 2))
      (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  -- The three functions of the Cauchy–Schwarz step are a.e. strongly measurable on `(a,b]`.
  have hw_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - γ) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hwcont.aestronglyMeasurable measurableSet_Ioo).mono_set hS_Ioo
  have hV_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((γ - 2) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hVcont.aestronglyMeasurable measurableSet_Ioo).mono_set hS_Ioo
  have hg_aesm : AEStronglyMeasurable (fun x : ℝ => |g' x|)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    simpa only [Real.norm_eq_abs] using hmes.norm.mono_set hS_Iθ
  have hu_aesm : AEStronglyMeasurable
      (fun x : ℝ => |g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hg_aesm.mul hw_aesm
  have hSmeas : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  -- The pointwise identities on `(a,b]` (where `sin (2θ) > 0`).
  have hpt1 : ∀ x ∈ Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2
      = g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [mul_pow, sq_abs, rpow_sq_of_pos hs, show 2 * ((2 - γ) / 2) = 2 - γ by ring]
  have hu2 : MeasureTheory.Integrable
      (fun x : ℝ => (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hint2r.mono_set hS_T).congr_fun (fun x hx => (hpt1 x hx).symm) hSmeas
  have humem : MeasureTheory.MemLp
      (fun x : ℝ => |g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hu_aesm).mpr hu2
  have hpt2 : ∀ x ∈ Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [rpow_sq_of_pos hs, show 2 * ((γ - 2) / 2) = γ - 2 by ring]
  have hV2 : MeasureTheory.Integrable
      (fun x : ℝ => ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hWvI.mono_set hS_T).congr_fun (fun x hx => (hpt2 x hx).symm) hSmeas
  have hVmem : MeasureTheory.MemLp (fun x : ℝ => (Real.sin (2 * x)) ^ ((γ - 2) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hV_aesm).mpr hV2
  -- Cauchy–Schwarz on `(a,b]`.
  have hcs := Work.Spaces.cs_integral humem hVmem
  have e1 : (∫ x in Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
      = (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_congr_fun hSmeas hpt1
  have e2 : (∫ x in Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
      = (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_congr_fun hSmeas hpt2
  have hUV : (∫ x in Set.Ioc a b,
        (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) * (Real.sin (2 * x)) ^ ((γ - 2) / 2))
      = (∫ x in Set.Ioc a b, |g' x|) := by
    refine MeasureTheory.setIntegral_congr_fun hSmeas (fun x hx => ?_)
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [mul_assoc, ← Real.rpow_add hs, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring,
      Real.rpow_zero, mul_one]
  -- Monotonicity of the integral of a nonnegative function for `(a,b] ⊆ (0,π/2]`.
  have hTmeas : MeasurableSet (Set.Ioc (0:ℝ) (Real.pi / 2)) := measurableSet_Ioc
  have h1nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2))]
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) :=
    (MeasureTheory.ae_restrict_iff' hTmeas).mpr
      (Filter.Eventually.of_forall (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIoc x hx) _)))
  have h2nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2))]
      (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) :=
    (MeasureTheory.ae_restrict_iff' hTmeas).mpr
      (Filter.Eventually.of_forall (fun x hx => Real.rpow_nonneg (hsinIoc x hx) _))
  have hst : Set.Ioc a b ≤ᵐ[MeasureTheory.volume] Set.Ioc (0:ℝ) (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun x hx => hS_T hx)
  have m1 : (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
      ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_mono_set hint2r h1nn hst
  have m2 : (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2))
      ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_mono_set hWvI h2nn hst
  have hBSnn : 0 ≤ (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_nonneg hSmeas
      (fun x hx => Real.rpow_nonneg (le_of_lt (hsinpos x (hS_Ioo hx))) _)
  have hAnn : 0 ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2),
      g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_nonneg hTmeas (fun x hx =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIoc x hx) _))
  calc (∫ x in a..b, |g' x|) ^ 2
      = (∫ x in Set.Ioc a b, |g' x|) ^ 2 := by rw [intervalIntegral.integral_of_le hab]
    _ = (∫ x in Set.Ioc a b,
          (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) * (Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2 := by
          rw [hUV]
    _ ≤ (∫ x in Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
        * (∫ x in Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2) := hcs
    _ = (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) := by rw [e1, e2]
    _ ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (γ - 2)) :=
        mul_le_mul m1 m2 hBSnn hAnn

end Work.FTS_RXTPieces.Angular
