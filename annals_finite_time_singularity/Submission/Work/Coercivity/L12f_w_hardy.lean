import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Elliptic.HardyLeftW
import Submission.Work.Elliptic.HardyRightW
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.FM.Core6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

/-- The Hardy/weighted-`L²` core of Lemma `HardyWeight` of Elgindi (Annals 194 (3) 2021): with
`U z = L12f f z = ∫_z^∞ ∫_θ K θ f s θ / s` and angular average `g z = ∫_θ K θ f z θ`,
`U` inherits the weighted Hardy bound `∫ U² w² ≤ 107 ∫ g² w²` on `[0,∞)`.

Intended proof: split `Iz = [0,∞)` into `(0,1)` and `(1,∞)` and apply
`Work.Elliptic.HardyLeftW` resp. `Work.Elliptic.HardyRightW` with `U z := L12f f z`,
`f z := ∫ θ in Spaces.Iθ, Spaces.K θ * f z θ`.  The derivative hypothesis
`HasDerivAt U (-(g z / z)) z` comes from `Work.FM.hasDerivAt_L12` (density integrable by
`HardyHyp.hint`, continuous by `HardyHyp.hcont`) together with `Work.FM.L12dens_eq`
(`L12dens K f z = (∫ θ, K θ * f z θ) / z`).  Continuity on `[0,1]`, the value `U 0 = 0`
and the decay `U → 0` at `+∞` come from `Work.Elliptic.L12_values`, whose hypothesis
`L12 f 0 = 0` is derived from `HardyHyp.bd0` at `j = 1` (which gives `(U z)²/z → 0` as
`z → 0⁺`, hence `U z → 0`) together with `Work.FM.continuousWithinAt_L12`
(giving `U z → U 0` as `z → 0⁺`). -/
theorem L12f_w_hardy (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hgint : MeasureTheory.IntegrableOn
      (fun z => (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2) Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => (L12f f z * Spaces.w z) ^ 2) Spaces.Iz ∧
      ∫ z in Spaces.Iz, (L12f f z * Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Spaces.Iz,
            (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) ^ 2 * (Spaces.w z) ^ 2 := by
  set U : ℝ → ℝ := L12f f with hU
  set g : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.K θ * f z θ with hg
  -- ## (A) The density of `U` is `g z / z`, hence `U' = -(g z / z)` on `(0,∞)`.
  have hdens : ∀ z ∈ Set.Ioi (0 : ℝ), FM.L12dens Spaces.K f z = g z / z := by
    intro z hz
    rw [FM.L12dens_eq (K := Spaces.K) (f := f) (ne_of_gt hz)]
    rfl
  have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt U (-(g z / z)) z := by
    intro z hz
    have h1 : HasDerivAt (fun ρ => FM.L12 Spaces.K f ρ) (-(g z / z)) z := by
      have h := FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
        hf.hint (hf.hcont z hz) hz
      rw [hdens z hz] at h
      exact h
    exact h1
  -- ## (B) `U → 0` at `0⁺`, from `HardyHyp.bd0` at `j = 1`.
  have hbd1 : Tendsto (fun z => (L12f f z) ^ 2 / z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (hf.bd0 1 (by norm_num)).1
    have hexp : (2 * ((1 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [hexp] at h
    simpa [Real.rpow_one] using h
  have hSqTend : Tendsto (fun z => (L12f f z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun z : ℝ => z) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      (tendsto_id : Tendsto (fun z : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mono_left
        nhdsWithin_le_nhds
    have hmul : Tendsto (fun z => ((L12f f z) ^ 2 / z) * z) (𝓝[>] (0 : ℝ)) (𝓝 (0 * 0)) :=
      hbd1.mul hid
    rw [mul_zero] at hmul
    refine Filter.Tendsto.congr' ?_ hmul
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact div_mul_cancel₀ _ (ne_of_gt hz)
  have hU2 : Tendsto (fun z => (U z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hU] using hSqTend
  have hUtend : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsqrt : Tendsto (fun z => Real.sqrt ((U z) ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hU2
      rw [Real.sqrt_zero] at h
      exact h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun z => ‖U z‖) = fun z => Real.sqrt ((U z) ^ 2) := by
      funext z; rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    rw [heq]
    exact hsqrt
  -- ## (C) `U 0 = 0`, by uniqueness of the limit `U z → 0` at `0⁺`.
  have hcontWithin : ContinuousWithinAt U (Set.Ici 0) 0 := by
    have h := FM.continuousWithinAt_L12 (K := Spaces.K) (f := f) (ρ := 0) hf.hint
    exact h
  have hU0 : U 0 = 0 := by
    have hlim : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (U 0)) :=
      hcontWithin.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    exact tendsto_nhds_unique hlim hUtend
  -- ## (D) `L12_values`: continuity on `[0,1]` and decay at `+∞`.
  have h0' : Work.Elliptic.L12 f 0 = 0 := hU0
  obtain ⟨_hval, hdecay, hcontIcc⟩ := Work.Elliptic.L12_values f hf.hint h0'
  have htendU : Tendsto U atTop (𝓝 0) := hdecay
  have hcontU : ContinuousOn U (Set.Icc 0 1) := hcontIcc
  -- ## (E) Restrict the source integrability to `(0,1)` and `(1,∞)`.
  have hintL : IntegrableOn (fun z => (g z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioo (0 : ℝ) 1) :=
    hgint.mono_set (fun z hz => le_of_lt hz.1)
  have hintR : IntegrableOn (fun z => (g z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ioi (1 : ℝ)) :=
    hgint.mono_set (fun z hz => le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hz))
  -- ## (F) The two Hardy inequalities.
  obtain ⟨hLWint, hLWle⟩ :=
    Work.Elliptic.HardyLeftW g U (fun z hz => hderiv z hz.1) hcontU hU0 hintL
  obtain ⟨hRWint, hRWle⟩ :=
    Work.Elliptic.HardyRightW g U
      (fun z hz => hderiv z (Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hz))))
      htendU hintR
  -- Convert `(U)² w²` into `(U w)²` on each half-line.
  have hFL : IntegrableOn (fun z => (U z * Spaces.w z) ^ 2) (Set.Ioo (0 : ℝ) 1) := by
    simpa only [mul_pow] using hLWint
  have hFLle : ∫ z in Set.Ioo (0 : ℝ) 1, (U z * Spaces.w z) ^ 2 ∂volume
      ≤ 107 * ∫ z in Set.Ioo (0 : ℝ) 1, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume := by
    simpa only [mul_pow] using hLWle
  have hFR : IntegrableOn (fun z => (U z * Spaces.w z) ^ 2) (Set.Ioi (1 : ℝ)) := by
    simpa only [mul_pow] using hRWint
  have hFRle : ∫ z in Set.Ioi (1 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume
      ≤ 107 * ∫ z in Set.Ioi (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume := by
    simpa only [mul_pow] using hRWle
  -- ## (G) Integrability on `[1,∞)` and the exact decomposition `(0,∞) = (0,1) ∪ [1,∞)`.
  have hIci1_F : IntegrableOn (fun z => (U z * Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hFR.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hIci1_G : IntegrableOn (fun z => (g z) ^ 2 * (Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hintR.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hone : Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hz)
    · intro hz
      rcases lt_or_ge z 1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => (not_lt.mpr hz2) hz1.2)
  have hFdecomp1 : ∫ z in Set.Ioi (0 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioo (0 : ℝ) 1, (U z * Spaces.w z) ^ 2 ∂volume
        + ∫ z in Set.Ici (1 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hFL hIci1_F
  have hGdecomp1 : ∫ z in Set.Ioi (0 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioo (0 : ℝ) 1, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
        + ∫ z in Set.Ici (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hintL hIci1_G
  have hIci1_F' : ∫ z in Set.Ici (1 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioi (1 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hIci1_G' : ∫ z in Set.Ici (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioi (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  -- ## (H) Integrability on `Iz` and the weighted Hardy bound there.
  have hIci0_F : IntegrableOn (fun z => (U z * Spaces.w z) ^ 2) Spaces.Iz := by
    have h1 : IntegrableOn (fun z => (U z * Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
      rw [← hone]
      exact hFL.union hIci1_F
    exact h1.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hIzF : ∫ z in Spaces.Iz, (U z * Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioi (0 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hIzG : ∫ z in Spaces.Iz, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
      = ∫ z in Set.Ioi (0 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hmain : ∫ z in Spaces.Iz, (U z * Spaces.w z) ^ 2 ∂volume
      ≤ 107 * ∫ z in Spaces.Iz, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume := by
    rw [hIzF, hIzG, hFdecomp1, hIci1_F', hGdecomp1, hIci1_G']
    calc ∫ z in Set.Ioo (0 : ℝ) 1, (U z * Spaces.w z) ^ 2 ∂volume
            + ∫ z in Set.Ioi (1 : ℝ), (U z * Spaces.w z) ^ 2 ∂volume
        ≤ 107 * ∫ z in Set.Ioo (0 : ℝ) 1, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
            + 107 * ∫ z in Set.Ioi (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume :=
          add_le_add hFLle hFRle
      _ = 107 * (∫ z in Set.Ioo (0 : ℝ) 1, (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume
            + ∫ z in Set.Ioi (1 : ℝ), (g z) ^ 2 * (Spaces.w z) ^ 2 ∂volume) := by ring
  refine ⟨?_, ?_⟩
  · simpa only [hU] using hIci0_F
  · simpa only [hU, hg] using hmain

end Work.Coercivity
