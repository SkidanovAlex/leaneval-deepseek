import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Elliptic.HardyLeftW
import Submission.Work.Elliptic.HardyRightW
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set Filter
open scoped Real Topology

/-- Weighted Hardy bound for the tail integral `L₁₂`: with
`U z = L12f g z = ∫_z^∞ ∫_θ K θ g s θ / s` and angular average
`A z = ∫_θ K θ g z θ`, one has `∫_{[0,∞)} U² w² ≤ 107 ∫_{[0,∞)} A² w²`.

Route: `U' = -(A z / z)` on `(0,∞)` (`Work.FM.hasDerivAt_L12` with the density
`L12dens K g z = A z / z` continuous by `SmoothNbhd`), `U 0 = 0` and `U → 0` at `+∞`
and `U` continuous on `[0,1]` (`Work.Elliptic.L12_values`); then the weighted Hardy
inequalities `HardyLeftW` / `HardyRightW` on the two half-lines. -/
theorem L12_w_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g)
    (hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K g) (Set.Ioi 0))
    (h0 : Work.Coercivity.L12f g 0 = 0)
    (hQ1 : MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioo 0 1))
    (hQ2 : MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi 1)) :
    ∫ z in Work.Spaces.Iz, (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 107 * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
  -- ## (A) The density is `A z / z` where `A` is the angular average.
  have hdens : ∀ z : ℝ, z ≠ 0 → Work.FM.L12dens Work.Spaces.K g z
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) / z := by
    intro z hz
    rw [Work.FM.L12dens_eq (K := Work.Spaces.K) (f := g) (s := z) hz]
    rfl
  -- ## (B) Identification of the elliptic density with the fundamental-model one.
  have hdensE : Work.Elliptic.L12dens g = Work.FM.L12dens Work.Spaces.K g := by
    funext z
    simp only [Work.Elliptic.L12dens, Work.FM.L12dens, Work.Elliptic.Ktheta_eq_K,
      Work.Spaces.Iθ]
  -- ## (C) Identification of `L12f g` with the elliptic `L₁₂`.
  have hLEq : (fun z => Work.Elliptic.L12 g z) = Work.Coercivity.L12f g := by
    funext z
    rw [Work.Elliptic.L12_eq_FM, ← Work.Coercivity.K_eq_Kpaper]
    rfl
  -- ## (D) `U' = -(A z / z)` on `(0,∞)`.
  have hderivAll : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Coercivity.L12f g)
        (-((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) / z)) z := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hcont : ContinuousAt (Work.FM.L12dens Work.Spaces.K g) z := by
      have hc := Work.Elliptic.L12dens_continuousAt_aux g hsm z hz
      rwa [hdensE] at hc
    have hh := Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := g) (a := 0) (ρ := z)
      hint hcont hz
    rw [hdens z hz0] at hh
    exact hh
  -- ## (E) `L12 g 0 = 0` and `L12dens` integrable for `L12_values`.
  have h0E : Work.Elliptic.L12 g 0 = 0 := by
    rw [Work.Elliptic.L12_eq_FM, ← Work.Coercivity.K_eq_Kpaper]
    exact h0
  have hintE : IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := hdensE ▸ hint
  -- ## (F) Continuity on `[0,1]` and decay at `+∞`.
  obtain ⟨_hval, hdecay, hcontIcc⟩ := Work.Elliptic.L12_values g hintE h0E
  have hcontU : ContinuousOn (Work.Coercivity.L12f g) (Set.Icc 0 1) := hLEq ▸ hcontIcc
  have htendU : Tendsto (Work.Coercivity.L12f g) atTop (𝓝 0) := hLEq ▸ hdecay
  -- ## (G) The two weighted Hardy inequalities.
  obtain ⟨hLWint, hLWle⟩ := Work.Elliptic.HardyLeftW
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) (Work.Coercivity.L12f g)
    (fun z hz => hderivAll z hz.1) hcontU h0 hQ1
  obtain ⟨hRWint, hRWle⟩ := Work.Elliptic.HardyRightW
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) (Work.Coercivity.L12f g)
    (fun z hz => hderivAll z (Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hz))))
    htendU hQ2
  -- ## (H) Integrability on `[1,∞)` and the decomposition `(0,∞) = (0,1) ∪ [1,∞)`.
  have hIci1_U : IntegrableOn
      (fun z => (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hRWint.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hIci1_A : IntegrableOn
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ici (1 : ℝ)) :=
    hQ2.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hone : Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ioi 0 := by
    ext z; constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hz)
    · intro hz
      rcases lt_or_ge z 1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => (not_lt.mpr hz2) hz1.2)
  have hUdecomp : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1, (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ici (1 : ℝ), (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hLWint hIci1_U
  have hUdecomp' : (∫ z in Set.Ici (1 : ℝ),
        (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (1 : ℝ), (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  have hAdecomp : (∫ z in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      = (∫ z in Set.Ioo (0 : ℝ) 1,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ici (1 : ℝ),
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [← hone]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ici hQ1 hIci1_A
  have hAdecomp' : (∫ z in Set.Ici (1 : ℝ),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (1 : ℝ),
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (1 : ℝ))).symm
  -- ## (I) Reduction of the integrals over `Iz` to `(0,∞)`.
  have hIzU : (∫ z in Work.Spaces.Iz,
        (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  have hIzA : (∫ z in Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
  -- ## (J) Assembly.
  have hmain : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (∫ z in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [hUdecomp, hUdecomp', hAdecomp, hAdecomp']
    calc (∫ z in Set.Ioo (0 : ℝ) 1,
            (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (∫ z in Set.Ioi (1 : ℝ),
            (Work.Coercivity.L12f g z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Set.Ioo (0 : ℝ) 1,
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
          + 107 * (∫ z in Set.Ioi (1 : ℝ),
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          add_le_add hLWle hRWle
      _ = 107 * ((∫ z in Set.Ioo (0 : ℝ) 1,
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (∫ z in Set.Ioi (1 : ℝ),
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * g z θ) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
          ring
  rw [hIzU, hIzA]
  exact hmain

end Work.Coercivity
