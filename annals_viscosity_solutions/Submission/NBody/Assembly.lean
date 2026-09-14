import Submission.NBody.CalibratingCurve
import Submission.NBody.NonSuperhyperbolic
import Submission.NBody.EnergyAsymptotic
import Submission.NBody.WeakToStrong
import Mathlib

/-!
# From the calibrating curve of a horofunction to a hyperbolic motion

This file assembles the output of `Submission.NBody.CalibratingCurve` into a genuine solution of
Newton's equations.  The single deep input still missing is **Marchal's theorem**: for
`dim E ≥ 2` an `h`-minimiser of the Newtonian action has no *interior* collisions.  Everything else
in this file is proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Marchal's theorem** (Marchal 2002; Chenciner; Ferrario--Terracini): for `dim E ≥ 2`, an
absolutely continuous `h`-minimiser of the Newtonian action has no *interior* collisions. -/
def MarchalProperty (m : Fin N → ℝ) (h : ℝ) : Prop :=
  ∀ (γ : ℝ → EN E N) (a b : ℝ), a < b → AbsolutelyContinuousOnInterval γ a b →
    IsHMinimizer m h γ a b → ∀ t ∈ Set.Ioo a b, WithoutCollisions (γ t)

/-- The constant extension of a curve to the negative half-line (so that the result is continuous
at `0` when the curve is continuous from the right at `0`). -/
noncomputable def extendLeft (γ : ℝ → EN E N) : ℝ → EN E N := fun t => if t ≤ 0 then γ 0 else γ t

lemma extendLeft_of_pos {γ : ℝ → EN E N} {t : ℝ} (ht : 0 < t) : extendLeft γ t = γ t :=
  if_neg (not_le_of_gt ht)

lemma extendLeft_of_nonpos {γ : ℝ → EN E N} {t : ℝ} (ht : t ≤ 0) : extendLeft γ t = γ 0 :=
  if_pos ht

/-- **The calibrating curve is a genuine motion**, assuming Marchal's theorem. -/
theorem isNBodySolution_extendLeft_of_calibrating {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ : ℝ → EN E N} (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hM : MarchalProperty (E := E) m h)
    (hcal : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧
      IsHMinimizer m h γ 0 t ∧ actionOn m h γ 0 t = ENNReal.ofReal (u (γ 0) - u (γ t))) :
    IsNBodySolution m (extendLeft γ) ∧ (∀ t > 0, WithoutCollisions (γ t)) := by
  classical
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh.le
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  -- Marchal: the curve is collision free for positive times
  have hnc : ∀ t > 0, WithoutCollisions (γ t) := by
    intro t ht
    have h1 : 0 < t + 1 := by linarith
    have h2 : t < t + 1 := by linarith
    exact hM γ 0 (t + 1) h1 (hcal _ h1).1 (hcal _ h1).2.1 t ⟨ht, h2⟩
  have hncIcc : ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t) :=
    fun ha hab t ht => hnc t (lt_of_lt_of_le ha ht.1)
  -- the motion equation and smoothness at each positive time
  have hmotion : ∀ t > 0, iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
    intro t ht
    obtain ⟨ε, hε0, hεt⟩ := exists_between ht
    have h2pos : 0 < t + 2 := by linarith
    have hmin' : IsHMinimizer m h γ ε (t + 1) :=
      IsHMinimizer.sub (a := 0) (b := t + 2) (c := ε) (d := t + 1) (hcal _ h2pos).1
        (hcal _ h2pos).2.1 ((hcal _ h2pos).2.1 ▸ hfin (γ 0) (γ (t + 2)))
        hε0 (by linarith) (by linarith)
    exact minimizer_iteratedDeriv_two (a := ε) (b := t + 1) hm hh (by linarith)
      ((hcal _ h2pos).1.mono (by
        rw [uIcc_of_le (by linarith : ε ≤ t + 1), uIcc_of_le (by linarith : (0:ℝ) ≤ t + 2)]
        exact Set.Icc_subset_Icc hε0.le (by linarith)))
      (hncIcc hε0 (by linarith)) hmin' (hfin _ _) t ⟨hεt, by linarith⟩
  have hcd : ContDiffOn ℝ 2 γ (Set.Ioi 0) := by
    intro x hx
    obtain ⟨ε, hε0, hεx⟩ := exists_between (show (0:ℝ) < x from hx)
    have h2pos : 0 < x + 2 := by linarith
    have hcd' : ContDiffOn ℝ 2 γ (Set.Ioo ε (x + 1)) :=
      minimizer_contDiffOn_two (a := ε) (b := x + 1) hm hh (by linarith)
        ((hcal _ h2pos).1.mono (by
          rw [uIcc_of_le (by linarith : ε ≤ x + 1), uIcc_of_le (by linarith : (0:ℝ) ≤ x + 2)]
          exact Set.Icc_subset_Icc hε0.le (by linarith)))
        (hncIcc hε0 (by linarith))
        (IsHMinimizer.sub (a := 0) (b := x + 2) (c := ε) (d := x + 1) (hcal _ h2pos).1
          (hcal _ h2pos).2.1 ((hcal _ h2pos).2.1 ▸ hfin (γ 0) (γ (x + 2)))
          hε0 (by linarith) (by linarith))
        (hfin _ _)
    exact (hcd'.contDiffAt (IsOpen.mem_nhds isOpen_Ioo ⟨hεx, lt_add_one x⟩)).contDiffWithinAt
  -- continuity at `0`
  have hright : ContinuousWithinAt (extendLeft γ) (Set.Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcont1 : ContinuousOn γ (Set.Icc 0 1) := by
      have h := (hcal 1 one_pos).1.continuousOn
      rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
    obtain ⟨δ, hδ, hδp⟩ := (Metric.continuousOn_iff.mp hcont1) 0
      (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) ε hε
    refine ⟨min δ 1, lt_min hδ one_pos, fun t ht htd => ?_⟩
    have ht1 : t < 1 := by
      have := lt_of_lt_of_le htd (min_le_right δ 1)
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      exact this.2
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ t from ht) with h | h
    · have e1 : extendLeft γ t = γ 0 := by rw [← h]; exact extendLeft_of_nonpos le_rfl
      have e2 : extendLeft γ 0 = γ 0 := extendLeft_of_nonpos le_rfl
      rw [e1, e2]
      simpa using hε
    · rw [extendLeft_of_pos h, extendLeft_of_nonpos le_rfl]
      exact hδp t ⟨h.le, ht1.le⟩ (lt_of_lt_of_le htd (min_le_left δ 1))
  have hcontAt : ContinuousAt (extendLeft γ) 0 := by
    have h1 : Tendsto (extendLeft γ) (𝓝[Set.Iic 0] 0) (𝓝 (γ 0)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (extendLeft_of_nonpos ht).symm
    have h2 : Tendsto (extendLeft γ) (𝓝[Set.Ici 0] 0) (𝓝 (γ 0)) := by
      have hr : Tendsto (extendLeft γ) (𝓝[Set.Ici 0] 0) (𝓝 ((extendLeft γ) 0)) := hright
      rw [show (extendLeft γ) 0 = γ 0 from extendLeft_of_nonpos le_rfl] at hr
      exact hr
    have h3 : 𝓝 (0 : ℝ) = 𝓝[Set.Iic 0] 0 ⊔ 𝓝[Set.Ici 0] 0 := by
      have h := nhdsWithinLE_sup_nhdsWithinGE (s := Set.univ) (a := (0 : ℝ))
      rw [Set.univ_inter, Set.univ_inter, nhdsWithin_univ] at h
      exact h.symm
    rw [ContinuousAt, show (extendLeft γ) 0 = γ 0 from extendLeft_of_nonpos le_rfl, h3,
      tendsto_sup]
    exact ⟨h1, h2⟩
  -- the solution structure
  refine ⟨⟨?_, ?_, ?_⟩, hnc⟩
  · intro x hx
    have hev : extendLeft γ =ᶠ[𝓝[Set.Ioi 0] x] γ := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact extendLeft_of_pos hy
    exact (hcd x hx).congr_of_eventuallyEq hev (extendLeft_of_pos hx)
  · exact hcontAt
  · intro t ht
    have hev : ∀ᶠ s in 𝓝 t, extendLeft γ s = γ s := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact extendLeft_of_pos hs
    have hev' : deriv (extendLeft γ) =ᶠ[𝓝 t] deriv γ := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hs] with y hy
      exact extendLeft_of_pos hy
    have h1 : iteratedDeriv 2 (extendLeft γ) t = iteratedDeriv 2 γ t := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_succ, iteratedDeriv_one]
      exact Filter.EventuallyEq.deriv_eq hev'
    rw [h1, hmotion t ht, extendLeft_of_pos ht]

/-- **A calibrating curve grows at most linearly.**  (`thm-calib.direct.horo`, first step: `γ` is
not superhyperbolic.)  No deep input is needed: the Hölder estimate for `φ_h` together with
`lema-time.estim` bounds a minimiser's displacement linearly in time. -/
theorem norm_sub_le_of_calibrating_curve {m : Fin N → ℝ} {h : ℝ} {u : EN E N → ℝ}
    {γ : ℝ → EN E N} (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hcal : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧ IsHMinimizer m h γ 0 t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖γ t - γ 0‖ ≤ C * (1 + t) := by
  classical
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh.le
  obtain ⟨c, hc, hmc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    rcases isEmpty_or_nonempty (Fin N) with hN' | hN'
    · exact False.elim (isEmptyElim (⟨0, hN⟩ : Fin N))
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty m, ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]; intro i _; exact hm i
      · exact Finset.inf'_le _ (Finset.mem_univ i)
  refine ⟨max 1 (2 * Real.sqrt (α + h * β) / c), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro t ht
  have hbound := norm_sub_le_of_isHMinimizer hh.le hα.le hβ (fun x y => hest x y) hc hmc ht
    (hcal t ht).1 (hcal t ht).2
  have hM0 : 0 ≤ max 1 (2 * Real.sqrt (α + h * β) / c) :=
    le_trans zero_le_one (le_max_left _ _)
  have h2 : 2 * Real.sqrt (α + h * β) * t / c ≤ max 1 (2 * Real.sqrt (α + h * β) / c) * (1 + t) := by
    rcases le_total 1 t with h1 | h1
    · have heq : 2 * Real.sqrt (α + h * β) * t / c = (2 * Real.sqrt (α + h * β) / c) * t := by ring
      rw [heq]
      calc (2 * Real.sqrt (α + h * β) / c) * t
          ≤ max 1 (2 * Real.sqrt (α + h * β) / c) * t :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
        _ ≤ max 1 (2 * Real.sqrt (α + h * β) / c) * (1 + t) :=
            mul_le_mul_of_nonneg_left (by linarith) hM0
    · have h3 : 2 * Real.sqrt (α + h * β) * t / c ≤ 2 * Real.sqrt (α + h * β) / c := by
        rw [div_le_div_iff_of_pos_right hc]
        nlinarith [Real.sqrt_nonneg (α + h * β), ht.le, h1]
      calc 2 * Real.sqrt (α + h * β) * t / c ≤ 2 * Real.sqrt (α + h * β) / c := h3
        _ ≤ max 1 (2 * Real.sqrt (α + h * β) / c) := le_max_right _ _
        _ ≤ max 1 (2 * Real.sqrt (α + h * β) / c) * (1 + t) := by
            nth_rewrite 1 [← mul_one (max 1 (2 * Real.sqrt (α + h * β) / c))]
            exact mul_le_mul_of_nonneg_left (by linarith) hM0
  have h5 : (1 : ℝ) ≤ max 1 (2 * Real.sqrt (α + h * β) / c) * (1 + t) := by
    have h4 : (1 : ℝ) ≤ max 1 (2 * Real.sqrt (α + h * β) / c) := le_max_left _ _
    nlinarith [h4, hM0, ht.le]
  exact hbound.trans (max_le h5 h2)

/-- **The calibrating curve for the problem's own data.**  Given masses, an energy `h > 0` and a
collision-free direction `a ≠ 0`, for every initial configuration `x₀` there is a horofunction `𝔲`
directed by `a` (with `𝔲 0 = 0` and dominated by `L + h`) and a curve `γ` through `x₀` which is an
`h`-minimiser on every `[0,t]` and calibrates `𝔲`. -/
theorem exists_calibrating_curve_of_masses {m : Fin N → ℝ} {h : ℝ} (hN : 0 < N)
    (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (a : EN E N) (ha : a ≠ 0) (ha_nc : WithoutCollisions a) (x₀ : EN E N) :
    ∃ (𝔲 : EN E N → ℝ) (γ : ℝ → EN E N) (ψ : ℕ → ℕ),
      StrictMono ψ ∧ (∀ k, 0 < ψ k) ∧ Dominated m h 𝔲 ∧ 𝔲 0 = 0 ∧ γ 0 = x₀ ∧
      (∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧ IsHMinimizer m h γ 0 t ∧
        actionOn m h γ 0 t = ENNReal.ofReal (𝔲 x₀ - 𝔲 (γ t))) ∧
      (∀ K : Set (EN E N), IsCompact K → TendstoUniformlyOn
        (fun k x => normPot m h ((((ψ k : ℕ) : ℝ)) • a) x) 𝔲 atTop K) := by
  classical
  obtain ⟨φ, hφ, 𝔲, huni, hdom, h𝔲0⟩ := exists_horofunction_of_masses (E := E) hN hm hh.le a
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  -- shift the sequence so that all indices are non-zero (hence the configurations collision free)
  have huni' : ∀ K : Set (EN E N), IsCompact K →
      TendstoUniformlyOn (fun k x => normPot m h (((φ (k + 1) : ℕ) : ℝ) • a) x) 𝔲 atTop K := by
    intro K hK
    have h1 := (huni K hK).seq_tendstoUniformlyOn (fun k => k + 1) (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, normPot] using h1
  have hpnc : ∀ k : ℕ, WithoutCollisions ((((φ (k + 1) : ℕ) : ℝ)) • a) := by
    intro k
    refine withoutCollisions_smul ha_nc ?_
    have h2 : 1 ≤ φ (k + 1) := by
      have h3 : φ 0 < φ (k + 1) := hφ (Nat.succ_pos k)
      omega
    exact ne_of_gt (by exact_mod_cast h2 : (0:ℝ) < ((φ (k + 1) : ℕ) : ℝ))
  have hpgrow : Tendsto (fun k : ℕ => ‖((((φ (k + 1) : ℕ) : ℝ)) • a)‖) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN'⟩ := tendsto_atTop_atTop.mp (hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1))
      (Nat.ceil (max b 0 / ‖a‖) + 1)
    refine ⟨N, fun k hk => ?_⟩
    have h1 : ((Nat.ceil (max b 0 / ‖a‖) + 1 : ℕ) : ℝ) ≤ ((φ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hN' k hk
    have h2 : max b 0 / ‖a‖ ≤ ((Nat.ceil (max b 0 / ‖a‖) + 1 : ℕ) : ℝ) := by
      have h3 := Nat.le_ceil (max b 0 / ‖a‖)
      push_cast
      linarith
    have h3 : max b 0 / ‖a‖ ≤ ((φ (k + 1) : ℕ) : ℝ) := h2.trans h1
    have h4 : max b 0 ≤ ((φ (k + 1) : ℕ) : ℝ) * ‖a‖ := by
      rw [div_le_iff₀ hapos] at h3
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact le_trans (le_max_left b 0) h4
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh.le
  obtain ⟨γ, hγ0, hcal⟩ := exists_calibrating_curve (m := m) (h := h) (u := 𝔲)
    (p := fun k => (((φ (k + 1) : ℕ) : ℝ)) • a) hN hm hh hdom hpnc hpgrow huni'
    hα hβ hest x₀
  refine ⟨𝔲, γ, fun k => φ (k + 1), ?_, ?_, hdom, h𝔲0, hγ0, hcal, ?_⟩
  · exact fun a b hab => Nat.lt_of_lt_of_le (hφ (Nat.succ_lt_succ hab)) le_rfl
  · intro k
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hφ (Nat.succ_pos k))
  · intro K hK
    simpa only [Function.comp_apply] using huni' K hK

/-- **The calibrating curve is a hyperbolic motion modulo Marchal.**  Combining
`exists_calibrating_curve_of_masses` with `isNBodySolution_extendLeft_of_calibrating`: assuming
Marchal's theorem there is a genuine solution of Newton's equations through `x₀`, collision free for
`t > 0`, whose energy is constant on `(0,∞)`. -/
theorem exists_solution_of_masses_of_marchal {m : Fin N → ℝ} {h : ℝ} (hN : 0 < N)
    (hm : ∀ i, 0 < m i) (hh : 0 < h)
    (hM : MarchalProperty (E := E) m h)
    (a : EN E N) (ha : a ≠ 0) (ha_nc : WithoutCollisions a) (x₀ : EN E N) :
    ∃ (𝔲 : EN E N → ℝ) (γ : ℝ → EN E N),
      Dominated m h 𝔲 ∧ 𝔲 0 = 0 ∧ γ 0 = x₀ ∧
      IsNBodySolution m (extendLeft γ) ∧ (∀ t > 0, WithoutCollisions (γ t)) ∧
      (∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧ IsHMinimizer m h γ 0 t ∧
        actionOn m h γ 0 t = ENNReal.ofReal (𝔲 x₀ - 𝔲 (γ t))) := by
  obtain ⟨𝔲, γ, -, -, -, hdom, h𝔲0, hγ0, hcal, -⟩ :=
    exists_calibrating_curve_of_masses (E := E) hN hm hh a ha ha_nc x₀
  have hcal' : ∀ t : ℝ, 0 < t → AbsolutelyContinuousOnInterval γ 0 t ∧ IsHMinimizer m h γ 0 t ∧
      actionOn m h γ 0 t = ENNReal.ofReal (𝔲 (γ 0) - 𝔲 (γ t)) := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := hcal t ht
    exact ⟨h1, h2, by rw [h3, hγ0]⟩
  obtain ⟨hsol, hnc⟩ := isNBodySolution_extendLeft_of_calibrating (γ := γ) hN hm hh hM hcal'
  exact ⟨𝔲, γ, hdom, h𝔲0, hγ0, hsol, hnc, hcal⟩

end Submission.NBody
