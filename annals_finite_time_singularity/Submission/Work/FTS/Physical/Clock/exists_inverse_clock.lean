/-
# `Work.FTS.Physical.Clock.exists_inverse_clock` — the inverse clock `t ↦ τ(t)`

The clock `t(τ) = ∫₀^τ A` is strictly increasing and continuous on `[0,∞)` with `t(τ) → T` and
`t 0 = 0`, so every physical time `t ∈ [0,T)` is `t = t(τ)` for a *unique* fake time `τ = τ(t)`.
This module builds that inverse (by choice, from `PhysClock.exists_t_eq`) and proves the three
properties the reconstruction uses:

* `t(τ(t)) = t` and `τ(t) ≥ 0`;
* the clock comparison `T - t ≤ 2 A(τ(t))` (`A ≍ T - t`);
* **differentiability**: `τ'(t) = 1/A(τ(t))` — the inverse function theorem at the integral
  clock, whose derivative is `A > 0`.

The proof of differentiability does not need a global inverse-function theorem: `τ` is continuous
at `t` by an elementary `ε`-`δ` argument from the strict monotonicity of `t` (for `s > t`,
`τ(t) < τ(s) < τ(t) + η` because otherwise `s = t(τ(s)) ≥ t(τ(t) + η)`), and then
`HasDerivAt.of_local_left_inverse` applies to the identity `t(τ(s)) = s`, which holds on an open
neighbourhood of `t` inside `[0,T)`.
-/
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.exists_t_eq
import Submission.Work.FTS.Physical.Clock.tail_le_two_mul
import Submission.Work.FTS.Physical.Clock.hasDerivAt_t
import Submission.Work.FTS.Physical.Clock.t_strictMonoOn
import Mathlib.Analysis.Calculus.Deriv.Inverse

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical.Clock

open Work.FTS.Physical (PhysClock)
open Work.FTS.Physical.PhysClock

/-- **The inverse clock.**  There is a function `τ : ℝ → ℝ` such that for every physical time
`t < T`: `t(τ(t)) = t`, `τ(t) ≥ 0`, `T - t ≤ 2 A(τ(t))`, and `τ` is differentiable at every
interior time with derivative `1/A(τ(t))`. -/
theorem exists_inverse_clock (C : Work.FTS.Physical.PhysClock) :
    ∃ tau : ℝ → ℝ, (∀ t ∈ Set.Ico 0 C.T, C.t (tau t) = t) ∧
      (∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t) ∧
      (∀ t ∈ Set.Ico 0 C.T, C.T - t ≤ 2 * C.A (tau t)) ∧
      ∀ t ∈ Set.Ioo 0 C.T, HasDerivAt tau ((C.A (tau t))⁻¹) t := by
  classical
  -- the inverse, built by choice from the surjectivity of the clock
  let tau : ℝ → ℝ := fun t => if h : t ∈ Set.Ico 0 C.T then (Work.FTS.Physical.Clock.exists_t_eq C h).choose else 0
  have htau : ∀ t ∈ Set.Ico 0 C.T, 0 ≤ tau t ∧ C.t (tau t) = t := by
    intro t ht
    have h := (Work.FTS.Physical.Clock.exists_t_eq C ht).choose_spec
    simpa only [tau, dif_pos ht] using h
  have hmono : MonotoneOn C.t (Set.Ici (0 : ℝ)) := (Work.FTS.Physical.Clock.t_strictMonoOn C).monotoneOn
  refine ⟨tau, fun t ht => (htau t ht).2, fun t ht => (htau t ht).1, fun t ht => ?_, ?_⟩
  · have h1 : C.T - C.t (tau t) ≤ 2 * C.A (tau t) := Work.FTS.Physical.Clock.tail_le_two_mul C (htau t ht).1
    rwa [(htau t ht).2] at h1
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have htIco : t ∈ Set.Ico 0 C.T := ⟨ht0.le, htT⟩
  have hτpos : 0 < tau t := by
    rcases lt_or_eq_of_le (htau t htIco).1 with h | h
    · exact h
    · exfalso
      have h0 : C.t (tau t) = 0 := by rw [← h]; exact PhysClock.t_zero C
      rw [(htau t htIco).2] at h0
      exact absurd h0 (ne_of_gt ht0)
  have hτnn : 0 ≤ tau t := hτpos.le
  -- the one-sided windows
  have hη'le : ∀ η' , η' ≤ tau t / 2 → 0 ≤ tau t - η' := fun η' h => by linarith
  -- continuity of `tau` at `t`, from the strict monotonicity of `C.t`
  have hcont : ContinuousAt tau t := by
    rw [Metric.continuousAt_iff]
    intro η hη
    set η' : ℝ := min η (tau t / 2) with hη'def
    have hη'pos : 0 < η' := lt_min hη (by linarith)
    have hη'leη : η' ≤ η := min_le_left _ _
    have hη'let : η' ≤ tau t / 2 := min_le_right _ _
    have hmem_lo : (0 : ℝ) ≤ tau t - η' := by linarith
    have hmem_hi : (0 : ℝ) ≤ tau t + η' := by linarith
    have hmem_t : (0 : ℝ) ≤ tau t := hτnn
    set δ : ℝ := min (min (C.t (tau t + η') - t) (t - C.t (tau t - η'))) (min (C.T - t) t)
      with hδdef
    have hδ1 : 0 < C.t (tau t + η') - t := by
      have h : C.t (tau t) < C.t (tau t + η') :=
        Work.FTS.Physical.Clock.t_strictMonoOn C hmem_t hmem_hi (by linarith)
      rw [(htau t htIco).2] at h
      linarith
    have hδ2 : 0 < t - C.t (tau t - η') := by
      have h : C.t (tau t - η') < C.t (tau t) :=
        Work.FTS.Physical.Clock.t_strictMonoOn C hmem_lo hmem_t (by linarith)
      rw [(htau t htIco).2] at h
      linarith
    have hδpos : 0 < δ := lt_min (lt_min hδ1 hδ2) (lt_min (by linarith) ht0)
    have hδle1 : δ ≤ C.t (tau t + η') - t := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδle2 : δ ≤ t - C.t (tau t - η') := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδleT : δ ≤ C.T - t := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδlet : δ ≤ t := le_trans (min_le_right _ _) (min_le_right _ _)
    refine ⟨δ, hδpos, fun s hs => ?_⟩
    have hsδ : |s - t| < δ := by rwa [Real.dist_eq] at hs
    have hw := abs_lt.mp hsδ
    rw [Real.dist_eq]
    rcases lt_trichotomy s t with hst | heq | hts
    · -- `s < t`
      have hsIco : s ∈ Set.Ico 0 C.T := by
        refine ⟨?_, by linarith⟩
        linarith [hw.1, hδlet]
      have hlt : tau s < tau t := by
        rcases lt_trichotomy (tau s) (tau t) with h | h | h
        · exact h
        · have hst_eq : s = t := by rw [← (htau s hsIco).2, ← (htau t htIco).2, h]
          exact absurd hst_eq (ne_of_lt hst)
        · have hle : C.t (tau t) ≤ C.t (tau s) :=
            hmono (htau t htIco).1 (htau s hsIco).1 h.le
          rw [(htau s hsIco).2, (htau t htIco).2] at hle
          exact absurd hle (not_le.mpr hst)
      have hlow : tau t - η' < tau s := by
        by_contra hcon
        push_neg at hcon
        have hle : C.t (tau s) ≤ C.t (tau t - η') :=
          hmono (show tau s ∈ Set.Ici (0 : ℝ) from (htau s hsIco).1)
            (show tau t - η' ∈ Set.Ici (0 : ℝ) from hmem_lo) hcon
        rw [(htau s hsIco).2] at hle
        linarith [hw.1, hδle2]
      rw [abs_of_neg (by linarith)]
      have : tau t - tau s < η' := by linarith
      linarith
    · subst heq
      simpa using hη
    · -- `t < s`
      have hsIco : s ∈ Set.Ico 0 C.T := by
        refine ⟨by linarith, ?_⟩
        linarith [hw.2, hδleT]
      have hlt : tau t < tau s := by
        rcases lt_trichotomy (tau t) (tau s) with h | h | h
        · exact h
        · have hst_eq : s = t := by rw [← (htau s hsIco).2, ← (htau t htIco).2, ← h]
          exact absurd hst_eq (ne_of_gt hts)
        · have hle : C.t (tau s) ≤ C.t (tau t) :=
            hmono (htau s hsIco).1 (htau t htIco).1 h.le
          rw [(htau s hsIco).2, (htau t htIco).2] at hle
          exact absurd hle (not_le.mpr hts)
      have hhigh : tau s < tau t + η' := by
        by_contra hcon
        push_neg at hcon
        have hle : C.t (tau t + η') ≤ C.t (tau s) :=
          hmono (show tau t + η' ∈ Set.Ici (0 : ℝ) from hmem_hi)
            (show tau s ∈ Set.Ici (0 : ℝ) from (htau s hsIco).1) hcon
        rw [(htau s hsIco).2] at hle
        linarith [hw.2, hδle1]
      rw [abs_of_pos (by linarith)]
      have : tau s - tau t < η' := by linarith
      linarith
  -- the local identity and the inverse function theorem
  have hloc : ∀ᶠ s in 𝓝 t, C.t (tau s) = s := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Set.Ioo (t - min (t / 2) ((C.T - t) / 2))
      (t + min (t / 2) ((C.T - t) / 2)) from
      ⟨by have h := lt_min (by linarith : (0 : ℝ) < t / 2)
            (by linarith : (0 : ℝ) < (C.T - t) / 2); linarith,
       by have h := lt_min (by linarith : (0 : ℝ) < t / 2)
            (by linarith : (0 : ℝ) < (C.T - t) / 2); linarith⟩)] with s hs
    obtain ⟨hs1, hs2⟩ := hs
    have hεt : min (t / 2) ((C.T - t) / 2) ≤ t / 2 := min_le_left _ _
    have hεT : min (t / 2) ((C.T - t) / 2) ≤ (C.T - t) / 2 := min_le_right _ _
    exact (htau s ⟨by linarith, by linarith⟩).2
  exact HasDerivAt.of_local_left_inverse hcont (Work.FTS.Physical.Clock.hasDerivAt_t C hτpos)
    (ne_of_gt (C.hApos (tau t) hτnn)) hloc

end Work.FTS.Physical.Clock
