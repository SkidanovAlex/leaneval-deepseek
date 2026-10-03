/-
# The narrowness of the packet bump, from the A6 core

The A6 core condition `Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n` contains the large-scale cut
`splitCut ρ L < ⌊a n⌋` with `L = max (max l₁ l₂) (max k₁ k₂)` and
`splitCut ρ L = 2^{2^{uScale ρ L}}`.  Hence `logN ⌊a n⌋ ≥ 2^{uScale ρ L} ≥ uScale ρ L + 1`, so the
modulated bump `varphiNt N 0 t` is supported in the arc `realArc (-(uScale ρ L) - 1)` — the
plateau of the cutoff `periodize (etaCut kmtEta (-(uScale ρ L)))`, whose non-vanishing part is
`realArc (-(uScale ρ L) - 1)`.  This is the narrowness hypothesis of the model-side functional
calculus (`Work.KMTPlan.A6.Tle_mdlF_eq_Tm_local`, and the singleton-gate height-`0` version
`Tle_mdlF_eq_Tle_atZero_singleton`).

Everything here is a consequence of `Work.KMTAreas.A7.varphiNt_support` and
`Work.KMTPlan.A6.supportedInArc_periodize'` (neither of which needs any separation of the
Ionescu--Wainger arc system).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.tmRandSymb_l2

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

noncomputable section

/-- `SupportedInArc` is monotone: a larger (coarser) level is easier. -/
lemma pkt_supportedInArc_mono_level {k k' : ℤ} (h : k ≤ k')
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : SupportedInArc k Φ) : SupportedInArc k' Φ :=
  fun ξ hξ => let ⟨θ, hθ, hθ'⟩ := hΦ ξ hξ; ⟨θ, realArc_mono h hθ, hθ'⟩

/-- The bump `varphiNt N 0 t` is supported in the arc of level `-(logN N)`. -/
theorem supportedInArc_varphiNt_zero (N : ℕ) (t : ℝ) :
    SupportedInArc (-(Work.Analysis.EndVar.logN N))
      (periodize (varphiNt N 0 t)) := by
  refine Work.KMTPlan.A6.supportedInArc_periodize' (fun ξ hξ => ?_)
  have h := Work.KMTAreas.A7.varphiNt_support N 0 t ξ hξ
  have hcast : (0 : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)
      = ((-(Work.Analysis.EndVar.logN N) : ℤ) : ℝ) := by push_cast; ring
  rw [Nat.cast_zero] at h
  rw [hcast, Real.rpow_intCast] at h
  simp only [realArc, Set.mem_Icc, abs_le] at h ⊢
  exact ⟨h.1, h.2⟩

/-- **The narrowness of the packet bump on the A6 core.**  On the core the bump `varphiNt ⌊a n⌋ 0 t`
is supported in `realArc (-(uScale ρ L) - 1)`, the plateau of `periodize (etaCut kmtEta (-(uScale ρ L)))`. -/
theorem supportedInArc_varphiNt_zero_of_core (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₂ n : ℕ) (t : ℝ)
    (h : mdlCore ρ C₀ a 0 l₂ 0 k₂ n) :
    SupportedInArc (-((Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂)) : ℕ) : ℤ) - 1)
      (periodize (varphiNt (Nat.floor (a n)) 0 t)) := by
  obtain ⟨_, hcut, _⟩ := h
  set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂)) with hudef
  -- `2^{2^u} < ⌊a n⌋` gives `u + 1 ≤ logN ⌊a n⌋`
  have hn : (2 : ℕ) ^ (2 ^ u) < Nat.floor (a n) := hcut
  have hlog_nat : 2 ^ u ≤ Nat.log 2 (max (Nat.floor (a n)) 2) :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans hn.le (le_max_left _ _))
  have hlog : ((2 : ℕ) ^ u : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
    rw [Work.Analysis.EndVar.logN]
    exact_mod_cast hlog_nat
  have hup : ((u : ℤ)) + 1 ≤ ((2 : ℕ) ^ u : ℤ) := by
    have hone : ((u : ℤ)) + 1 = ((u + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hone]
    exact_mod_cast Nat.succ_le_of_lt (show u < 2 ^ u from Nat.lt_two_pow_self)
  have hle : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ -((u : ℤ)) - 1 := by
    have : ((u : ℤ)) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := le_trans hup hlog
    omega
  exact pkt_supportedInArc_mono_level hle (supportedInArc_varphiNt_zero (Nat.floor (a n)) t)

end

end Work.KMTPlan.A6
