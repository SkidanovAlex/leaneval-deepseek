import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Cocycle.log_frob_iterC_nonneg
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob
import Submission.Work.TMC7Core.Lyap.lyap_bddBelow
import Mathlib.Analysis.Subadditive

/-!
# The Lyapunov exponent as a limit of averaged log-Frobenius norms

The Lyapunov exponent of the almost Mathieu cocycle is *defined* (AJ (2.2)--(2.5),
`Work.TMC7Core.lyap`) as the infimum

`lyap α lam E = ⨅ n, (1/(n+1)) ∫₀¹ log ‖A_{n+1}(x)‖_F dx`.

Fekete's lemma (`Subadditive.tendsto_lim`) says that for a subadditive sequence `u` which is
bounded below the averages `u n / n` converge, with limit the infimum of the averages.  Since
the transfer iterates satisfy `A_{m+n}(x) = A_m(x + nα) · A_n(x)` and `frob` is
submultiplicative, `u n = ∫₀¹ log ‖A_n(x)‖_F dx` is subadditive
(`subadditive_integral_log_frob`), and it is bounded below by `0`
(`log_frob_iterC_nonneg`).  Passing to the subsequence `n ↦ n+1` and identifying the infimum
of the shifted averages with the infimum in the definition of `lyap` gives the claim.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMC7Core.Lyap

open Work.TMC7Core

/-! ## Fekete's lemma in the form used below -/

/-- Fekete's lemma for a subadditive sequence `u` bounded below, phrased for the *shifted*
family `n ↦ u (n+1) / (n+1)` and with its infimum as the limit.  This is the form in which
the definition of `lyap` presents the sequence of averages. -/
theorem tendsto_shift_div_iInf {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ))) :
    Tendsto (fun n : ℕ => u (n + 1) / ((n : ℝ) + 1)) atTop
      (nhds (⨅ n : ℕ, u (n + 1) / ((n : ℝ) + 1))) := by
  -- Fekete's lemma for the unshifted averages.
  have hlim : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (nhds h.lim) := h.tendsto_lim hbdd
  -- The shifted averages still converge, to the same limit.
  have hshift : Tendsto (fun n : ℕ => u (n + 1) / (((n + 1 : ℕ)) : ℝ)) atTop (nhds h.lim) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hshift' : Tendsto (fun n : ℕ => u (n + 1) / ((n : ℝ) + 1)) atTop (nhds h.lim) := by
    refine hshift.congr' ?_
    filter_upwards with n
    simp only [Nat.cast_add, Nat.cast_one]
  -- `h.lim` is the infimum of the same set of averages.
  have hlim_eq : h.lim = ⨅ n : ℕ, u (n + 1) / ((n : ℝ) + 1) := by
    have hS : h.lim = sInf ((fun n : ℕ => u n / (n : ℝ)) '' Set.Ici 1) := by
      rw [Subadditive.lim]
    have hrange : Set.range (fun n : ℕ => u (n + 1) / ((n : ℝ) + 1))
        = (fun n : ℕ => u n / (n : ℝ)) '' Set.Ici 1 := by
      ext x; constructor
      · rintro ⟨n, rfl⟩
        refine ⟨n + 1, Set.mem_Ici.mpr (by omega), ?_⟩
        push_cast
        ring_nf
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Set.mem_Ici.mp hm)
        refine ⟨k, ?_⟩
        push_cast
        ring_nf
    rw [hS, ← hrange, sInf_range]
  rw [← hlim_eq]
  exact hshift'

/-! ## The main statement

Fekete's lemma is applied to `u n = ∫₀¹ log ‖A_n(x)‖_F dx`; the two hypotheses are
`subadditive_integral_log_frob` (`Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob`)
and `lyap_bddBelow` (`Submission.Work.TMC7Core.Lyap.lyap_bddBelow`). -/

theorem lyap_eq_lim (α lam : ℝ) (E : ℂ) : Filter.Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)) Filter.atTop (nhds (lyap α lam E)) := by
  have hmain := tendsto_shift_div_iInf (subadditive_integral_log_frob α lam E)
    (lyap_bddBelow α lam E)
  rw [lyap]
  exact hmain

end Work.TMC7Core.Lyap
