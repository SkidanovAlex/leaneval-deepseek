import Mathlib
import Submission.Work.RPV.VBasic
import Submission.Work.RPCore.Core.Steps
import Submission.Work.RPCore.Core.GenFuns
import Submission.Work.RPCore.Chain.chainAction_crit
import Submission.Work.RPCore.Chain.chainAction_has_crit

/-!
# CORE: the composite `Φ_1⁻¹ ∘ τ_θ ∘ Φ_1` meets the zero section

*The statement.* Let `H` be a compactly supported (mod `2π` in the angle coordinate `q₂`)
time-dependent Hamiltonian on `T^*ℝ² = PS`, `Φ` its flow, and `0 < θ < π`.  Then there are
`x, y` on the zero section `Zsec = {p = 0}` with `τ_θ (Φ 1 x) = Φ 1 y`.

*The proof.*  With `δ = θ/N` for a large `N`, the composite `Ψ = Φ_1⁻¹ ∘ τ_θ ∘ Φ_1` is written as
a chain of `3N` steps: the `N` flow slices of `Φ_1`, the `N` rotations `τ_δ`, and the `N` flow
slices of `Φ_1⁻¹` (`Core/Steps`, `Core/GenFuns`).  Each step has a global type-2 generating
function (`GenFun.exists_type2GF` for the slices, `Wrot δ` for the rotations), the chain action
`chainAction (3N-1) W` has a critical point (`Chain.chainAction_has_crit`, the saddle-point step),
and `Chain.chainAction_crit` turns such a critical point into a chain of points running from
`Zsec` back into `Zsec`; `Core.Steps.foldl_ofFn_chain'` identifies the fold of that chain with
`Ψ`.  The statement follows because `Ψ x = y` is equivalent to `τ_θ (Φ 1 x) = Φ 1 y`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Core

open Real
open Work.RPV Work.RPCore.Chain Work.RPCore.Flow

theorem core (Hh : Work.RPV.CptPerHam) (Φ : ℝ → Work.RPV.PS → Work.RPV.PS)
    (hΦ : Work.RPV.IsFlow Hh.H Φ) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < π) :
    ∃ x ∈ Work.RPV.Zsec, ∃ y ∈ Work.RPV.Zsec, Work.RPV.tau θ (Φ 1 x) = Φ 1 y := by
  -- ## The number of steps and the rotation increment
  obtain ⟨N, hNgt⟩ := exists_nat_gt
    (max ((clampedData Hh).K / Real.log (5 / 4)) (2 * θ / Real.pi) + 1)
  have hlog : (0 : ℝ) < Real.log (5 / 4) := Real.log_pos (by norm_num)
  have hmaxnn : (0 : ℝ) ≤ max ((clampedData Hh).K / Real.log (5 / 4)) (2 * θ / Real.pi) :=
    le_trans (div_nonneg (clampedData Hh).hK₀ hlog.le) (le_max_left _ _)
  have hN1 : 1 ≤ N := by
    have h1' : (1 : ℝ) < N :=
      lt_of_le_of_lt (by simpa using add_le_add_right hmaxnn 1) hNgt
    exact_mod_cast le_of_lt h1'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hKbound : (clampedData Hh).K / N < Real.log (5 / 4) := by
    have hlt : (clampedData Hh).K / Real.log (5 / 4) < N :=
      lt_of_le_of_lt (le_max_left _ _)
        (lt_of_lt_of_le (lt_add_one _) (le_of_lt hNgt))
    have h2 : (clampedData Hh).K < N * Real.log (5 / 4) := (div_lt_iff₀ hlog).mp hlt
    rw [div_lt_iff₀ hNpos]
    exact h2.trans_le (le_of_eq (mul_comm _ _))
  have hKN : Real.exp ((clampedData Hh).K / N) - 1 ≤ 1 / 4 := by
    have hexp : Real.exp ((clampedData Hh).K / N) ≤ 5 / 4 := by
      calc Real.exp ((clampedData Hh).K / N) ≤ Real.exp (Real.log (5 / 4)) :=
            Real.exp_le_exp.mpr hKbound.le
        _ = 5 / 4 := Real.exp_log (by norm_num)
    linarith only [hexp]
  set δ : ℝ := θ / N with hδdef
  have hθN : 2 * θ / Real.pi < N :=
    lt_of_le_of_lt (le_max_right _ _)
      (lt_of_lt_of_le (lt_add_one _) (le_of_lt hNgt))
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδπ : δ < Real.pi / 2 := by
    rw [hδdef, div_lt_iff₀ hNpos]
    have h2 : θ = (2 * θ / Real.pi) * (Real.pi / 2) := by field_simp
    rw [h2]
    calc (2 * θ / Real.pi) * (Real.pi / 2) < N * (Real.pi / 2) :=
          mul_lt_mul_of_pos_right hθN (by positivity)
      _ = Real.pi / 2 * N := by ring
  have hNδ : (N : ℝ) * δ = θ := by rw [hδdef]; field_simp
  have hθπ : (N : ℝ) * δ < Real.pi := by rw [hNδ]; exact h1
  have hδabs : |δ| < Real.pi / 2 := by rw [abs_of_pos hδ0]; exact hδπ
  -- ## The `3N` generating functions
  have hn : 3 * N - 1 + 1 = 3 * N := by omega
  have hWc : ∀ j : Fin (3 * N - 1 + 1), ContDiff ℝ 3
      (gfFam Hh (3 * N - 1) N hN1 hn δ hKN j) :=
    fun j => gfFam_contDiff Hh (3 * N - 1) N hN1 hn δ hKN j
  have hWmid : ∀ j : Fin (3 * N - 1 + 1), midBlock N (j : ℕ) →
      gfFam Hh (3 * N - 1) N hN1 hn δ hKN j = Wrot δ :=
    fun j hj => gfFam_mid Hh (3 * N - 1) N hN1 hn δ hKN j hj
  have hWper : ∀ (j : Fin (3 * N - 1 + 1)) (x : PS),
      gfFam Hh (3 * N - 1) N hN1 hn δ hKN j (Tk 1 x) =
        gfFam Hh (3 * N - 1) N hN1 hn δ hKN j x :=
    fun j x => gfFam_per Hh (3 * N - 1) N hN1 hn δ hKN j x
  have hWsup : ∀ j : Fin (3 * N - 1 + 1), ¬ midBlock N (j : ℕ) →
      ∃ R : ℝ, ∀ x, R ≤ |x.1.1| + |x.2.1| + |x.2.2| →
        gfFam Hh (3 * N - 1) N hN1 hn δ hKN j x = 0 :=
    fun j hj => gfFam_sup Hh (3 * N - 1) N hN1 hn δ hKN j hj
  -- ## A critical point of the chain action, hence a chain from `Z` to `Z`
  obtain ⟨z, hz⟩ := chainAction_has_crit (3 * N - 1) N hN1 rfl δ hδ0 hδπ hθπ
    (gfFam Hh (3 * N - 1) N hN1 hn δ hKN) hWc hWmid hWper hWsup
  obtain ⟨x₀, hx₀, y₀, hy₀, hfold⟩ := chainAction_crit (3 * N - 1)
    (stepMap Hh (3 * N - 1) N δ) (gfFam Hh (3 * N - 1) N hN1 hn δ hKN)
    (fun j => gfFam_isType2GF Hh (3 * N - 1) N hN1 hn δ hKN hδabs j)
    (fun j => (gfFam_contDiff Hh (3 * N - 1) N hN1 hn δ hKN j).differentiable (by norm_num))
    z.1 z.2 hz
  -- ## The fold of the chain is the composite `Φ_1⁻¹ ∘ τ_θ ∘ Φ_1`
  have hchain : List.foldl (fun acc f => f acc) x₀
      (List.ofFn (stepMap Hh (3 * N - 1) N δ)) =
      chainSeq Hh (3 * N - 1) N δ x₀ (Fin.last (3 * N - 1 + 1)) := by
    conv_lhs => rw [← chainSeq_zero Hh (3 * N - 1) N δ x₀]
    exact foldl_ofFn_chain' (3 * N - 1 + 1) (stepMap Hh (3 * N - 1) N δ)
      (chainSeq Hh (3 * N - 1) N δ x₀) (chainSeq_step Hh (3 * N - 1) N hN1 hn δ x₀)
  have hy : y₀ = Phi Hh 1 0 (tau θ (Phi Hh 0 1 x₀)) := by
    rw [← hfold, hchain, chainSeq_last Hh (3 * N - 1) N hN1 hn δ x₀, hNδ]
  -- ## Conclusion
  refine ⟨x₀, hx₀, y₀, hy₀, ?_⟩
  have hΦ1 : ∀ w : PS, Φ 1 w = Phi Hh 0 1 w := fun w =>
    Phi_unique Hh Φ hΦ.2 hΦ.1 (by norm_num : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 2) w
  rw [hΦ1 x₀, hΦ1 y₀, hy]
  rw [Phi_add Hh 1 0 1 (tau θ (Phi Hh 0 1 x₀)), Phi_self]

end Work.RPCore.Core
