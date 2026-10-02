import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Local uniform escape on the complement of the filled Julia set

If `f : ℂ → ℂ` is continuous and admits a real `R ≥ 2` with `2 ‖z‖ ≤ ‖f z‖` whenever
`‖z‖ ≥ R` (an *escape radius*), then the iterates of `f` escape locally uniformly to
infinity on a neighbourhood of every point of the complement of the filled Julia set.

Formally: for every `z` whose orbit is unbounded there is an open neighbourhood `U ∋ z`
on which `f^[n] → ∞` locally uniformly (`TendstoLocallyUniformlyAtTop`).

The proof is the classical one: an unbounded orbit meets `{‖·‖ > R}`, so `‖f^[N] z‖ > R`
for some `N`; by continuity `‖f^[N] w‖ > R` on a whole neighbourhood `U` of `z`, after which
each application of `f` at least doubles the modulus, giving uniform (indeed geometric)
divergence on compact subsets of `U`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology

theorem filledJulia_locallyUniform_escape {f : ℂ → ℂ} {R : ℝ} (hR : 2 ≤ R)
    (hcont : Continuous f) (h : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) :
    ∀ z : ℂ, z ∉ Work.Normal.FilledJuliaSet f → ∃ U : Set ℂ, U ∈ nhds z ∧ IsOpen U ∧
      Work.Normal.TendstoLocallyUniformlyAtTop (fun n : ℕ => f^[n]) U := by
  -- Geometric growth of the modulus while the orbit stays outside the disk of radius `R`.
  have growth : ∀ (k : ℕ) (w : ℂ), R ≤ ‖w‖ → (2 : ℝ) ^ k * ‖w‖ ≤ ‖f^[k] w‖ := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hle1 : ‖w‖ ≤ (2 : ℝ) ^ k * ‖w‖ := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        nlinarith [norm_nonneg w]
      have hRk : R ≤ ‖f^[k] w‖ := hw.trans (hle1.trans (ih w hw))
      have hstep : 2 * ‖f^[k] w‖ ≤ ‖f (f^[k] w)‖ := h _ hRk
      calc (2 : ℝ) ^ (k + 1) * ‖w‖ = 2 * ((2 : ℝ) ^ k * ‖w‖) := by ring
        _ ≤ 2 * ‖f^[k] w‖ := by nlinarith [ih w hw]
        _ ≤ ‖f (f^[k] w)‖ := hstep
        _ = ‖f^[k + 1] w‖ := by rw [Function.iterate_succ_apply']
  intro z hz
  -- An unbounded orbit exceeds every bound, in particular `R`.
  simp only [FilledJuliaSet, Set.mem_ofPred_eq, not_exists, not_forall, not_le] at hz
  obtain ⟨N, hN⟩ := hz R
  have hopen : IsOpen {w : ℂ | R < ‖f^[N] w‖} :=
    isOpen_lt continuous_const ((hcont.iterate N).norm)
  refine ⟨{w : ℂ | R < ‖f^[N] w‖}, hopen.mem_nhds hN, hopen, ?_⟩
  intro K hKV hK R'
  by_cases hKne : K.Nonempty
  · -- On a compact subset the lower bound on `‖f^[N] ·‖` is attained.
    obtain ⟨w0, hw0K, hmin⟩ := hK.exists_isMinOn hKne ((hcont.iterate N).norm).continuousOn
    have hcR : R < ‖f^[N] w0‖ := hKV hw0K
    have hcpos : 0 < ‖f^[N] w0‖ := lt_of_lt_of_le (by linarith) (le_of_lt hcR)
    -- Choose how many extra iterations are needed to beat `R'`.
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R' / ‖f^[N] w0‖) (show (1 : ℝ) < 2 by norm_num)
    have hk' : R' ≤ (2 : ℝ) ^ k * ‖f^[N] w0‖ := le_of_lt ((div_lt_iff₀ hcpos).mp hk)
    refine ⟨N + k, ?_⟩
    intro n hn w hwK
    have hNn : N ≤ n := le_trans (Nat.le_add_right N k) hn
    obtain ⟨m, hm⟩ := Nat.le.dest hNn
    have hkm : k ≤ m := by
      have hle : N + k ≤ N + m := by rw [hm]; exact hn
      exact (Nat.add_le_add_iff_left).mp hle
    have hRw : R ≤ ‖f^[N] w‖ := by
      have hmw : ‖f^[N] w0‖ ≤ ‖f^[N] w‖ := (isMinOn_iff.mp hmin) w hwK
      linarith [le_of_lt hcR]
    have heq : ‖f^[n] w‖ = ‖f^[m] (f^[N] w)‖ := by
      rw [← hm, Nat.add_comm N m, Function.iterate_add_apply]
    calc R' ≤ (2 : ℝ) ^ k * ‖f^[N] w0‖ := hk'
      _ ≤ (2 : ℝ) ^ m * ‖f^[N] w0‖ := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hcpos)
          exact pow_le_pow_right₀ (by norm_num) hkm
      _ ≤ (2 : ℝ) ^ m * ‖f^[N] w‖ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (isMinOn_iff.mp hmin) w hwK
      _ ≤ ‖f^[m] (f^[N] w)‖ := growth m (f^[N] w) hRw
      _ = ‖f^[n] w‖ := heq.symm
  · -- An empty compact set carries no constraint.
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    refine ⟨0, ?_⟩
    intro _ _ w hwK
    rw [hKne] at hwK
    exact absurd hwK (Set.notMem_empty w)

end Work.Normal
