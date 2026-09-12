import ChallengeDeps
import Submission.Helpers
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.poels_exists_infinite
import Submission.Commons.Order.ENNReal.exists_positive_nnreal_lt
import Submission.Commons.Analysis.SpecialFunctions.Log.two_sub_log_two_pos

open OnApproximationOfReals
open NNReal ENNReal EReal
open Set

set_option autoImplicit false

namespace Submission

open Commons.NumberTheory.DiophantineApproximation.BoundedDegree

private lemma omega_mem_stars_of_poels (n : ℕ) (hn : 2 ≤ n) (ξ : ℝ) (hξ : Transcendental ℚ ξ)
    (ω : ℝ≥0) (hω0 : 0 < ω) (hω : (ω : ℝ) < (1 / (2 - Real.log 2)) * n) :
    ω ∈ ω_stars n ξ := by
  have hS : (poelsSet n ξ (ω : ℝ)).Infinite :=
    poels_exists_infinite n hn ξ hξ (ω : ℝ) hω0 hω
  unfold ω_stars
  refine ⟨hω0, ?_⟩
  classical
  let dom : Set ℂ := poelsSet n ξ (ω : ℝ)
  have hInfDom : Infinite {x : ℂ // x ∈ dom} := infinite_coe_iff.mpr hS
  let f : {x : ℂ // x ∈ dom} → AlgebraicDegLE n := fun x =>
    ⟨x.1, x.2.1, x.2.2.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv : (f x).1 = (f y).1 := congrArg Subtype.val hxy
    dsimp [f] at hv
    exact Subtype.ext hv
  have htarget : ∀ x : {x : ℂ // x ∈ dom}, f x ∈
      {α : AlgebraicDegLE n | 0 < ‖ξ - α.1‖ ∧ ‖ξ - α.1‖ ≤ (height α.1) ^ (- (ω : ℝ) - 1)} := by
    intro x
    have hx : x.1 ∈ poelsSet n ξ (ω : ℝ) := x.2
    dsimp [dom, f] at hx ⊢
    change 0 < ‖ξ - (x.1 : ℂ)‖ ∧ ‖ξ - (x.1 : ℂ)‖ ≤
      (OnApproximationOfReals.height x.1) ^ (-(ω : ℝ) - 1)
    rcases hx with ⟨hAlg, hDeg, hpos, hdist⟩
    refine ⟨hpos, ?_⟩
    have hh : poelsHeight x.1 = OnApproximationOfReals.height x.1 := by
      dsimp [poelsHeight, OnApproximationOfReals.height]
    rw [hh] at hdist
    exact hdist
  exact Set.infinite_of_injective_forall_mem hf htarget

theorem theorem_1_1 (n : ℕ) (hn : n ≥ 2) (ξ : ℝ) (hξ : Transcendental ℚ ξ) :
    letI a : ℝ := 1 / (2 - Real.log 2)
    (ω⋆ n ξ : EReal) ≥ (a : EReal) * n := by
  let a : ℝ := 1 / (2 - Real.log 2)
  let ω0 : ℝ≥0 := ⟨a * n, by
    have hden : 0 < 2 - Real.log 2 := Commons.Analysis.SpecialFunctions.Log.two_sub_log_two_pos
    have hn0 : 0 ≤ (n:ℝ) := by exact_mod_cast (Nat.zero_le n)
    positivity⟩
  have hR : (a : EReal) * n = ((ω0 : ℝ≥0∞) : EReal) := by
    rw [← EReal.coe_natCast (n := n), ← EReal.coe_mul]
    rw [EReal.coe_nnreal_eq_coe_real]
    rfl
  rw [hR]
  rw [ge_iff_le]
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  change (ω0 : ℝ≥0∞) ≤ sSup (((↑) : ℝ≥0 → ℝ≥0∞) '' ω_stars n ξ)
  rw [le_sSup_iff_forall_lt]
  intro b hb
  have hω0pos : 0 < ω0 := by
    have hden : 0 < 2 - Real.log 2 := Commons.Analysis.SpecialFunctions.Log.two_sub_log_two_pos
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    have hprod : 0 < a * (n:ℝ) := mul_pos ha hn0
    exact_mod_cast hprod
  obtain ⟨ω, hωpos, hbω, hωlt⟩ :=
    Commons.Order.ENNReal.exists_positive_nnreal_lt hω0pos b hb
  refine ⟨(ω : ℝ≥0∞), ?_, hbω⟩
  refine ⟨ω, ?_, rfl⟩
  have hωlt_real : (ω : ℝ) < a * n := by
    exact ENNReal.coe_lt_coe.mp (by simpa [ω0] using hωlt)
  exact omega_mem_stars_of_poels n hn ξ hξ ω hωpos hωlt_real

end Submission
