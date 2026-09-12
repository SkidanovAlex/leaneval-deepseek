import Mathlib
import Submission.F_eps
import Submission.F_existsT

/-!
Diagonal instantiation: apply the epsilon partial-coloring lemma along δ_k = 1/(k+10) (child task).

STATEMENT.  Given n ≥ 1, x0 ∈ [-1,1]^n, nonzero vectors v : ι → Vec n and
thresholds c ≥ 0 with Σ exp(-(c j)²/16) ≤ n/16, produce a SEQUENCE of points
xseq k : Vec n (one per k : ℕ) with, writing δ_k := 1/((k:ℝ)+10):
  · |(xseq k) i| ≤ 1 for all coordinates i,
  · |⟨xseq k − x0, v j⟩| ≤ c j ‖v j‖ for all rows j,
  · at least n/2 coordinates of xseq k are frozen at level δ_k.
-/

open scoped BigOperators RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open Classical

set_option linter.unusedVariables false

namespace Submission.Discrepancy

/-- For any `M ≥ 0`, `a > 0`, `B > 0` there is a natural `T ≥ 1` with
`M * T * exp (-a * T) < B`. -/
lemma exists_nat_small_exp_ge_one (M a B : ℝ) (hM : 0 ≤ M) (ha : 0 < a) (hB : 0 < B) :
    ∃ T : ℕ, 1 ≤ T ∧ M * (T : ℝ) * Real.exp (-a * (T : ℝ)) < B := by
  have hbase : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa [pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have harg : Tendsto (fun x : ℝ => a * x) atTop atTop := tendsto_id.const_mul_atTop ha
  have hcomp : Tendsto (fun x : ℝ => (a * x) * Real.exp (-(a * x))) atTop (𝓝 0) :=
    hbase.comp harg
  have hsc : Tendsto (fun x : ℝ => (M / a) * ((a * x) * Real.exp (-(a * x)))) atTop (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul (M / a) hcomp)
  have hF : Tendsto (fun x : ℝ => M * x * Real.exp (-(a * x))) atTop (𝓝 0) := by
    refine hsc.congr' ?_
    filter_upwards with x
    field_simp [ha.ne']
  have hFn : Tendsto (fun T : ℕ => M * (T : ℝ) * Real.exp (-(a * (T : ℝ)))) atTop (𝓝 0) :=
    hF.comp tendsto_natCast_atTop_atTop
  have hB' : ∀ᶠ T : ℕ in atTop, M * (T : ℝ) * Real.exp (-(a * (T : ℝ))) < B :=
    (tendsto_order.1 hFn).2 B hB
  rcases (eventually_atTop.1 hB') with ⟨N, hN⟩
  refine ⟨max N 1, le_max_right N 1, ?_⟩
  simpa [neg_mul] using hN (max N 1) (le_max_left N 1)

/-- A sequence of ε-valid points with δ_k = 1/(k+10) → 0. -/
lemma diag_eps {ι : Type*} [Fintype ι] (n : ℕ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (hn : 1 ≤ n) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j)
    (hne : ∀ j : ι, ‖v j‖ ≠ 0) (hsum : ∑ j : ι, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) :
    ∃ xseq : ℕ → Vec n,
      (∀ k : ℕ, ∀ i : Fin n, |xseq k i| ≤ 1) ∧
      (∀ k : ℕ, ∀ j : ι, |vin (xseq k - x0) (v j)| ≤ c j * ‖v j‖) ∧
      (∀ k : ℕ, (n : ℝ) / 2 ≤ ((frozenVars (1 / ((k : ℝ) + 10)) (xseq k)).card : ℝ)) := by
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 10)
  have hδpos : ∀ k : ℕ, 0 < δ k := by
    intro k
    dsimp [δ]
    positivity
  have hδsq : ∀ k : ℕ, 0 < (δ k) ^ 2 := fun k => sq_pos_of_pos (hδpos k)
  have hδle : ∀ k : ℕ, δ k ≤ 1 / 10 := by
    intro k
    dsimp [δ]
    have hk10 : 0 < (k : ℝ) + 10 := by positivity
    field_simp [hk10.ne']
    have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    linarith
  let M : ℝ := 2 * ((n : ℝ) + (Fintype.card ι : ℝ))
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hTchoice : ∀ k : ℕ,
      ∃ T : ℕ, 1 ≤ T ∧ M * (T : ℝ) * Real.exp (-((δ k) ^ 2 / 10) * (T : ℝ)) < 1 / 1000000 := by
    intro k
    apply exists_nat_small_exp_ge_one M ((δ k) ^ 2 / 10) (1 / 1000000) hM
    · positivity
    · norm_num
  let T : ℕ → ℕ := fun k => (hTchoice k).choose
  have hT1 : ∀ k : ℕ, 1 ≤ T k := fun k => (hTchoice k).choose_spec.1
  have hTsmall : ∀ k : ℕ,
      M * (T k : ℝ) * Real.exp (-((δ k) ^ 2 / 10) * (T k : ℝ)) < 1 / 1000000 :=
    fun k => (hTchoice k).choose_spec.2
  have hTkposR : ∀ k : ℕ, 0 < (T k : ℝ) := by
    intro k
    have hk : (1 : ℝ) ≤ (T k : ℝ) := by exact_mod_cast hT1 k
    exact lt_of_lt_of_le (by norm_num) hk
  have hTkne : ∀ k : ℕ, (T k : ℝ) ≠ 0 := fun k => ne_of_gt (hTkposR k)
  let γ : ℕ → ℝ := fun k => Real.sqrt (5 / (T k : ℝ))
  have hγpos : ∀ k : ℕ, 0 < γ k := by
    intro k
    dsimp [γ]
    exact Real.sqrt_pos.2 (div_pos (by norm_num) (hTkposR k))
  have hγ2 : ∀ k : ℕ, γ k ^ 2 = 5 / (T k : ℝ) := by
    intro k
    dsimp [γ]
    rw [Real.sq_sqrt]
    positivity
  have hγT : ∀ k : ℕ, γ k ^ 2 * (T k : ℝ) = 5 := by
    intro k
    rw [hγ2 k]
    field_simp [hTkne k]
  have hKge : ∀ k : ℕ, 5 ≤ γ k ^ 2 * (T k : ℝ) := by
    intro k
    rw [hγT k]
  have hKle : ∀ k : ℕ, γ k ^ 2 * (T k : ℝ) ≤ 6 := by
    intro k
    rw [hγT k]
    norm_num
  have hexp : ∀ k : ℕ,
      Real.exp (-(δ k ^ 2) / (2 * γ k ^ 2)) =
        Real.exp (-((δ k) ^ 2 / 10) * (T k : ℝ)) := by
    intro k
    refine congrArg Real.exp ?_
    rw [hγ2 k]
    field_simp [hTkne k]
    ring
  have hsmallk : ∀ k : ℕ,
      2 * (T k : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) *
        Real.exp (-(δ k ^ 2) / (2 * γ k ^ 2)) ≤ 1 / 1000000 := by
    intro k
    have h := hTsmall k
    have hEq : 2 * (T k : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) *
          Real.exp (-(δ k ^ 2) / (2 * γ k ^ 2))
        = M * (T k : ℝ) * Real.exp (-((δ k) ^ 2 / 10) * (T k : ℝ)) := by
      rw [hexp k]
      dsimp [M]
      ring
    rw [hEq]
    exact le_of_lt h
  have hmain : ∀ k : ℕ, ∃ x : Vec n,
      (∀ i : Fin n, |x i| ≤ 1) ∧
      (∀ j : ι, |vin (x - x0) (v j)| ≤ c j * ‖v j‖) ∧
      ((n : ℝ) / 2 ≤ (frozenVars (δ k) x).card) := by
    intro k
    exact eps_coloring (n := n) (T := T k) (δ := δ k) (γ := γ k) x0 v c
      (hγpos k) (hT1 k) hn (hKge k) (hKle k) (hδpos k) (hδle k) (hsmallk k) hx0 hc hne hsum
  refine ⟨fun k => (hmain k).choose, ?_, ?_, ?_⟩
  · intro k i
    exact ((hmain k).choose_spec).1 i
  · intro k j
    exact ((hmain k).choose_spec).2.1 j
  · intro k
    simpa [δ] using ((hmain k).choose_spec).2.2

end Discrepancy

end Submission
