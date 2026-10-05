import Mathlib
import Submission.Work.RPB.B5.noL_defs
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPV.Defs
import Submission.Work.RPB.Defs

/-!
# B5: the `σ`-jets of the phase constant `A0`

`Work.RPB.B5.A0` is the constant of integration of the phase of the no-`L` collar.  It is designed
so that its `σ`-jets at `σ = 0` reproduce the `σ`-jets of the chart phase `σ ↦ (W τ 0 (ρh τ 0 σ)).1.2`:
writing

`A0 W ρh δ k τ σ = (phc δ k σ + π/2 + 2πk) + ∑_{j<9} (cj τ j - cj 0 j) · (σ^j/j!) · jbump δ σ`

and observing that `phc δ k σ = 0` and `jbump δ σ = 1` for `σ ≤ 0`, the difference between `A0` and
the truncated Taylor polynomial `(π/2 + 2πk) + ∑_{j<9} (cj τ j - cj 0 j) σ^j/j!` is a `C^8` function
vanishing on `(-∞,0]`, hence is flat at `0` to order `8` (`chartJets_oneSided`).  The jets of the
Taylor polynomial are the coefficients themselves.

The main statement `noL_A0_jets` then follows by subtracting the chart phase and using that the
`τ = 0` chart phase is constant `π/2 + 2πk` on `(-δ,0)` (`hphase0`), which again forces its jets to
vanish (`cj W ρh 0 j = 0` for `j ≥ 1` and `cj W ρh 0 0 = π/2 + 2πk`).
-/

namespace Work.RPB.B5

open scoped ContDiff Topology

/-- The `j`-th iterated derivative at `0` of a truncated Taylor polynomial
`σ ↦ ∑_{i ≤ N} b i · σ^i / i!` is the coefficient `b j`, for `j ≤ N`. -/
lemma iteratedDeriv_taylorSum (b : ℕ → ℝ) (N j : ℕ) (hj : j ≤ N) :
    iteratedDeriv j (fun σ : ℝ => ∑ i ∈ Finset.range (N+1),
      b i * (σ^i / (Nat.factorial i : ℝ))) 0 = b j := by
  have hfun : (fun σ : ℝ => ∑ i ∈ Finset.range (N+1), b i * (σ^i / (Nat.factorial i : ℝ)))
      = (∑ i ∈ Finset.range (N+1), fun σ : ℝ => b i * (σ^i / (Nat.factorial i : ℝ))) := by
    funext σ; simp
  rw [hfun, iteratedDeriv_sum]
  · have hterm : ∀ i, iteratedDeriv j (fun σ : ℝ => b i * (σ^i / (Nat.factorial i : ℝ))) 0
        = if i = j then b i else 0 := by
      intro i
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
      by_cases h : i = j
      · rw [ite_eq_left h.symm, ite_eq_left h]
        rw [div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)), mul_one]
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
        simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq']
    rw [ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
  · intro i hi
    fun_prop

/-- `σ ↦ A0 W ρh δ k τ σ` is `C^n`, for every `n` and at every point. -/
lemma contDiffAt_A0_sigma_aux (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ₀ : ℝ) (n : ℕ) :
    ContDiffAt ℝ n (fun σ : ℝ => A0 W ρh δ k τ σ) σ₀ := by
  simp only [A0]
  refine ContDiffAt.add ?_ ?_
  · simp only [phc, stp]
    fun_prop
  · refine ContDiffAt.sum (fun i hi => ?_)
    simp only [jbump, stp]
    fun_prop

/-- The `σ`-jets of `A0` at `σ = 0`, up to order `8`: they are the constant `π/2 + 2πk` (only in
order `0`) plus the differences `cj W ρh τ j - cj W ρh 0 j` of the chart-phase jets. -/
lemma noL_A0_jets_aux (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (k : ℤ) (τ : ℝ) (j : ℕ) (hj : j ≤ 8) :
    iteratedDeriv j (fun σ : ℝ => A0 W ρh δ k τ σ) 0
      = (if j = 0 then (Real.pi/2 + 2*Real.pi*k) else 0)
        + (cj W ρh τ j - cj W ρh 0 j) := by
  -- ## the decomposition of `A0` as a Taylor polynomial plus a flat remainder
  set C : ℝ → ℝ := fun _ => (Real.pi/2 + 2*Real.pi*k) with hC
  set P : ℝ → ℝ := fun σ => ∑ i ∈ Finset.range 9,
      (cj W ρh τ i - cj W ρh 0 i) * (σ^i / (Nat.factorial i : ℝ)) with hP
  set T : ℝ → ℝ := C + P with hT
  set Φ : ℝ → ℝ := A0 W ρh δ k τ - T with hΦ
  have hP_cd : ∀ n : ℕ, ContDiffAt ℝ n P 0 := by
    intro n
    rw [hP]
    refine ContDiffAt.sum (fun i hi => ?_)
    fun_prop
  have hT_cd : ∀ n : ℕ, ContDiffAt ℝ n T 0 := by
    intro n
    rw [hT]
    exact ContDiffAt.add (by rw [hC]; fun_prop) (hP_cd n)
  have hΦ_cd : ∀ n : ℕ, ContDiffAt ℝ n Φ 0 := by
    intro n
    rw [hΦ]
    exact (contDiffAt_A0_sigma_aux W ρh δ k τ 0 n).sub (hT_cd n)
  -- ## `Φ` vanishes on the left half-line
  have hΦ_zero : ∀ σ : ℝ, σ ≤ 0 → Φ σ = 0 := by
    intro σ hσ
    have hphc : phc δ k σ = 0 := by
      rw [phc, stp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)), mul_zero]
    have hjb : jbump δ σ = 1 := by
      rw [jbump, stp_zero (div_nonpos_of_nonpos_of_nonneg hσ (le_of_lt hδ)), sub_zero]
    have hA0u : A0 W ρh δ k τ σ = (Real.pi/2 + 2*Real.pi*k) + P σ := by
      rw [hP]
      simp only [A0, hphc, hjb, mul_one, zero_add]
    simp only [hΦ, hT, hC, Pi.sub_apply, Pi.add_apply]
    rw [hA0u]
    ring
  -- ## hence `Φ` is flat at `0` to order `8`
  have hΦ_flat : ∀ j' : ℕ, j' ≤ 8 → iteratedDeriv j' Φ 0 = 0 := by
    intro j' hj'
    have hjet := chartJets_oneSided (E := ℝ) (f := Φ) (g := fun _ : ℝ => (0:ℝ))
        (x₀ := 0) (δ := δ) hδ (n := 8) (hΦ_cd 8) contDiffAt_const
        (fun x hx => hΦ_zero x (le_of_lt hx.2)) hj'
    rw [hjet, iteratedDeriv_const]
    split <;> rfl
  -- ## the jets of `A0` are those of `T`
  have hA0_eq : A0 W ρh δ k τ = T + Φ := by
    rw [hΦ]
    abel
  have hP_jets : iteratedDeriv j P 0 = cj W ρh τ j - cj W ρh 0 j := by
    rw [hP]
    exact iteratedDeriv_taylorSum (fun i => cj W ρh τ i - cj W ρh 0 i) 8 j hj
  have hT_jets : iteratedDeriv j T 0
      = (if j = 0 then (Real.pi/2 + 2*Real.pi*k) else 0)
        + (cj W ρh τ j - cj W ρh 0 j) := by
    rw [hT, iteratedDeriv_add (by rw [hC]; fun_prop) (hP_cd j), hC, iteratedDeriv_const,
      hP_jets]
  rw [hA0_eq, iteratedDeriv_add (hT_cd j) (hΦ_cd j), hT_jets, hΦ_flat j hj, add_zero]

end Work.RPB.B5
