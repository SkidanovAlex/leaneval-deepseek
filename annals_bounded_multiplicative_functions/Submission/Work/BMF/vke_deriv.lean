import Mathlib
import Submission.Work.BMF.vke_defs
import Submission.Work.BMF.logPhase_iteratedDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **Two-sided iterated-derivative bounds for the block phase.**  Let `k ≥ 2` be even, `t > 0`,
`u > 0` and `L, M : ℕ`.  Then for every `x` with `0 < x < M+1` the `k`-th derivative of
`Work.BMF.blkPh L t u` is squeezed between its endpoint values on `(L + u, L + M + 1 + u)`:
`(t/2π)(k-1)!/(L+M+1+u)^k ≤ (blkPh L t u)^{(k)}(x) ≤ (t/2π)(k-1)!/(L+u)^k`.

Route.  `Work.BMF.logPhase_iteratedDeriv` gives, for `F(y) = -(t log(y+u))/(2π)` and `0 < x+u`,
`iteratedDeriv k F x = -(t/2π)(-1)^{k-1}(k-1)!/(x+u)^k`.  Since `blkPh L t u x = F (L + x)`
(`iteratedDeriv_comp_add_const`) and `k` is even makes `(-1)^{k-1} = -1`, we get
`(blkPh L t u)^{(k)}(x) = (t/2π)(k-1)!/(L+x+u)^k` (here `L + x + u > 0` because `L ≥ 0`, `x > 0`,
`u > 0`).  On that range `L + u < L + x + u < L + M + 1 + u`, and `y ↦ 1/y^k` is antitone on
`y > 0`. -/
theorem vke_deriv (k L M : ℕ) (t u : ℝ) (hk : 2 ≤ k) (heven : Even k) (ht : 0 < t) (hu : 0 < u) :
    ∀ x ∈ Set.Ioo (0 : ℝ) ((M : ℝ) + 1),
      (t / (2 * Real.pi)) * (((Nat.factorial (k - 1) : ℕ)) : ℝ) / ((L : ℝ) + (M : ℝ) + 1 + u) ^ k
        ≤ iteratedDeriv k (blkPh L t u) x ∧
      iteratedDeriv k (blkPh L t u) x
        ≤ (t / (2 * Real.pi)) * (((Nat.factorial (k - 1) : ℕ)) : ℝ) / ((L : ℝ) + u) ^ k := by
  intro x hx
  obtain ⟨hx0, hxM⟩ := hx
  have hk1 : 1 ≤ k := by omega
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hpos1 : (0 : ℝ) < (L : ℝ) + x + u := by linarith
  have hpos2 : (0 : ℝ) < (L : ℝ) + u := by linarith
  have hnn1 : (0 : ℝ) ≤ (L : ℝ) + x + u := hpos1.le
  have hnn2 : (0 : ℝ) ≤ (L : ℝ) + u := hpos2.le
  have hle1 : (L : ℝ) + x + u ≤ (L : ℝ) + (M : ℝ) + 1 + u := by linarith
  have hle2 : (L : ℝ) + u ≤ (L : ℝ) + x + u := by linarith
  set A : ℝ := (t / (2 * Real.pi)) * (((Nat.factorial (k - 1) : ℕ)) : ℝ) with hA
  -- For even `k`, `(-1)^{k-1} = -1`.
  have hneg : (-1 : ℝ) ^ (k - 1) = -1 := by
    have hkm : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
    have h1 : (-1 : ℝ) ^ k = 1 := heven.neg_one_pow
    calc (-1 : ℝ) ^ (k - 1) = ((-1 : ℝ) ^ (k - 1) * (-1 : ℝ)) * (-1 : ℝ) := by ring
      _ = (-1 : ℝ) ^ ((k - 1) + 1) * (-1 : ℝ) := by rw [pow_succ]
      _ = (-1 : ℝ) ^ k * (-1 : ℝ) := by rw [hkm]
      _ = -1 := by rw [h1]; ring
  -- The exact value of the `k`-th derivative of the block phase.
  have hderiv : iteratedDeriv k (blkPh L t u) x = A / ((L : ℝ) + x + u) ^ k := by
    have hblk : blkPh L t u
        = fun z : ℝ => (fun y => -(t * Real.log (y + u)) / (2 * Real.pi)) ((L : ℝ) + z) := by
      funext z
      simp only [blkPh]
    have hstep : iteratedDeriv k
          (fun z : ℝ => (fun y => -(t * Real.log (y + u)) / (2 * Real.pi)) ((L : ℝ) + z)) x
        = iteratedDeriv k (fun y => -(t * Real.log (y + u)) / (2 * Real.pi)) ((L : ℝ) + x) := by
      have h := congrFun (iteratedDeriv_comp_const_add
        (f := fun y : ℝ => -(t * Real.log (y + u)) / (2 * Real.pi)) (s := (L : ℝ)) k) x
      simpa using h
    rw [hblk, hstep, logPhase_iteratedDeriv t u k hk1 ((L : ℝ) + x) hpos1, hneg, hA]
    ring
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
  rw [hderiv]
  constructor
  · -- lower bound: `L + x + u ≤ L + M + 1 + u`
    refine div_le_div_of_nonneg_left hA0 (pow_pos hpos1 k) ?_
    exact pow_le_pow_left₀ hnn1 hle1 k
  · -- upper bound: `L + u ≤ L + x + u`
    refine div_le_div_of_nonneg_left hA0 (pow_pos hpos2 k) ?_
    exact pow_le_pow_left₀ hnn2 hle2 k

end Work.BMF
