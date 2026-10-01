import Mathlib
import Submission.Work.LinnikAreas.CrudeWideDefs
import Submission.Work.LinnikAreas.JMAuxSh.ShAux

namespace Work.LinnikAreas

/-- **The per-cell comparison against the two-branch `cellBoundJMcw`.**  This is
`Work.LinnikAreas.JMAuxSh.CellMultLeBoundJMsh` with the middle branch deleted: the crude
non-principal input `hfamJ` (coefficient `24/5 + 1/1000`, valid on the whole range
`σ ≥ 1 - 1021/5000`) now covers *both* `(m+1) ≤ L/5` and `L/5 < (m+1) ≤ (1021/5000)L`, and
everything above `(1021/5000)L` is the σ-blind count `Work.LinnikAreas.finset_sum_le_trivial`
at the scaled height `2^k/L`.  Proof: copy the proof of `CellMultLeBoundJMsh`, branch 1 calling
`Work.LinnikAreas.JMAuxSh.finsetSumLeFamGeNP` at `σlo = 1 - 1021/5000`, `σhi = 1`,
`A = 24/5 + 1/1000`, and the else case calling `Work.LinnikAreas.finset_sum_le_trivial` at
`T = 2^k/L` (as in branch 3 of the reference). -/
lemma CellMultLeBoundJMcw {q : ℕ} [NeZero q] (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    {CJ c0 : ℝ} (hCJ : 0 < CJ) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ (((24:ℝ)/5 + 1/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (hS : ∀ z ∈ S, z.1 ≠ 1 ∧ Work.LinnikContract.zeroMult z.1 z.2 ≠ 0) (m k : ℕ) :
    Work.LinnikAreas.cellMult L S m k ≤ Work.LinnikAreas.cellBoundJMcw q CJ c0 L m k := by
  classical
  rw [Work.LinnikAreas.cellMult, Work.LinnikAreas.cellBoundJMcw]
  set σ : ℝ := 1 - ((m:ℝ)+1)/L with hσdef
  have hσ1 : σ ≤ 1 := by
    rw [hσdef]
    have h0 : (0:ℝ) ≤ ((m:ℝ)+1)/L := div_nonneg (by positivity) hLp.le
    linarith
  have hT1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hT0 : (0:ℝ) ≤ (2:ℝ)^k := pow_nonneg (by norm_num) k
  set S' : Finset (DirichletCharacter ℂ q × ℂ) :=
    S.filter (fun z => Work.LinnikAreas.farM L z = m ∧ Work.LinnikAreas.farY L z ≤ (2:ℝ)^k)
  have h1 : ∀ z ∈ S', z.1 ≠ 1 := fun z hz => (hS z (Finset.mem_filter.mp hz).1).1
  have hreS : ∀ z ∈ S', σ ≤ z.2.re := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hmlt : (1 - z.2.re) * L < (m:ℝ) + 1 := by
      have hh : (1 - z.2.re) * L < ((Work.LinnikAreas.farM L z : ℕ) : ℝ) + 1 := by
        simp only [Work.LinnikAreas.farM]; exact Nat.lt_floor_add_one _
      rw [hzm] at hh; linarith
    have h2 : 1 - z.2.re < ((m:ℝ)+1)/L := by rw [lt_div_iff₀ hLp]; linarith
    rw [hσdef]; linarith
  have hre0 : ∀ z ∈ S', 0 ≤ z.2.re := by
    intro z hz
    exact le_of_lt (Work.LinnikAreas.zeroMult_re z.1 (hS z (Finset.mem_filter.mp hz).1).1
      (hS z (Finset.mem_filter.mp hz).1).2).1
  have himS : ∀ z ∈ S', |z.2.im| ≤ (2:ℝ)^k := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hz' : Work.LinnikAreas.farY L z = |z.2.im| * L := rfl
    rw [hz'] at hzy
    have h3 : |z.2.im| ≤ (2:ℝ)^k / L := by rw [le_div_iff₀ hLp]; linarith
    have h4 : (2:ℝ)^k / L ≤ (2:ℝ)^k := by
      rw [div_le_iff₀ hLp]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k, hL1]
    linarith
  have himS' : ∀ z ∈ S', |z.2.im| ≤ (2:ℝ)^k / L := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hz' : Work.LinnikAreas.farY L z = |z.2.im| * L := rfl
    rw [hz'] at hzy
    rw [le_div_iff₀ hLp]; linarith
  by_cases hM : ((m:ℝ) + 1) ≤ (1021/5000)*L
  · rw [if_pos hM]
    have hσ0 : (1:ℝ) - 1021/5000 ≤ σ := by
      rw [hσdef]
      have h1' : ((m:ℝ)+1)/L ≤ 1021/5000 := by rw [div_le_iff₀ hLp]; linarith
      linarith
    have hmain := Work.LinnikAreas.JMAuxSh.finsetSumLeFamGeNP (q := q) CJ (24/5 + 1/1000)
      (1 - 1021/5000) 1 hfamJ
      (by norm_num : (0:ℝ) ≤ 1 - 1021/5000) (by norm_num : (1:ℝ) ≤ 1)
      hσ0 hσ1 hT1 h1 hreS himS
    have heq : (24/5 + 1/1000 : ℝ) * (1 - σ) = (24/5 + 1/1000) * (((m:ℝ)+1)/L) := by
      rw [hσdef]; ring
    rw [heq] at hmain
    exact hmain
  · rw [if_neg hM]
    have hTs : (0:ℝ) ≤ (2:ℝ)^k / L := by positivity
    exact Work.LinnikAreas.finset_sum_le_trivial (q := q) hc0 hball (T := (2:ℝ)^k / L) hTs
      h1 hre0 himS'

end Work.LinnikAreas
