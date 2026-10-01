import Mathlib

namespace Work.LinnikAreas

/-- A finite family of nonnegative weights `m` supported on indices `i ∈ S` whose "heights" `lam i` are
at most `L`, and whose partial weight below every cutoff `t ∈ [Λ, L]` is at most `D * lam₁ * exp (c t)`:
then the partial weight below the cutoff `Λ + k + 1` (which may lie above `L`, in which case the whole
weight is counted) is at most `D * lam₁ * exp (c * (Λ + k + 1))`. -/
lemma count_filter_le_exp {ι : Type*} (S : Finset ι) (m lam : ι → ℝ)
    {D lam₁ c Λ L : ℝ} (hc0 : 0 ≤ c)
    (hm : ∀ i ∈ S, 0 ≤ m i) (hlamL : ∀ i ∈ S, lam i ≤ L) (hΛL : Λ ≤ L)
    (hcount : ∀ t : ℝ, Λ ≤ t → t ≤ L →
      (∑ i ∈ S.filter (fun i => lam i ≤ t), m i) ≤ D * lam₁ * Real.exp (c * t))
    (k : ℕ) :
    (∑ i ∈ S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1), m i)
      ≤ D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)) := by
  -- The target cutoff `T = Λ + k + 1` lies at or above `Λ`.
  have hTΛ : Λ ≤ Λ + (k:ℝ) + 1 := by
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  -- Nonnegativity of the partial weight at the cutoff `Λ` forces `D * lam₁ ≥ 0`.
  have hDlam : 0 ≤ D * lam₁ := by
    have hsum0 : 0 ≤ ∑ i ∈ S.filter (fun i => lam i ≤ Λ), m i :=
      Finset.sum_nonneg (fun i hi => hm i (Finset.mem_of_mem_filter i hi))
    have hb := hcount Λ le_rfl hΛL
    have hexp : 0 < Real.exp (c * Λ) := Real.exp_pos _
    exact nonneg_of_mul_nonneg_left (le_trans hsum0 hb) hexp
  by_cases hTL : Λ + (k:ℝ) + 1 ≤ L
  · -- The cutoff falls inside `[Λ, L]`: apply the hypothesis directly.
    exact hcount _ hTΛ hTL
  · -- The cutoff lies above `L`: the whole of `S` is counted, and we use the bound at `L`.
    rw [not_le] at hTL
    have hLT : L ≤ Λ + (k:ℝ) + 1 := le_of_lt hTL
    have hfiltT : S.filter (fun i => lam i ≤ Λ + (k:ℝ) + 1) = S :=
      Finset.filter_true_of_mem (fun i hi => le_trans (hlamL i hi) hLT)
    have hfiltL : S.filter (fun i => lam i ≤ L) = S :=
      Finset.filter_true_of_mem (fun i hi => hlamL i hi)
    have hsumL := hcount L hΛL le_rfl
    rw [hfiltL] at hsumL
    have hexpmono : Real.exp (c * L) ≤ Real.exp (c * (Λ + (k:ℝ) + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith [hc0, hLT])
    have hstep : D * lam₁ * Real.exp (c * L) ≤ D * lam₁ * Real.exp (c * (Λ + (k:ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hexpmono hDlam
    rw [hfiltT]
    linarith

end Work.LinnikAreas
