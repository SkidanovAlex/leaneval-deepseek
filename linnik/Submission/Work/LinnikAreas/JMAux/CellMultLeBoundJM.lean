import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery

namespace Work.LinnikAreas.JMAux

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- Family count of pairs with `σ₀ ≤ σ ≤ 1`, `σ ≤ Re ρ` and `|Im ρ| ≤ T`, from a family
zero-density hypothesis that is available only on the range `σ₀ ≤ σ`. -/
lemma finset_sum_le_fam_ge {q : ℕ} [NeZero q] (C A σ₀ : ℝ)
    (hfam : ∀ σ T : ℝ, σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)))
    (hσ₀ : 0 ≤ σ₀)
    {σ T : ℝ} (hσ : σ₀ ≤ σ) (hσ1 : σ ≤ 1) (hT : 1 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.univ) (g := fun z : DirichletCharacter ℂ q × ℂ => z.1)
    (f := fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) (fun z _ => Finset.mem_univ _)
  rw [← hfib]
  refine le_trans (Finset.sum_le_sum (fun χ _ => ?_)) (hfam σ T hσ hσ1 hT)
  by_cases hχ : χ = 1
  · have hempty : S.filter (fun z => z.1 = χ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz hc
      exact h1 z hz (by rw [hc, hχ])
    rw [hempty, Finset.sum_empty]
    exact Work.LinnikAreas.zeroCountIn_nonneg χ σ T
  · exact Work.LinnikAreas.fiber_sum_le_zeroCountIn χ hχ (by linarith) (by linarith) _
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hre z (Finset.mem_filter.mp hz).1)
      (fun z hz => him z (Finset.mem_filter.mp hz).1)

lemma CellMultLeBoundJM {q : ℕ} [NeZero q] (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    {CJ CM c0 : ℝ} (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)))
    (hfamM : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2451/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (hS : ∀ z ∈ S, z.1 ≠ 1 ∧ Work.LinnikContract.zeroMult z.1 z.2 ≠ 0) (m k : ℕ) :
    Work.LinnikAreas.cellMult L S m k ≤ Work.LinnikAreas.cellBoundJM q CJ CM c0 L m k := by
  classical
  rw [Work.LinnikAreas.cellMult, Work.LinnikAreas.cellBoundJM]
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
      rw [div_le_iff₀ hLp]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
    linarith
  by_cases hJ : ((m:ℝ)+1) ≤ L/5
  · rw [if_pos hJ]
    have hσ45 : (4:ℝ)/5 ≤ σ := by
      rw [hσdef]
      have h1' : ((m:ℝ)+1)/L ≤ 1/5 := by rw [div_le_iff₀ hLp]; linarith
      linarith
    have hmain := finset_sum_le_fam_ge (q := q) CJ (2+1/1000) (4/5) hfamJ
      (by norm_num : (0:ℝ) ≤ 4/5) hσ45 hσ1 hT1 h1 hreS himS
    have heq : (2 + 1/1000 : ℝ) * (1 - σ) = (2 + 1/1000) * (((m:ℝ)+1)/L) := by
      rw [hσdef]; ring
    rw [heq] at hmain
    exact hmain
  · rw [if_neg hJ]
    by_cases hM : ((m:ℝ)+1) ≤ (5/12)*L
    · rw [if_pos hM]
      have hσ0 : 0 ≤ σ := by
        rw [hσdef]
        have h1' : ((m:ℝ)+1)/L ≤ 5/12 := by rw [div_le_iff₀ hLp]; linarith
        linarith
      have hmain := finset_sum_le_fam_ge (q := q) CM (2451/1000) 0 hfamM
        (le_refl (0:ℝ)) hσ0 hσ1 hT1 h1 hreS himS
      have heq : (2451/1000 : ℝ) * (1 - σ) = (2451/1000) * (((m:ℝ)+1)/L) := by
        rw [hσdef]; ring
      rw [heq] at hmain
      exact hmain
    · rw [if_neg hM]
      exact Work.LinnikAreas.finset_sum_le_trivial (q := q) hc0 hball (T := (2:ℝ)^k) hT0
        h1 hre0 himS

end Work.LinnikAreas.JMAux
