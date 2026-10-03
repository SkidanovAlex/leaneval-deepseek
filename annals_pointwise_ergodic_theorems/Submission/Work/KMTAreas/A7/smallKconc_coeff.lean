import Mathlib
import Submission.Work.KMTAreas.A7.SmallModApprox

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **The coefficients of the exact-height Ionescu--Wainger kernel `tmKernel`.**

For an integrable symbol `φ`, the `j`-th Fourier coefficient of the exact-height IW kernel
`tmKernel ρ l φ = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ))` factors as the arithmetic
character sum `∑_{α ∈ (ℚ/ℤ)_l} e(-jα)` times the continuous Fourier transform `cw φ j`.  This is
`Work.KMTPlan.A6.IwKernelArithChar` specialised to the exact-height frequency set `diffFreqs ρ l`. -/
lemma tmKernel_coeff {φ : ℝ → ℂ} (hφ : Integrable φ) (ρ : ℝ) (l : ℕ) (j : ℤ) :
    tmKernel ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j := by
  simpa only [tmKernel] using
    Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l) hφ j

/-- **The composition of the halved-average kernel with two convolution kernels.**

The bilinear kernel `kernComp (khalf m P) κ κ'` has the `b`-sum collapsing to the single value
`b' = b - P.eval (a - a')` (because `khalf m P x y = 0` unless `y = P.eval x`), and then the
`a`-sum to the finite set of shifts `a - n`, `n ∈ Ioc (m/2) m`, on which `khalf` equals `m⁻¹`. -/
lemma kernComp_khalf (m : ℕ) (P : ℤ[X]) (κ κ' : ℤ → ℂ) (a b : ℤ) :
    kernComp (khalf m P) κ κ' a b
      = ((m : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (m / 2) m,
          κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ)) := by
  rw [kernComp]
  -- collapse the inner `b`-sum to the single shift `b' = b - P.eval (a - a')`
  have hinner : ∀ a' : ℤ,
      (∑' b' : ℤ, khalf m P (a - a') (b - b') * κ a' * κ' b')
        = khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')) := by
    intro a'
    refine (tsum_eq_single (b - P.eval (a - a')) ?_).trans ?_
    · intro b' hb'
      have hne : ¬ (b - b' = P.eval (a - a')) := fun h => hb' (by omega)
      rw [khalf, if_neg (fun hc => hne hc.2.2)]
      ring
    · have h : b - (b - P.eval (a - a')) = P.eval (a - a') := by omega
      rw [h]
  simp_rw [hinner]
  -- reindex the outer sum by the shift `z = a - a'`
  have hreindex :
      (∑' a' : ℤ, khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')))
        = ∑' z : ℤ, khalf m P z (P.eval z) * κ (a - z) * κ' (b - P.eval z) := by
    rw [(Equiv.tsum_eq (Equiv.subLeft a)
      (fun a' : ℤ => khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')))).symm]
    refine tsum_congr (fun z => ?_)
    have h : a - (a - z) = z := by omega
    simp only [Equiv.subLeft_apply, h]
  rw [hreindex]
  -- the resulting family is supported on `{a - n : n ∈ Ioc (m/2) m}`
  rw [tsum_eq_sum (s := (Finset.Ioc (m / 2) m).map ⟨(↑· : ℕ → ℤ), Nat.cast_injective⟩)]
  · rw [Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' : m / 2 < n ∧ n ≤ m := Finset.mem_Ioc.mp hn
    have hk : khalf m P (n : ℤ) (P.eval (n : ℤ)) = ((m : ℂ))⁻¹ := by
      have hc : (↑m : ℤ) / 2 < (↑n : ℤ) ∧ (↑n : ℤ) ≤ (↑m : ℤ)
          ∧ P.eval (↑n) = P.eval (↑n) := by
        refine ⟨?_, ?_, rfl⟩
        · have h1 : (↑m : ℤ) / 2 = ((m / 2 : ℕ) : ℤ) := by
            rw [eq_comm, Int.natCast_div]; norm_num
          rw [h1]; exact_mod_cast hn'.1
        · exact_mod_cast hn'.2
      rw [khalf, if_pos hc]
    change khalf m P (n : ℤ) (P.eval (n : ℤ)) * κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ))
        = ((m : ℂ))⁻¹ * (κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ)))
    rw [hk]
    ring
  · intro z hz
    by_cases h : (↑m : ℤ) / 2 < z ∧ z ≤ (↑m : ℤ)
    · exfalso
      apply hz
      refine Finset.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
      · rw [Finset.mem_Ioc, Int.lt_toNat, Int.natCast_div, Int.toNat_le]
        exact h
      · have h0 : (0 : ℤ) ≤ z :=
          le_of_lt (lt_of_le_of_lt (Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)) h.1)
        exact Int.toNat_of_nonneg h0
    · rw [khalf, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
      ring

theorem smallKconc_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ N a b
      = ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
          ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-(a - (m : ℤ))) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiN N k₁) (a - (m : ℤ)))
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-(b - P.eval (m : ℤ))) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ))) := by
  rw [smallKconc, kernComp_khalf]
  refine congrArg (fun z : ℂ => ((N : ℂ))⁻¹ * z) ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h1 : tmKernel ρ l₁ (varphiN N k₁) (a - (m : ℤ))
      = (∑ α ∈ diffFreqs ρ l₁, fourier (T := 1) (-(a - (m : ℤ))) α)
          * cw (varphiN N k₁) (a - (m : ℤ)) :=
    tmKernel_coeff (integrable_varphiN N k₁) ρ l₁ (a - (m : ℤ))
  have h2 : tmKernel ρ l₂ (varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ))
      = (∑ α ∈ diffFreqs ρ l₂, fourier (T := 1) (-(b - P.eval (m : ℤ))) α)
          * cw (varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ)) :=
    tmKernel_coeff (integrable_varphitildeN_aux P.natDegree N k₂) ρ l₂ (b - P.eval (m : ℤ))
  rw [h1, h2]

end

end Work.KMTAreas.A7
