import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.multiplicity_engine
import Submission.Work.BW.zeroest_defs
import Submission.Work.BW.transversal_true_gen
import Submission.Work.BW.transversal_true_one_gen
import Submission.Work.BW.transversal_false_gen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem transversal_exclusion_spec {N r : ℕ} (hr : 2 ≤ r) (hNr : N < r)
    (δ : Fin (N + 1) → ℝ) (hδnn : ∀ i, 0 ≤ δ i) (hδ0 : 1 ≤ δ 0) (hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊)
    (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m)
    (hE0 : ∀ j : Fin N, ((r : ℝ) + 1) * δ j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (N + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (θ : Fin N → ℂ)
    (ε : Bool) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ) (m : ℕ)
    (hρN : ρ ≤ N) (hM : PrimSys M) (hε : ¬ (ε = true ∧ ρ = 0))
    (hm : m + 1 ≤ (if ε then 0 else 1) + ρ)
    (hcard : (ε = false → Sq m + 1 ≤ cardMod false M θ (Sq m)) ∧
             (2 ≤ ρ → Sq m + 1 ≤ cardMod true M θ (Sq m)) ∧
             (1 ≤ cardMod true M θ (Sq m)))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((Tq m + ((if ε then 0 else 1) + ρ)).choose ((if ε then 0 else 1) + ρ) : ℕ) : ℝ) *
          (cardMod ε M θ (Sq m) : ℝ) *
        ((N + 1 - ((if ε then 0 else 1) + ρ)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        (if ε then ((⌊δ 0⌋₊ : ℕ) : ℝ) else 1) *
          ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ)) :
    False := by
  cases ε with
  | false =>
    have hc : Sq m + 1 ≤ cardMod false M θ (Sq m) := hcard.1 rfl
    have hm' : m + 1 ≤ 1 + ρ := by
      simpa only [Bool.false_eq_true, ↓reduceIte] using hm
    have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
        (((Tq m + (1 + ρ)).choose (1 + ρ) : ℕ) : ℝ) * (cardMod false M θ (Sq m) : ℝ) *
          ((N + 1 - (1 + ρ)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * 1 *
          ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
          ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
      intro J hJ hΔ
      simpa only [Bool.false_eq_true, ↓reduceIte] using hineq J hJ hΔ
    exact transversal_false_gen hNr δ hδnn hδ0 hδ1 Sq Tq hSa hTa hE1 θ ρ M m hρN hM hm' hc hineq'
  | true =>
    have hρ1 : 1 ≤ ρ := by
      by_contra h
      exact hε ⟨rfl, by omega⟩
    have hmρ : m + 1 ≤ ρ := by
      have h := hm
      simp only [↓reduceIte, Nat.zero_add] at h
      exact h
    by_cases hρ2 : 2 ≤ ρ
    · have hc : Sq m + 1 ≤ cardMod true M θ (Sq m) := hcard.2.1 hρ2
      have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
          (((Tq m + ρ).choose ρ : ℕ) : ℝ) * (cardMod true M θ (Sq m) : ℝ) *
            ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
            ((⌊δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
            ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
        intro J hJ hΔ
        simpa only [↓reduceIte, Nat.zero_add] using hineq J hJ hΔ
      exact transversal_true_gen hNr δ hδnn hδ1 Sq Tq hSa hTa hE1 θ ρ M m hρN hM hρ2 hmρ hc hineq'
    · have hρe : ρ = 1 := by omega
      subst hρe
      have hm1 : m + 1 ≤ 1 := hmρ
      have hc : 1 ≤ cardMod true M θ (Sq m) := hcard.2.2
      have hineq' : ∀ (J : Finset (Fin N)) (hJ : J.card = 1), minorJ M J hJ ≠ 0 →
          (((Tq m + 1).choose 1 : ℕ) : ℝ) * (cardMod true M θ (Sq m) : ℝ) *
            ((N + 1 - 1).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
            ((⌊δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
            ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
        intro J hJ hΔ
        simpa only [↓reduceIte, Nat.zero_add] using hineq J hJ hΔ
      exact transversal_true_one_gen hNr δ hδnn hδ1 Sq Tq hE0 θ M m hM hm1 hc hineq'

end Work.BW
