import Mathlib
import Submission.Work.BW.transversal_gen_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- **Cancellation of the zero estimate's inequality (`ε = true`, reduced package).** Reading
the zero estimate's inequality at `L = j` and step `m`, and comparing with a step `i ≥ m`, one
dominates `(Sq i + 1) · C(Tq i + j, j) · |Δ_J|` by `(N+1).descFactorial ρ · ∏_{i∈J} ⌊δ_{i+1}⌋₊`. -/
lemma ze_cancel_true_gen {N r : ℕ} (D : ZEDataG N r) (ρ i j : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hL : L = j) (hmi : m ≤ i) (hiN : i ≤ N) (hρN : ρ ≤ N)
    (hcard : D.Sq m + 1 ≤ cardMod true M D.ℓ (D.Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((D.Tq m + L).choose L : ℕ) : ℝ) *
          (cardMod true M D.ℓ (D.Sq m) : ℝ) *
        ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ))
    (J : Finset (Fin N)) (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)| ≤
      ((N + 1).descFactorial ρ : ℝ) * ∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
  classical
  have hCr : ((D.Tq i + j).choose j : ℝ) ≤ ((D.Tq m + L).choose L : ℝ) := by
    have h1 : D.Tq i ≤ D.Tq m := anti_of_step D.hTa hmi hiN
    have h2 : (D.Tq i + j).choose j ≤ (D.Tq m + L).choose L := by
      rw [hL]
      exact Nat.choose_le_choose j (Nat.add_le_add_right h1 j)
    exact_mod_cast h2
  have hS : (D.Sq i : ℝ) + 1 ≤ (D.Sq m : ℝ) + 1 := by
    have h1 : D.Sq i ≤ D.Sq m := anti_of_step D.hSa hmi hiN
    exact_mod_cast Nat.succ_le_succ h1
  have hze := hineq J hJ hΔ
  try simp only [mul_one, one_mul] at hze
  have hPCpos : (0 : ℝ) < ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊D.δ i.succ⌋₊ := D.hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊D.δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊D.δ i⌋₊ : ℕ) : ℝ) =
      ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) J]
    ring
  have hfact : ((N + 1).factorial : ℝ) =
      ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ) (by omega)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hstep : (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
      (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      ≤ ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
    calc (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
          (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
            (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
        ≤ (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
            (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_rightℝ (mul_le_mulℝ hS hCr (by positivity) (by positivity))
          positivity
      _ ≤ (cardMod true M D.ℓ (D.Sq m) : ℝ) *
            ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - ρ).factorial : ℝ) *
              |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) := by
          have h1 : (D.Sq m : ℝ) + 1 ≤
              (cardMod true M D.ℓ (D.Sq m) : ℝ) := by
            exact_mod_cast hcard
          calc (((D.Sq m : ℝ) + 1) * ((D.Tq m + L).choose L : ℝ)) *
                (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
              = ((D.Sq m : ℝ) + 1) * (((D.Tq m + L).choose L : ℝ) *
                  ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                  (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
            _ ≤ (cardMod true M D.ℓ (D.Sq m) : ℝ) *
                  ((((D.Tq m + L).choose L : ℝ) * ((N + 1 - ρ).factorial : ℝ) *
                    |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
                    (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_rightℝ h1 (by positivity)
      _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := by
          calc _ = (((D.Tq m + L).choose L : ℕ) : ℝ) *
                (cardMod true M D.ℓ (D.Sq m) : ℝ) *
                ((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                ((⌊D.δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ) := by ring
            _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊D.δ i⌋₊ : ℕ) : ℝ) := hze
      _ = ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
            (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
              (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by
          rw [hfact, hprod] <;> try ring
  have hdivpos : (0 : ℝ) < ((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
      (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) := by
    refine mul_pos (mul_pos ?_ ?_) hPCpos
    · exact_mod_cast Nat.factorial_pos _
    · exact_mod_cast (by have h := D.hδ1 0; omega : (0 : ℕ) < ⌊D.δ 0⌋₊)
  refine le_of_mul_le_mul_right ?_ hdivpos
  calc ((((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)|) *
        (((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)))
      = (((D.Sq i : ℝ) + 1) * ((D.Tq i + j).choose j : ℝ)) *
        (((N + 1 - ρ).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
    _ ≤ ((N + 1 - ρ).factorial : ℝ) * ((N + 1).descFactorial ρ : ℝ) *
        (((⌊D.δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := hstep
    _ = (((N + 1).descFactorial ρ : ℝ) * (∏ i ∈ J, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) *
        (((N + 1 - ρ).factorial : ℝ) * ((⌊D.δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊D.δ i.succ⌋₊ : ℕ) : ℝ))) := by ring

end Work.BW
