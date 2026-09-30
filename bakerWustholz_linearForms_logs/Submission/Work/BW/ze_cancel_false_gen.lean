import Mathlib
import Submission.Work.BW.multiplicity_engine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Cancellation of the zero estimate's inequality, `ε = false`, general `δ`, `Sq`, `Tq`, `θ`.**
This is `ze_cancel_false` with the `ZEData` fields unpacked into explicit hypotheses, so that it
can be instantiated with data (`N`, `δ`, `Sq`, `Tq`, `θ = exp ∘ ℓ`) that is not bundled in a
`ZEData`. If the zero estimate's inequality is read at `L = j` and step `m ≥ i`, then it dominates

`(Sq i + 1) · C(Tq i + j, j) · |Δ_J| ≤ (N+1).descFactorial (ρ+1) · ⌊δ 0⌋ · ∏_{i∈J} ⌊δ_{i+1}⌋`.

for every `J` with non-vanishing minor. -/
lemma ze_cancel_false_gen {N : ℕ}
    (δ : Fin (N + 1) → ℝ) (hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊)
    (Sq Tq : ℕ → ℕ) (hSa : ∀ m, m < N → Sq (m + 1) ≤ Sq m)
    (hTa : ∀ m, m < N → Tq (m + 1) ≤ Tq m)
    (θ : Fin N → ℂ) (ρ i j : ℕ) (M : Fin ρ → Fin N → ℤ) (m L : ℕ)
    (hL : L = j) (hmi : m ≤ i) (hiN : i ≤ N) (hρN : ρ ≤ N)
    (hcard : Sq m + 1 ≤ cardMod false M θ (Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = ρ), minorJ M J hJ ≠ 0 →
      (((Tq m + L).choose L : ℕ) : ℝ) * (cardMod false M θ (Sq m) : ℝ) *
        ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| * 1 *
        ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ))
    (J : Finset (Fin N)) (hJ : J.card = ρ) (hΔ : minorJ M J hJ ≠ 0) :
    (((Sq i : ℝ) + 1) * ((Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)| ≤
      ((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
        ∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := by
  classical
  have hCr : ((Tq i + j).choose j : ℝ) ≤ ((Tq m + L).choose L : ℝ) := by
    have h1 : Tq i ≤ Tq m := anti_of_step hTa hmi hiN
    have h2 : (Tq i + j).choose j ≤ (Tq m + L).choose L := by
      rw [hL]
      exact Nat.choose_le_choose j (Nat.add_le_add_right h1 j)
    exact_mod_cast h2
  have hS : (Sq i : ℝ) + 1 ≤ (Sq m : ℝ) + 1 := by
    have h1 : Sq i ≤ Sq m := anti_of_step hSa hmi hiN
    exact_mod_cast Nat.succ_le_succ h1
  have hze := hineq J hJ hΔ
  try simp only [mul_one, one_mul] at hze
  have hPCpos : (0 : ℝ) < ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊δ i.succ⌋₊ := hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊δ i⌋₊ : ℕ) : ℝ) =
      ((⌊δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) J]
    ring
  have hfact : ((N + 1).factorial : ℝ) =
      ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) := by
    have h := factorial_eq_factorial_mul_descFactorial (n := N + 1) (k := ρ + 1) (by omega)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hstep : (((Sq i : ℝ) + 1) * ((Tq i + j).choose j : ℝ)) *
      (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))
      ≤ ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
        (((⌊δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by
    calc (((Sq i : ℝ) + 1) * ((Tq i + j).choose j : ℝ)) *
          (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
            (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))
        ≤ (((Sq m : ℝ) + 1) * ((Tq m + L).choose L : ℝ)) *
            (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
              (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_rightℝ (mul_le_mulℝ hS hCr (by positivity) (by positivity))
          positivity
      _ ≤ (cardMod false M θ (Sq m) : ℝ) *
            ((((Tq m + L).choose L : ℝ) * ((N + 1 - (ρ + 1)).factorial : ℝ) *
              |(minorJ M J hJ : ℝ)| *
              (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))) := by
          have h1 : (Sq m : ℝ) + 1 ≤
              (cardMod false M θ (Sq m) : ℝ) := by
            exact_mod_cast hcard
          calc (((Sq m : ℝ) + 1) * ((Tq m + L).choose L : ℝ)) *
                (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                  (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))
              = ((Sq m : ℝ) + 1) * (((Tq m + L).choose L : ℝ) *
                  ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                  (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
            _ ≤ (cardMod false M θ (Sq m) : ℝ) *
                  ((((Tq m + L).choose L : ℝ) * ((N + 1 - (ρ + 1)).factorial : ℝ) *
                    |(minorJ M J hJ : ℝ)| *
                    (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_rightℝ h1 (by positivity)
      _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
          calc _ = (((Tq m + L).choose L : ℕ) : ℝ) *
                (cardMod false M θ (Sq m) : ℝ) *
                ((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
                ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := by ring
            _ ≤ ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := hze
      _ = ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
            (((⌊δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) *
              (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by
          rw [hfact, hprod] <;> try ring
  have hdivpos : (0 : ℝ) < ((N + 1 - (ρ + 1)).factorial : ℝ) *
      (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos _) hPCpos
  refine le_of_mul_le_mul_right ?_ hdivpos
  calc ((((Sq i : ℝ) + 1) * ((Tq i + j).choose j : ℝ)) * |(minorJ M J hJ : ℝ)|) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) * (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))
      = (((Sq i : ℝ) + 1) * ((Tq i + j).choose j : ℝ)) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
          (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
    _ ≤ ((N + 1 - (ρ + 1)).factorial : ℝ) * ((N + 1).descFactorial (ρ + 1) : ℝ) *
        (((⌊δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) *
          (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := hstep
    _ = (((N + 1).descFactorial (ρ + 1) : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ J, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) *
        (((N + 1 - (ρ + 1)).factorial : ℝ) *
          (∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by ring

end Work.BW
