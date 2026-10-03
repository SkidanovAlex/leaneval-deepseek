import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.P13basic
import Submission.Work.FIArea4.P13Scale
import Submission.Work.FIArea4.P13Assembly
import Submission.Work.FIArea4.P13_caseB2

/-!
# FI Proposition 13.1 from Proposition 12.1 (assembly of the §13 inputs)

This module assembles the §13 argument: the two cases (`P ≤ 1`, `1 < P`) are supplied by
`p13_caseA` and `P13_caseB`, and the inputs (divisor bound, prime counts, numerical bracket
comparisons, local-variance estimates) enter as explicit hypotheses so that the file compiles
independently of them.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The final assembly: given the §13 inputs, Proposition 12.1 (for every `ε > 0`) implies
Proposition 13.1 (for every `ε > 0`). -/
theorem p13_final_aux
    (hEner : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ),
        1 ≤ R → 1 ≤ S →
        p14Ener R S α ≤ C * (((R : ℝ) * (S : ℝ)) ^ ε) * p14L2 R S α)
    (hnl : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ) (P : ℝ),
        1 ≤ D → 1 ≤ R → 1 ≤ S → P = p13P D R S → P ≤ 1 →
        p14T12 D R S (ε/8) ≤ K * p14T13 D R S ε * (((R : ℝ) * (S : ℝ)) ^ (ε/2)))
    (hns : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ) (P : ℝ) (D' : ℕ),
        1 ≤ D → 1 ≤ R → 1 ≤ S → P = p13P D R S → 1 < P → 1 ≤ D' →
        (D : ℝ) * P^2 / 2 ≤ (D' : ℝ) → (D' : ℝ) ≤ 16 * (D : ℝ) * P^2 →
        P * p14T12 D' R S (ε/8) ≤ K * p14T13 D R S ε * (((R : ℝ) * (S : ℝ)) ^ (ε/2)))
    (hpc : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) / Real.log (2 * (n:ℝ)) ≤ (((Finset.Ioc n (2*n)).filter Nat.Prime).card : ℝ))
    (hpd : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (R S N r : ℕ),
        1 ≤ R → 1 ≤ S → 1 ≤ r → r ≤ 2 * R →
        ((((Finset.Ioc N (2 * N)).filter Nat.Prime).filter (fun p => p ∣ r)).card : ℝ)
          ≤ C * (((R : ℝ) * (S : ℝ)) ^ ε))
    (haf : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ),
        1 ≤ D → 1 ≤ R → 1 ≤ S → 1 < p13P D R S →
        (D:ℝ) / p13P D R S ≤ p14T13 D R S ε ∧
        1 / p13P D R S ≤ p14T13 D R S ε ∧
        ((R:ℝ)*(S:ℝ)) / (p13P D R S)^2 ≤ p14T13 D R S ε ∧
        Real.log (4 * p13P D R S) ≤ K * (((R:ℝ)*(S:ℝ))^(ε/8)) ∧
        (∀ x : ℝ, 1 ≤ x → x ≤ 32 * (((R:ℝ)*(S:ℝ))^(3/4)) →
            Real.log x ≤ K * (((R:ℝ)*(S:ℝ))^(ε/8))))
    (htau : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε)
    (heb : ∀ (D R S p : ℕ) (α : ℕ → ℕ → ℂ) (B : ℝ), 1 ≤ p →
        (∀ m : ℕ, 1 ≤ m → m ≤ 8*R*S → ((m.divisors.card : ℕ):ℝ) ≤ B) →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2*s)) →
        ∑ d ∈ Finset.Ioc D (2*D), EvarB R S d p α ≤
          ((D:ℝ) + B * (4*(R:ℝ)*(S:ℝ)/(p:ℝ) + 4)) * L2p R S p α)
    (hL2p : ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ) (W : Finset ℕ) (K : ℝ), 0 ≤ K →
        (∀ r : ℕ, 1 ≤ r → r ≤ 2 * R → ((W.filter (fun p => p ∣ r)).card : ℝ) ≤ K) →
        ∑ p ∈ W, L2p R S p α ≤ K * p14L2 R S α)
    (hea : ∀ (R S d p : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ d → p.Prime →
        EvarA R S d p α ≤ (p:ℝ)^2 * Work.FIPlan.Evar R S (d * p^2) α)
    (hm : ∀ (D R S : ℕ) (W : Finset ℕ) (α : ℕ → ℕ → ℂ) (e₁ e₂ : ℕ), 1 ≤ e₁ →
        (∀ p ∈ W, Nat.Prime p) →
        (∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), e₁ < d * p ^ 2) →
        (∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), d * p ^ 2 ≤ e₂) →
        ∑ p ∈ W, ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S (d * p ^ 2) α
          ≤ (Real.log (e₂:ℝ)/Real.log 4 + 2) * ∑ e ∈ Finset.Ioc e₁ e₂, Work.FIPlan.Evar R S e α)
    : p14Prop121All → p14Prop131All := by
  intro h121All ε hε
  obtain ⟨C121, hC121, h121⟩ := h121All (ε/8) (by linarith)
  obtain ⟨KE, hKE, hEnerε⟩ := hEner (ε/4) (by linarith)
  obtain ⟨Knl, hKnl, hnlε⟩ := hnl ε hε
  obtain ⟨Kns, hKns, hnsε⟩ := hns ε hε
  obtain ⟨cp, hcp, hpc'⟩ := hpc
  obtain ⟨Kpd, hKpd, hpdε⟩ := hpd (ε/8) (by linarith)
  obtain ⟨Kaf, hKaf, hafε⟩ := haf ε hε
  obtain ⟨Ktd, hKtd, htauε⟩ := htau (ε/4) (by linarith)
  have hA := p13_caseA ε hε C121 hC121 h121 KE hKE (fun R S α hR hS => hEnerε R S α hR hS)
    Knl hKnl hnlε Kaf hKaf (fun D R S hD hR hS hP => ⟨(hafε D R S hD hR hS hP).2.2.2.1,
      (hafε D R S hD hR hS hP).2.2.2.2⟩) Ktd hKtd htauε Kns hKns cp hcp Kpd hKpd
  have hB := P13_caseB2 ε hε C121 hC121 h121 KE hKE (fun R S α hR hS => hEnerε R S α hR hS)
    Kns hKns hnsε cp hcp hpc' Kpd hKpd hpdε hL2p Kaf hKaf hafε Ktd hKtd htauε
    heb hea hm
  exact p13_combine ε hA hB

end

end Work.FIArea4
