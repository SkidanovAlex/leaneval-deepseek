import Mathlib
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **`λ(p)` has at most two terms.**  For a rational prime `p ≡ 1 (mod 4)` the primary Gaussian
integers of norm `p` are exactly the two conjugate primary primes `π` and `π'` supplied by
`splitPrimaryClass` (the `ν = 1` case), so the Hecke eigenvalue `λ(p) = ∑_{|z|²=p} ψ(z)` is a sum
over at most two elements. -/
theorem heckeLam_prime_norm_le_two {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ}
    (hp : p.Prime) (h4 : p % 4 = 1) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ‖heckeLam chi k p‖ ≤ 2 := by
  classical
  obtain ⟨π, π', hπp, hπ'p, hπg, hπ'g, hπirr, hπ'irr, hnassoc, huniq⟩ :=
    splitPrimaryClass p hp h4
  -- Every primary `z` of norm `p` lies in the two-element set `{π, π'}`.
  have hsub : (gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p) ⊆
      ({π, π'} : Finset GaussianInt) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hzp, hzg⟩ := hz
    obtain ⟨a, ha, -⟩ := huniq 1 z hzp (by rw [pow_one]; exact hzg)
    obtain ⟨hale, haeq⟩ := ha
    rw [Finset.mem_insert, Finset.mem_singleton]
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · right; rw [haeq]; simp
    · left; rw [haeq]; simp
  have hcard : ((gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p)).card ≤ 2 :=
    (Finset.card_le_card hsub).trans (Finset.card_le_two (a := π) (b := π'))
  calc ‖heckeLam chi k p‖
      = ‖∑ z ∈ (gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p), psi chi k z‖ := by
        rw [heckeLam]
    _ ≤ ∑ z ∈ (gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p), ‖psi chi k z‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _z ∈ (gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p), (1 : ℝ) :=
        Finset.sum_le_sum (fun z _ => norm_psi_le_one chi k hb z)
    _ = (((gBox (p : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = p)).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hcard

end

end Work.FIArea5.S16Hecke
