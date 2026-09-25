import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.sigmaN_separated
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.IonescuWainger.taoSetS_coprime
import Submission.Work.BourgainPlan.Maximal.taoSetS_two_le
import Submission.Work.BourgainPlan.Maximal.taoSetS_le_ceil
import Submission.Work.BourgainPlan.Maximal.iwEps_qmax_pow_lt

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- The arithmetic of Tao's set `S_N = taoSetS ρ N` needed to instantiate Tao's `main`: the elements are `≥ 2`, they are pairwise coprime, they are all at most `qmax := ⌈N^{⌊N^{ρ/2}⌋+1}⌉₊`, and for large `N` the threshold `ε_N = exp(−N^ρ)` is small enough for the `(r,1/2)`-goodness (`ε · 2r · qmax^{2rk} < 1/2`). -/
theorem taoSetS_arith (ρ : ℝ) (hρ : 0 < ρ) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (∀ q ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N, 2 ≤ q) ∧
      (∀ p ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N,
        ∀ q ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N, p ≠ q → Nat.Coprime p q) ∧
      (∀ q ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N,
        q ≤ ⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ Work.BourgainPlan.Maximal.iwEps ρ N →
        ε * (2 * (r : ℝ)
          * ((⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ^ (2 * r * k))
          < 1 / 2) := by
  obtain ⟨N₁, hN₁⟩ := taoSetS_two_le ρ hρ
  obtain ⟨N₂, hN₂⟩ := iwEps_qmax_pow_lt ρ hρ r k (by omega) hk
  refine ⟨max (max N₁ N₂) 2, fun N hN => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- the elements are `≥ 2`
    exact hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  · -- pairwise coprimality (Tao, Lemma `iwac`)
    intro p hp q hq hpq
    exact taoSetS_coprime ρ N p hp q hq hpq
  · -- the size bound `q ≤ ⌈N^{⌊N^{ρ/2}⌋+1}⌉₊`
    intro q hq
    exact taoSetS_le_ceil ρ N (by omega) q hq
  · -- the smallness of `ε_N = exp(−N^ρ)`
    intro ε hε hεN
    have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hkey := hN₂ N hN2
    rw [iwEps] at hεN
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hεN (by positivity)) hkey

end Work.BourgainPlan.Maximal
