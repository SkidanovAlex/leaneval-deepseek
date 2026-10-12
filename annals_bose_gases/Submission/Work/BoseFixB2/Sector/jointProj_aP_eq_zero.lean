import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.jointProj_aP_eq_zero`

If the slot `k` belongs to the set `S` then the joint sector projection
`E_S = ∏_{i∈S} Q_i ∏_{j∉S} P_j` contains the factor `Q_k`, hence its image is
annihilated by `P_k`:

  `aP ℓ k (jointProj ℓ S Φ) = 0   (k ∈ S, k < n, Φ smooth)`.

The proof is the observation that, in the iterated application defining
`blockOp = jointProj`, the slot projection `Q_k` is applied at step `k+1`, and all
later slot projections `P_j`/`Q_j` (`j > k`, `j < n`) commute with `P_k`
(`aP_comm`, `aP_aQ_comm`), while `P_k Q_k = 0` (`aP_aQ_eq_zero`).

## Auxiliary lemmas

* `aP_zero_of_zero` — `P_i 0 = 0` (here, to keep the file self-contained).
* `blockOp_continuous_le` — slot projections preserve continuity, so every
  intermediate `blockOp ℓ S m Φ` (`m ≤ n`) is continuous, which is the
  hypothesis needed by the commutation lemmas.
* `blockOp_aP_eq_zero_aux` — the induction on the number of processed slots:
  `aP ℓ k (blockOp ℓ S m Φ) = 0` for all `k + 1 ≤ m ≤ n`.
-/

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option linter.unusedVariables false

/-- The zero state is fixed by `aP`. -/
private lemma aP_zero_of_zero {N : ℕ} {ℓ : ℝ} (i : Fin N) :
    Submission.BoseGases.aP ℓ i (0 : Submission.BoseGases.X N → ℝ) = 0 := by
  funext x
  simp [Submission.BoseGases.aP]

/-- Slot projections preserve continuity of the state: any partial product
`blockOp ℓ S m Φ` of slot projections applied to a continuous `Φ` is continuous. -/
private lemma blockOp_continuous_le {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (S : Finset ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∀ m ≤ n, Continuous (Work.BoseFixB2.blockOp ℓ S m Φ) := by
  intro m
  induction m with
  | zero => intro _; simpa using hΦc
  | succ m ih =>
      intro hm
      have hmn : m < n := Nat.lt_of_succ_le hm
      rw [Work.BoseFixB2.blockOp_succ S hmn Φ]
      by_cases hmem : m ∈ S
      · rw [if_pos hmem]
        exact Submission.BoseGases.aQ_continuous hℓ ⟨m, hmn⟩ (ih (Nat.le_of_lt hmn))
      · rw [if_neg hmem]
        exact Submission.BoseGases.aP_continuous hℓ ⟨m, hmn⟩ (ih (Nat.le_of_lt hmn))

/-- **The induction core.**  Once the slot `k ∈ S` has been processed (i.e. from
step `k+1` on), every partial product `blockOp ℓ S m Φ` is killed by `aP ℓ k`. -/
private lemma blockOp_aP_eq_zero_aux {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ}
    (hkS : k ∈ S) (hkn : k < n) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    ∀ m, k + 1 ≤ m → m ≤ n →
      Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ S m Φ) = 0 := by
  intro M
  refine Nat.le_induction (P := fun m _ =>
    m ≤ n → Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ S m Φ) = 0)
    ?_ ?_ M
  · -- base case: the slot-`k` operator `Q_k` has just been applied
    intro _
    have hψ : Continuous (Work.BoseFixB2.blockOp ℓ S k Φ) :=
      blockOp_continuous_le hℓ S hΦc k (Nat.le_of_lt hkn)
    rw [Work.BoseFixB2.blockOp_succ S hkn Φ, if_pos hkS]
    funext x
    exact Submission.BoseGases.aP_aQ_eq_zero hℓ ⟨k, hkn⟩ hψ x
  · -- induction step: the next slot `j > k` commutes with `P_k`
    intro j _hj ih hjle
    have hjn : j < n := Nat.lt_of_succ_le hjle
    have hψc : Continuous (Work.BoseFixB2.blockOp ℓ S j Φ) :=
      blockOp_continuous_le hℓ S hΦc j (Nat.le_of_lt hjn)
    have hkne : (⟨k, hkn⟩ : Fin n) ≠ ⟨j, hjn⟩ := by
      intro h
      have : k = j := congrArg Fin.val h
      omega
    rw [Work.BoseFixB2.blockOp_succ S hjn Φ]
    by_cases hmem : j ∈ S
    · rw [if_pos hmem]
      funext x
      rw [Submission.BoseGases.aP_aQ_comm hℓ hkne hψc x, ih (Nat.le_of_lt hjn)]
      simp [Submission.BoseGases.aQ, aP_zero_of_zero]
    · rw [if_neg hmem]
      funext x
      rw [Submission.BoseGases.aP_comm hℓ ⟨k, hkn⟩ ⟨j, hjn⟩ hψc x, ih (Nat.le_of_lt hjn)]
      simp [aP_zero_of_zero]

theorem jointProj_aP_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ} (hkS : k ∈ S) (hkn : k < n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ S Φ) = 0 :=
  blockOp_aP_eq_zero_aux hℓ hkS hkn hΦ.continuous n (Nat.succ_le_of_lt hkn) le_rfl

end Work.BoseFixB2.Sector
