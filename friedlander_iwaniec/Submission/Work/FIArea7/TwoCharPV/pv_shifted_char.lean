import Mathlib
import Submission.Work.FIArea7.pv_weighted_jacobiSym

namespace Work.FIArea7.TwoCharPV

open Finset
open scoped BigOperators

/-- **Pólya–Vinogradov for a shifted Jacobi-symbol character.**  For `Q ≥ 1` whose odd part is
not a perfect square (so `n ↦ J(n|Q)` is a non-trivial Dirichlet character), any shift `d : ℤ` and
any weight `φ` bounded by `M` with first differences bounded by `D`,

  `|Σ_{n ≤ N} J(n + d | Q)·φ(n)| ≤ C·(M + N·D)·√Q·(log Q + 1)`.

Suggested proof: replace `d` by `d % Q ∈ [0, Q)` using `jacobiSym.mod_left'` (the Jacobi symbol is
periodic in its upper argument modulo `Q`), then reindex `n ↦ m = n + d`, so that `m` runs over
`Finset.Icc d (d + N)`, and apply `Work.FIArea7.pv_weighted_jacobiSym` (in
`Submission/Work/FIArea7/pv_weighted_jacobiSym.lean`) to the weight `m ↦ φ (m - d)`, whose bound
`M` and first-difference bound `D` are unchanged. -/
theorem pv_shifted_char :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (d : ℤ) (N : ℕ) (φ : ℕ → ℝ) (M D : ℝ),
      1 ≤ Q → (∀ k : ℕ, Work.FIPlan.oddPart Q ≠ k ^ 2) →
      (∀ n : ℕ, |φ n| ≤ M) → (∀ n : ℕ, |φ (n + 1) - φ n| ≤ D) →
      |∑ n ∈ Finset.Icc 0 N, (jacobiSym (n + d) Q : ℝ) * φ n|
        ≤ C * (M + (N : ℝ) * D) * Real.sqrt Q * (Real.log Q + 1) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FIArea7.pv_weighted_jacobiSym
  refine ⟨C, hCpos, ?_⟩
  intro Q d N φ M D hQ hns hφ hd
  -- reduce the shift modulo `Q`
  have hQz : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast (show 0 < Q by omega)
  have hQne : (Q : ℤ) ≠ 0 := by
    have : Q ≠ 0 := by omega
    exact_mod_cast this
  set R : ℕ := (d % (Q : ℤ)).toNat with hR_def
  have hrnn : 0 ≤ d % (Q : ℤ) := Int.emod_nonneg d hQne
  have hrlt : d % (Q : ℤ) < (Q : ℤ) := Int.emod_lt_of_pos d hQz
  have hRcast : (R : ℤ) = d % (Q : ℤ) := by
    rw [hR_def]; exact Int.toNat_of_nonneg hrnn
  -- the shifted weight `m ↦ φ (m - R)` keeps the bounds `M` and `D`
  have hψbound : ∀ n : ℕ, |φ (n - R)| ≤ M := fun n => hφ (n - R)
  have hD : 0 ≤ D := le_trans (abs_nonneg _) (hd 0)
  have hψdiff : ∀ n : ℕ, |φ ((n + 1) - R) - φ (n - R)| ≤ D := by
    intro n
    by_cases h : R ≤ n
    · have h1 : n + 1 - R = (n - R) + 1 := by omega
      rw [h1]; exact hd (n - R)
    · have h1 : n + 1 - R = 0 := by omega
      have h2 : n - R = 0 := by omega
      rw [h1, h2, sub_self, abs_zero]; exact hD
  -- periodicity of the Jacobi symbol in its upper argument modulo `Q`
  have hstepA : ∀ n : ℕ, (jacobiSym (n + d) Q : ℝ)
      = (jacobiSym (((n + R : ℕ) : ℤ)) Q : ℝ) := by
    intro n
    have hZ : jacobiSym ((n : ℤ) + d) Q = jacobiSym (((n + R : ℕ) : ℤ)) Q := by
      refine jacobiSym.mod_left' ?_
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      have hcast : (((n + R : ℕ) : ℤ)) = (n : ℤ) + d % (Q : ℤ) := by
        push_cast; rw [hRcast]
      rw [hcast, show (n : ℤ) + d - ((n : ℤ) + d % (Q : ℤ)) = d - d % (Q : ℤ) by ring]
      apply Int.emod_eq_zero_of_dvd
      apply Int.dvd_of_emod_eq_zero
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      rw [Int.emod_eq_of_lt hrnn hrlt]
    exact_mod_cast hZ
  -- reindex `n ↦ m = n + R`, so `m` runs over `Icc R (R + N)`
  have hkey : (∑ n ∈ Finset.Icc 0 N, (jacobiSym (n + d) Q : ℝ) * φ n)
      = ∑ m ∈ Finset.Icc R (R + N), (jacobiSym ((m : ℤ)) Q : ℝ) * φ (m - R) := by
    rw [Finset.sum_congr rfl (fun n _ => by rw [hstepA n])]
    let F : ℕ → ℝ := fun m => (jacobiSym ((m : ℤ)) Q : ℝ)
    let H : ℕ → ℝ := fun m => F m * φ (m - R)
    have step1 : (∑ n ∈ Finset.Icc 0 N, F (n + R) * φ n) = ∑ n ∈ Finset.Icc 0 N, H (n + R) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      show F (n + R) * φ n = F (n + R) * φ (n + R - R)
      rw [Nat.add_sub_cancel]
    change (∑ n ∈ Finset.Icc 0 N, F (n + R) * φ n) = ∑ m ∈ Finset.Icc R (R + N), H m
    rw [step1]
    rw [show Finset.Icc 0 N = Finset.Ico 0 (N + 1) from rfl,
        show Finset.Icc R (R + N) = Finset.Ico R (R + N + 1) from rfl]
    rw [show (∑ x ∈ Finset.Ico 0 (N + 1), H (x + R)) = ∑ x ∈ Finset.Ico 0 (N + 1), H (R + x) from
          Finset.sum_congr rfl (fun x _ => by rw [Nat.add_comm])]
    rw [Finset.sum_Ico_add (f := H) (a := 0) (b := N + 1) (c := R)]
    rw [show (0 : ℕ) + R = R from by omega, show N + 1 + R = R + N + 1 from by omega]
  rw [hkey]
  exact hC Q R N (fun m => φ (m - R)) M D hQ hns hψbound hψdiff

end Work.FIArea7.TwoCharPV
