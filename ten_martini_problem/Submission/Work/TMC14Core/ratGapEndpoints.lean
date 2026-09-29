import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.continuous_trAq_pair
import Submission.Work.TMC14Core.isClosed_exists_norm_le
import Submission.Work.TMC14Core.exists_gap_endpoints_of_isClosed

/-!
# TMC14Core: the endpoints of the gaps of the rational union spectrum

`RatGapEndpoints` (ROUTE_LEAD §4 C14, item 14d's bookkeeping) is the elementary topological
input of the gap-finding argument: for the rational approximant `p/q`,

* `ratSpec p q lam = {E | ∃ θ, ‖tr A_q(θ,E)‖ ≤ 2}` is **closed** (the union spectrum of the
  periodic problem is a finite union of bands), and
* around any point `E` **outside** `ratSpec` inside a window `[c,d]` there is a *gap*
  interval `(a',b')` containing `E`, whose interior avoids `ratSpec`, whose left end is
  either outside the window (`a' < c`) or a spectral point, and whose right end is either
  `d` or a spectral point.

The closedness uses the `1`-periodicity of `θ ↦ tr A_q(θ,·)` (`Rat.trAq_add_one`) to restrict
the phase to the compact interval `[0,1]`; the two ingredients are delegated:
`continuous_trAq_pair` (joint continuity) and `isClosed_exists_norm_le` (the set
`{E | ∃ θ ∈ [a,b], ‖F (E,θ)‖ ≤ 2}` is closed for continuous `F`), assembled by
`ratSpec_eq_aux` + `ratSpec_isClosed`.  The gap statement is
`exists_gap_endpoints_of_isClosed`, a general fact about closed subsets of `ℝ` (take the
connected component of `E` in the complement and cut it with the window).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. Periodicity of `trAq` in the phase by integers -/

theorem trAq_add_nat (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) (θ : ℝ) :
    trAq p q lam z (θ + (n : ℝ)) = trAq p q lam z θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show θ + ((n + 1 : ℕ) : ℝ) = (θ + (n : ℝ)) + 1 from by push_cast; ring,
      trAq_add_one, ih]

theorem trAq_sub_nat (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (n : ℕ) (θ : ℝ) :
    trAq p q lam z (θ - (n : ℝ)) = trAq p q lam z θ := by
  have h := trAq_add_nat p q lam z n (θ - (n : ℝ))
  rw [show θ - (n : ℝ) + (n : ℝ) = θ from by ring] at h
  exact h.symm

theorem trAq_add_int (p : ℤ) (q : ℕ) (lam : ℝ) (z : ℂ) (m : ℤ) (θ : ℝ) :
    trAq p q lam z (θ + (m : ℝ)) = trAq p q lam z θ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have h : ((↑n : ℤ) : ℝ) = (n : ℝ) := by simp
    rw [h]
    exact trAq_add_nat p q lam z n θ
  · have h : ((-↑n : ℤ) : ℝ) = -(n : ℝ) := by simp
    rw [h]
    exact trAq_sub_nat p q lam z n θ

/-! ## 2. `ratSpec` as a "there exists a phase in `[0,1]`" set -/

theorem ratSpec_eq_aux (p : ℤ) (q : ℕ) (lam : ℝ) :
    ratSpec p q lam = {E : ℝ | ∃ θ ∈ Set.Icc (0 : ℝ) 1, ‖trAq p q lam (E : ℂ) θ‖ ≤ 2} := by
  ext E
  constructor
  · rintro ⟨θ, hθ⟩
    have htr : trAq p q lam (E : ℂ) (Int.fract θ) = trAq p q lam (E : ℂ) θ := by
      conv_rhs => rw [← Int.fract_add_floor θ]
      rw [trAq_add_int]
    exact ⟨Int.fract θ, ⟨Int.fract_nonneg θ, le_of_lt (Int.fract_lt_one θ)⟩, by rwa [htr]⟩
  · rintro ⟨θ, _, hθ⟩
    exact ⟨θ, hθ⟩

/-- The union spectrum `ratSpec p q lam` of the rational approximant is closed. -/
theorem ratSpec_isClosed (p : ℤ) (q : ℕ) (lam : ℝ) : IsClosed (ratSpec p q lam) := by
  have h := isClosed_exists_norm_le (fun u : ℝ × ℝ => trAq p q lam (u.1 : ℂ) u.2)
    (continuous_trAq_pair p q lam) 0 1
  rw [← ratSpec_eq_aux p q lam] at h
  exact h

/-! ## 3. The assembly -/

theorem ratGapEndpoints : Work.TMC14Core.RatGapEndpoints := by
  refine ⟨ratSpec_isClosed, ?_⟩
  intro p q lam c d E hE hcE hEd hcd
  exact exists_gap_endpoints_of_isClosed (ratSpec_isClosed p q lam) hE hcE hEd hcd

end Work.TMC14Core
