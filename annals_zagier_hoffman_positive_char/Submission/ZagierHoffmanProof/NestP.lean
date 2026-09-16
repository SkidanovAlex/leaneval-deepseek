import Submission.ZagierHoffmanProof.AmbInf
import Submission.ZagierHoffmanProof.ZetaCMPL

/-!
# The MZV as an iterated sum of the power sums `P_d` (general entries)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The tail of a `Fin`-indexed tuple. -/
def ftail (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+) : Fin r → ℕ+ := fun j => 𝔰 j.succ

lemma ftail_apply (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+) (j : Fin r) :
    ftail r 𝔰 j = 𝔰 j.succ := rfl

/-- `nestLvlP r 𝔰 d` is the sum of `∏_j ambInfHom (P_{d_j}(𝔰_j))` over the strictly decreasing
tuples `d > d_0 > d_1 > ⋯ > d_{r-1} ≥ 0`. -/
noncomputable def nestLvlP : (r : ℕ) → (Fin r → ℕ+) → ℕ → Ambient F
  | 0, _, _ => 1
  | (r + 1), 𝔰, d => ∑ i ∈ Finset.range d,
      ambInfHom F (P F i (𝔰 0)) * nestLvlP r (ftail r 𝔰) i

@[simp] lemma nestLvlP_zero (𝔰 : Fin 0 → ℕ+) (d : ℕ) : nestLvlP F 0 𝔰 d = 1 := rfl

lemma nestLvlP_succ (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+) (d : ℕ) :
    nestLvlP F (r + 1) 𝔰 d = ∑ i ∈ Finset.range d,
      ambInfHom F (P F i (𝔰 0)) * nestLvlP F r (ftail r 𝔰) i :=
  rfl

/-- The block recursion with the tail written as `ftail`. -/
lemma S_d_recursion_ftail (r : ℕ) (𝔰 : Fin (r + 2) → ℕ+) (d : ℕ) :
    S F (r + 2) (by omega) 𝔰 d
      = P F d (𝔰 0) * S_lt F (r + 1) (by omega) (ftail (r + 1) 𝔰) d := by
  have h := S_d_recursion F (r + 2) (by omega) (by omega) (by omega) 𝔰 d
  rw [show (fun j : Fin (r + 2 - 1) => 𝔰 ⟨j.1 + 1, by omega⟩) = ftail (r + 1) 𝔰
    from by funext j; rfl] at h
  exact h

/-- **The level-wise form of the MZV `↔` iterated power sum identity** (general entries):
`ambInfHom (S_d(𝔰)) = ambInfHom (P_d(𝔰_0))·(the iterated sum over the tail)`. -/
theorem ambInfHom_S_eq_nestLvlP (r : ℕ) : ∀ (𝔰 : Fin (r + 1) → ℕ+) (d : ℕ),
    ambInfHom F (S F (r + 1) (Nat.succ_pos r) 𝔰 d)
      = ambInfHom F (P F d (𝔰 0)) * nestLvlP F r (ftail r 𝔰) d := by
  induction r with
  | zero =>
    intro 𝔰 d
    rw [nestLvlP_zero, mul_one]
    simpa using congrArg (ambInfHom F) (S_one_eq_P F d (Nat.succ_pos 0) 𝔰)
  | succ r ih =>
    intro 𝔰 d
    have hrec := S_d_recursion_ftail F r 𝔰 d
    rw [hrec, map_mul, ambInfHom_S_lt]
    rw [nestLvlP_succ (F := F) (r := r) (𝔰 := ftail (r + 1) 𝔰) d]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := ih (ftail (r + 1) 𝔰) i
    rw [h2]

/-- **The capstone**: for arbitrary entries, `ambInfHom (ζ_A 𝔰)` is the iterated sum of the
power sums `ambInfHom (P_d(𝔰_j))` along strictly decreasing chains. -/
theorem ambInfHom_zeta_A_eq_nestLvlP (r : ℕ) (𝔰 : Fin (r + 1) → ℕ+) :
    ambInfHom F (ζ_A F 𝔰)
      = ∑' d : ℕ, ambInfHom F (P F d (𝔰 0)) * nestLvlP F r (ftail r 𝔰) d := by
  have h := (summable_S F (Nat.succ_pos r) 𝔰).hasSum.map (ambInfHom F) (continuous_ambInfHom F)
  rw [← zeta_eq_tsum_block F (Nat.succ_pos r) 𝔰] at h
  rw [← h.tsum_eq]
  exact tsum_congr (fun d => ambInfHom_S_eq_nestLvlP F r 𝔰 d)

end ZagierHoffmanPositiveChar
