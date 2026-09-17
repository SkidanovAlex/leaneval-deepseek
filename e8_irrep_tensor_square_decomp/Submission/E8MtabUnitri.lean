import Submission.E8Star
import Submission.E8Extract
import Submission.E8Enum

/-!
# The unitriangularity of the Freudenthal table and the extraction of the multiplicities

`Submission.E8Extract.ccv_system` states, for the literal tables of the paper,

  `mf2v i = ∑ d, (if Λ i = Λ d ∨ Λ d ⪰ Λ i then ccv d * Mtab d i else 0)`,

and `ccv_pos` that every `ccv d ≥ 1`.  This file proves the *abstract* form of that triangular
system: if a family `b : Fin 40 → ℤ` satisfies the same system, then `b = ccv`.  The two inputs are

* `Mtab_diag : Mtab i i = 1` (the top weight multiplicities are one), and
* `Mtab_unitri : Mtab i e ≠ 0 → Λ e ⪰ Λ i` (the support bound), together with the fact that
  `ord40` is ordered by *strictly decreasing height*, so that `Λ e ⪰ Λ i` with `e ≠ i` forces
  `e` to come strictly before `i` in the list.

Consequently, if the weight multiplicities of the tensor square at the forty dominant weights are
the table `mf2v` (i.e. `dim T_{Λ i} = mf2v i`), then every constituent type occurs.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8MtabUnitri

open Submission.E8Extract Submission.E8Star Submission.E8Character
open Submission.E8Enum

/-- The top weight multiplicity is one. -/
theorem Mtab_diag (i : Fin 40) : Mtab i i = 1 := by
  have h := Submission.E8Star.Mnu_top i
  rw [Submission.E8Star.Mnu_dom] at h
  exact h

/-- **Unitriangularity**: a non-zero Freudenthal matrix entry forces `Λ e ⪰ Λ i`. -/
theorem Mtab_unitri (i e : Fin 40) (h : Mtab i e ≠ 0) :
    posCon (ord40get i - ord40get e) := by
  have h' := Submission.E8Star.Mtab_support i e h
  rw [Submission.E8Star.posF_true] at h'
  exact h'

/-- The entries of `ord40` are distinct. -/
theorem ord40get_inj : ∀ i j : Fin 40, ord40get i = ord40get j → i = j := by
  decide

/-- **`ord40` is non-increasing in height.** -/
theorem ord40_ht_nonincreasing : ∀ i j : Fin 40, i ≤ j → htOf (ord40get j) ≤ htOf (ord40get i) := by
  decide

/-- A non-zero Freudenthal entry with a *later* row forces a height increase. -/
theorem ht_lt_of_Mtab_ne (i d : Fin 40) (h : Mtab d i ≠ 0) (hne : d ≠ i) :
    htOf (ord40get i) < htOf (ord40get d) := by
  have hp := Mtab_unitri d i h
  have hne0 : ord40get d - ord40get i ≠ 0 := by
    intro h0
    exact hne (ord40get_inj d i (sub_eq_zero.mp h0))
  have hpos : 0 < htOf (ord40get d - ord40get i) := htOf_pos hp hne0
  rw [htOf_sub] at hpos
  linarith

/-! ## The extraction -/

/-- The system of `E8Extract.ccv_system`, for an arbitrary family `b`. -/
def System (b : Fin 40 → ℤ) : Prop :=
  ∀ i : Fin 40, mf2v i = ∑ d : Fin 40,
    if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
    then b d * Mtab d i else 0

/-- The sum of the system at `i` splits into the diagonal term and the terms with `d < i`. -/
theorem system_sum_split (i : Fin 40) (c : Fin 40 → ℤ) :
    (∑ d : Fin 40,
        (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
         then c d * Mtab d i else 0))
      = c i + ∑ d ∈ (Finset.univ.filter (fun d => d < i)),
          (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
           then c d * Mtab d i else 0) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ) (fun d => d < i)
        (fun d => (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
                   then c d * Mtab d i else 0))]
  have hcompl : (∑ d ∈ (Finset.univ.filter (fun d => ¬ d < i)),
      (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
       then c d * Mtab d i else 0)) = c i := by
    have hi : i ∈ Finset.univ.filter (fun d => ¬ d < i) := by
      simp
    rw [Finset.sum_eq_single i]
    · simp [Mtab_diag]
    · intro d hdmem hd
      have hdi : i < d := by
        have := (Finset.mem_filter.mp hdmem).2
        omega
      have hfalse : ¬ ((ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)) := by
        rintro (heq | hpos)
        · exact hd (ord40get_inj i d heq).symm
        · have hp : posCon (ord40get d - ord40get i) := (posB_true).mp hpos
          have hne0 : ord40get d - ord40get i ≠ 0 := by
            intro h0
            exact hd (ord40get_inj d i (sub_eq_zero.mp h0))
          have hposh : 0 < htOf (ord40get d - ord40get i) := htOf_pos hp hne0
          rw [htOf_sub] at hposh
          have hle := ord40_ht_nonincreasing i d hdi.le
          linarith
      simp [hfalse]
    · intro hnot
      exact absurd hi hnot
  rw [hcompl]
  ring

/-- **The triangular system has a unique solution.** -/
theorem eq_ccv_of_system {b : Fin 40 → ℤ} (h : System b) (i : Fin 40) : b i = ccv i := by
  classical
  suffices hall : ∀ n : ℕ, ∀ i : Fin 40, i.1 < n → b i = ccv i by
    exact hall (i.1 + 1) i (by omega)
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hsys := h i
    have hccv := ccv_system i
    rw [system_sum_split i b] at hsys
    rw [system_sum_split i ccv] at hccv
    have hsame : (∑ d ∈ (Finset.univ.filter (fun d => d < i)),
          (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
           then b d * Mtab d i else 0))
        = ∑ d ∈ (Finset.univ.filter (fun d => d < i)),
          (if (ord40get i = ord40get d) ∨ (posB (ord40get d - ord40get i) = true)
           then ccv d * Mtab d i else 0) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_filter] at hd
      rw [ih d (by omega)]
    rw [hsame] at hsys
    omega

/-- Every value `ccv i` is positive, hence so is any solution of the system: **every one of the
forty dominant weights is the top weight of a constituent of the tensor square.** -/
theorem pos_of_system {b : Fin 40 → ℤ} (h : System b) (i : Fin 40) : 1 ≤ b i := by
  rw [eq_ccv_of_system h i]
  exact ccv_pos i

end Submission.E8MtabUnitri
