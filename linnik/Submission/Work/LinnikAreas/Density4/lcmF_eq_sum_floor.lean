/-
# Area 4 / HB §11 — the cut-off bookkeeping for the "lcm" weight `F(s)`

`lcmF` (see `SsmSetup`) is defined as the double sum over `1 ≤ d ≤ ⌈V⌉`, `1 ≤ e ≤ ⌈W⌉`.  HB's
shape (11.8) of the same object runs the sums only up to the *floors* `⌊V⌋`, `⌊W⌋`: the extra
indices carry a zero weight, because `psiM U V d = 0` for `d > V` (using `U ≤ V`) and
`thetaM W e = 0` for `e > W`.

This file proves that bookkeeping (`lcmF_eq_sum_floor`), together with the elementary vanishing
of the two mollifier coefficients beyond their cut-offs and a general Finset re-indexing lemma
replacing `⌈·⌉` by `⌊·⌋` for summands vanishing past the cut-off.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-! ## Vanishing of the mollifier coefficients past the cut-off -/

/-- `psiM U V d` vanishes strictly beyond the cut-off `V` (as soon as `U ≤ V`, so that the inner
linear piece cannot be reached either). -/
lemma psiM_eq_zero_of_lt {U V : ℝ} (hUV : U ≤ V) {d : ℕ} (h : V < (d : ℝ)) : psiM U V d = 0 := by
  have h1 : ¬ ((d : ℝ) ≤ U) := not_le.mpr (lt_of_le_of_lt hUV h)
  have h2 : ¬ ((d : ℝ) ≤ V) := not_le.mpr h
  simp only [psiM, if_neg h1, if_neg h2]

/-- `thetaM W e` vanishes strictly beyond the cut-off `W`. -/
lemma thetaM_eq_zero_of_lt {W : ℝ} {e : ℕ} (h : W < (e : ℝ)) : thetaM W e = 0 := by
  have h2 : ¬ ((e : ℝ) ≤ W) := not_le.mpr h
  simp only [thetaM, if_neg h2]

/-! ## Replacing `⌈V⌉` by `⌊V⌋` in a sum with summand vanishing past `V` -/

/-- `⌊V⌋ < n` implies `V < n` (for `V ≥ 0` this is `Nat.floor_lt`; for `V < 0` it is immediate
since `⌊V⌋ = 0 < n` forces `n ≥ 1 > 0 > V`). -/
lemma lt_of_floor_lt {V : ℝ} {n : ℕ} (h : Nat.floor V < n) : V < (n : ℝ) := by
  rcases lt_or_ge 0 V with hV | hV
  · exact (Nat.floor_lt hV.le).mp h
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith

/-- A sum over `1 ≤ d ≤ ⌈V⌉` of a summand vanishing for `V < d` is the same sum over
`1 ≤ d ≤ ⌊V⌋`: the only indices dropped are `⌊V⌋ < d ≤ ⌈V⌉`, and those satisfy `V < d`. -/
lemma sum_Icc_ceil_eq_sum_Icc_floor {V : ℝ} (f : ℕ → ℂ)
    (hzero : ∀ d : ℕ, V < (d : ℝ) → f d = 0) :
    (∑ d ∈ Finset.Icc 1 (Nat.ceil V), f d) = ∑ d ∈ Finset.Icc 1 (Nat.floor V), f d := by
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_le_ceil V)) ?_).symm
  intro x hx hxn
  rw [Finset.mem_Icc] at hx
  obtain ⟨h1, -⟩ := hx
  have hlt : Nat.floor V < x := by
    by_contra hcon
    exact hxn (by rw [Finset.mem_Icc]; exact ⟨h1, le_of_not_gt hcon⟩)
  exact hzero x (lt_of_floor_lt hlt)

/-- Two-dimensional form: the iterated sum over `⌈V⌉ × ⌈W⌉` equals the one over `⌊V⌋ × ⌊W⌋`
whenever the summand vanishes past either cut-off. -/
lemma sum_sum_Icc_ceil_eq_sum_sum_Icc_floor {V W : ℝ} (f : ℕ → ℕ → ℂ)
    (hV : ∀ d : ℕ, V < (d : ℝ) → (∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e) = 0)
    (hW : ∀ d e : ℕ, W < (e : ℝ) → f d e = 0) :
    (∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W), f d e)
      = ∑ d ∈ Finset.Icc 1 (Nat.floor V), ∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e := by
  have h1 : (∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W), f d e)
      = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e :=
    Finset.sum_congr rfl fun d _ =>
      sum_Icc_ceil_eq_sum_Icc_floor (f d) (fun e he => hW d e he)
  have h2 : (∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e)
      = ∑ d ∈ Finset.Icc 1 (Nat.floor V), ∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e :=
    sum_Icc_ceil_eq_sum_Icc_floor (fun d => ∑ e ∈ Finset.Icc 1 (Nat.floor W), f d e) hV
  rw [h1, h2]

/-! ## The target: `lcmF` with floor cut-offs -/

/-- **HB §11, the floor form of the finite weight `F(s)`.**  In `lcmF` the summations run up to
`⌈V⌉` and `⌈W⌉`; since every index `d > ⌊V⌋` in the range has `d > V` (and `⌊V⌋ ≤ ⌈V⌉`), and
`psiM U V d = 0` for such `d` (here `U ≤ V` is used), while `thetaM W e = 0` for `e > W`, the
sums may equally well be taken up to `⌊V⌋` and `⌊W⌋`. -/
lemma lcmF_eq_sum_floor (q : ℕ) [NeZero q] {U V W : ℝ} (hUV : U ≤ V)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    lcmF q U V W χ s
      = ∑ d ∈ Finset.Icc 1 (Nat.floor V), ∑ e ∈ Finset.Icc 1 (Nat.floor W),
          ((psiM U V d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
            * (χ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s)) := by
  rw [lcmF]
  refine sum_sum_Icc_ceil_eq_sum_sum_Icc_floor
    (fun d e => ((psiM U V d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
            * (χ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))) ?_ ?_
  · intro d hd
    exact Finset.sum_eq_zero fun e _ => by simp [psiM_eq_zero_of_lt hUV hd]
  · intro d e he
    simp [thetaM_eq_zero_of_lt he]

end Work.LinnikAreas.Density4
