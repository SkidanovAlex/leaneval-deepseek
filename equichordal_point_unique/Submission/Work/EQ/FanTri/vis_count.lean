import Mathlib
import Submission.Work.EQ.FanTri.DecayDefs

/-! Combinatorics of the level counts `Vis` and `fVis`, the per-step gain `tau` and the fan
centre of a word. -/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- One step of the level shift in `fLvl`. -/
theorem fLvl_cons_succ (s : Bool) (ε : List Bool) (j : ℕ) :
    fLvl (s :: ε) (j + 1) = fLvl ε j := by
  simp [fLvl, List.drop_succ_cons]

/-- Adding the top index `n` to the range does not change the filtered cardinality when
`f n = 0`. -/
theorem card_filter_range_succ {n : ℕ} {f : ℕ → ℕ} (hn : f n = 0) :
    ((Finset.range (n + 1)).filter (fun j => f j ≠ 0)).card
      = ((Finset.range n).filter (fun j => f j ≠ 0)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
  have hn' : (if f n ≠ 0 then (1 : ℕ) else 0) = 0 := by simp [hn]
  rw [hn']; omega

/-- Splitting off the `0`-th index and shifting the rest. -/
theorem card_filter_range_shift {n : ℕ} {f : ℕ → ℕ} (hn : f n = 0) :
    ((Finset.range n).filter (fun j => f j ≠ 0)).card
      = (if f 0 = 0 then 0 else 1)
        + ((Finset.range n).filter (fun j => f (j + 1) ≠ 0)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  have h1 := Finset.sum_range_succ (fun j => if f j ≠ 0 then (1 : ℕ) else 0) n
  have h2 := Finset.sum_range_succ' (fun j => if f j ≠ 0 then (1 : ℕ) else 0) n
  have hn' : (if f n ≠ 0 then (1 : ℕ) else 0) = 0 := by simp [hn]
  have h0 : (if f 0 ≠ 0 then (1 : ℕ) else 0) = (if f 0 = 0 then 0 else 1) := by
    by_cases h : f 0 = 0 <;> simp [h]
  rw [hn', add_zero] at h1
  rw [h0] at h2
  omega

theorem vis_count {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    (0 < fanTh a) ∧ (fanTh a < 1) ∧ (eqLam a ≤ fanTh a) ∧
    (Vis ([] : List Bool) = 0) ∧
    (∀ (s : Bool) (ε : List Bool), Vis (s :: ε) = fVis ε) ∧
    (∀ ε : List Bool, Vis ε ≤ fVis ε) ∧
    (∀ ε : List Bool, fVis ε = Vis ε + (if fLvl ε 0 = 0 then 0 else 1)) ∧
    (∀ ε : List Bool, (fanTh a) ^ (fVis ε) = (fanTh a) ^ (Vis ε) * tau a ε) ∧
    (∀ ε : List Bool, 0 < tau a ε ∧ tau a ε ≤ 1 ∧ eqLam a ≤ tau a ε) ∧
    (∀ ε : List Bool, ((fan a h ε 0).1 = ((-1 : ℝ) / 2 : ℂ) ↔ fLvl ε 0 = 0)) := by
  have hth0 : 0 < fanTh a := by rw [fanTh]; apply div_pos <;> nlinarith
  have hth1 : fanTh a < 1 := by
    rw [fanTh]
    have hb : (0 : ℝ) < (1 + a) * (5 - a) := by nlinarith
    rw [div_lt_one hb]; nlinarith
  have hlam_le : eqLam a ≤ fanTh a := by
    rw [fanTh, eqLam]
    have h1 : (0 : ℝ) < 1 + a := by linarith
    have hb : (0 : ℝ) < (1 + a) * (5 - a) := by nlinarith
    rw [div_le_div_iff₀ h1 hb]
    have hfac : (0 : ℝ) ≤ (1 - a) * (1 + a) := by nlinarith
    calc (1 - a) * ((1 + a) * (5 - a)) = ((1 - a) * (1 + a)) * (5 - a) := by ring
      _ ≤ ((1 - a) * (1 + a)) * (5 + a) := mul_le_mul_of_nonneg_left (by linarith) hfac
      _ = ((1 - a) * (5 + a)) * (1 + a) := by ring
  have hlam1 : eqLam a ≤ 1 := le_of_lt (eqLam_lt_one' ha0 ha1)
  -- the two counting identities for `fVis`
  have hfvisA : ∀ ε : List Bool, fVis ε
      = (if fLvl ε 0 = 0 then 0 else 1) + Vis ε := by
    intro ε
    rw [fVis, Vis]
    exact card_filter_range_shift (f := fun j => fLvl ε j) (fLvl_self ε)
  have hfvisB : ∀ ε : List Bool, fVis ε = Vis ε + (if fLvl ε 0 = 0 then 0 else 1) :=
    fun ε => by rw [hfvisA ε]; ring
  refine ⟨hth0, hth1, hlam_le, ?_, ?_, ?_, hfvisB, ?_, ?_, ?_⟩
  · rw [Vis]; simp
  · intro s ε
    have hA : Vis (s :: ε)
        = ((Finset.range (ε.length + 1)).filter (fun j => fLvl ε j ≠ 0)).card := by
      rw [Vis]; congr 1
    have hB : ((Finset.range (ε.length + 1)).filter (fun j => fLvl ε j ≠ 0)).card
        = fVis ε :=
      card_filter_range_succ (f := fun j => fLvl ε j) (fLvl_self ε)
    exact hA.trans hB
  · intro ε
    have := hfvisB ε
    omega
  · intro ε
    have hD := hfvisB ε
    by_cases h0 : fLvl ε 0 = 0
    · have ht : tau a ε = 1 := by unfold tau; rw [if_pos h0]
      rw [ht, hD, if_pos h0, add_zero, mul_one]
    · have ht : tau a ε = fanTh a := by unfold tau; rw [if_neg h0]
      rw [hD, if_neg h0, pow_succ, ← ht]
  · intro ε
    by_cases h0 : fLvl ε 0 = 0
    · have ht : tau a ε = 1 := by unfold tau; rw [if_pos h0]
      rw [ht]
      exact ⟨one_pos, le_rfl, hlam1⟩
    · have ht : tau a ε = fanTh a := by unfold tau; rw [if_neg h0]
      rw [ht]
      exact ⟨hth0, le_of_lt hth1, hlam_le⟩
  · intro ε
    have h1 : (fan a h ε 0).1 = ((stCtr (fLvl ε 0) : ℝ) : ℂ) := by
      rw [fan_centre_walk ha0 ha1 hh ε]; rfl
    rw [h1]
    constructor
    · intro hc
      have hc' : ((stCtr (fLvl ε 0) : ℝ) : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
        rw [hc]; norm_num
      exact stCtr_eq_iff.mp (Complex.ofReal_injective hc')
    · intro hc
      rw [hc, stCtr_zero]
      norm_num

end

end Work.EQ.FanTri
