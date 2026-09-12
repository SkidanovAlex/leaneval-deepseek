import Mathlib
import Submission.RS
import Submission.Sec3Base
import Submission.ArcFamily

/-!
Theorem 2.3 quadrant-family core.  Build the bad-run interval family for the
cosine polynomial and prove the count and coverage bounds.
-/
noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3

noncomputable instance (t q : ℕ) (j : ℕ) : Decidable (cellGood t q j) := Classical.propDecidable _

/-! ## 0. Far bounds for bad cells in the quadrant -/

/-- A bad cell `j < q/2` is far from the right edge: `2(j+1)+200 ≤ q`. -/
lemma far_right_of_bad (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (hj : ¬ cellGood t q j) (hjq : j < q / 2) :
    2 * (j + 1) + 200 ≤ q := by
  have h := bad_index_q2 t q j ht hq0 hlo hj hjq
  have h2 : (2 * (j : ℝ) + 2048) < (q : ℝ) := by nlinarith [h]
  have h2nat : 2 * j + 2048 < q := by
    exact_mod_cast h2
  omega

/-- `q` is large (positive). -/
lemma q_large_pos (q : ℕ) (hq0 : 2 ^ 400 ≤ q) : 1 ≤ q := by omega

/-- A bad cell `j < q/2` has room: `j + 1024 ≤ q/2`. -/
lemma bad_far_from_q2 (t q : ℕ) (j : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (hj : ¬ cellGood t q j) (hjq : j < q / 2) :
    j + 1024 ≤ q / 2 := by
  have h := bad_index_q2 t q j ht hq0 hlo hj hjq
  have h2 : (2 * (j : ℝ) + 2048) < (q : ℝ) := by nlinarith [h]
  have h2nat : 2 * j + 2048 < q := by
    exact_mod_cast h2
  omega

/-! ## 1. Run machinery

A *bad cell* is one where `¬ cellGood`.  We work on the quadrant cells
`j = 0, ..., q/2 - 1`.  A *run* is a maximal block of consecutive bad cells;
runs never touch the boundary, have length ≤ 6 and are separated by at least
one good cell.  We encode a run by its first (smallest) cell index `s`, and
recover the run end with `runEnd`.
-/

/-- A start-spec for the maximal bad run through a bad cell `j`: `j` itself works. -/
lemma startSpec (t q : ℕ) {j : ℕ} (hj : ¬ cellGood t q j) :
    ∃ s : ℕ, s ≤ j ∧ ∀ k : ℕ, s ≤ k → k ≤ j → ¬ cellGood t q k :=
  ⟨j, le_rfl, by
    intro k hkj hjk
    have : k = j := by omega
    subst k
    exact hj⟩

/-- The start cell of the maximal run of consecutive bad cells through `j`
(defined as `j` itself when `j` is good). -/
noncomputable def runStart (t q : ℕ) (j : ℕ) : ℕ :=
  if hb : ¬ cellGood t q j then
    Nat.find (startSpec t q hb)
  else j

/-- `runStart j ≤ j`. -/
lemma runStart_le (t q : ℕ) (j : ℕ) : runStart t q j ≤ j := by
  unfold runStart
  by_cases hb : ¬ cellGood t q j
  · rw [dif_pos hb]
    exact (Nat.find_spec (startSpec t q hb)).1
  · rw [dif_neg hb]

/-- Basic spec of `runStart` for a bad cell: everything from the start through
`j` is bad. -/
lemma runStart_spec (t q : ℕ) {j : ℕ} (hj : ¬ cellGood t q j) :
    runStart t q j ≤ j ∧
      ∀ k : ℕ, runStart t q j ≤ k → k ≤ j → ¬ cellGood t q k := by
  unfold runStart
  rw [dif_pos hj]
  exact Nat.find_spec (startSpec t q hj)

/-- Minimality: `runStart j` is the least start with everything through `j` bad. -/
lemma runStart_min (t q : ℕ) {j s : ℕ} (hj : ¬ cellGood t q j) (hs : s ≤ j)
    (hall : ∀ k : ℕ, s ≤ k → k ≤ j → ¬ cellGood t q k) : runStart t q j ≤ s := by
  unfold runStart
  rw [dif_pos hj]
  exact Nat.find_min' (startSpec t q hj) ⟨hs, hall⟩

/-- The start cell of a bad cell is itself bad. -/
lemma runStart_bad (t q : ℕ) {j : ℕ} (hj : ¬ cellGood t q j) :
    ¬ cellGood t q (runStart t q j) := by
  have hspec := runStart_spec t q hj
  exact hspec.2 (runStart t q j) (Nat.le_refl _) hspec.1

/-- The cell before a (positive) start is good. -/
lemma runStart_left_good (t q : ℕ) {j : ℕ} (hj : ¬ cellGood t q j)
    (hpos : 0 < runStart t q j) : cellGood t q (runStart t q j - 1) := by
  by_contra hg
  have hspec := runStart_spec t q hj
  have hs : runStart t q j - 1 ≤ j := by omega
  have hall : ∀ k : ℕ, runStart t q j - 1 ≤ k → k ≤ j → ¬ cellGood t q k := by
    intro k hk1 hk2
    by_cases hk : runStart t q j ≤ k
    · exact hspec.2 k hk hk2
    · have : k = runStart t q j - 1 := by omega
      subst k
      exact hg
  have hle := runStart_min t q hj hs hall
  omega

/-- A good cell strictly beyond a bad cell `j` exists. -/
lemma exists_good_beyond (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : ∃ g : ℕ, j + 1 ≤ g ∧ cellGood t q g := by
  rcases exists_good_in_seven t q j hq0 hlo with ⟨m, hm⟩
  refine ⟨j + m.1, ?_⟩
  constructor
  · have hm0 : m.1 ≠ 0 := by
      intro hmz
      have : cellGood t q j := by simpa [hmz] using hm
      exact hj this
    omega
  · exact hm

/-- The first good cell strictly beyond a bad cell `j`. -/
noncomputable def goodAfter (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (j : ℕ) (hj : ¬ cellGood t q j) : ℕ :=
  Nat.find (exists_good_beyond t q hq0 hlo hj)

/-- The run end of the maximal bad run starting at the bad cell `j`. -/
noncomputable def runEnd (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (j : ℕ) (hj : ¬ cellGood t q j) : ℕ :=
  goodAfter t q hq0 hlo j hj - 1

/-- `goodAfter` is good and strictly beyond. -/
lemma goodAfter_spec (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) :
    j + 1 ≤ goodAfter t q hq0 hlo j hj ∧ cellGood t q (goodAfter t q hq0 hlo j hj) := by
  unfold goodAfter
  exact Nat.find_spec (exists_good_beyond t q hq0 hlo hj)

/-- `goodAfter` is the *first* good cell beyond `j`. -/
lemma goodAfter_min (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) {g : ℕ} (hg1 : j + 1 ≤ g) (hg2 : cellGood t q g) :
    goodAfter t q hq0 hlo j hj ≤ g := by
  unfold goodAfter
  exact Nat.find_min' (exists_good_beyond t q hq0 hlo hj) ⟨hg1, hg2⟩

/-- The run-end is beyond its start: `j ≤ runEnd j`. -/
lemma runEnd_ge (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : j ≤ runEnd t q hq0 hlo j hj := by
  have hg := (goodAfter_spec t q hq0 hlo hj).1
  unfold runEnd
  omega

/-- Every cell of the run is bad, and the cell after the run is good. -/
lemma runEnd_spec (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) :
    (∀ k : ℕ, j ≤ k → k ≤ runEnd t q hq0 hlo j hj → ¬ cellGood t q k) ∧
      cellGood t q (runEnd t q hq0 hlo j hj + 1) := by
  have hg1 : j + 1 ≤ goodAfter t q hq0 hlo j hj := (goodAfter_spec t q hq0 hlo hj).1
  have hg2 : cellGood t q (goodAfter t q hq0 hlo j hj) := (goodAfter_spec t q hq0 hlo hj).2
  constructor
  · intro k hk1 hk2
    by_cases hkj : k = j
    · subst k
      exact hj
    · have hkj1 : j + 1 ≤ k := by omega
      by_contra hk
      have hgmin := goodAfter_min t q hq0 hlo hj hkj1 hk
      have hklt : k < goodAfter t q hq0 hlo j hj := by
        unfold runEnd at hk2
        omega
      omega
  · unfold runEnd
    have heq : goodAfter t q hq0 hlo j hj - 1 + 1 = goodAfter t q hq0 hlo j hj := by omega
    rw [heq]
    exact hg2

/-- Run length is at most 6 cells (`runEnd j ≤ j + 5`). -/
lemma runEnd_len (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : runEnd t q hq0 hlo j hj ≤ j + 5 := by
  rcases exists_good_in_seven t q j hq0 hlo with ⟨m, hm⟩
  have hm0 : m.1 ≠ 0 := by
    intro hmz
    have : cellGood t q j := by simpa [hmz] using hm
    exact hj this
  have hg := goodAfter_min t q hq0 hlo hj (by omega : j + 1 ≤ j + m.1) hm
  have hg6 : goodAfter t q hq0 hlo j hj ≤ j + 6 := by omega
  unfold runEnd
  omega

/-- The quadrant cells with badness. -/
def badCells (t q : ℕ) : Finset ℕ :=
  (Finset.range (q / 2)).filter (fun j : ℕ => ¬ cellGood t q j)

/-- The set of run starts in the quadrant. -/
def runSet (t q : ℕ) : Finset ℕ :=
  (badCells t q).image (fun j : ℕ => runStart t q j)

/-- A bad quadrant cell's run start belongs to `runSet`. -/
lemma runStart_mem_runSet (t q : ℕ) {j : ℕ} (hj1 : j < q / 2) (hj2 : ¬ cellGood t q j) :
    runStart t q j ∈ runSet t q := by
  unfold runSet badCells
  rw [Finset.mem_image]
  refine ⟨j, ?_, rfl⟩
  simp [hj1, hj2]

/-- Membership in `runSet` means "a bad quadrant cell starts a run here". -/
lemma mem_runSet_iff (t q : ℕ) (s : ℕ) :
    s ∈ runSet t q ↔ ∃ j : ℕ, j < q / 2 ∧ ¬ cellGood t q j ∧ runStart t q j = s := by
  unfold runSet badCells
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_filter] at hj
    exact ⟨j, by simpa using hj.1, hj.2, rfl⟩
  · rintro ⟨j, hj1, hj2, hs⟩
    refine ⟨j, ?_, hs⟩
    rw [Finset.mem_filter]
    exact ⟨by simpa using hj1, hj2⟩

/-- Elements of `runSet` are quadrant cells. -/
lemma runSet_mem_lt (t q : ℕ) {s : ℕ} (hs : s ∈ runSet t q) : s < q / 2 := by
  rcases (mem_runSet_iff t q s).mp hs with ⟨j, hj1, hj2, hs'⟩
  rw [← hs']
  exact lt_of_le_of_lt (runStart_le t q j) hj1

/-- Elements of `runSet` are bad cells. -/
lemma runSet_mem_bad (t q : ℕ) {s : ℕ} (hs : s ∈ runSet t q) : ¬ cellGood t q s := by
  rcases (mem_runSet_iff t q s).mp hs with ⟨j, hj1, hj2, hs'⟩
  rw [← hs']
  exact runStart_bad t q hj2

/-- A run start is well away from the left edge. -/
lemma runSet_mem_ge (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s : ℕ} (hs : s ∈ runSet t q) : 1024 ≤ s :=
  bad_index_ge t q s ht hq0 hlo (runSet_mem_bad t q hs)

/-- The cell before a run start is good. -/
lemma runSet_left_good (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s : ℕ} (hs : s ∈ runSet t q) : cellGood t q (s - 1) := by
  rcases (mem_runSet_iff t q s).mp hs with ⟨j, hj1, hj2, hs'⟩
  subst s
  apply runStart_left_good t q hj2
  have hge : 1024 ≤ runStart t q j :=
    bad_index_ge t q (runStart t q j) ht hq0 hlo (runStart_bad t q hj2)
  omega

/-! ## 2. Positivity and the θ-x bridge -/

/-- `2T > 0`. -/
lemma twoT_pos (t : ℕ) : (0 : ℝ) < 2 * (Sec3H.T t : ℝ) := by
  have hT : (0 : ℝ) < (Sec3H.T t : ℝ) := T_pos_real t
  positivity

/-- `goodCellBound > 0`. -/
lemma goodCellBound_pos (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) : 0 < goodCellBound t q := by
  have hct : 0 < cellThresh t q := by
    unfold cellThresh
    have hη : 0 < eta t q := eta_pos t q hq0
    positivity
  have hsq : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  rw [goodCellBound_eq]
  positivity

/-- η = 2T · (π/q). -/
lemma eta_eq_twoT (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) :
    eta t q = 2 * (Sec3H.T t : ℝ) * (Real.pi / (q : ℝ)) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (q_pos_of_large q hq0))
  unfold eta
  field_simp [hq]

/-- `j·η = 2T·(j·π/q)`. -/
lemma eta_mul_cell (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (j : ℕ) :
    ((j : ℕ) : ℝ) * eta t q = 2 * (Sec3H.T t : ℝ) * (((j : ℕ) : ℝ) * Real.pi / (q : ℝ)) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (q_pos_of_large q hq0))
  rw [eta_eq_twoT t q hq0]
  field_simp [hq]

/-- x-cell `[jη,(j+1)η]` membership ↔ θ interval `[jπ/q,(j+1)π/q]`. -/
lemma theta_in_cell_iff (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) {j : ℕ} {θ : ℝ} :
    (2 * (Sec3H.T t : ℝ) * θ) ∈ cell t q j ↔
      θ ∈ Set.Icc (((j : ℕ) : ℝ) * Real.pi / (q : ℝ))
        ((((j + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ))) := by
  have h2T : (0 : ℝ) < 2 * (Sec3H.T t : ℝ) := twoT_pos t
  unfold cell
  have hm1 := eta_mul_cell t q hq0 j
  have hm2 := eta_mul_cell t q hq0 (j + 1)
  have hle1 : ((((j : ℕ) : ℝ) * eta t q ≤ 2 * (Sec3H.T t : ℝ) * θ) ↔
      (((j : ℕ) : ℝ) * Real.pi / (q : ℝ)) ≤ θ) := by
    rw [hm1]
    rw [mul_le_mul_iff_of_pos_left h2T]
  have hle2 : (2 * (Sec3H.T t : ℝ) * θ ≤ (((j + 1 : ℕ) : ℝ) * eta t q)) ↔
      θ ≤ (((j + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) := by
    rw [hm2]
    rw [mul_le_mul_iff_of_pos_left h2T]
  constructor
  · intro hx
    exact ⟨(hle1).1 hx.1, (hle2).1 hx.2⟩
  · intro hθ
    exact ⟨(hle1).2 hθ.1, (hle2).2 hθ.2⟩

/-- Every `x ∈ [0, Mη)` lies in one of the cells `0..M-1`. -/
lemma exists_cell_index (x η : ℝ) (hη : 0 < η) (hx0 : 0 ≤ x) {M : ℕ}
    (hxM : x < (M : ℝ) * η) : ∃ j : ℕ, j < M ∧
      (j : ℝ) * η ≤ x ∧ x ≤ ((j + 1 : ℕ) : ℝ) * η := by
  let f : ℤ := Int.floor (x / η)
  have hf0 : 0 ≤ f := (Int.floor_nonneg).2 (by positivity)
  let j : ℕ := f.toNat
  have hjc : (j : ℝ) = (f : ℝ) := by
    have hz : (j : ℤ) = f := by
      dsimp [j]
      exact Int.toNat_of_nonneg hf0
    exact_mod_cast hz
  refine ⟨j, ?_, ?_⟩
  · have hfj : (j : ℝ) ≤ x / η := by
      have h := Int.floor_le (x / η)
      rw [hjc]
      exact h
    have hxl : x / η < (M : ℝ) := (div_lt_iff₀ hη).mpr hxM
    have hjr : (j : ℝ) < (M : ℝ) := lt_of_le_of_lt hfj hxl
    exact_mod_cast hjr
  · constructor
    · have hfj : (j : ℝ) ≤ x / η := by
        have h := Int.floor_le (x / η)
        rw [hjc]
        exact h
      have hmul := mul_le_mul_of_nonneg_right hfj (le_of_lt hη)
      have hx : (x / η) * η = x := by field_simp [hη.ne']
      simpa [hx] using hmul
    · have hxlt : x / η < (f : ℝ) + 1 := Int.lt_floor_add_one (x / η)
      have hxj : x / η < (j : ℝ) + 1 := by
        rw [hjc]
        exact hxlt
      have hmul := mul_lt_mul_of_pos_right hxj hη
      have hx : (x / η) * η = x := by field_simp [hη.ne']
      have hmain : x < ((j : ℝ) + 1) * η := by
        rwa [hx] at hmul
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
      rw [hcast]
      exact le_of_lt hmain

/-! ## 3. The level crossing of each run -/

/-- Near `x = Tπ` the cosine is large (in the good-cell sense). -/
lemma abs_c_of_near_Tpi (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {θ : ℝ} (hx : |2 * (Sec3H.T t : ℝ) * θ - (Sec3H.T t : ℝ) * Real.pi| ≤ 1 / 8) :
    goodCellBound t q ≤ |c t θ| := by
  have hh := Sec3H.H_re_ge_half_near_Tpi t ht (2 * (Sec3H.T t : ℝ) * θ) hx
  have h1 := thresh_of_half hq0 hlo (2 * (Sec3H.T t : ℝ) * θ) hh
  exact abs_c_of_thresh h1

/-- Each bad run `[s,e]` (with good cell `e+1`) crosses the level `goodCellBound`:
there is `θ ∈ [sπ/q, (e+1)π/q] ∩ (0,π)` with `|c t θ| = goodCellBound t q`. -/
lemma run_level_point (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s e : ℕ} (hse : s ≤ e)
    (hbad : ∀ j : ℕ, s ≤ j → j ≤ e → ¬ cellGood t q j)
    (hgood : cellGood t q (e + 1)) (heq : e + 1 < q) :
    ∃ θ : ℝ, (s : ℝ) * Real.pi / (q : ℝ) ≤ θ ∧ θ ≤ ((e + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) ∧
      0 < θ ∧ θ < Real.pi ∧ |c t θ| = goodCellBound t q := by
  classical
  have h2T : (0 : ℝ) < 2 * (Sec3H.T t : ℝ) := twoT_pos t
  have h2T0 : (2 * (Sec3H.T t : ℝ)) ≠ 0 := ne_of_gt h2T
  have hT0 : (Sec3H.T t : ℝ) ≠ 0 := by
    intro hz
    exact h2T0 (by simp [hz])
  have hη0 : 0 < eta t q := eta_pos t q hq0
  have hq0r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (q_pos_of_large q hq0)
  have hbs : ¬ cellGood t q s := hbad s (Nat.le_refl s) hse
  have hs1 : 1 ≤ s := by
    have h1024 : 1024 ≤ s := bad_index_ge t q s ht hq0 hlo hbs
    omega
  -- a bad point inside cell s
  have hsmall : ∃ x : ℝ, x ∈ cell t q s ∧ |(Sec3H.H t x).re| < cellThresh t q := by
    by_contra hc
    push_neg at hc
    exact hbs hc
  rcases hsmall with ⟨x1, hx1c, hx1s⟩
  let θ1 : ℝ := x1 / (2 * (Sec3H.T t : ℝ))
  let θ2 : ℝ := ((e + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)
  have hx1' : 2 * (Sec3H.T t : ℝ) * θ1 = x1 := by
    dsimp [θ1]
    field_simp [h2T0, hT0]
  -- small cosine at θ1
  have hc1 : |c t θ1| < goodCellBound t q := by
    apply c_abs_lt_of_reH_lt
    rwa [hx1']
  -- large cosine at θ2 (the boundary point of the good cell e+1)
  have hx2 : 2 * (Sec3H.T t : ℝ) * θ2 = ((e + 1 : ℕ) : ℝ) * eta t q := by
    dsimp [θ2]
    rw [← eta_mul_cell t q hq0 (e + 1)]
  have hx2in : 2 * (Sec3H.T t : ℝ) * θ2 ∈ cell t q (e + 1) := by
    rw [hx2]
    unfold cell
    constructor
    · exact le_rfl
    · have hle : ((e + 1 : ℕ) : ℝ) ≤ (((e + 1) + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ (e + 1))
      exact mul_le_mul_of_nonneg_right hle (le_of_lt hη0)
  have hgood2 : cellThresh t q ≤ |(Sec3H.H t (2 * (Sec3H.T t : ℝ) * θ2)).re| :=
    hgood (2 * (Sec3H.T t : ℝ) * θ2) hx2in
  have hB2 : goodCellBound t q ≤ |c t θ2| := abs_c_of_thresh hgood2
  -- θ1 is inside the run arc, and θ1 ≤ θ2
  have hθ1lo : (s : ℝ) * Real.pi / (q : ℝ) ≤ θ1 := by
    have hm : (s : ℝ) * eta t q ≤ 2 * (Sec3H.T t : ℝ) * θ1 := by
      rw [hx1']
      exact hx1c.1
    have hm' : 2 * (Sec3H.T t : ℝ) * ((s : ℝ) * Real.pi / (q : ℝ)) ≤ 2 * (Sec3H.T t : ℝ) * θ1 := by
      rw [← eta_mul_cell t q hq0 s]
      exact hm
    exact le_of_mul_le_mul_left hm' h2T
  have hθ1hi : θ1 ≤ ((s + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) := by
    have hm : 2 * (Sec3H.T t : ℝ) * θ1 ≤ ((s + 1 : ℕ) : ℝ) * eta t q := by
      rw [hx1']
      exact hx1c.2
    have hm' : 2 * (Sec3H.T t : ℝ) * θ1 ≤ 2 * (Sec3H.T t : ℝ) * (((s + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) := by
      rw [← eta_mul_cell t q hq0 (s + 1)]
      exact hm
    exact le_of_mul_le_mul_left hm' h2T
  have hθ12 : θ1 ≤ θ2 := by
    have hle : (s + 1 : ℕ) ≤ e + 1 := by omega
    have hc : ((s + 1 : ℕ) : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := by exact_mod_cast hle
    have hπ' : ((s + 1 : ℕ) : ℝ) * Real.pi ≤ ((e + 1 : ℕ) : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hc Real.pi_pos.le
    have hπ'' : ((s + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) ≤ ((e + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) :=
      div_le_div_of_nonneg_right hπ' (le_of_lt hq0r)
    exact le_trans hθ1hi (by simpa [θ2] using hπ'')
  -- IVT between θ1 and θ2
  have hf : ContinuousOn (fun θ : ℝ => |c t θ|) (Set.Icc θ1 θ2) := (cont_abs_c t).continuousOn
  have hmem : goodCellBound t q ∈ Set.Icc (|c t θ1|) (|c t θ2|) := by
    constructor
    · exact le_of_lt hc1
    · exact hB2
  rcases (intermediate_value_Icc hθ12 hf hmem) with ⟨θ, hθ, hθeq⟩
  dsimp [θ2] at hθ
  -- assemble
  refine ⟨θ, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans hθ1lo hθ.1
  · exact hθ.2
  · have hθ1pos : 0 < (s : ℝ) * Real.pi / (q : ℝ) := by
      have hs : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
      positivity
    exact lt_of_lt_of_le hθ1pos (le_trans hθ1lo hθ.1)
  · have hθ2lt : ((e + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) < Real.pi := by
      have heq' : ((e + 1 : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast heq
      have hπ' : ((e + 1 : ℕ) : ℝ) * Real.pi < (q : ℝ) * Real.pi :=
        mul_lt_mul_of_pos_right heq' Real.pi_pos
      rw [div_lt_iff₀ hq0r]
      nlinarith
    exact lt_of_le_of_lt hθ.2 hθ2lt
  · simpa using hθeq

/-! ## 4. Bundled run info for members of `runSet` -/

/-- Total version of `runEnd` (returns `j` when `j` is good; used only at bad
run starts). -/
noncomputable def runEndT (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (j : ℕ) : ℕ :=
  if hj : ¬ cellGood t q j then runEnd t q hq0 hlo j hj else j

lemma runEndT_eq (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : runEndT t q hq0 hlo j = runEnd t q hq0 hlo j hj := by
  unfold runEndT
  rw [dif_pos hj]

lemma runEndT_ge (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : j ≤ runEndT t q hq0 hlo j := by
  rw [runEndT_eq t q hq0 hlo hj]
  exact runEnd_ge t q hq0 hlo hj

lemma runEndT_spec (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) :
    (∀ k : ℕ, j ≤ k → k ≤ runEndT t q hq0 hlo j → ¬ cellGood t q k) ∧
      cellGood t q (runEndT t q hq0 hlo j + 1) := by
  rw [runEndT_eq t q hq0 hlo hj]
  exact runEnd_spec t q hq0 hlo hj

lemma runEndT_len (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : runEndT t q hq0 hlo j ≤ j + 5 := by
  rw [runEndT_eq t q hq0 hlo hj]
  exact runEnd_len t q hq0 hlo hj

/-- The run end of a quadrant run start stays inside the quadrant. -/
lemma runEndT_lt_half (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s : ℕ} (hs : s ∈ runSet t q) : runEndT t q hq0 hlo s < q / 2 := by
  have hsBad := runSet_mem_bad t q hs
  have hsLt := runSet_mem_lt t q hs
  have hfr := bad_far_from_q2 t q s ht hq0 hlo hsBad hsLt
  have hlen := runEndT_len t q hq0 hlo hsBad
  omega

/-- Far-right bound for the whole run: `2(e+1)+200 ≤ q`. -/
lemma runEndT_far_right (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s : ℕ} (hs : s ∈ runSet t q) : 2 * (runEndT t q hq0 hlo s + 1) + 200 ≤ q := by
  have hsBad := runSet_mem_bad t q hs
  have he := runEndT_spec t q hq0 hlo hsBad
  have heLt := runEndT_lt_half t q ht hq0 hlo hs
  have heBad : ¬ cellGood t q (runEndT t q hq0 hlo s) :=
    he.1 (runEndT t q hq0 hlo s) (runEndT_ge t q hq0 hlo hsBad) (Nat.le_refl _)
  exact far_right_of_bad t q (runEndT t q hq0 hlo s) ht hq0 hlo heBad heLt

/-- Far-left bound for the whole run. -/
lemma runStart_ge_100 (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s : ℕ} (hs : s ∈ runSet t q) : (100 : ℤ) ≤ (s : ℤ) := by
  have h1024 : 1024 ≤ s := runSet_mem_ge t q ht hq0 hlo hs
  omega

/-- Distinct runs are separated by at least one good cell: the run from `s1`
ends strictly before the next run starts at `s2`. -/
lemma runSet_sep (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {s1 s2 : ℕ} (hs1 : s1 ∈ runSet t q) (hs2 : s2 ∈ runSet t q) (hlt : s1 < s2) :
    runEndT t q hq0 hlo s1 + 1 < s2 := by
  have hb1 := runSet_mem_bad t q hs1
  have hb2 := runSet_mem_bad t q hs2
  have he := runEndT_spec t q hq0 hlo hb1
  have hgl : cellGood t q (s2 - 1) := runSet_left_good t q ht hq0 hlo hs2
  have hs2ge : 1 ≤ s2 := by
    have h1024 : 1024 ≤ s2 := bad_index_ge t q s2 ht hq0 hlo hb2
    omega
  by_contra h
  have hs2le : s2 ≤ runEndT t q hq0 hlo s1 + 1 := by omega
  by_cases hs2e : s2 ≤ runEndT t q hq0 hlo s1
  · have hs1m : s1 ≤ s2 - 1 := by omega
    have hem : s2 - 1 ≤ runEndT t q hq0 hlo s1 := by omega
    exact (he.1 (s2 - 1) hs1m hem) hgl
  · have hs2eq : s2 = runEndT t q hq0 hlo s1 + 1 := by omega
    have hg : cellGood t q s2 := by
      rw [hs2eq]
      exact he.2
    exact hb2 hg

/-- The level point of a run in the quadrant. -/
lemma run_level_point_of_set (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q)
    (hlo : 2 ^ 43 * m_t t ≤ q) (s : ℕ) (hs : s ∈ runSet t q) :
    ∃ θ : ℝ,
      (s : ℝ) * Real.pi / (q : ℝ) ≤ θ ∧
      θ ≤ (((runEndT t q hq0 hlo s) + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) ∧
      0 < θ ∧ θ < Real.pi ∧ |c t θ| = goodCellBound t q := by
  let e := runEndT t q hq0 hlo s
  have hsBad := runSet_mem_bad t q hs
  have hege : s ≤ e := runEndT_ge t q hq0 hlo hsBad
  have hespec := runEndT_spec t q hq0 hlo hsBad
  have heq : e + 1 < q := by
    have hfr := runEndT_far_right t q ht hq0 hlo hs
    have hq1 : 1 ≤ q := q_large_pos q hq0
    omega
  rcases run_level_point t q ht hq0 hlo hege hespec.1 hespec.2 heq with ⟨θ, h1, h2, h3, h4, h5⟩
  exact ⟨θ, h1, by simpa [e] using h2, h3, h4, h5⟩


/-! ## 5. The number of runs is `≤ 4·m_t t` (via level crossings) -/

/-- The level points of distinct runs are distinct (runs are separated). -/
lemma runSet_lp_injective (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    (lp : ℕ → ℝ)
    (hlp_ge : ∀ {s : ℕ}, s ∈ runSet t q → (s : ℝ) * Real.pi / (q : ℝ) ≤ lp s)
    (hlp_le : ∀ {s : ℕ}, s ∈ runSet t q → lp s ≤
      (((runEndT t q hq0 hlo s) + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) :
    ∀ {s1 : ℕ}, s1 ∈ runSet t q → ∀ {s2 : ℕ}, s2 ∈ runSet t q →
      lp s1 = lp s2 → s1 = s2 := by
  classical
  intro s1 hs1 s2 hs2 h
  by_contra hne
  have hq0r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (q_pos_of_large q hq0)
  have hlt : s1 < s2 ∨ s2 < s1 := lt_or_gt_of_ne hne
  rcases hlt with h12 | h21
  · have hsep := runSet_sep t q ht hq0 hlo hs1 hs2 h12
    have hsep' : ((runEndT t q hq0 hlo s1 + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) <
        (s2 : ℝ) * Real.pi / (q : ℝ) := by
      have hc : ((runEndT t q hq0 hlo s1 + 1 : ℕ) : ℝ) < (s2 : ℝ) := by exact_mod_cast hsep
      have hπ : ((runEndT t q hq0 hlo s1 + 1 : ℕ) : ℝ) * Real.pi < (s2 : ℝ) * Real.pi :=
        mul_lt_mul_of_pos_right hc Real.pi_pos
      exact div_lt_div_of_pos_right hπ hq0r
    have hl : lp s1 < lp s2 :=
      lt_of_le_of_lt (hlp_le hs1) (lt_of_lt_of_le hsep' (hlp_ge hs2))
    rw [h] at hl
    exact (lt_irrefl (lp s2)) hl
  · have hsep := runSet_sep t q ht hq0 hlo hs2 hs1 h21
    have hsep' : ((runEndT t q hq0 hlo s2 + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) <
        (s1 : ℝ) * Real.pi / (q : ℝ) := by
      have hc : ((runEndT t q hq0 hlo s2 + 1 : ℕ) : ℝ) < (s1 : ℝ) := by exact_mod_cast hsep
      have hπ : ((runEndT t q hq0 hlo s2 + 1 : ℕ) : ℝ) * Real.pi < (s1 : ℝ) * Real.pi :=
        mul_lt_mul_of_pos_right hc Real.pi_pos
      exact div_lt_div_of_pos_right hπ hq0r
    have hl : lp s2 < lp s1 :=
      lt_of_le_of_lt (hlp_le hs2) (lt_of_lt_of_le hsep' (hlp_ge hs1))
    rw [← h] at hl
    exact (lt_irrefl (lp s1)) hl

/-- The quadrant has at most `4·m_t t` bad runs. -/
lemma runSet_card_le (t q : ℕ) (ht : Odd t) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    (runSet t q).card ≤ 4 * m_t t := by
  classical
  let S : Finset ℕ := runSet t q
  let B : ℝ := goodCellBound t q
  let lp : ℕ → ℝ := fun s => if hs : s ∈ S then
      Classical.choose (run_level_point_of_set t q ht hq0 hlo s hs) else 0
  have lp_ge : ∀ {s : ℕ}, (hs : s ∈ S) → (s : ℝ) * Real.pi / (q : ℝ) ≤ lp s := by
    intro s hs
    unfold lp
    rw [dif_pos hs]
    exact (Classical.choose_spec (run_level_point_of_set t q ht hq0 hlo s hs)).1
  have lp_le : ∀ {s : ℕ}, (hs : s ∈ S) → lp s ≤
      (((runEndT t q hq0 hlo s) + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ) := by
    intro s hs
    unfold lp
    rw [dif_pos hs]
    exact (Classical.choose_spec (run_level_point_of_set t q ht hq0 hlo s hs)).2.1
  have lp_pos : ∀ {s : ℕ}, (hs : s ∈ S) → 0 < lp s := by
    intro s hs
    unfold lp
    rw [dif_pos hs]
    exact (Classical.choose_spec (run_level_point_of_set t q ht hq0 hlo s hs)).2.2.1
  have lp_pi : ∀ {s : ℕ}, (hs : s ∈ S) → lp s < Real.pi := by
    intro s hs
    unfold lp
    rw [dif_pos hs]
    exact (Classical.choose_spec (run_level_point_of_set t q ht hq0 hlo s hs)).2.2.2.1
  have lp_abs : ∀ {s : ℕ}, (hs : s ∈ S) → |c t (lp s)| = B := by
    intro s hs
    unfold lp
    rw [dif_pos hs]
    exact (Classical.choose_spec (run_level_point_of_set t q ht hq0 hlo s hs)).2.2.2.2
  have lp_inj : ∀ {s1 : ℕ}, s1 ∈ S → ∀ {s2 : ℕ}, s2 ∈ S → lp s1 = lp s2 → s1 = s2 := by
    intro s1 hs1 s2 hs2 h
    exact runSet_lp_injective t q ht hq0 hlo lp (fun {s} hs => lp_ge hs) (fun {s} hs => lp_le hs) hs1 hs2 h
  let posRuns : Finset ℕ := S.filter (fun s => c t (lp s) = B)
  let negRuns : Finset ℕ := S.filter (fun s => c t (lp s) = -B)
  -- S ⊆ posRuns ∪ negRuns
  have hcov : S ⊆ posRuns ∪ negRuns := by
    intro s hs
    have habs := lp_abs hs
    rcases eq_or_eq_neg_of_abs_eq habs with hp | hn
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hs, hp⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hs, hn⟩))
  have hposle : posRuns.card ≤ 2 * m_t t := by
    let img : Finset ℝ := posRuns.image lp
    have hinj : (posRuns.image lp).card = posRuns.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb h
      exact lp_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h
    have hmem : ∀ θ : ℝ, θ ∈ img → θ ∈ Set.Ioo 0 Real.pi := by
      intro θ hθ
      rcases Finset.mem_image.mp hθ with ⟨s, hs, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp hs).1
      exact ⟨lp_pos hsS, lp_pi hsS⟩
    have hz : ∀ θ : ℝ, θ ∈ img → c t θ = B := by
      intro θ hθ
      rcases Finset.mem_image.mp hθ with ⟨s, hs, rfl⟩
      exact (Finset.mem_filter.mp hs).2
    have hcount := zero_count t B img hmem hz
    rw [← hinj]
    exact hcount
  have hnegle : negRuns.card ≤ 2 * m_t t := by
    let img : Finset ℝ := negRuns.image lp
    have hinj : (negRuns.image lp).card = negRuns.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb h
      exact lp_inj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h
    have hmem : ∀ θ : ℝ, θ ∈ img → θ ∈ Set.Ioo 0 Real.pi := by
      intro θ hθ
      rcases Finset.mem_image.mp hθ with ⟨s, hs, rfl⟩
      have hsS : s ∈ S := (Finset.mem_filter.mp hs).1
      exact ⟨lp_pos hsS, lp_pi hsS⟩
    have hz : ∀ θ : ℝ, θ ∈ img → c t θ = -B := by
      intro θ hθ
      rcases Finset.mem_image.mp hθ with ⟨s, hs, rfl⟩
      exact (Finset.mem_filter.mp hs).2
    have hcount := zero_count t (-B) img hmem hz
    rw [← hinj]
    exact hcount
  calc
    S.card ≤ (posRuns ∪ negRuns).card := Finset.card_le_card hcov
    _ ≤ posRuns.card + negRuns.card := Finset.card_union_le posRuns negRuns
    _ ≤ 2 * m_t t + 2 * m_t t := Nat.add_le_add hposle hnegle
    _ = 4 * m_t t := by ring

/-- A bad cell `j` is covered by its run: `j ≤ runEnd (runStart j)`. -/
lemma runStart_le_end (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q)
    {j : ℕ} (hj : ¬ cellGood t q j) : j ≤ runEndT t q hq0 hlo (runStart t q j) := by
  have hbstart : ¬ cellGood t q (runStart t q j) := runStart_bad t q hj
  have hspec := runStart_spec t q hj
  have hg1 : runStart t q j + 1 ≤ goodAfter t q hq0 hlo (runStart t q j) hbstart :=
    (goodAfter_spec t q hq0 hlo hbstart).1
  have hg2 : cellGood t q (goodAfter t q hq0 hlo (runStart t q j) hbstart) :=
    (goodAfter_spec t q hq0 hlo hbstart).2
  by_contra h
  have hgleq : goodAfter t q hq0 hlo (runStart t q j) hbstart ≤ j := by
    unfold runEndT at h
    rw [dif_pos hbstart] at h
    unfold runEnd at h
    omega
  have hgmem : runStart t q j ≤ goodAfter t q hq0 hlo (runStart t q j) hbstart := by omega
  exact (hspec.2 (goodAfter t q hq0 hlo (runStart t q j) hbstart) hgmem hgleq) hg2


/-! ## 6. The grid interval of a run -/

/-- The `θ`-grid interval `[s·π/q, (e(s)+1)·π/q]` of a run starting at `s`. -/
noncomputable def runGrid (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    (s : ℕ) (hs : s ∈ runSet t q) : Family.Grid q :=
  Family.Grid.mk (p := (s : ℤ))
    (q := ((runEndT t q hq0 hlo s + 1 : ℕ) : ℤ))
    (by omega)
    (by
      have hb := runSet_mem_bad t q hs
      have hge := runEndT_ge t q hq0 hlo hb
      have hz : (s : ℤ) ≤ ((runEndT t q hq0 hlo s : ℕ) : ℤ) := by exact_mod_cast hge
      omega)

/-- The run interval is short (`len ≤ 6`). -/
lemma runGrid_len_le (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    {s : ℕ} (hs : s ∈ runSet t q) : (runGrid t q hq0 hlo ht s hs).len ≤ 6 := by
  have hb := runSet_mem_bad t q hs
  have hlen := runEndT_len t q hq0 hlo hb
  change ((runEndT t q hq0 hlo s + 1 : ℕ) : ℤ) - (s : ℤ) ≤ 6
  have hz : ((runEndT t q hq0 hlo s : ℕ) : ℤ) ≤ ((s + 5 : ℕ) : ℤ) := by exact_mod_cast hlen
  omega

/-- The run interval is far from `0`. -/
lemma runGrid_far_left (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    {s : ℕ} (hs : s ∈ runSet t q) : (100 : ℤ) ≤ (runGrid t q hq0 hlo ht s hs).p := by
  have h1024 : 1024 ≤ s := runSet_mem_ge t q ht hq0 hlo hs
  change (100 : ℤ) ≤ (s : ℤ)
  omega

/-- The run interval is far from `π/2`. -/
lemma runGrid_far_right (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    {s : ℕ} (hs : s ∈ runSet t q) : 2 * (runGrid t q hq0 hlo ht s hs).q + 200 ≤ (q : ℤ) := by
  have hfr := runEndT_far_right t q ht hq0 hlo hs
  change 2 * ((runEndT t q hq0 hlo s + 1 : ℕ) : ℤ) + 200 ≤ (q : ℤ)
  have hz : (((2 * (runEndT t q hq0 hlo s + 1) + 200 : ℕ) : ℕ) : ℤ) ≤ (q : ℤ) := by
    exact_mod_cast hfr
  omega

/-- Run intervals of different runs are ordered & disjoint. -/
lemma runGrid_sep (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    {s1 s2 : ℕ} (hs1 : s1 ∈ runSet t q) (hs2 : s2 ∈ runSet t q) (hlt : s1 < s2) :
    (runGrid t q hq0 hlo ht s1 hs1).q < (runGrid t q hq0 hlo ht s2 hs2).p := by
  have hsep := runSet_sep t q ht hq0 hlo hs1 hs2 hlt
  change (((runEndT t q hq0 hlo s1 + 1 : ℕ) : ℕ) : ℤ) < (s2 : ℤ)
  have hz : (((runEndT t q hq0 hlo s1 + 1 : ℕ) : ℕ) : ℤ) < (s2 : ℤ) := by exact_mod_cast hsep
  exact hz


/-- The lo/hi endpoints of a run grid interval. -/
lemma runGrid_lo_hi (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) (ht : Odd t)
    {s : ℕ} (hs : s ∈ runSet t q) :
    Family.Grid.lo (runGrid t q hq0 hlo ht s hs) = (s : ℝ) * Real.pi / (q : ℝ) ∧
    Family.Grid.hi (runGrid t q hq0 hlo ht s hs) =
      (((runEndT t q hq0 hlo s + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) := by
  unfold runGrid Family.Grid.lo Family.Grid.hi
  constructor <;> norm_num

/-- The last cell bound: `Mη ≥ Tπ - η` where `M = q/2`. -/
lemma Tpi_le_M_eta (t q : ℕ) (hq0 : 2 ^ 400 ≤ q) :
    (Sec3H.T t : ℝ) * Real.pi ≤ ((q / 2 : ℕ) : ℝ) * eta t q + eta t q := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (q_pos_of_large q hq0))
  have hle_nat : q ≤ 2 * (q / 2) + 2 := by omega
  have hle_nat' : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast (by omega : q ≤ 2 * (q / 2) + 2)
  have hTpi : (Sec3H.T t : ℝ) * Real.pi = ((q : ℝ) / 2) * eta t q := by
    rw [eta_eq_twoT t q hq0]
    field_simp [hq]
  rw [hTpi]
  have hη0 : 0 ≤ eta t q := le_of_lt (eta_pos t q hq0)
  have hd0 : (q : ℝ) / 2 - ((q / 2 : ℕ) : ℝ) ≤ 1 := by nlinarith
  have hd : ((q : ℝ) / 2 - ((q / 2 : ℕ) : ℝ)) * eta t q ≤ eta t q := by
    simpa [one_mul] using (mul_le_mul_of_nonneg_right hd0 hη0)
  have hsplit : ((q : ℝ) / 2) * eta t q =
      ((q / 2 : ℕ) : ℝ) * eta t q + ((q : ℝ) / 2 - ((q / 2 : ℕ) : ℝ)) * eta t q := by ring
  rw [hsplit]
  exact add_le_add_right hd (((q / 2 : ℕ) : ℝ) * eta t q)

/-- Theorem 2.3 (quadrant), core: existence of the bad-run family with count and
coverage bounds (the `hhi` bound of the paper is not needed for the construction). -/
theorem family_core (t q : ℕ) (ht : Odd t)
    (hq0 : 2 ^ 400 ≤ q) (hlo : 2 ^ 43 * m_t t ≤ q) :
    ∃ (N : ℕ) (F : Family.Quad q N),
      (N : ℝ) ≤ (q : ℝ) / 2 ^ 41 ∧
      (∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
        θ ∈ F.union ∨ goodCellBound t q ≤ |c t θ|) := by
  classical
  let S : Finset ℕ := runSet t q
  let N : ℕ := S.card
  let eRun : ℕ → ℕ := runEndT t q hq0 hlo
  let iso := Finset.orderIsoOfFin S (by rfl : S.card = N)
  let sOf : Fin N → ℕ := fun i => (iso i).1
  have hsOf : ∀ i : Fin N, sOf i ∈ S := by
    intro i
    exact (iso i).2
  let arc : Fin N → Family.Grid q := fun i => runGrid t q hq0 hlo ht (sOf i) (hsOf i)
  -- (a) count bound
  have hNle : (N : ℝ) ≤ (q : ℝ) / 2 ^ 41 := by
    have hcard := runSet_card_le t q ht hq0 hlo
    have h4m : (4 : ℝ) * (m_t t : ℝ) ≤ (q : ℝ) / (2 : ℝ) ^ 41 := by
      have h43 : (2 : ℝ) ^ 43 = 4 * (2 : ℝ) ^ 41 := by
        rw [show (43 : ℕ) = 41 + 2 by norm_num, pow_add]
        norm_num
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 41)]
      have hb : ((4 * (m_t t : ℝ)) * (2 : ℝ) ^ 41) = ((2 : ℝ) ^ 43) * (m_t t : ℝ) := by
        rw [h43]
        ring
      rw [hb]
      have hq43 : (2 : ℝ) ^ 43 * (m_t t : ℝ) ≤ (q : ℝ) := by
        have h1 : (((2 ^ 43 * m_t t : ℕ)) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlo
        have h2 : ((2 ^ 43 * m_t t : ℕ) : ℝ) = (2 : ℝ) ^ 43 * (m_t t : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow]
          norm_num
        rw [h2] at h1
        exact h1
      exact hq43
    have hcast : (N : ℝ) ≤ (4 : ℝ) * (m_t t : ℝ) := by
      have hn : N ≤ 4 * m_t t := by
        dsimp [N, S]
        exact hcard
      exact_mod_cast hn
    exact le_trans hcast h4m
  -- (b) quad axioms
  have hlen_le : ∀ i : Fin N, (arc i).len ≤ 6 := by
    intro i
    dsimp [arc]
    exact runGrid_len_le t q hq0 hlo ht (hsOf i)
  have hfar_left : ∀ i : Fin N, (100 : ℤ) ≤ (arc i).p := by
    intro i
    dsimp [arc]
    exact runGrid_far_left t q hq0 hlo ht (hsOf i)
  have hfar_right : ∀ i : Fin N, 2 * (arc i).q + 200 ≤ (q : ℤ) := by
    intro i
    dsimp [arc]
    exact runGrid_far_right t q hq0 hlo ht (hsOf i)
  have sOf_inj : Function.Injective sOf := by
    intro i j h
    have hsub : iso i = iso j := by
      apply Subtype.ext
      exact h
    exact iso.injective hsub
  have hsep : ∀ i j : Fin N, i ≠ j → (arc i).q < (arc j).p ∨ (arc j).q < (arc i).p := by
    intro i j hij
    have hne : sOf i ≠ sOf j := by
      intro h
      exact hij (sOf_inj h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      dsimp [arc]
      exact runGrid_sep t q hq0 hlo ht (hsOf i) (hsOf j) hlt
    · right
      dsimp [arc]
      exact runGrid_sep t q hq0 hlo ht (hsOf j) (hsOf i) hgt
  have hinj : Function.Injective arc := by
    intro i j heq
    by_contra hij
    rcases hsep i j hij with h1 | h2
    · have hq : (arc i).q < (arc j).p := h1
      have hp : (arc j).p = (arc i).p := by rw [heq]
      have hltp : (arc i).p < (arc i).q := (arc i).hlt
      rw [← hp] at hltp
      exact (lt_asymm hq) hltp
    · have hq : (arc j).q < (arc i).p := h2
      have hp : (arc i).p = (arc j).p := by rw [heq]
      have hltp : (arc j).p < (arc j).q := (arc j).hlt
      rw [← hp] at hltp
      exact (lt_asymm hq) hltp
  let F : Family.Quad q N :=
    { arc := arc
      inj := hinj
      len_le := hlen_le
      far_left := hfar_left
      far_right := hfar_right
      sep := hsep }
  -- (c) coverage
  have hcov : ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
      θ ∈ F.union ∨ goodCellBound t q ≤ |c t θ| := by
    intro θ hθ
    let x : ℝ := 2 * (Sec3H.T t : ℝ) * θ
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (Sec3.T_pos_real t))) hθ.1
    have hxT : x ≤ (Sec3H.T t : ℝ) * Real.pi := by
      have h2T0 : 0 ≤ 2 * (Sec3H.T t : ℝ) := le_of_lt (twoT_pos t)
      have hm := mul_le_mul_of_nonneg_left hθ.2 h2T0
      dsimp [x]
      calc
        2 * (Sec3H.T t : ℝ) * θ ≤ 2 * (Sec3H.T t : ℝ) * (Real.pi / 2) := hm
        _ = (Sec3H.T t : ℝ) * Real.pi := by ring
    by_cases hnear : |x - (Sec3H.T t : ℝ) * Real.pi| ≤ 1 / 8
    · right
      dsimp [x] at hnear
      exact abs_c_of_near_Tpi t q ht hq0 hlo hnear
    · have hxsub : x < (Sec3H.T t : ℝ) * Real.pi - 1 / 8 := by
        have hgt : 1 / 8 < |x - (Sec3H.T t : ℝ) * Real.pi| := by
          exact lt_of_not_ge hnear
        have habs : |x - (Sec3H.T t : ℝ) * Real.pi| = (Sec3H.T t : ℝ) * Real.pi - x := by
          rw [abs_sub_comm]
          rw [abs_of_nonneg (sub_nonneg.mpr hxT)]
        rw [habs] at hgt
        linarith
      let M : ℕ := q / 2
      have hMbound : (Sec3H.T t : ℝ) * Real.pi - 1 / 8 ≤ (M : ℝ) * eta t q := by
        have hb1 := Tpi_le_M_eta t q hq0
        have hη18 : eta t q ≤ 1 / 8 := by
          have h1 := eta_le_2n13 t q hq0 hlo
          nlinarith
        dsimp [M]
        nlinarith
      have hxM : x < (M : ℝ) * eta t q := lt_of_lt_of_le hxsub hMbound
      rcases exists_cell_index x (eta t q) (eta_pos t q hq0) hx0 hxM with ⟨j, hjM, hj1, hj2⟩
      have hxcell : x ∈ cell t q j := by
        unfold cell
        exact ⟨hj1, hj2⟩
      by_cases hgood : cellGood t q j
      · right
        have hxcell' : 2 * (Sec3H.T t : ℝ) * θ ∈ cell t q j := by
          simpa [x] using hxcell
        exact abs_c_of_thresh (hgood (2 * (Sec3H.T t : ℝ) * θ) hxcell')
      · left
        -- j is bad in the quadrant; it belongs to the run starting at sj
        let sj : ℕ := runStart t q j
        have hsjsj : sj ∈ S := by
          dsimp [S, sj]
          exact runStart_mem_runSet t q hjM hgood
        have hslej : sj ≤ j := by
          dsimp [sj]
          exact runStart_le t q j
        have hje : j ≤ eRun sj := by
          dsimp [eRun, sj]
          exact runStart_le_end t q hq0 hlo hgood
        have hθcell : θ ∈ Set.Icc (((j : ℕ) : ℝ) * Real.pi / (q : ℝ))
            ((((j + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ))) := by
          have hxdef : 2 * (Sec3H.T t : ℝ) * θ ∈ cell t q j := by
            simpa [x] using hxcell
          exact (theta_in_cell_iff t q hq0 (j := j) (θ := θ)).mp hxdef
        have hθ1 : (sj : ℝ) * Real.pi / (q : ℝ) ≤ θ := by
          have hjlo : ((j : ℕ) : ℝ) * Real.pi / (q : ℝ) ≤ θ := hθcell.1
          have hc : (sj : ℝ) ≤ (j : ℝ) := by exact_mod_cast hslej
          have hπ : (sj : ℝ) * Real.pi ≤ (j : ℝ) * Real.pi :=
            mul_le_mul_of_nonneg_right hc Real.pi_pos.le
          have hqpos : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (by exact_mod_cast (q_pos_of_large q hq0) : (0 : ℝ) < (q : ℝ))
          exact le_trans (div_le_div_of_nonneg_right hπ hqpos) hjlo
        have hθ2 : θ ≤ (((eRun sj + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) := by
          have hjhi : θ ≤ (((j + 1 : ℕ) : ℝ) * Real.pi / (q : ℝ)) := hθcell.2
          have hc : ((j + 1 : ℕ) : ℝ) ≤ (((eRun sj + 1 : ℕ) : ℝ)) := by
            exact_mod_cast (Nat.succ_le_succ hje)
          have hπ : ((j + 1 : ℕ) : ℝ) * Real.pi ≤ ((eRun sj + 1 : ℕ) : ℝ) * Real.pi :=
            mul_le_mul_of_nonneg_right hc Real.pi_pos.le
          have hqpos : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (by exact_mod_cast (q_pos_of_large q hq0) : (0 : ℝ) < (q : ℝ))
          exact le_trans hjhi (div_le_div_of_nonneg_right hπ hqpos)
        let i0 : Fin N := iso.symm ⟨sj, hsjsj⟩
        have hiso : iso i0 = ⟨sj, hsjsj⟩ := iso.apply_symm_apply ⟨sj, hsjsj⟩
        have hsOfi0 : sOf i0 = sj := by
          dsimp [sOf]
          rw [hiso]
        rw [Family.Quad.union_def]
        refine ⟨i0, ?_⟩
        have hlo0 := (runGrid_lo_hi t q hq0 hlo ht (hsOf i0)).1
        have hhi0 := (runGrid_lo_hi t q hq0 hlo ht (hsOf i0)).2
        constructor
        · dsimp [F, arc] at hlo0 ⊢
          rw [hlo0]
          rw [hsOfi0]
          exact hθ1
        · dsimp [F, arc] at hhi0 ⊢
          rw [hhi0]
          rw [hsOfi0]
          dsimp [eRun] at hθ2
          exact hθ2
  exact ⟨N, F, hNle, hcov⟩


end Sec3
end Submission
