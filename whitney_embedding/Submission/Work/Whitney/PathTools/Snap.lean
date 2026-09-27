import Submission.Work.Whitney.PathTools.GridGeom2

/-!
# Snapping a path to the grid

A path in the plane staying at positive distance from a set `S` can be followed by a grid chain of
mesh `h` much smaller than that distance: the chain's edges have their closed segments disjoint
from `S`.
-/

namespace Work.Whitney.PathTools.Grid

noncomputable section

open scoped BigOperators Topology
open Filter Set

set_option maxHeartbeats 800000

/-- Test: rewriting a vertex identity inside an `if`-condition. -/
example (a b : ℤ × ℤ) (hab : a = b) (x : ℤ × ℤ) :
    (if x = a then (1 : ZMod 2) else 0) = (if x = b then 1 else 0) := by
  rw [hab]

/-! ## Runs -/

/-- The chain of a run of `m` unit steps to the right starting at `(i,j)`. -/
def hRun (i j : ℤ) : ℕ → Chain1
  | 0 => 0
  | (m + 1) => hRun i j m + eChain (true, i + (m : ℤ), j)

/-- The chain of a run of `m` unit steps upwards starting at `(i,j)`. -/
def vRun (i j : ℤ) : ℕ → Chain1
  | 0 => 0
  | (m + 1) => vRun i j m + eChain (false, i, j + (m : ℤ))

lemma hRun_eq_succ (i j : ℤ) (m : ℕ) :
    hRun i j (m + 1) = hRun i j m + eChain (true, i + (m : ℤ), j) := rfl

lemma vRun_eq_succ (i j : ℤ) (m : ℕ) :
    vRun i j (m + 1) = vRun i j m + eChain (false, i, j + (m : ℤ)) := rfl

lemma hRun_zero_bdry (i j : ℤ) (x : ℤ × ℤ) :
    bdry1 ((hRun i j 0 : Chain1) : Edge → ZMod 2) x = 0 := by
  rw [show hRun i j 0 = (0 : Chain1) from rfl]
  rw [show ((0 : Chain1) : Edge → ZMod 2) = 0 from Finsupp.coe_zero]
  obtain ⟨a, b⟩ := x
  simp [bdry1]

lemma vRun_zero_bdry (i j : ℤ) (x : ℤ × ℤ) :
    bdry1 ((vRun i j 0 : Chain1) : Edge → ZMod 2) x = 0 := by
  rw [show vRun i j 0 = (0 : Chain1) from rfl]
  rw [show ((0 : Chain1) : Edge → ZMod 2) = 0 from Finsupp.coe_zero]
  obtain ⟨a, b⟩ := x
  simp [bdry1]

lemma hRun_bdry (i j : ℤ) (m : ℕ) (x : ℤ × ℤ) :
    bdry1 ((hRun i j m : Chain1) : Edge → ZMod 2) x
      = (if x = (i, j) then 1 else 0) + (if x = (i + (m : ℤ), j) then 1 else 0) := by
  induction m with
  | zero =>
      rw [hRun_zero_bdry, show (((i + (((0 : ℕ) : ℤ)) : ℤ), j) : ℤ × ℤ) = (i, j) from by
        norm_num]
      exact (CharTwo.add_self_eq_zero _).symm
  | succ m ih =>
      rw [hRun_eq_succ i j m, Finsupp.coe_add, bdry1_add, Pi.add_apply, ih, bdry1_eChain]
      rw [show (((i + (((m + 1 : ℕ)) : ℤ)), j) : ℤ × ℤ) = ((i + (m : ℤ)) + 1, j) from by
        congr 1; push_cast; ring]
      exact add_pair_eq (i, j) (i + (m : ℤ), j) ((i + (m : ℤ)) + 1, j) x

lemma vRun_bdry (i j : ℤ) (m : ℕ) (x : ℤ × ℤ) :
    bdry1 ((vRun i j m : Chain1) : Edge → ZMod 2) x
      = (if x = (i, j) then 1 else 0) + (if x = (i, j + (m : ℤ)) then 1 else 0) := by
  induction m with
  | zero =>
      rw [vRun_zero_bdry, show (((i, j + (((0 : ℕ) : ℤ))) : ℤ × ℤ)) = (i, j) from by
        norm_num]
      exact (CharTwo.add_self_eq_zero _).symm
  | succ m ih =>
      rw [vRun_eq_succ i j m, Finsupp.coe_add, bdry1_add, Pi.add_apply, ih, bdry1_eChain]
      rw [show (((i, j + (((m + 1 : ℕ)) : ℤ))) : ℤ × ℤ) = (i, (j + (m : ℤ)) + 1) from by
        congr 1; push_cast; ring]
      exact add_pair_eq (i, j) (i, j + (m : ℤ)) (i, (j + (m : ℤ)) + 1) x

lemma hRun_support {i j : ℤ} {m : ℕ} {e : Edge} (he : e ∈ (hRun i j m).support) :
    ∃ k : ℕ, k < m ∧ e = (true, i + (k : ℤ), j) := by
  induction m with
  | zero =>
      rw [show hRun i j 0 = (0 : Chain1) from rfl, Finsupp.support_zero] at he
      exact absurd he (Finset.notMem_empty e)
  | succ m ih =>
      rw [hRun_eq_succ] at he
      rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
      · obtain ⟨k, hk, hke⟩ := ih h
        exact ⟨k, by omega, hke⟩
      · have hke : e = (true, i + (m : ℤ), j) := by
          have := Finsupp.support_single_subset (a := (true, i + (m : ℤ), j))
            (b := (1 : ZMod 2)) h
          rw [Finset.mem_singleton] at this
          simpa only [eChain] using this
        exact ⟨m, by omega, hke⟩

lemma vRun_support {i j : ℤ} {m : ℕ} {e : Edge} (he : e ∈ (vRun i j m).support) :
    ∃ k : ℕ, k < m ∧ e = (false, i, j + (k : ℤ)) := by
  induction m with
  | zero =>
      rw [show vRun i j 0 = (0 : Chain1) from rfl, Finsupp.support_zero] at he
      exact absurd he (Finset.notMem_empty e)
  | succ m ih =>
      rw [vRun_eq_succ] at he
      rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
      · obtain ⟨k, hk, hke⟩ := ih h
        exact ⟨k, by omega, hke⟩
      · have hke : e = (false, i, j + (m : ℤ)) := by
          have := Finsupp.support_single_subset (a := (false, i, j + (m : ℤ)))
            (b := (1 : ZMod 2)) h
          rw [Finset.mem_singleton] at this
          simpa only [eChain] using this
        exact ⟨m, by omega, hke⟩

/-! ## Segments spanning two vertices -/

/-- The horizontal run spanning the two indices `i` and `i'`. -/
def hSeg (i i' j : ℤ) : Chain1 := hRun (min i i') j (Int.natAbs (i' - i))

/-- The vertical run spanning the two indices `j` and `j'`. -/
def vSeg (i : ℤ) (j j' : ℤ) : Chain1 := vRun i (min j j') (Int.natAbs (j' - j))

lemma min_add_natAbs (a b : ℤ) : min a b + ((Int.natAbs (b - a) : ℕ) : ℤ) = max a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h,
      Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ b - a)]
    ring
  · rw [show b - a = -(a - b) from by ring, Int.natAbs_neg,
      Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ a - b),
      min_eq_right h, max_eq_left h]
    ring

lemma hSeg_bdry (i i' j : ℤ) (x : ℤ × ℤ) :
    bdry1 ((hSeg i i' j : Chain1) : Edge → ZMod 2) x
      = (if x = (i, j) then 1 else 0) + (if x = (i', j) then 1 else 0) := by
  obtain hkey := hRun_bdry (min i i') j (Int.natAbs (i' - i)) x
  have hv1 : min i i' + ((Int.natAbs (i' - i) : ℕ) : ℤ) = max i i' := min_add_natAbs i i'
  rw [hSeg, hkey]
  rcases le_total i i' with h | h
  · rw [show ((min i i', j) : ℤ × ℤ) = (i, j) from by rw [min_eq_left h]]
    rw [show min i i' + ((Int.natAbs (i' - i) : ℕ) : ℤ) = i' from by rw [hv1, max_eq_right h]]
  · rw [show ((min i i', j) : ℤ × ℤ) = (i', j) from by rw [min_eq_right h]]
    rw [show min i i' + ((Int.natAbs (i' - i) : ℕ) : ℤ) = i from by rw [hv1, max_eq_left h],
      add_comm]

lemma vSeg_bdry (i j j' : ℤ) (x : ℤ × ℤ) :
    bdry1 ((vSeg i j j' : Chain1) : Edge → ZMod 2) x
      = (if x = (i, j) then 1 else 0) + (if x = (i, j') then 1 else 0) := by
  obtain hkey := vRun_bdry i (min j j') (Int.natAbs (j' - j)) x
  have hv1 : min j j' + ((Int.natAbs (j' - j) : ℕ) : ℤ) = max j j' := min_add_natAbs j j'
  rw [vSeg, hkey]
  rcases le_total j j' with h | h
  · rw [show ((i, min j j') : ℤ × ℤ) = (i, j) from by rw [min_eq_left h]]
    rw [show min j j' + ((Int.natAbs (j' - j) : ℕ) : ℤ) = j' from by rw [hv1, max_eq_right h]]
  · rw [show ((i, min j j') : ℤ × ℤ) = (i, j') from by rw [min_eq_right h]]
    rw [show min j j' + ((Int.natAbs (j' - j) : ℕ) : ℤ) = j from by rw [hv1, max_eq_left h],
      add_comm]

/-! ## The staircase -/

/-- The two-legged staircase chain from `a` to `b`. -/
def stairChain (a b : ℤ × ℤ) : Chain1 := hSeg a.1 b.1 a.2 + vSeg b.1 a.2 b.2

lemma stairChain_bdry (a b : ℤ × ℤ) (x : ℤ × ℤ) :
    bdry1 ((stairChain a b : Chain1) : Edge → ZMod 2) x
      = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  rw [stairChain, Finsupp.coe_add, bdry1_add, Pi.add_apply, hSeg_bdry, vSeg_bdry]
  exact add_pair_eq (a.1, a.2) (b.1, a.2) (b.1, b.2) x

/-! ## How far the staircase gets from its endpoint -/

lemma gseg_true_coord {h : ℝ} (hh : 0 < h) {p j : ℤ} {z : Pt}
    (hz : z ∈ gseg h (true, p, j)) :
    |z 0 - (p : ℝ) * h| ≤ h ∧ z 1 = (j : ℝ) * h := by
  rw [gseg, segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  simp only [eTail_true, eHead_true, gptH_apply_zero, gptH_apply_one, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_one]
  refine ⟨?_, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith [ht0, ht1, hh]
  · ring

lemma gseg_false_coord {h : ℝ} (hh : 0 < h) {p j : ℤ} {z : Pt}
    (hz : z ∈ gseg h (false, p, j)) :
    z 0 = (p : ℝ) * h ∧ |z 1 - (j : ℝ) * h| ≤ h := by
  rw [gseg, segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  simp only [eTail_false, eHead_false, gptH_apply_zero, gptH_apply_one, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_one]
  refine ⟨?_, ?_⟩
  · ring
  · rw [abs_le]; constructor <;> nlinarith [ht0, ht1, hh]

lemma hSeg_support' {i i' j : ℤ} {e : Edge} (he : e ∈ (hSeg i i' j).support) :
    ∃ p : ℤ, min i i' ≤ p ∧ p + 1 ≤ max i i' ∧ e = (true, p, j) := by
  obtain ⟨k, hk, rfl⟩ := hRun_support (m := Int.natAbs (i' - i)) he
  refine ⟨min i i' + (k : ℤ), ?_, ?_, rfl⟩
  · omega
  · have hk' : (k : ℤ) + 1 ≤ ((Int.natAbs (i' - i) : ℕ) : ℤ) := by exact_mod_cast hk
    have hv := min_add_natAbs i i'
    omega

lemma vSeg_support' {i j j' : ℤ} {e : Edge} (he : e ∈ (vSeg i j j').support) :
    ∃ p : ℤ, min j j' ≤ p ∧ p + 1 ≤ max j j' ∧ e = (false, i, p) := by
  obtain ⟨k, hk, rfl⟩ := vRun_support (m := Int.natAbs (j' - j)) he
  refine ⟨min j j' + (k : ℤ), ?_, ?_, rfl⟩
  · omega
  · have hk' : (k : ℤ) + 1 ≤ ((Int.natAbs (j' - j) : ℕ) : ℤ) := by exact_mod_cast hk
    have hv := min_add_natAbs j j'
    omega

/-- Every point of an edge of the staircase from `a` to `b` is within `(n+2) h √2` of the vertex
`a`, provided the two vertices differ by at most `n` in each coordinate. -/
lemma stairChain_edges_near {h : ℝ} (hh : 0 < h) {a b : ℤ × ℤ} {n : ℕ}
    (h1 : |a.1 - b.1| ≤ (n : ℤ)) (h2 : |a.2 - b.2| ≤ (n : ℤ)) {e : Edge}
    (he : e ∈ (stairChain a b).support) :
    ∀ z ∈ gseg h e, dist z (gptH h a) ≤ ((n : ℝ) + 2) * h * Real.sqrt 2 := by
  have h1' : |a.1 - b.1| ≤ ((n : ℤ)) := h1
  have h2' : |a.2 - b.2| ≤ ((n : ℤ)) := h2
  rw [stairChain] at he
  rcases Finset.mem_union.mp (Finsupp.support_add he) with hh1 | hh2
  · obtain ⟨p, hp1, hp2, rfl⟩ := hSeg_support' hh1
    intro z hz
    obtain ⟨hz0, hz1⟩ := gseg_true_coord hh hz
    have ha0 : (gptH h a) 0 = h * (a.1 : ℝ) := by simp
    have ha1 : (gptH h a) 1 = h * (a.2 : ℝ) := by simp
    have hp : |p - a.1| ≤ (n : ℤ) := by
      rw [abs_le] at h1' ⊢
      constructor <;> omega
    have hpR : |(p : ℝ) - (a.1 : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hp
    refine dist_le_of_coord ?_ ?_
    · rw [ha0, abs_le]
      have hzp := abs_le.mp hz0
      have hpa := abs_le.mp hpR
      constructor <;> nlinarith [hzp.1, hzp.2, hpa.1, hpa.2, hh]
    · rw [ha1, hz1, mul_comm (a.2 : ℝ) h, sub_self, abs_zero]
      positivity
  · obtain ⟨p, hp1, hp2, rfl⟩ := vSeg_support' hh2
    intro z hz
    obtain ⟨hz0, hz1⟩ := gseg_false_coord hh hz
    have ha0 : (gptH h a) 0 = h * (a.1 : ℝ) := by simp
    have ha1 : (gptH h a) 1 = h * (a.2 : ℝ) := by simp
    have hp : |p - a.2| ≤ (n : ℤ) := by
      rw [abs_le] at h2' ⊢
      constructor <;> omega
    have hpR : |(p : ℝ) - (a.2 : ℝ)| ≤ (n : ℝ) := by exact_mod_cast hp
    refine dist_le_of_coord ?_ ?_
    · rw [ha0, hz0, abs_le]
      have hab : |(a.1 : ℝ) - (b.1 : ℝ)| ≤ (n : ℝ) := by exact_mod_cast h1'
      have hpa := abs_le.mp (abs_sub_comm (a.1 : ℝ) (b.1 : ℝ) ▸ hab)
      constructor <;> nlinarith [hpa.1, hpa.2, hh]
    · rw [ha1, abs_le]
      have hzp := abs_le.mp hz1
      have hpa := abs_le.mp hpR
      constructor <;> nlinarith [hzp.1, hzp.2, hpa.1, hpa.2, hh]


/-! ## The nearest grid vertex -/

/-- The grid vertex nearest to a point. -/
def nearGrid (h : ℝ) (z : Pt) : ℤ × ℤ := (⌊z 0 / h + 1 / 2⌋, ⌊z 1 / h + 1 / 2⌋)

lemma nearGrid_fst (h : ℝ) (z : Pt) : (nearGrid h z).1 = ⌊z 0 / h + 1 / 2⌋ := rfl

lemma nearGrid_snd (h : ℝ) (z : Pt) : (nearGrid h z).2 = ⌊z 1 / h + 1 / 2⌋ := rfl

lemma abs_sub_floor_half (t : ℝ) : |t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ)| ≤ 1 / 2 := by
  have h1 : ((⌊t + 1 / 2⌋ : ℤ) : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have h2 : t + 1 / 2 < ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

lemma nearGrid_dist {h : ℝ} (hh : 0 < h) (z : Pt) : dist z (gptH h (nearGrid h z)) ≤ h := by
  have h0 : (gptH h (nearGrid h z)) 0 = h * ((nearGrid h z).1 : ℝ) := by simp
  have h1 : (gptH h (nearGrid h z)) 1 = h * ((nearGrid h z).2 : ℝ) := by simp
  refine le_trans (dist_le_of_coord (C := h / 2) ?_ ?_) ?_
  · rw [h0]
    have hk : |z 0 / h - ((nearGrid h z).1 : ℝ)| ≤ 1 / 2 := by
      rw [nearGrid_fst]; exact abs_sub_floor_half _
    have key : z 0 - h * ((nearGrid h z).1 : ℝ)
        = h * (z 0 / h - ((nearGrid h z).1 : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hh)]
    rw [key, abs_mul, abs_of_pos hh]
    nlinarith [hk, hh]
  · rw [h1]
    have hk : |z 1 / h - ((nearGrid h z).2 : ℝ)| ≤ 1 / 2 := by
      rw [nearGrid_snd]; exact abs_sub_floor_half _
    have key : z 1 - h * ((nearGrid h z).2 : ℝ)
        = h * (z 1 / h - ((nearGrid h z).2 : ℝ)) := by
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hh)]
    rw [key, abs_mul, abs_of_pos hh]
    nlinarith [hk, hh]
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hh,
      sq_nonneg (2 - Real.sqrt 2)]

/-! ## The telescoping identity in `ZMod 2` -/

lemma sum_range_pair (g : ℕ → ZMod 2) (N : ℕ) :
    (∑ i ∈ Finset.range N, (g i + g (i + 1))) = g 0 + g N := by
  induction N with
  | zero => exact (CharTwo.add_self_eq_zero (g 0)).symm
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show (g 0 + g N) + (g N + g (N + 1)) = g 0 + (g N + g N) + g (N + 1) from by abel,
        CharTwo.add_self_eq_zero]
      abel

/-- Additivity of the boundary over a finite sum of chains. -/
lemma bdry1_finset_sum {ι : Type*} (u : Finset ι) (L : ι → Chain1) :
    bdry1 ((∑ i ∈ u, L i : Chain1) : Edge → ZMod 2)
      = ∑ i ∈ u, bdry1 ((L i : Chain1) : Edge → ZMod 2) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      funext x
      simp [bdry1]
  | insert a u ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.coe_add, bdry1_add, ih]

/-- Membership in the support of a finite sum of chains. -/
lemma mem_support_finset_sum {ι : Type*} {u : Finset ι} {L : ι → Chain1} {e : Edge}
    (he : e ∈ (∑ i ∈ u, L i : Chain1).support) : ∃ i ∈ u, e ∈ (L i).support := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finsupp.support_zero] at he
      simp at he
  | insert a u ha ih =>
      rw [Finset.sum_insert ha] at he
      rcases Finset.mem_union.mp (Finsupp.support_add he) with h | h
      · exact ⟨a, Finset.mem_insert_self a u, h⟩
      · obtain ⟨i, hi, hie⟩ := ih h
        exact ⟨i, Finset.mem_insert_of_mem hi, hie⟩

/-! ## Subdivision of the unit interval -/

/-- The clamped point `i/N` of the unit interval. -/
def subsample (N i : ℕ) : unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one ((i : ℝ) / N)

lemma subsample_zero {N : ℕ} : subsample N 0 = 0 := by
  rw [subsample, show (((0 : ℕ) : ℝ) / (N : ℝ)) = 0 from by simp]
  exact Set.projIcc_of_mem zero_le_one ⟨le_refl 0, zero_le_one⟩

lemma subsample_last {N : ℕ} (hN : 0 < N) : subsample N N = 1 := by
  rw [subsample, show ((N : ℝ) / (N : ℝ)) = 1 from by field_simp]
  exact Set.projIcc_of_mem zero_le_one ⟨zero_le_one, le_refl 1⟩

lemma subsample_dist {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    dist (subsample N i) (subsample N (i + 1)) = 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((i : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN']; exact_mod_cast le_of_lt hi
  have h2 : (((i : ℝ) + 1) / N) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN']
    have : (i : ℝ) + 1 ≤ (N : ℝ) := by
      have : i + 1 ≤ N := hi
      exact_mod_cast this
    linarith
  have harg : (((i + 1 : ℕ) : ℝ)) / (N : ℝ) = ((i : ℝ) + 1) / N := by push_cast; ring
  have hval : ((subsample N i : unitInterval) : ℝ) = (i : ℝ) / N := by
    rw [show subsample N i = ⟨(i : ℝ) / N, h1⟩ from Set.projIcc_of_mem zero_le_one h1]
  have hval' : ((subsample N (i + 1) : unitInterval) : ℝ) = ((i : ℝ) + 1) / N := by
    rw [show subsample N (i + 1) = ⟨((i : ℝ) + 1) / N, h2⟩ from by
      rw [subsample, harg]
      exact Set.projIcc_of_mem zero_le_one h2]
  rw [Subtype.dist_eq, hval, hval', Real.dist_eq,
    show (i : ℝ) / N - ((i : ℝ) + 1) / N = -(1 / N) from by ring, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]

/-- A `δ` for which the path moves by less than `ε`. -/
lemma exists_delta {γ : unitInterval → Pt} (hγ : Continuous γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : unitInterval, dist t s < δ → dist (γ t) (γ s) < 2 * ε := by
  have hcov : ∀ t : unitInterval, ∃ r : ℝ, 0 < r ∧
      ∀ s : unitInterval, dist s t < r → dist (γ s) (γ t) < ε := by
    intro t
    have h1 : ∀ᶠ s in 𝓝 t, γ s ∈ Metric.ball (γ t) ε :=
      hγ.continuousAt (Metric.ball_mem_nhds _ hε)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨r, hr, fun s hs => hrsub (by simpa [Metric.mem_ball] using hs)⟩
  choose r hrpos hrball using hcov
  have hcov2 : (univ : Set unitInterval) ⊆ ⋃ t, Metric.ball t (r t / 2) :=
    fun t _ => Set.mem_iUnion.mpr ⟨t, Metric.mem_ball_self (by linarith [hrpos t])⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun t : unitInterval => Metric.ball t (r t / 2))
    (fun t => Metric.isOpen_ball) hcov2
  obtain ⟨u₀, hu₀⟩ : F.Nonempty := by
    have h := hF (Set.mem_univ (⟨0, ⟨le_refl 0, zero_le_one⟩⟩ : unitInterval))
    simp only [Set.mem_iUnion] at h
    obtain ⟨u, huF, _⟩ := h
    exact ⟨u, huF⟩
  have hne : (F.image r).Nonempty := ⟨r u₀, Finset.mem_image_of_mem r hu₀⟩
  have hδpos : 0 < (F.image r).min' hne := by
    obtain ⟨u, huF, hu⟩ := Finset.mem_image.mp ((F.image r).min'_mem hne)
    rw [← hu]
    exact hrpos u
  have hδle : ∀ u ∈ F, (F.image r).min' hne ≤ r u :=
    fun u hu => Finset.min'_le _ _ (Finset.mem_image_of_mem r hu)
  refine ⟨(F.image r).min' hne / 2, by linarith, ?_⟩
  intro t s hts
  have htF := hF (Set.mem_univ t)
  simp only [Set.mem_iUnion] at htF
  obtain ⟨u, huF, htu⟩ := htF
  rw [Metric.mem_ball] at htu
  have hδu : (F.image r).min' hne ≤ r u := hδle u huF
  have hsu : dist s u < r u := by
    have h1 : dist s u ≤ dist s t + dist t u := dist_triangle _ _ _
    have h2 : dist s t < (F.image r).min' hne / 2 := by rwa [dist_comm] at hts
    have h3 : dist s t + dist t u < (F.image r).min' hne / 2 + r u / 2 := add_lt_add h2 htu
    have h4 : (F.image r).min' hne / 2 + r u / 2 ≤ r u := by linarith [hδu, hrpos u]
    linarith [h1, h3, h4]
  have h1 : dist (γ t) (γ u) < ε := hrball u t (by linarith [htu, hrpos u])
  have h2 : dist (γ s) (γ u) < ε := hrball u s hsu
  have h3 : dist (γ t) (γ s) ≤ dist (γ t) (γ u) + dist (γ u) (γ s) := dist_triangle _ _ _
  rw [dist_comm (γ u) (γ s)] at h3
  linarith

/-- Coordinate difference bound from a distance bound on the corresponding grid vertices. -/
lemma grid_coord_le {h : ℝ} (hh : 0 < h) {a b : ℤ × ℤ} {C : ℝ}
    (hd : dist (gptH h a) (gptH h b) ≤ C * h) {n : ℕ} (hC : C ≤ (n : ℝ)) :
    |a.1 - b.1| ≤ (n : ℤ) ∧ |a.2 - b.2| ≤ (n : ℤ) := by
  have key : ∀ i : Fin 2, |(gptH h a) i - (gptH h b) i| ≤ C * h := by
    intro i
    have h1 : ‖gptH h a - gptH h b‖ = dist (gptH h a) (gptH h b) := by rw [dist_eq_norm]
    have h2 := abs_coord_le_norm (gptH h a - gptH h b) i
    rw [h1] at h2
    refine le_trans ?_ hd
    calc |(gptH h a) i - (gptH h b) i| = |(gptH h a - gptH h b) i| := by simp
      _ ≤ dist (gptH h a) (gptH h b) := h2
  have hcoord : ∀ i : Fin 2, |(gptH h a) i - (gptH h b) i| ≤ C * h := key
  have hfr : ∀ (u v : ℤ), |(u : ℝ) - (v : ℝ)| ≤ (n : ℝ) → |u - v| ≤ (n : ℤ) := by
    intro u v huv
    have h7 : ((|u - v| : ℤ) : ℝ) ≤ (n : ℝ) := by
      rw [Int.cast_abs, Int.cast_sub]
      exact huv
    exact_mod_cast h7
  constructor
  · have h0 := hcoord 0
    simp only [gptH_apply_zero] at h0
    refine hfr a.1 b.1 ?_
    have h3 : |(a.1 : ℝ) - (b.1 : ℝ)| ≤ C := by
      have h4 : |(a.1 : ℝ) - (b.1 : ℝ)| * h ≤ C * h := by
        rw [show h * (a.1 : ℝ) - h * (b.1 : ℝ) = ((a.1 : ℝ) - (b.1 : ℝ)) * h from by ring]
          at h0
        rw [abs_mul, abs_of_pos hh] at h0
        exact h0
      exact le_of_mul_le_mul_right h4 hh
    exact le_trans h3 hC
  · have h0 := hcoord 1
    simp only [gptH_apply_one] at h0
    refine hfr a.2 b.2 ?_
    have h3 : |(a.2 : ℝ) - (b.2 : ℝ)| ≤ C := by
      have h4 : |(a.2 : ℝ) - (b.2 : ℝ)| * h ≤ C * h := by
        rw [show h * (a.2 : ℝ) - h * (b.2 : ℝ) = ((a.2 : ℝ) - (b.2 : ℝ)) * h from by ring]
          at h0
        rw [abs_mul, abs_of_pos hh] at h0
        exact h0
      exact le_of_mul_le_mul_right h4 hh
    exact le_trans h3 hC

/-- The function-level form of the staircase boundary. -/
lemma stairChain_bdry_fun (a b : ℤ × ℤ) :
    bdry1 ((stairChain a b : Chain1) : Edge → ZMod 2)
      = fun x => (if x = a then (1 : ZMod 2) else 0) + (if x = b then 1 else 0) := by
  funext x
  exact stairChain_bdry a b x

/-- Applying a finite sum of indicator functions. -/
lemma sum_apply' {ι : Type*} (s : Finset ι) (F : ι → (ℤ × ℤ → ZMod 2)) (x : ℤ × ℤ) :
    (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Pi.add_apply, ih]

/-- The telescoping identity for a sequence of vertices, at the level of functions. -/
lemma sum_range_pair_fun (w : ℕ → ℤ × ℤ) (M : ℕ) :
    (∑ i ∈ Finset.range M,
        (fun y => (if y = w i then (1 : ZMod 2) else 0) + (if y = w (i + 1) then 1 else 0)))
      = (fun y => (if y = w 0 then 1 else 0) + (if y = w M then 1 else 0)) := by
  funext y
  rw [sum_apply']
  exact (sum_range_pair (fun (i : ℕ) => if y = w i then (1 : ZMod 2) else 0) M : _)

/-- The lower endpoint of an edge of a cell lies in the closure of that cell. -/
lemma eTail_mem_gsq_of_mem_cellEdges {h : ℝ} (hh : 0 < h) {c : Cell} {e : Edge}
    (he : e ∈ cellEdges c) : gptH h (eTail e) ∈ gsq h c := by
  rw [← mem_edgeCells_iff] at he
  obtain ⟨b, i, j⟩ := e
  cases b
  · simp only [edgeCells, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h <;> rw [h]
    · simp only [gsq, Set.mem_ofPred_eq, eTail_false, gptH_apply_zero, gptH_apply_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith [hh]
    · simp only [gsq, Set.mem_ofPred_eq, eTail_false, gptH_apply_zero, gptH_apply_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith [hh]
  · simp only [edgeCells, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h <;> rw [h]
    · simp only [gsq, Set.mem_ofPred_eq, eTail_true, gptH_apply_zero, gptH_apply_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith [hh]
    · simp only [gsq, Set.mem_ofPred_eq, eTail_true, gptH_apply_zero, gptH_apply_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith [hh]

/-- An edge of a cell meeting `S` has a point within `h√2` of `S`. -/
lemma exists_near_of_mem_edgeSet {h : ℝ} (hh : 0 < h) {S : Set Pt} {e : Edge}
    (he : e ∈ edgeSet (cellSet h S)) :
    ∃ z ∈ gseg h e, ∃ s ∈ S, dist z s ≤ h * Real.sqrt 2 := by
  obtain ⟨c, hc, hec⟩ := he
  obtain ⟨a, hag, has⟩ := hc
  refine ⟨gptH h (eTail e), gseg_self h e, a, has, ?_⟩
  have h1 := eTail_mem_gsq_of_mem_cellEdges hh hec
  exact dist_le_of_coord
    (by rw [abs_le]; constructor <;> nlinarith [gsq_fst hag, gsq_fst' hag, gsq_fst h1, gsq_fst' h1])
    (by rw [abs_le]; constructor <;> nlinarith [gsq_snd hag, gsq_snd' hag, gsq_snd h1, gsq_snd' h1])

/-- **Snapping.**  A path whose image stays at distance `≥ 20 h` from `S` can be followed by a
mesh-`h` grid chain whose endpoints are the grid vertices nearest to the endpoints of the path and
whose edges avoid `S`. -/
theorem exists_chain_avoiding {S : Set Pt} {h : ℝ} (hh : 0 < h) {X Y : Pt} {γ : Path X Y}
    (hγ : ∀ t : unitInterval, ∀ s ∈ S, 20 * h ≤ dist (γ t) s) :
    ∃ l : Chain1, (∀ v : ℤ × ℤ, bdry1 ((l : Chain1) : Edge → ZMod 2) v
        = (if v = nearGrid h X then 1 else 0) + (if v = nearGrid h Y then 1 else 0)) ∧
      ∀ e ∈ l.support, e ∉ edgeSet (cellSet h S) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta γ.continuous (show (0 : ℝ) < h / 2 by linarith)
  obtain ⟨M, hM⟩ := exists_nat_gt (max (1 / δ) 1)
  have hM2 : (0 : ℝ) < (M : ℝ) := by
    have h1 : (1 : ℝ) ≤ (max (1 / δ) 1) := le_max_right _ _
    linarith
  have hMpos : 0 < M := Nat.cast_pos.mp hM2
  have hMδ : 1 / (M : ℝ) < δ := by
    have h1 : 1 / δ < (M : ℝ) := lt_of_le_of_lt (le_max_left (1 / δ) 1) hM
    rw [div_lt_iff₀ hδpos] at h1
    rw [div_lt_iff₀ (by exact_mod_cast hMpos : (0 : ℝ) < (M : ℝ))]
    linarith
  set v : ℕ → ℤ × ℤ := fun i => nearGrid h (γ (subsample M i)) with hvdef
  have hvdef' : ∀ i, v i = nearGrid h (γ (subsample M i)) := by intro i; rw [hvdef]
  have hv0 : v 0 = nearGrid h X := by
    rw [hvdef' 0, subsample_zero, show γ (0 : unitInterval) = X from γ.source]
  have hvM : v M = nearGrid h Y := by
    rw [hvdef' M, subsample_last hMpos, show γ (1 : unitInterval) = Y from γ.target]
  have hstep : ∀ i, i < M → dist (γ (subsample M i)) (γ (subsample M (i + 1))) < h := by
    intro i hi
    have := hδ (subsample M i) (subsample M (i + 1)) (by
      rw [subsample_dist hMpos hi]
      exact hMδ)
    rwa [show 2 * (h / 2) = h from by ring] at this
  refine ⟨∑ i ∈ Finset.range M, stairChain (v i) (v (i + 1)), ?_, ?_⟩
  · intro x
    have h5 : (∑ i ∈ Finset.range M,
          bdry1 ((stairChain (v i) (v (i + 1)) : Chain1) : Edge → ZMod 2))
        = ∑ i ∈ Finset.range M,
            (fun y => (if y = v i then (1 : ZMod 2) else 0) + (if y = v (i + 1) then 1 else 0)) := by
      simp only [stairChain_bdry_fun]
    have hfun : bdry1 ((∑ i ∈ Finset.range M, stairChain (v i) (v (i + 1)) : Chain1) :
          Edge → ZMod 2)
        = (fun y => (if y = v 0 then (1 : ZMod 2) else 0) + (if y = v M then 1 else 0)) := by
      rw [bdry1_finset_sum, h5, sum_range_pair_fun v M]
    rw [hfun, hv0, hvM]
  · intro e he hmem
    obtain ⟨i, hi, hie⟩ := mem_support_finset_sum he
    have hdist_γ := hstep i (Finset.mem_range.mp hi)
    have h1 : dist (gptH h (v i)) (γ (subsample M i)) ≤ h := by
      rw [hvdef' i, dist_comm]
      exact nearGrid_dist hh _
    have h2 : dist (γ (subsample M (i + 1))) (gptH h (v (i + 1))) ≤ h := by
      rw [hvdef' (i + 1)]
      exact nearGrid_dist hh _
    have hdisp : dist (gptH h (v i)) (gptH h (v (i + 1))) ≤ 3 * h := by
      have a := dist_triangle (gptH h (v i)) (γ (subsample M i)) (gptH h (v (i + 1)))
      have b := dist_triangle (γ (subsample M i)) (γ (subsample M (i + 1)))
        (gptH h (v (i + 1)))
      linarith [a, b, h1, h2, hdist_γ, hh]
    obtain ⟨hc1, hc2⟩ := grid_coord_le hh hdisp (by norm_num : (3 : ℝ) ≤ (3 : ℕ))
    obtain ⟨z, hz1, s, hs, hzs⟩ := exists_near_of_mem_edgeSet hh hmem
    have hnear := stairChain_edges_near hh hc1 hc2 hie z hz1
    have hnear' : dist z (gptH h (v i)) ≤ 5 * h * Real.sqrt 2 := by
      rw [show (((3 : ℕ) : ℝ) + 2) = 5 from by norm_num] at hnear
      exact hnear
    have hγs : 20 * h ≤ dist (γ (subsample M i)) s := hγ (subsample M i) s hs
    have h1' : dist (γ (subsample M i)) (gptH h (v i)) ≤ h := by rw [dist_comm]; exact h1
    have htri : dist (γ (subsample M i)) s
        ≤ dist (γ (subsample M i)) (gptH h (v i)) + dist (gptH h (v i)) z + dist z s := by
      have a := dist_triangle (γ (subsample M i)) (gptH h (v i)) s
      have b := dist_triangle (gptH h (v i)) z s
      linarith [a, b]
    have hnear'' : dist (gptH h (v i)) z ≤ 5 * h * Real.sqrt 2 := by
      rw [dist_comm]; exact hnear'
    have hc : 5 * h * Real.sqrt 2 + h * Real.sqrt 2 + h < 20 * h := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hh]
    linarith [hnear'', hzs, hγs, h1', htri, hc]

end

end Work.Whitney.PathTools.Grid
