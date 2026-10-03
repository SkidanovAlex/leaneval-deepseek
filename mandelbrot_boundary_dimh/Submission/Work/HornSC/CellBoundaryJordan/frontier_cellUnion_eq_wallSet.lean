import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells

/-!
# The frontier of a finite union of lattice cells is its wall set

`frontier (cellUnion A) = wallSet A`: the frontier of a union of closed unit lattice cells is
exactly the union of the closed unit grid segments separating a cell of `A` from a cell outside
`A`.

The proof goes through the characterisation of the interior,
`interior (cellUnion A) = {z | every cell containing z belongs to A}`,
and the combinatorial description of the wall set,
`z ∈ wallSet A ↔ (z lies in a cell of A) ∧ (z lies in a cell outside A)`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

def colSet (x : ℝ) : Set ℤ := {n : ℤ | (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1}

lemma mem_colSet {x : ℝ} {n : ℤ} : n ∈ colSet x ↔ (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1 := Iff.rfl

lemma mem_cell_iff_cols {p : ℤ × ℤ} {z : ℂ} :
    z ∈ cell p ↔ p.1 ∈ colSet z.re ∧ p.2 ∈ colSet z.im := by
  simp only [colSet, Set.mem_ofPred_eq, Work.HornSC.mem_cell]
  tauto

lemma exists_mem_colSet (x : ℝ) : ∃ n : ℤ, n ∈ colSet x :=
  ⟨⌊x⌋, Int.floor_le x, le_of_lt (Int.lt_floor_add_one x)⟩

lemma exists_mem_cell (z : ℂ) : ∃ p : ℤ × ℤ, z ∈ cell p := by
  obtain ⟨a, ha⟩ := exists_mem_colSet z.re
  obtain ⟨b, hb⟩ := exists_mem_colSet z.im
  exact ⟨(a, b), mem_cell_iff_cols.mpr ⟨ha, hb⟩⟩

lemma colSet_intCast (m : ℤ) : colSet (m : ℝ) = {m - 1, m} := by
  ext n
  rw [mem_colSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : n ≤ m := by exact_mod_cast h1
    have h2' : m ≤ n + 1 := by exact_mod_cast h2
    omega
  · rintro (rfl | rfl) <;> refine ⟨?_, ?_⟩ <;> push_cast <;> linarith

lemma colSet_subset_pair {x : ℝ} {m : ℤ} (h1 : (m : ℝ) - 1 < x) (h2 : x < (m : ℝ) + 1) :
    colSet x ⊆ ({m - 1, m} : Set ℤ) := by
  intro n hn
  rw [mem_colSet] at hn
  obtain ⟨hn1, hn2⟩ := hn
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  have h1' : n ≤ m := by
    have h : (n : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt hn1 h2
    have : n < m + 1 := by exact_mod_cast h
    omega
  have h2' : m ≤ n + 1 := by
    have h : (m : ℝ) - 1 < (n : ℝ) + 1 := lt_of_lt_of_le h1 hn2
    have : m - 1 < n + 1 := by exact_mod_cast h
    omega
  omega

lemma colSet_eq_singleton {x : ℝ} {m : ℤ} (h1 : (m : ℝ) < x) (h2 : x < (m : ℝ) + 1) :
    colSet x = {m} := by
  ext n
  rw [mem_colSet, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn1, hn2⟩
    have h1' : n ≤ m := by
      have h : (n : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt hn1 h2
      have : n < m + 1 := by exact_mod_cast h
      omega
    have h2' : m ≤ n := by
      have h : (m : ℝ) < (n : ℝ) + 1 := lt_of_lt_of_le h1 hn2
      have : m < n + 1 := by exact_mod_cast h
      omega
    omega
  · intro h; subst h; exact ⟨le_of_lt h1, le_of_lt h2⟩

lemma mem_iCell_iff {p : ℤ × ℤ} {z : ℂ} :
    z ∈ iCell p ↔ (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 1 := Iff.rfl

lemma iCell_subset_cell (p : ℤ × ℤ) : iCell p ⊆ cell p := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact Work.HornSC.mem_cell.mpr ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

lemma eq_of_mem_iCell_of_mem_cell {z : ℂ} {p q : ℤ × ℤ} (hp : z ∈ iCell p)
    (hq : z ∈ cell q) : q = p := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  have h1 : q.1 = p.1 := by
    have ha : q.1 ≤ p.1 := by
      have h : (q.1 : ℝ) < (p.1 : ℝ) + 1 := lt_of_le_of_lt hq1 hp2
      have : q.1 < p.1 + 1 := by exact_mod_cast h
      omega
    have hb : p.1 ≤ q.1 := by
      have h : (p.1 : ℝ) < (q.1 : ℝ) + 1 := lt_of_lt_of_le hp1 hq2
      have : p.1 < q.1 + 1 := by exact_mod_cast h
      omega
    omega
  have h2 : q.2 = p.2 := by
    have ha : q.2 ≤ p.2 := by
      have h : (q.2 : ℝ) < (p.2 : ℝ) + 1 := lt_of_le_of_lt hq3 hp4
      have : q.2 < p.2 + 1 := by exact_mod_cast h
      omega
    have hb : p.2 ≤ q.2 := by
      have h : (p.2 : ℝ) < (q.2 : ℝ) + 1 := lt_of_lt_of_le hp3 hq4
      have : p.2 < q.2 + 1 := by exact_mod_cast h
      omega
    omega
  exact Prod.ext h1 h2

noncomputable def cellCenter (p : ℤ × ℤ) : ℂ := ⟨(p.1 : ℝ) + 1/2, (p.2 : ℝ) + 1/2⟩

lemma cellCenter_re (p : ℤ × ℤ) : (cellCenter p).re = (p.1 : ℝ) + 1/2 := rfl
lemma cellCenter_im (p : ℤ × ℤ) : (cellCenter p).im = (p.2 : ℝ) + 1/2 := rfl

lemma cellCenter_mem_iCell (p : ℤ × ℤ) : cellCenter p ∈ iCell p := by
  rw [mem_iCell_iff, cellCenter_re, cellCenter_im]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma smul_mem_iCell {p : ℤ × ℤ} {z c : ℂ} (hz : z ∈ cell p) (hc : c ∈ iCell p) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) : z + s • (c - z) ∈ iCell p := by
  obtain ⟨hz1, hz2, hz3, hz4⟩ := Work.HornSC.mem_cell.mp hz
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  have h1s : 0 ≤ 1 - s := by linarith
  have hre : (z + s • (c - z)).re = (1 - s) * z.re + s * c.re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul]; ring
  have him : (z + s • (c - z)).im = (1 - s) * z.im + s * c.im := by
    simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul]; ring
  rw [mem_iCell_iff, hre, him]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA : (1 - s) * (p.1 : ℝ) ≤ (1 - s) * z.re := mul_le_mul_of_nonneg_left hz1 h1s
    have hB : s * (p.1 : ℝ) < s * c.re := mul_lt_mul_of_pos_left hc1 hs0
    have hC : (1 - s) * (p.1 : ℝ) + s * (p.1 : ℝ) = (p.1 : ℝ) := by ring
    linarith
  · have hA : (1 - s) * z.re ≤ (1 - s) * ((p.1 : ℝ) + 1) := mul_le_mul_of_nonneg_left hz2 h1s
    have hB : s * c.re < s * ((p.1 : ℝ) + 1) := mul_lt_mul_of_pos_left hc2 hs0
    have hC : (1 - s) * ((p.1 : ℝ) + 1) + s * ((p.1 : ℝ) + 1) = (p.1 : ℝ) + 1 := by ring
    linarith
  · have hA : (1 - s) * (p.2 : ℝ) ≤ (1 - s) * z.im := mul_le_mul_of_nonneg_left hz3 h1s
    have hB : s * (p.2 : ℝ) < s * c.im := mul_lt_mul_of_pos_left hc3 hs0
    have hC : (1 - s) * (p.2 : ℝ) + s * (p.2 : ℝ) = (p.2 : ℝ) := by ring
    linarith
  · have hA : (1 - s) * z.im ≤ (1 - s) * ((p.2 : ℝ) + 1) := mul_le_mul_of_nonneg_left hz4 h1s
    have hB : s * c.im < s * ((p.2 : ℝ) + 1) := mul_lt_mul_of_pos_left hc4 hs0
    have hC : (1 - s) * ((p.2 : ℝ) + 1) + s * ((p.2 : ℝ) + 1) = (p.2 : ℝ) + 1 := by ring
    linarith

lemma exists_mem_iCell_dist_lt {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ cell p) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ iCell p, dist w z < ε := by
  have hcmem : cellCenter p ∈ iCell p := cellCenter_mem_iCell p
  set s : ℝ := min 1 (ε / (2 * (‖cellCenter p - z‖ + 1))) with hsdef
  have hspos : 0 < s := by
    rw [hsdef]; exact lt_min one_pos (by positivity)
  have hsle : s ≤ 1 := by rw [hsdef]; exact min_le_left _ _
  refine ⟨z + s • (cellCenter p - z), smul_mem_iCell hz hcmem hspos hsle, ?_⟩
  have hdist : z + s • (cellCenter p - z) - z = s • (cellCenter p - z) := by abel
  rw [dist_eq_norm, hdist, norm_smul, Real.norm_of_nonneg (le_of_lt hspos)]
  have hsle' : s ≤ ε / (2 * (‖cellCenter p - z‖ + 1)) := by rw [hsdef]; exact min_le_right _ _
  have hd : (0:ℝ) ≤ ‖cellCenter p - z‖ := norm_nonneg _
  have hstep : s * ‖cellCenter p - z‖ ≤ (ε / (2 * (‖cellCenter p - z‖ + 1))) * ‖cellCenter p - z‖ :=
    mul_le_mul_of_nonneg_right hsle' hd
  have hstep2 : (ε / (2 * (‖cellCenter p - z‖ + 1))) * ‖cellCenter p - z‖ ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hε, hd]
  linarith


/-! ## The interior of a finite union of cells -/

lemma isOpen_iCell (p : ℤ × ℤ) : IsOpen (iCell p) := by
  have k1 : IsOpen {z : ℂ | (p.1 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have k2 : IsOpen {z : ℂ | z.re < (p.1 : ℝ) + 1} := isOpen_lt Complex.continuous_re continuous_const
  have k3 : IsOpen {z : ℂ | (p.2 : ℝ) < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have k4 : IsOpen {z : ℂ | z.im < (p.2 : ℝ) + 1} := isOpen_lt Complex.continuous_im continuous_const
  have kk := ((k1.inter k2).inter k3).inter k4
  convert kk using 1
  ext w
  simp only [mem_iCell_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

lemma colSet_nat {x : ℝ} (hx : ¬ ∃ n : ℤ, (n : ℝ) = x) :
    ((⌊x⌋ : ℤ) : ℝ) < x ∧ x < ((⌊x⌋ : ℤ) : ℝ) + 1 := by
  refine ⟨?_, Int.lt_floor_add_one x⟩
  rcases lt_or_eq_of_le (Int.floor_le x) with h | h
  · exact h
  · exact absurd ⟨⌊x⌋, h⟩ hx

lemma interior_cellUnion_eq (A : Finset (ℤ × ℤ)) :
    interior (cellUnion A) = {z : ℂ | ∀ p : ℤ × ℤ, z ∈ cell p → p ∈ A} := by
  apply le_antisymm
  · intro z hz
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
    obtain ⟨ε, hε, hball⟩ := hz
    intro p hpz
    by_contra hpA
    obtain ⟨w, hwi, hwdist⟩ := exists_mem_iCell_dist_lt hpz hε
    have hwball : w ∈ Metric.ball z ε := by
      rw [Metric.mem_ball]; simpa [dist_comm] using hwdist
    have hwU : w ∈ cellUnion A := hball hwball
    rw [Work.HornSC.cellUnion, Set.mem_iUnion₂] at hwU
    obtain ⟨r, hrA, hwr⟩ := hwU
    have hrp : r = p := eq_of_mem_iCell_of_mem_cell hwi hwr
    exact hpA (hrp ▸ hrA)
  · intro z hz
    by_cases hri : ∃ m : ℤ, (m : ℝ) = z.re
    · obtain ⟨m, hm⟩ := hri
      by_cases hii : ∃ n : ℤ, (n : ℝ) = z.im
      · obtain ⟨n, hn⟩ := hii
        have hzcols : colSet z.re = ({m - 1, m} : Set ℤ) := by rw [← hm, colSet_intCast]
        have hzrows : colSet z.im = ({n - 1, n} : Set ℤ) := by rw [← hn, colSet_intCast]
        set U : Set ℂ := {w : ℂ | (m : ℝ) - 1 < w.re ∧ w.re < (m : ℝ) + 1 ∧
            (n : ℝ) - 1 < w.im ∧ w.im < (n : ℝ) + 1} with hU
        have hopen : IsOpen U := by
          have k1 : IsOpen {w : ℂ | (m : ℝ) - 1 < w.re} :=
            isOpen_lt continuous_const Complex.continuous_re
          have k2 : IsOpen {w : ℂ | w.re < (m : ℝ) + 1} :=
            isOpen_lt Complex.continuous_re continuous_const
          have k3 : IsOpen {w : ℂ | (n : ℝ) - 1 < w.im} :=
            isOpen_lt continuous_const Complex.continuous_im
          have k4 : IsOpen {w : ℂ | w.im < (n : ℝ) + 1} :=
            isOpen_lt Complex.continuous_im continuous_const
          have kk := ((k1.inter k2).inter k3).inter k4
          rw [hU]
          convert kk using 1
          ext w
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          tauto
        have hzU : z ∈ U := by
          rw [hU]
          simp only [Set.mem_ofPred_eq]
          rw [← hm, ← hn]
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩
        have hUsub : U ⊆ cellUnion A := by
          intro w hw
          rw [hU] at hw
          obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
          obtain ⟨p, hpw⟩ := exists_mem_cell w
          have hp1 : p.1 ∈ colSet z.re := by
            rw [hzcols]
            exact colSet_subset_pair hw1 hw2 (mem_cell_iff_cols.mp hpw).1
          have hp2 : p.2 ∈ colSet z.im := by
            rw [hzrows]
            exact colSet_subset_pair hw3 hw4 (mem_cell_iff_cols.mp hpw).2
          exact Set.mem_iUnion₂.mpr ⟨p, hz p (mem_cell_iff_cols.mpr ⟨hp1, hp2⟩), hpw⟩
        exact interior_maximal hUsub hopen hzU
      · have hzcols : colSet z.re = ({m - 1, m} : Set ℤ) := by rw [← hm, colSet_intCast]
        obtain ⟨hg1, hg2⟩ := colSet_nat hii
        have hzrows : colSet z.im = ({⌊z.im⌋} : Set ℤ) := colSet_eq_singleton hg1 hg2
        set U : Set ℂ := {w : ℂ | (m : ℝ) - 1 < w.re ∧ w.re < (m : ℝ) + 1 ∧
            ((⌊z.im⌋ : ℤ) : ℝ) < w.im ∧ w.im < ((⌊z.im⌋ : ℤ) : ℝ) + 1} with hU
        have hopen : IsOpen U := by
          have k1 : IsOpen {w : ℂ | (m : ℝ) - 1 < w.re} :=
            isOpen_lt continuous_const Complex.continuous_re
          have k2 : IsOpen {w : ℂ | w.re < (m : ℝ) + 1} :=
            isOpen_lt Complex.continuous_re continuous_const
          have k3 : IsOpen {w : ℂ | ((⌊z.im⌋ : ℤ) : ℝ) < w.im} :=
            isOpen_lt continuous_const Complex.continuous_im
          have k4 : IsOpen {w : ℂ | w.im < ((⌊z.im⌋ : ℤ) : ℝ) + 1} :=
            isOpen_lt Complex.continuous_im continuous_const
          have kk := ((k1.inter k2).inter k3).inter k4
          rw [hU]
          convert kk using 1
          ext w
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          tauto
        have hzU : z ∈ U := by
          rw [hU]
          simp only [Set.mem_ofPred_eq]
          rw [← hm]
          exact ⟨by linarith, by linarith, hg1, hg2⟩
        have hUsub : U ⊆ cellUnion A := by
          intro w hw
          rw [hU] at hw
          obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
          obtain ⟨p, hpw⟩ := exists_mem_cell w
          have hp1 : p.1 ∈ colSet z.re := by
            rw [hzcols]
            exact colSet_subset_pair hw1 hw2 (mem_cell_iff_cols.mp hpw).1
          have hp2 : p.2 ∈ colSet z.im := by
            rw [hzrows, Set.mem_singleton_iff]
            have h := (mem_cell_iff_cols.mp hpw).2
            rw [colSet_eq_singleton hw3 hw4, Set.mem_singleton_iff] at h
            exact h
          exact Set.mem_iUnion₂.mpr ⟨p, hz p (mem_cell_iff_cols.mpr ⟨hp1, hp2⟩), hpw⟩
        exact interior_maximal hUsub hopen hzU
    · obtain ⟨hf1, hf2⟩ := colSet_nat hri
      have hzcols : colSet z.re = ({⌊z.re⌋} : Set ℤ) := colSet_eq_singleton hf1 hf2
      by_cases hii : ∃ n : ℤ, (n : ℝ) = z.im
      · obtain ⟨n, hn⟩ := hii
        have hzrows : colSet z.im = ({n - 1, n} : Set ℤ) := by rw [← hn, colSet_intCast]
        set U : Set ℂ := {w : ℂ | ((⌊z.re⌋ : ℤ) : ℝ) < w.re ∧ w.re < ((⌊z.re⌋ : ℤ) : ℝ) + 1 ∧
            (n : ℝ) - 1 < w.im ∧ w.im < (n : ℝ) + 1} with hU
        have hopen : IsOpen U := by
          have k1 : IsOpen {w : ℂ | ((⌊z.re⌋ : ℤ) : ℝ) < w.re} :=
            isOpen_lt continuous_const Complex.continuous_re
          have k2 : IsOpen {w : ℂ | w.re < ((⌊z.re⌋ : ℤ) : ℝ) + 1} :=
            isOpen_lt Complex.continuous_re continuous_const
          have k3 : IsOpen {w : ℂ | (n : ℝ) - 1 < w.im} :=
            isOpen_lt continuous_const Complex.continuous_im
          have k4 : IsOpen {w : ℂ | w.im < (n : ℝ) + 1} :=
            isOpen_lt Complex.continuous_im continuous_const
          have kk := ((k1.inter k2).inter k3).inter k4
          rw [hU]
          convert kk using 1
          ext w
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
          tauto
        have hzU : z ∈ U := by
          rw [hU]
          simp only [Set.mem_ofPred_eq]
          rw [← hn]
          exact ⟨hf1, hf2, by linarith, by linarith⟩
        have hUsub : U ⊆ cellUnion A := by
          intro w hw
          rw [hU] at hw
          obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
          obtain ⟨p, hpw⟩ := exists_mem_cell w
          have hp1 : p.1 ∈ colSet z.re := by
            rw [hzcols, Set.mem_singleton_iff]
            have h := (mem_cell_iff_cols.mp hpw).1
            rw [colSet_eq_singleton hw1 hw2, Set.mem_singleton_iff] at h
            exact h
          have hp2 : p.2 ∈ colSet z.im := by
            rw [hzrows]
            exact colSet_subset_pair hw3 hw4 (mem_cell_iff_cols.mp hpw).2
          exact Set.mem_iUnion₂.mpr ⟨p, hz p (mem_cell_iff_cols.mpr ⟨hp1, hp2⟩), hpw⟩
        exact interior_maximal hUsub hopen hzU
      · obtain ⟨hg1, hg2⟩ := colSet_nat hii
        have hzrows : colSet z.im = ({⌊z.im⌋} : Set ℤ) := colSet_eq_singleton hg1 hg2
        have hzU : z ∈ iCell (⌊z.re⌋, ⌊z.im⌋) := by
          rw [mem_iCell_iff]
          exact ⟨hf1, hf2, hg1, hg2⟩
        have hUsub : iCell (⌊z.re⌋, ⌊z.im⌋) ⊆ cellUnion A := by
          intro w hw
          rw [mem_iCell_iff] at hw
          obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
          have hw1' : ((⌊z.re⌋ : ℤ) : ℝ) < w.re := by simpa using hw1
          have hw2' : w.re < ((⌊z.re⌋ : ℤ) : ℝ) + 1 := by simpa using hw2
          have hw3' : ((⌊z.im⌋ : ℤ) : ℝ) < w.im := by simpa using hw3
          have hw4' : w.im < ((⌊z.im⌋ : ℤ) : ℝ) + 1 := by simpa using hw4
          obtain ⟨p, hpw⟩ := exists_mem_cell w
          have hp1 : p.1 ∈ colSet z.re := by
            rw [hzcols, Set.mem_singleton_iff]
            have h := (mem_cell_iff_cols.mp hpw).1
            rw [colSet_eq_singleton hw1' hw2', Set.mem_singleton_iff] at h
            exact h
          have hp2 : p.2 ∈ colSet z.im := by
            rw [hzrows, Set.mem_singleton_iff]
            have h := (mem_cell_iff_cols.mp hpw).2
            rw [colSet_eq_singleton hw3' hw4', Set.mem_singleton_iff] at h
            exact h
          exact Set.mem_iUnion₂.mpr ⟨p, hz p (mem_cell_iff_cols.mpr ⟨hp1, hp2⟩), hpw⟩
        exact interior_maximal hUsub (isOpen_iCell _) hzU


/-! ## The wall set in terms of cells -/

lemma hSeg_subset_cell_down (u : ℤ × ℤ) : hSeg u ⊆ cell (u.1, u.2 - 1) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine Work.HornSC.mem_cell.mpr ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

lemma vSeg_subset_cell_left (u : ℤ × ℤ) : vSeg u ⊆ cell (u.1, u.2) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine Work.HornSC.mem_cell.mpr ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

lemma vSeg_subset_cell_right (u : ℤ × ℤ) : vSeg u ⊆ cell (u.1 - 1, u.2) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  refine Work.HornSC.mem_cell.mpr ⟨?_, ?_, ?_, ?_⟩ <;> push_cast <;> linarith

lemma pair_eq_of {a b c d : ℤ} (h1 : a = c) (h2 : b = d) :
    ((a, b) : ℤ × ℤ) = (c, d) := by rw [h1, h2]

lemma mem_wallSet_iff_cells (A : Finset (ℤ × ℤ)) (z : ℂ) :
    z ∈ wallSet A ↔ (∃ p ∈ A, z ∈ cell p) ∧ (∃ q : ℤ × ℤ, q ∉ A ∧ z ∈ cell q) := by
  constructor
  · intro hz
    rw [mem_wallSet] at hz
    rcases hz with ⟨u, hwall, hzu⟩ | ⟨u, hwall, hzu⟩
    · rcases hwall with ⟨hab, hbe⟩ | ⟨hab, hbe⟩
      · exact ⟨⟨(u.1, u.2), hab, hSeg_subset_cell_left u hzu⟩,
          ⟨(u.1, u.2 - 1), hbe, hSeg_subset_cell_down u hzu⟩⟩
      · exact ⟨⟨(u.1, u.2 - 1), hbe, hSeg_subset_cell_down u hzu⟩,
          ⟨(u.1, u.2), hab, hSeg_subset_cell_left u hzu⟩⟩
    · rcases hwall with ⟨hab, hbe⟩ | ⟨hab, hbe⟩
      · exact ⟨⟨(u.1, u.2), hab, vSeg_subset_cell_left u hzu⟩,
          ⟨(u.1 - 1, u.2), hbe, vSeg_subset_cell_right u hzu⟩⟩
      · exact ⟨⟨(u.1 - 1, u.2), hbe, vSeg_subset_cell_right u hzu⟩,
          ⟨(u.1, u.2), hab, vSeg_subset_cell_left u hzu⟩⟩
  · rintro ⟨⟨p, hpA, hzp⟩, ⟨q, hqA, hzq⟩⟩
    rw [mem_wallSet]
    have hpq : p ≠ q := fun h => hqA (h ▸ hpA)
    obtain ⟨hp1, hp2, hp3, hp4⟩ := Work.HornSC.mem_cell.mp hzp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := Work.HornSC.mem_cell.mp hzq
    have hd1 : p.1 - q.1 ≤ 1 := by
      have h : (p.1 : ℝ) ≤ (q.1 : ℝ) + 1 := le_trans hp1 hq2
      have : p.1 ≤ q.1 + 1 := by exact_mod_cast h
      omega
    have hd1' : q.1 - p.1 ≤ 1 := by
      have h : (q.1 : ℝ) ≤ (p.1 : ℝ) + 1 := le_trans hq1 hp2
      have : q.1 ≤ p.1 + 1 := by exact_mod_cast h
      omega
    have hd2 : p.2 - q.2 ≤ 1 := by
      have h : (p.2 : ℝ) ≤ (q.2 : ℝ) + 1 := le_trans hp3 hq4
      have : p.2 ≤ q.2 + 1 := by exact_mod_cast h
      omega
    have hd2' : q.2 - p.2 ≤ 1 := by
      have h : (q.2 : ℝ) ≤ (p.2 : ℝ) + 1 := le_trans hq3 hp4
      have : q.2 ≤ p.2 + 1 := by exact_mod_cast h
      omega
    by_cases hp2q2 : p.2 = q.2
    · -- vertical edge
      have hpq1 : p.1 ≠ q.1 := fun h => hpq (Prod.ext h hp2q2)
      have hor : q.1 = p.1 + 1 ∨ q.1 = p.1 - 1 := by omega
      rcases hor with e | e
      · have hzre : z.re = ((p.1 : ℤ) : ℝ) + 1 := by
          have hc : (q.1 : ℝ) = (p.1 : ℝ) + 1 := by rw [e]; push_cast; linarith
          exact le_antisymm hp2 (hc ▸ hq1)
        refine Or.inr ⟨(p.1 + 1, p.2), Or.inr ⟨?_, ?_⟩, ?_⟩
        · have heq : ((p.1 + 1, p.2) : ℤ × ℤ) = q := pair_eq_of e.symm hp2q2
          rw [heq]; exact hqA
        · have heq : ((p.1 + 1 - 1, p.2) : ℤ × ℤ) = p :=
            pair_eq_of (by omega : p.1 + 1 - 1 = p.1) rfl
          rw [heq]; exact hpA
        · rw [mem_vSeg]
          refine ⟨?_, ?_, ?_⟩
          · push_cast; linarith
          · exact hp3
          · exact hp4
      · have hzre : z.re = ((p.1 : ℤ) : ℝ) := by
          have hc : (q.1 : ℝ) = (p.1 : ℝ) - 1 := by rw [e]; push_cast; linarith
          have hle : z.re ≤ (p.1 : ℝ) := by
            have h := hq2; rw [hc] at h; linarith
          exact le_antisymm hle hp1
        refine Or.inr ⟨(p.1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
        · have heq : ((p.1, p.2) : ℤ × ℤ) = p := rfl
          rw [heq]; exact hpA
        · have heq : ((p.1 - 1, p.2) : ℤ × ℤ) = q := pair_eq_of e.symm hp2q2
          rw [heq]; exact hqA
        · rw [mem_vSeg]
          refine ⟨?_, ?_, ?_⟩
          · push_cast; linarith
          · exact hp3
          · exact hp4
    · by_cases hp1q1 : p.1 = q.1
      · -- horizontal edge
        have hor : q.2 = p.2 + 1 ∨ q.2 = p.2 - 1 := by omega
        rcases hor with e | e
        · have hzim : z.im = ((p.2 : ℤ) : ℝ) + 1 := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) + 1 := by rw [e]; push_cast; linarith
            exact le_antisymm hp4 (hc ▸ hq3)
          refine Or.inl ⟨(p.1, p.2 + 1), Or.inr ⟨?_, ?_⟩, ?_⟩
          · have heq : ((p.1, p.2 + 1) : ℤ × ℤ) = q := pair_eq_of hp1q1 e.symm
            rw [heq]; exact hqA
          · have heq : ((p.1, p.2 + 1 - 1) : ℤ × ℤ) = p :=
              pair_eq_of rfl (by omega : p.2 + 1 - 1 = p.2)
            rw [heq]; exact hpA
          · rw [mem_hSeg]
            refine ⟨?_, ?_, ?_⟩
            · push_cast; linarith
            · exact hp1
            · exact hp2
        · have hzim : z.im = ((p.2 : ℤ) : ℝ) := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) - 1 := by rw [e]; push_cast; linarith
            have hle : z.im ≤ (p.2 : ℝ) := by
              have h := hq4; rw [hc] at h; linarith
            exact le_antisymm hle hp3
          refine Or.inl ⟨(p.1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
          · have heq : ((p.1, p.2) : ℤ × ℤ) = p := rfl
            rw [heq]; exact hpA
          · have heq : ((p.1, p.2 - 1) : ℤ × ℤ) = q := pair_eq_of hp1q1 e.symm
            rw [heq]; exact hqA
          · rw [mem_hSeg]
            refine ⟨?_, ?_, ?_⟩
            · push_cast; linarith
            · exact hp1
            · exact hp2
      · -- corner
        have hor1 : q.1 = p.1 + 1 ∨ q.1 = p.1 - 1 := by omega
        have hor2 : q.2 = p.2 + 1 ∨ q.2 = p.2 - 1 := by omega
        rcases hor1 with e1 | e1 <;> rcases hor2 with e2 | e2
        · -- (+,+)  v = (p.1+1, p.2+1), r = (p.1,p.2+1)
          have hzre : z.re = ((p.1 : ℤ) : ℝ) + 1 := by
            have hc : (q.1 : ℝ) = (p.1 : ℝ) + 1 := by rw [e1]; push_cast; linarith
            exact le_antisymm hp2 (hc ▸ hq1)
          have hzim : z.im = ((p.2 : ℤ) : ℝ) + 1 := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) + 1 := by rw [e2]; push_cast; linarith
            exact le_antisymm hp4 (hc ▸ hq3)
          by_cases hA : ((p.1, p.2 + 1) : ℤ × ℤ) ∈ A
          · refine Or.inr ⟨(p.1 + 1, p.2 + 1), Or.inr ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1 + 1, p.2 + 1) : ℤ × ℤ) = q := pair_eq_of e1.symm e2.symm
              rw [heq]; exact hqA
            · have heq : ((p.1 + 1 - 1, p.2 + 1) : ℤ × ℤ) = (p.1, p.2 + 1) :=
                pair_eq_of (by omega : p.1 + 1 - 1 = p.1) rfl
              rw [heq]; exact hA
            · rw [mem_vSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
          · refine Or.inl ⟨(p.1, p.2 + 1), Or.inr ⟨?_, ?_⟩, ?_⟩
            · exact hA
            · have heq : ((p.1, p.2 + 1 - 1) : ℤ × ℤ) = p :=
                pair_eq_of rfl (by omega : p.2 + 1 - 1 = p.2)
              rw [heq]; exact hpA
            · rw [mem_hSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
        · -- (+,-)  v = (p.1+1, p.2), r = (p.1,p.2-1)
          have hzre : z.re = ((p.1 : ℤ) : ℝ) + 1 := by
            have hc : (q.1 : ℝ) = (p.1 : ℝ) + 1 := by rw [e1]; push_cast; linarith
            exact le_antisymm hp2 (hc ▸ hq1)
          have hzim : z.im = ((p.2 : ℤ) : ℝ) := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) - 1 := by rw [e2]; push_cast; linarith
            have hle : z.im ≤ (p.2 : ℝ) := by have h := hq4; rw [hc] at h; linarith
            exact le_antisymm hle hp3
          by_cases hA : ((p.1, p.2 - 1) : ℤ × ℤ) ∈ A
          · refine Or.inr ⟨(p.1 + 1, p.2 - 1), Or.inr ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1 + 1, p.2 - 1) : ℤ × ℤ) = q := pair_eq_of e1.symm e2.symm
              rw [heq]; exact hqA
            · have heq : ((p.1 + 1 - 1, p.2 - 1) : ℤ × ℤ) = (p.1, p.2 - 1) :=
                pair_eq_of (by omega : p.1 + 1 - 1 = p.1) rfl
              rw [heq]; exact hA
            · rw [mem_vSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
          · refine Or.inl ⟨(p.1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1, p.2) : ℤ × ℤ) = p := rfl
              rw [heq]; exact hpA
            · have heq : ((p.1, p.2 - 1) : ℤ × ℤ) = (p.1, p.2 - 1) := rfl
              rw [heq]; exact hA
            · rw [mem_hSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
        · -- (-,+)  v = (p.1, p.2+1), r = (p.1-1,p.2)
          have hzre : z.re = ((p.1 : ℤ) : ℝ) := by
            have hc : (q.1 : ℝ) = (p.1 : ℝ) - 1 := by rw [e1]; push_cast; linarith
            have hle : z.re ≤ (p.1 : ℝ) := by have h := hq2; rw [hc] at h; linarith
            exact le_antisymm hle hp1
          have hzim : z.im = ((p.2 : ℤ) : ℝ) + 1 := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) + 1 := by rw [e2]; push_cast; linarith
            exact le_antisymm hp4 (hc ▸ hq3)
          by_cases hA : ((p.1 - 1, p.2) : ℤ × ℤ) ∈ A
          · refine Or.inl ⟨(p.1 - 1, p.2 + 1), Or.inr ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1 - 1, p.2 + 1) : ℤ × ℤ) = q := pair_eq_of e1.symm e2.symm
              rw [heq]; exact hqA
            · have heq : ((p.1 - 1, p.2 + 1 - 1) : ℤ × ℤ) = (p.1 - 1, p.2) :=
                pair_eq_of rfl (by omega : p.2 + 1 - 1 = p.2)
              rw [heq]; exact hA
            · rw [mem_hSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
          · refine Or.inr ⟨(p.1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1, p.2) : ℤ × ℤ) = p := rfl
              rw [heq]; exact hpA
            · have heq : ((p.1 - 1, p.2) : ℤ × ℤ) = (p.1 - 1, p.2) := rfl
              rw [heq]; exact hA
            · rw [mem_vSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · exact hp3
              · exact hp4
        · -- (-,-)  v = (p.1,p.2), r = (p.1-1,p.2)
          have hzre : z.re = ((p.1 : ℤ) : ℝ) := by
            have hc : (q.1 : ℝ) = (p.1 : ℝ) - 1 := by rw [e1]; push_cast; linarith
            have hle : z.re ≤ (p.1 : ℝ) := by have h := hq2; rw [hc] at h; linarith
            exact le_antisymm hle hp1
          have hzim : z.im = ((p.2 : ℤ) : ℝ) := by
            have hc : (q.2 : ℝ) = (p.2 : ℝ) - 1 := by rw [e2]; push_cast; linarith
            have hle : z.im ≤ (p.2 : ℝ) := by have h := hq4; rw [hc] at h; linarith
            exact le_antisymm hle hp3
          by_cases hA : ((p.1 - 1, p.2) : ℤ × ℤ) ∈ A
          · refine Or.inl ⟨(p.1 - 1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1 - 1, p.2) : ℤ × ℤ) = (p.1 - 1, p.2) := rfl
              rw [heq]; exact hA
            · have heq : ((p.1 - 1, p.2 - 1) : ℤ × ℤ) = q := pair_eq_of e1.symm e2.symm
              rw [heq]; exact hqA
            · rw [mem_hSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith
          · refine Or.inr ⟨(p.1, p.2), Or.inl ⟨?_, ?_⟩, ?_⟩
            · have heq : ((p.1, p.2) : ℤ × ℤ) = p := rfl
              rw [heq]; exact hpA
            · have heq : ((p.1 - 1, p.2) : ℤ × ℤ) = (p.1 - 1, p.2) := rfl
              rw [heq]; exact hA
            · rw [mem_vSeg]
              refine ⟨?_, ?_, ?_⟩
              · push_cast; linarith
              · push_cast; linarith
              · push_cast; linarith


/-! ## The main theorem -/

lemma mem_cellUnion_iff {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ cellUnion A ↔ ∃ p ∈ A, z ∈ cell p := by
  rw [Work.HornSC.cellUnion, Set.mem_iUnion₂]
  constructor
  · rintro ⟨p, hpA, hzp⟩; exact ⟨p, hpA, hzp⟩
  · rintro ⟨p, hpA, hzp⟩; exact ⟨p, hpA, hzp⟩

lemma not_mem_interior_cellUnion_iff {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∉ interior (cellUnion A) ↔ ∃ q : ℤ × ℤ, q ∉ A ∧ z ∈ cell q := by
  rw [interior_cellUnion_eq A, Set.mem_ofPred_eq]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := not_forall.mp h
    obtain ⟨hzq, hqA⟩ := not_imp.mp hq
    exact ⟨q, hqA, hzq⟩
  · rintro ⟨q, hqA, hzq⟩ h
    exact hqA (h q hzq)

theorem frontier_cellUnion_eq_wallSet (A : Finset (ℤ × ℤ)) :
    frontier (cellUnion A) = wallSet A := by
  ext z
  rw [IsClosed.frontier_eq (isClosed_cellUnion A), Set.mem_sdiff, mem_cellUnion_iff,
    not_mem_interior_cellUnion_iff, mem_wallSet_iff_cells]

end Work.HornSC.CellBoundaryJordan
