import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory
open scoped Pointwise BigOperators

noncomputable section

/-- The small parameter used in the rigid tile construction. -/
def rigidEps : ℝ := (1 : ℝ) / 10

/-- The standard basis vector in `Fin d → ℝ`. -/
def rigidBasis {d : ℕ} (k : Fin d) : Fin d → ℝ := fun i => if i = k then 1 else 0

/-- The half-open unit cube in `ℝ^d`. -/
def rigidUnitCube (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) 1}

/-- The `k`-th small hole, sitting at the facet `x_k = 0`. -/
def rigidHole (d : ℕ) (k : Fin d) : Set (Fin d → ℝ) :=
  {x | x k ∈ Set.Ico (0 : ℝ) rigidEps ∧
    ∀ j : Fin d, j ≠ k → x j ∈ Set.Ico (2 * rigidEps) (3 * rigidEps)}

/-- The `k`-th bump, obtained by translating the hole by the basis vector `e_k`. -/
def rigidBump (d : ℕ) (k : Fin d) : Set (Fin d → ℝ) :=
  (fun x : Fin d → ℝ => x + rigidBasis k) '' rigidHole d k

/-- The rigid jigsaw tile. -/
def rigidTile (d : ℕ) : Set (Fin d → ℝ) :=
  (rigidUnitCube d \ ⋃ k : Fin d, rigidHole d k) ∪ ⋃ k : Fin d, rigidBump d k

/-- The integer lattice in `ℝ^d`. -/
def rigidLattice (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}

/-- Integer basis vector, real-cast version. -/
def rigidBasisInt {d : ℕ} (k : Fin d) : Fin d → ℤ := fun i => if i = k then 1 else 0

/-- Cast an integer vector into `ℝ^d`. -/
def rigidIntVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ := fun i => (z i : ℝ)

/-- Componentwise integer floor of a vector. -/
def rigidFloorVec {d : ℕ} (x : Fin d → ℝ) : Fin d → ℤ := fun i => Int.floor (x i)

lemma rigidEps_pos : 0 < rigidEps := by
  norm_num [rigidEps]

lemma rigidEps_lt_one : rigidEps < 1 := by
  norm_num [rigidEps]

lemma two_rigidEps_pos : 0 < 2 * rigidEps := by
  norm_num [rigidEps]

lemma three_rigidEps_lt_one : 3 * rigidEps < 1 := by
  norm_num [rigidEps]

lemma rigidEps_lt_two_rigidEps : rigidEps < 2 * rigidEps := by
  norm_num [rigidEps]

lemma rigidHole_subset_unitCube {d : ℕ} (k : Fin d) : rigidHole d k ⊆ rigidUnitCube d := by
  intro x hx i
  by_cases hik : i = k
  · subst hik
    exact ⟨(Set.mem_Ico.mp hx.1).1, lt_trans (Set.mem_Ico.mp hx.1).2 (by simpa using rigidEps_lt_one)⟩
  · have hi := hx.2 i hik
    rcases Set.mem_Ico.mp hi with ⟨hle, hlt⟩
    exact ⟨by linarith [two_rigidEps_pos], by linarith [three_rigidEps_lt_one]⟩

lemma rigidHole_pairwise_disjoint {d : ℕ} : Set.PairwiseDisjoint (Set.univ : Set (Fin d)) (rigidHole d) := by
  rw [Set.pairwiseDisjoint_iff]
  intro k hk l hl h
  by_cases hkl : k = l
  · exact hkl
  · exfalso
    rcases h with ⟨x, hx⟩
    have h1 : x k ∈ Set.Ico (0 : ℝ) rigidEps := hx.1.1
    have h2 : x k ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hx.2.2 k hkl
    have hlow : x k < rigidEps := (Set.mem_Ico.mp h1).2
    have hhigh : 2 * rigidEps ≤ x k := (Set.mem_Ico.mp h2).1
    have heps : 0 < rigidEps := rigidEps_pos
    linarith

lemma rigidIntVec_add {d} (m n : Fin d→ℤ) : rigidIntVec (fun i => m i + n i) = rigidIntVec m + rigidIntVec n := by ext i; simp [rigidIntVec, Pi.add_apply]
lemma rigidIntVec_basis {d} (k : Fin d) : rigidIntVec (rigidBasisInt k) = rigidBasis k := by ext i; simp [rigidIntVec, rigidBasisInt, rigidBasis]

lemma rigidHole_subset_unitCube2 {d} (k : Fin d) : rigidHole d k ⊆ rigidUnitCube d := by
  intro x hx i
  by_cases hik : i = k
  · subst hik
    rcases Set.mem_Ico.mp hx.1 with ⟨h0,hlt⟩
    exact ⟨h0, by linarith [rigidEps_lt_one]⟩
  · have hi := hx.2 i hik
    rcases Set.mem_Ico.mp hi with ⟨hle,hlt⟩
    constructor
    · norm_num [rigidEps] at hle ⊢; linarith
    · norm_num [rigidEps] at hlt ⊢; linarith

lemma rigidHole_pairwise_disjoint2 {d} : Set.PairwiseDisjoint (Set.univ : Set (Fin d)) (rigidHole d) := by
  rw [Set.pairwiseDisjoint_iff]
  intro k hk l hl h
  by_cases hkl : k = l
  · exact hkl
  · exfalso
    rcases h with ⟨x,hx⟩
    have h1 : x k ∈ Set.Ico (0:ℝ) rigidEps := hx.1.1
    have h2 : x k ∈ Set.Ico (2*rigidEps) (3*rigidEps) := hx.2.2 k hkl
    have hlow : x k < rigidEps := (Set.mem_Ico.mp h1).2
    have hhigh : 2*rigidEps ≤ x k := (Set.mem_Ico.mp h2).1
    have heps : 0 < rigidEps := rigidEps_pos
    linarith

lemma rigidTile_mem_iff {d} {r : Fin d→ℝ} :
    r ∈ rigidTile d ↔ (r ∈ rigidUnitCube d ∧ r ∉ ⋃ k : Fin d, rigidHole d k) ∨
      ∃ k : Fin d, ∃ q ∈ rigidHole d k, r = q + rigidBasis k := by
  constructor
  · intro h
    rcases h with hmain | hbump
    · exact Or.inl hmain
    · rw [Set.mem_iUnion] at hbump
      rcases hbump with ⟨k,hk⟩
      rcases hk with ⟨q,hq,hqk⟩
      exact Or.inr ⟨k,q,hq,hqk.symm⟩
  · intro h
    rcases h with hmain | hbump
    · exact Or.inl hmain
    · refine Or.inr ?_
      rw [Set.mem_iUnion]
      rcases hbump with ⟨k,q,hq,hqk⟩
      exact ⟨k,q,hq,hqk.symm⟩

lemma rigidUnitCube_sub_mem_Ioo {d} {a b : Fin d→ℝ} (ha : a ∈ rigidUnitCube d) (hb : b ∈ rigidUnitCube d) (i : Fin d) :
    a i - b i ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hai := Set.mem_Ico.mp (ha i)
  have hbi := Set.mem_Ico.mp (hb i)
  constructor <;> linarith

lemma int_eq_zero_of_intCast_mem_Ioo {n : ℤ} (h : (n : ℝ) ∈ Set.Ioo (-1 : ℝ) 1) : n = 0 := by
  rcases h with ⟨h1,h2⟩
  have h1i : (-1 : ℤ) < n := by exact_mod_cast h1
  have h2i : n < (1 : ℤ) := by exact_mod_cast h2
  omega

lemma rigid_sub_int_eq_of_mem_Ioo {d} {a b : Fin d→ℝ} {m : Fin d→ℤ}
    (ha : a ∈ rigidUnitCube d) (hb : b ∈ rigidUnitCube d) (h : ∀ i, a i - b i = (m i : ℝ)) : a = b ∧ m = 0 := by
  constructor
  · apply funext
    intro i
    have hmem := rigidUnitCube_sub_mem_Ioo ha hb i
    have hm : (m i : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [h i] using hmem
    have hmi : m i = 0 := int_eq_zero_of_intCast_mem_Ioo hm
    have := h i
    rw [hmi] at this
    norm_num at this
    linarith
  · apply funext
    intro i
    have hmem := rigidUnitCube_sub_mem_Ioo ha hb i
    have hm : (m i : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [h i] using hmem
    exact int_eq_zero_of_intCast_mem_Ioo hm

lemma rigidTile_disjoint_int {d} {n : Fin d→ℤ} (hn : n ≠ 0) :
    Disjoint (rigidTile d) (rigidIntVec n +ᵥ rigidTile d) := by
  rw [Set.disjoint_left]
  intro r hr hshift
  rw [Set.mem_vadd_set] at hshift
  rcases hshift with ⟨s, hs, hsr⟩
  have hsr' : rigidIntVec n + s = r := by simpa [vadd_eq_add] using hsr
  have hreq : r = rigidIntVec n + s := hsr'.symm
  rcases rigidTile_mem_iff.mp hr with hrmain | hrbump
  · rcases hrmain with ⟨hrQ, hrnot⟩
    rcases rigidTile_mem_iff.mp hs with hsmain | hsbump
    · rcases hsmain with ⟨hsQ, hsnot⟩
      apply hn
      have hdiff : ∀ i, r i - s i = (n i : ℝ) := by
        intro i
        have h := congrFun hreq i
        simp [rigidIntVec, Pi.add_apply] at h
        linarith
      exact (rigid_sub_int_eq_of_mem_Ioo hrQ hsQ hdiff).2
    · rcases hsbump with ⟨l, q, hq, hsq⟩
      have hqQ : q ∈ rigidUnitCube d := rigidHole_subset_unitCube2 l hq
      have hdiff : ∀ i, r i - q i = ((fun i => n i + rigidBasisInt l i) i : ℝ) := by
        intro i
        have h := congrFun hreq i
        have hsq_i := congrFun hsq i
        by_cases hil : i = l
        · subst hil
          simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply] at h hsq_i ⊢
          linarith
        · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hil] at h hsq_i ⊢
          linarith
      have hsub := rigid_sub_int_eq_of_mem_Ioo hrQ hqQ hdiff
      have hr_eq_q : r = q := hsub.1
      have hr_in_hole : r ∈ rigidHole d l := by simpa [hr_eq_q] using hq
      have hr_in_holes : r ∈ ⋃ k : Fin d, rigidHole d k := by
        rw [Set.mem_iUnion]; exact ⟨l, hr_in_hole⟩
      exact hrnot hr_in_holes
  · rcases hrbump with ⟨k, q, hq, hrq⟩
    rcases rigidTile_mem_iff.mp hs with hsmain | hsbump
    · rcases hsmain with ⟨hsQ, hsnot⟩
      have hqQ : q ∈ rigidUnitCube d := rigidHole_subset_unitCube2 k hq
      have hdiff : ∀ i, q i - s i = ((fun i => n i - rigidBasisInt k i) i : ℝ) := by
        intro i
        have h := congrFun hreq i
        have hrq_i := congrFun hrq i
        by_cases hik : i = k
        · subst hik
          simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply] at h hrq_i ⊢
          linarith
        · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hik] at h hrq_i ⊢
          linarith
      have hsub := rigid_sub_int_eq_of_mem_Ioo hqQ hsQ hdiff
      have hs_eq_q : s = q := by
        apply funext; intro i
        have hsub1_i := congrFun hsub.1 i
        linarith
      have hs_in_hole : s ∈ rigidHole d k := by simpa [hs_eq_q] using hq
      have hs_in_holes : s ∈ ⋃ j : Fin d, rigidHole d j := by
        rw [Set.mem_iUnion]; exact ⟨k, hs_in_hole⟩
      exact hsnot hs_in_holes
    · rcases hsbump with ⟨l, q', hq', hsq'⟩
      by_cases hkl : k = l
      · subst hkl
        apply hn
        have hqQ : q ∈ rigidUnitCube d := rigidHole_subset_unitCube2 k hq
        have hq'Q : q' ∈ rigidUnitCube d := rigidHole_subset_unitCube2 k hq'
        have hdiff : ∀ i, q i - q' i = (n i : ℝ) := by
          intro i
          have h := congrFun hreq i
          have hrq_i := congrFun hrq i
          have hsq'_i := congrFun hsq' i
          by_cases hik : i = k
          · subst hik
            simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply] at h hrq_i hsq'_i ⊢
            linarith
          · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hik] at h hrq_i hsq'_i ⊢
            linarith
        exact (rigid_sub_int_eq_of_mem_Ioo hqQ hq'Q hdiff).2
      · exfalso
        have hqQ : q ∈ rigidUnitCube d := rigidHole_subset_unitCube2 k hq
        have hq'Q : q' ∈ rigidUnitCube d := rigidHole_subset_unitCube2 l hq'
        have hdiff : ∀ i, q i - q' i = ((fun i => n i + rigidBasisInt l i - rigidBasisInt k i) i : ℝ) := by
          intro i
          have h := congrFun hreq i
          have hrq_i := congrFun hrq i
          have hsq'_i := congrFun hsq' i
          by_cases hik : i = k
          · subst hik
            by_cases hil : i = l
            · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hil] at h hrq_i hsq'_i ⊢
              linarith
            · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hil] at h hrq_i hsq'_i ⊢
              linarith
          · by_cases hil : i = l
            · subst hil
              simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hik] at h hrq_i hsq'_i ⊢
              linarith
            · simp [rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hik, hil] at h hrq_i hsq'_i ⊢
              linarith
        have hsub := rigid_sub_int_eq_of_mem_Ioo hqQ hq'Q hdiff
        have hqq' : q = q' := hsub.1
        have hq'_in_k : q' ∈ rigidHole d k := by simpa [← hqq'] using hq
        have hq'_in_l : q' ∈ rigidHole d l := hq'
        have hkl_eq : k = l := Set.PairwiseDisjoint.elim_set rigidHole_pairwise_disjoint2 (by simp) (by simp) q' hq'_in_k hq'_in_l
        exact hkl hkl_eq

-- rigidUnitCube tiling point
lemma rigidUnitCube_tiling_point (d) (x : Fin d→ℝ) :
    ∃! v : Fin d→ℝ, v ∈ rigidLattice d ∧ x ∈ v +ᵥ rigidUnitCube d := by
  let z : Fin d → ℤ := rigidFloorVec x
  let v : Fin d → ℝ := rigidIntVec z
  refine ⟨v, ?_, ?_⟩
  · constructor
    · refine ⟨z, ?_⟩; intro i; rfl
    · rw [Set.mem_vadd_set]
      refine ⟨fun i => x i - v i, ?_, ?_⟩
      · intro i
        have hle := Int.floor_le (x i)
        have hlt := Int.lt_floor_add_one (x i)
        have hvi : v i = (Int.floor (x i) : ℝ) := by simp [v, z, rigidIntVec, rigidFloorVec]
        constructor
        · change 0 ≤ x i - v i
          rw [hvi]; linarith
        · change x i - v i < 1
          rw [hvi]; linarith
      · ext i
        simp [vadd_eq_add, v]
  · intro w hw
    rcases hw with ⟨hwL, hxw⟩
    rcases hwL with ⟨n, hn⟩
    rw [Set.mem_vadd_set] at hxw
    rcases hxw with ⟨y, hyQ, hxy⟩
    apply funext
    intro i
    have hxyi : w i + y i = x i := by
      have h := congrFun hxy i
      simpa [vadd_eq_add, Pi.add_apply] using h
    have hxyi' : x i = w i + y i := hxyi.symm
    have hy0 : 0 ≤ y i := (Set.mem_Ico.mp (hyQ i)).1
    have hy1 : y i < 1 := (Set.mem_Ico.mp (hyQ i)).2
    have hwi : w i = (n i : ℝ) := hn i
    have hfloor : Int.floor (x i) = n i := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [hxyi', hwi]; linarith
      · rw [hxyi', hwi]; linarith
    simp [v, z, rigidIntVec, rigidFloorVec, hfloor, hwi]

lemma rigidUnitCube_tiling (d) : IsContinuousTiling (rigidUnitCube d) (rigidLattice d) := by
  refine MeasureTheory.ae_of_all (μ := volume) ?_
  intro x
  exact rigidUnitCube_tiling_point d x

lemma rigidTile_tiling_unique {d} (x : Fin d→ℝ) {v u : Fin d→ℝ}
    (hvL : v ∈ rigidLattice d) (huL : u ∈ rigidLattice d)
    (hxv : x ∈ v +ᵥ rigidTile d) (hxu : x ∈ u +ᵥ rigidTile d) : v = u := by
  rcases hvL with ⟨a, ha⟩
  rcases huL with ⟨b, hb⟩
  let n : Fin d→ℤ := fun i => a i - b i
  have hvu_add : v = u + rigidIntVec n := by
    ext i
    simp [n, rigidIntVec, Pi.add_apply, ha i, hb i]
  by_contra hvune
  have hn : n ≠ 0 := by
    intro hn0
    apply hvune
    rw [hvu_add]
    have hzero : rigidIntVec n = 0 := by
      ext i
      simp [n, rigidIntVec, hn0]
    rw [hzero]
    simp
  rw [Set.mem_vadd_set] at hxv hxu
  rcases hxv with ⟨r, hrR, hvr⟩
  rcases hxu with ⟨s, hsR, hus⟩
  have hvr_add : v + r = x := by simpa [vadd_eq_add] using hvr
  have hus_add : u + s = x := by simpa [vadd_eq_add] using hus
  have hsum : v + r = u + s := by rw [hvr_add, hus_add]
  have hsum' : (u + rigidIntVec n) + r = u + s := by simpa [hvu_add] using hsum
  have hshift_eq : rigidIntVec n + r = s := by
    ext i
    have hi := congrFun hsum' i
    simp [rigidIntVec, Pi.add_apply] at hi ⊢
    linarith
  have hs_shift : s ∈ rigidIntVec n +ᵥ rigidTile d := by
    rw [Set.mem_vadd_set]
    exact ⟨r, hrR, by simpa [vadd_eq_add] using hshift_eq⟩
  have hdisj : Disjoint (rigidTile d) (rigidIntVec n +ᵥ rigidTile d) := rigidTile_disjoint_int hn
  exact (Set.disjoint_left.mp hdisj) hsR hs_shift

-- rigidTile tiling point
lemma rigidTile_tiling_point (d) (x : Fin d→ℝ) :
    ∃! v : Fin d→ℝ, v ∈ rigidLattice d ∧ x ∈ v +ᵥ rigidTile d := by
  rcases rigidUnitCube_tiling_point d x with ⟨v, hv, huniq⟩
  rcases hv with ⟨hvL, hxvQ⟩
  rw [Set.mem_vadd_set] at hxvQ
  rcases hxvQ with ⟨y, hyQ, hvyx⟩
  have hvyx_add : v + y = x := by simpa [vadd_eq_add] using hvyx
  by_cases hy_holes : y ∈ ⋃ k : Fin d, rigidHole d k
  · rw [Set.mem_iUnion] at hy_holes
    rcases hy_holes with ⟨k, hk⟩
    let w : Fin d→ℝ := v - rigidIntVec (rigidBasisInt k)
    have hwL : w ∈ rigidLattice d := by
      rcases hvL with ⟨z,hz⟩
      refine ⟨fun i => z i - rigidBasisInt k i, ?_⟩
      intro i
      simp [w, rigidIntVec, rigidBasisInt, hz]
    have hybump : y + rigidBasis k ∈ rigidBump d k := by
      unfold rigidBump; exact ⟨y, hk, rfl⟩
    have hybR : y + rigidBasis k ∈ rigidTile d := by
      refine Or.inr ?_
      rw [Set.mem_iUnion]
      exact ⟨k, hybump⟩
    have hxw : x ∈ w +ᵥ rigidTile d := by
      rw [Set.mem_vadd_set]
      refine ⟨y + rigidBasis k, hybR, ?_⟩
      have hmain : w + (y + rigidBasis k) = x := by
        ext i
        have hi := congrFun hvyx_add i
        by_cases hik : i = k
        · subst hik
          simp [w, rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply] at hi ⊢
          linarith
        · simp [w, rigidIntVec, rigidBasisInt, rigidBasis, Pi.add_apply, hik] at hi ⊢
          linarith
      simpa [vadd_eq_add] using hmain
    refine ⟨w, ⟨hwL, hxw⟩, ?_⟩
    intro u hu
    rcases hu with ⟨huL, hxuR⟩
    exact (rigidTile_tiling_unique (x := x) (v := w) (u := u) hwL huL hxw hxuR).symm
  · -- y in main part
    have hyR : y ∈ rigidTile d := by
      refine Or.inl ⟨hyQ, hy_holes⟩
    have hxvR : x ∈ v +ᵥ rigidTile d := by
      rw [Set.mem_vadd_set]
      exact ⟨y, hyR, hvyx⟩
    refine ⟨v, ⟨hvL, hxvR⟩, ?_⟩
    intro u hu
    rcases hu with ⟨huL, hxuR⟩
    exact (rigidTile_tiling_unique (x := x) (v := v) (u := u) hvL huL hxvR hxuR).symm



lemma rigidUnitCube_eq_pi (d : ℕ) :
    rigidUnitCube d = Set.univ.pi (fun _ : Fin d => Set.Ico (0 : ℝ) 1) := by
  ext x
  simp [rigidUnitCube]

lemma rigidHole_eq_pi {d : ℕ} (k : Fin d) :
    rigidHole d k = Set.univ.pi (fun j : Fin d => if j = k then Set.Ico (0 : ℝ) rigidEps
      else Set.Ico (2 * rigidEps) (3 * rigidEps)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_pi]
    intro i hi
    by_cases hik : i = k
    · subst hik
      simpa using hx.1
    · simpa [hik] using hx.2 i hik
  · intro hx
    rw [Set.mem_pi] at hx
    constructor
    · simpa using hx k (by simp)
    · intro j hjk
      simpa [hjk] using hx j (by simp)

lemma rigidUnitCube_measurable (d : ℕ) : MeasurableSet (rigidUnitCube d) := by
  rw [rigidUnitCube_eq_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

lemma rigidHole_measurable {d : ℕ} (k : Fin d) : MeasurableSet (rigidHole d k) := by
  rw [rigidHole_eq_pi]
  apply MeasurableSet.univ_pi
  intro j
  by_cases h : j = k
  · simp [h]
  · simp [h]

lemma rigidBump_measurable {d : ℕ} (k : Fin d) : MeasurableSet (rigidBump d k) := by
  unfold rigidBump
  rw [Set.image_add_right]
  exact MeasurableSet.preimage (rigidHole_measurable k) (continuous_add_const (-rigidBasis k)).measurable

lemma rigidTile_measurable (d : ℕ) : MeasurableSet (rigidTile d) := by
  unfold rigidTile
  apply MeasurableSet.union
  · apply MeasurableSet.diff (rigidUnitCube_measurable d)
    apply MeasurableSet.iUnion
    intro k
    exact rigidHole_measurable k
  · apply MeasurableSet.iUnion
    intro k
    exact rigidBump_measurable k

lemma rigidTile_bounded (d : ℕ) : IsBounded (rigidTile d) := by
  let B : Set (Fin d → ℝ) := Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) (1 + rigidEps))
  have hB : IsBounded B := by
    rw [Bornology.isBounded_pi]
    right
    intro i
    exact Metric.isBounded_Icc _ _
  refine hB.subset ?_
  intro r hr i hi
  rw [rigidTile_mem_iff] at hr
  rcases hr with hmain | hbump
  · rcases hmain with ⟨hQ, _⟩
    rcases Set.mem_Ico.mp (hQ i) with ⟨hlo, hlt⟩
    exact ⟨hlo, by linarith [rigidEps_pos]⟩
  · rcases hbump with ⟨k, q, hq, hqk⟩
    have hqk_i : r i = q i + rigidBasis k i := by
      simpa [Pi.add_apply] using congrFun hqk i
    by_cases hik : i = k
    · subst hik
      rcases Set.mem_Ico.mp hq.1 with ⟨h0, hlt⟩
      rw [hqk_i]
      have hbk : rigidBasis i i = 1 := by simp [rigidBasis]
      rw [hbk]
      constructor <;> linarith [rigidEps_pos]
    · have hqj := hq.2 i hik
      rcases Set.mem_Ico.mp hqj with ⟨h0, hlt⟩
      rw [hqk_i]
      have hbk : rigidBasis k i = 0 := by simp [rigidBasis, hik]
      rw [hbk]
      have h31 : 3 * rigidEps < 1 + rigidEps := by norm_num [rigidEps]
      constructor <;> linarith [rigidEps_pos, h31]



def rigidCenterBox (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi (fun _ : Fin d => Set.Ico (4 * rigidEps) (5 * rigidEps))

lemma rigidCenterBox_subset_unitCube (d : ℕ) : rigidCenterBox d ⊆ rigidUnitCube d := by
  intro y hy i
  change y ∈ Set.univ.pi (fun _ : Fin d => Set.Ico (4 * rigidEps) (5 * rigidEps)) at hy
  rw [Set.mem_pi] at hy
  rcases Set.mem_Ico.mp (hy i (by simp)) with ⟨hlo, hlt⟩
  constructor <;> norm_num [rigidEps] at hlo hlt ⊢ <;> linarith

lemma rigidCenterBox_not_mem_hole {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ rigidCenterBox d) (k : Fin d) :
    y ∉ rigidHole d k := by
  change y ∈ Set.univ.pi (fun _ : Fin d => Set.Ico (4 * rigidEps) (5 * rigidEps)) at hy
  rw [Set.mem_pi] at hy
  rcases Set.mem_Ico.mp (hy k (by simp)) with ⟨hlo, hlt⟩
  rw [rigidHole]
  intro hk
  have h0 : y k < rigidEps := (Set.mem_Ico.mp hk.1).2
  linarith

lemma rigidCenterBox_subset_rigidTile (d : ℕ) : rigidCenterBox d ⊆ rigidTile d := by
  intro y hy
  refine Or.inl ⟨?_, ?_⟩
  · exact rigidCenterBox_subset_unitCube d hy
  · intro hmem
    rw [Set.mem_iUnion] at hmem
    rcases hmem with ⟨k, hk⟩
    exact rigidCenterBox_not_mem_hole hy k hk

lemma rigidCenterBox_volume_pos (d : ℕ) : 0 < volume (rigidCenterBox d) := by
  rw [rigidCenterBox, Real.volume_pi_Ico]
  have hpos : 0 < ENNReal.ofReal ((5 * rigidEps) - (4 * rigidEps)) := by
    rw [ENNReal.ofReal_pos]
    norm_num [rigidEps]
  have hpow := ENNReal.pow_pos hpos (Fintype.card (Fin d))
  simpa [Finset.prod_const] using hpow

lemma rigidTile_volume_pos (d : ℕ) : 0 < volume (rigidTile d) := by
  have hmono := MeasureTheory.measure_mono (μ := volume) (rigidCenterBox_subset_rigidTile d)
  exact lt_of_lt_of_le (rigidCenterBox_volume_pos d) hmono

lemma rigidTile_tiling (d : ℕ) : IsContinuousTiling (rigidTile d) (rigidLattice d) := by
  refine MeasureTheory.ae_of_all (μ := volume) ?_
  intro x
  exact rigidTile_tiling_point d x


-- ============ Rigidity framework ============

/-- sup-distance < 1 between coordinate functions -/
def rigidClose {d : ℕ} (u w : Fin d → ℝ) : Prop := ∀ i : Fin d, |u i - w i| < 1

/-- Positive volume of a half-open product box. -/
lemma volume_pos_pi_Ico {d : ℕ} (a b : Fin d → ℝ) (h : ∀ i : Fin d, a i < b i) :
    0 < volume (Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i))) := by
  rw [Real.volume_pi_Ico]
  let f : Fin d → ENNReal := fun i => ENNReal.ofReal (b i - a i)
  have hf : ∀ i : Fin d, 0 < f i := by
    intro i
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (h i))
  have hpos : 0 < ∏ i : Fin d, f i := by
    classical
    -- induction over the finite index set
    have hmain : ∀ (s : Finset (Fin d)), 0 < s.prod f := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s' has ihs
        rw [Finset.prod_insert has]
        exact ENNReal.mul_pos (ne_of_gt (hf a)) (ne_of_gt ihs)
    simpa using hmain Finset.univ
  simpa [f] using hpos

/-- A point whose `p`-th coordinate avoids the hole ranges is in no hole box. -/
lemma not_mem_hole_union_of_coord_avoid {d : ℕ} {x : Fin d → ℝ} {p : Fin d}
    (hp : x p ∉ Set.Ico (0 : ℝ) rigidEps ∪ Set.Ico (2 * rigidEps) (3 * rigidEps)) :
    x ∉ ⋃ j : Fin d, rigidHole d j := by
  intro hmem
  rw [Set.mem_iUnion] at hmem
  rcases hmem with ⟨j, hj⟩
  by_cases hjp : j = p
  · subst j
    exact hp (Or.inl hj.1)
  · exact hp (Or.inr (hj.2 p (by intro hpj; exact hjp hpj.symm)))

/-- If two distinct coordinates of `x` are `2ε`-small then `x` is in no hole. -/
lemma not_mem_hole_union_of_two_small {d : ℕ} {x : Fin d → ℝ} {a b : Fin d}
    (hab : a ≠ b) (ha : x a < 2 * rigidEps) (hb : x b < 2 * rigidEps) :
    x ∉ ⋃ j : Fin d, rigidHole d j := by
  intro hmem
  rw [Set.mem_iUnion] at hmem
  rcases hmem with ⟨j, hj⟩
  by_cases hja : j = a
  · subst j
    have hb' : x b ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hj.2 b (by intro h; exact hab h.symm)
    have hbge : 2 * rigidEps ≤ x b := (Set.mem_Ico.mp hb').1
    linarith
  · have ha' : x a ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hj.2 a (by intro haj; exact hja haj.symm)
    have hage : 2 * rigidEps ≤ x a := (Set.mem_Ico.mp ha').1
    linarith

lemma rigid_overlap_of_box {d : ℕ} (v : Fin d → ℝ) (a b : Fin d → ℝ)
    (hab : ∀ i : Fin d, a i < b i)
    (hR : ∀ x : Fin d → ℝ,
      x ∈ Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i)) → x ∈ rigidTile d)
    (hRv : ∀ x : Fin d → ℝ,
      x ∈ Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i)) → x - v ∈ rigidTile d) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  let B : Set (Fin d → ℝ) := Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i))
  have hposB : 0 < volume B := volume_pos_pi_Ico a b hab
  have hsub : B ⊆ {x | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
    intro x hx
    constructor
    · exact hR x hx
    · rw [Set.mem_vadd_set]
      exact ⟨x - v, hRv x hx, by simp⟩
  exact lt_of_lt_of_le hposB (measure_mono hsub)

lemma coord_not_in_ranges_of_ge {r : ℝ} (h : 3 * rigidEps ≤ r) :
    r ∉ Set.Ico (0 : ℝ) rigidEps ∪ Set.Ico (2 * rigidEps) (3 * rigidEps) := by
  rintro (h1 | h2)
  · have : r < rigidEps := (Set.mem_Ico.mp h1).2
    linarith [rigidEps_pos]
  · have : r < 3 * rigidEps := (Set.mem_Ico.mp h2).2
    linarith

lemma mem_rigidTile_box {d : ℕ} {a b : Fin d → ℝ} {x : Fin d → ℝ}
    (hx : x ∈ Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i)))
    (h0 : ∀ i : Fin d, 0 ≤ a i) (h1 : ∀ i : Fin d, b i ≤ 1)
    (hnot : x ∉ ⋃ j : Fin d, rigidHole d j) : x ∈ rigidTile d := by
  rw [rigidTile_mem_iff]
  left
  constructor
  · intro i
    have hxi := (Set.mem_pi.mp hx) i (by simp)
    rcases Set.mem_Ico.mp hxi with ⟨hlo, hlt⟩
    constructor <;> linarith [h0 i, h1 i]
  · exact hnot

lemma mem_shift_rigidTile_box {d : ℕ} {v a b : Fin d → ℝ} {x : Fin d → ℝ}
    (hx : x ∈ Set.univ.pi (fun i : Fin d => Set.Ico (a i) (b i)))
    (h0 : ∀ i : Fin d, 0 ≤ a i - v i) (h1 : ∀ i : Fin d, b i - v i ≤ 1)
    (hnot : x - v ∉ ⋃ j : Fin d, rigidHole d j) : x - v ∈ rigidTile d := by
  apply mem_rigidTile_box (a := fun i => a i - v i) (b := fun i => b i - v i) (x := x - v)
  · intro i hi
    change x i - v i ∈ Set.Ico (a i - v i) (b i - v i)
    have hxi := (Set.mem_pi.mp hx) i (by simp)
    rcases Set.mem_Ico.mp hxi with ⟨hlo, hlt⟩
    constructor <;> linarith
  · exact h0
  · exact h1
  · simpa using hnot

lemma coord_in_pi_of_coord {d : ℕ} {a b : Fin d → ℝ} {x : Fin d → ℝ} {i : Fin d}
    (hx : x ∈ Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j))) :
    x i ∈ Set.Ico (a i) (b i) := by
  exact (Set.mem_pi.mp hx) i (by simp)

lemma fin1_eq_zero (i : Fin 1) : i = 0 := by
  apply Fin.ext
  omega

lemma fin1_mem_rigidTile {x : Fin 1 → ℝ} (hlo : rigidEps ≤ x 0) (hup : x 0 < 1 + rigidEps) :
    x ∈ rigidTile 1 := by
  by_cases hx1 : x 0 < 1
  · rw [rigidTile_mem_iff]
    left
    constructor
    · intro i
      rw [fin1_eq_zero i]
      constructor
      · linarith [hlo, rigidEps_pos]
      · exact hx1
    · intro hmem
      rw [Set.mem_iUnion] at hmem
      rcases hmem with ⟨j, hj⟩
      have hj0 : j = 0 := fin1_eq_zero j
      subst j
      have : x 0 < rigidEps := (Set.mem_Ico.mp (hj.1)).2
      linarith
  · rw [rigidTile_mem_iff]
    right
    refine ⟨(0 : Fin 1), (fun i : Fin 1 => x i - 1), ?_, ?_⟩
    · -- q ∈ rigidHole 1 0
      constructor
      · have hqlo : 0 ≤ x 0 - 1 := by linarith
        have hqhi : x 0 - 1 < rigidEps := by linarith
        constructor
        · exact hqlo
        · exact hqhi
      · intro j hj
        exact False.elim (hj (fin1_eq_zero j))
    · -- x = q + rigidBasis 0
      funext i
      rw [fin1_eq_zero i]
      simp [rigidBasis]

lemma rigid_overlap_fin1 (v : Fin 1 → ℝ) (hv : rigidClose v 0) :
    0 < volume {x : Fin 1 → ℝ | x ∈ rigidTile 1 ∧ x ∈ v +ᵥ rigidTile 1} := by
  classical
  have hv0 : |v 0| < 1 := by simpa using hv 0
  have hv0lt : v 0 < 1 := by
    rw [abs_lt] at hv0
    linarith
  by_cases hvpos : 0 ≤ v 0
  · let a : Fin 1 → ℝ := fun i => v i + rigidEps
    let b : Fin 1 → ℝ := fun i => 1 + rigidEps
    apply rigid_overlap_of_box (d := 1) (v := v) (a := a) (b := b)
    · intro i
      rw [fin1_eq_zero i]
      dsimp [a, b]
      linarith [rigidEps_pos, hvpos]
    · intro x hx
      have hx0 : x 0 ∈ Set.Ico (v 0 + rigidEps) (1 + rigidEps) := (Set.mem_pi.mp hx) 0 (by simp)
      exact fin1_mem_rigidTile (by linarith [(Set.mem_Ico.mp hx0).1]) (by linarith [(Set.mem_Ico.mp hx0).2])
    · intro x hx
      have hx0 : x 0 ∈ Set.Ico (v 0 + rigidEps) (1 + rigidEps) := (Set.mem_pi.mp hx) 0 (by simp)
      have h1 : rigidEps ≤ (x - v) 0 := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hx0).1]
      have h2 : (x - v) 0 < 1 + rigidEps := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hx0).2]
      exact fin1_mem_rigidTile h1 h2
  · have hv0gt : -1 < v 0 := by
      rw [abs_lt] at hv0
      linarith
    let a : Fin 1 → ℝ := fun i => rigidEps
    let b : Fin 1 → ℝ := fun i => 1 + rigidEps + v i
    apply rigid_overlap_of_box (d := 1) (v := v) (a := a) (b := b)
    · intro i
      rw [fin1_eq_zero i]
      dsimp [a, b]
      linarith [rigidEps_pos, hvpos, hv0gt]
    · intro x hx
      have hx0 : x 0 ∈ Set.Ico rigidEps (1 + rigidEps + v 0) := (Set.mem_pi.mp hx) 0 (by simp)
      exact fin1_mem_rigidTile (by linarith [(Set.mem_Ico.mp hx0).1]) (by linarith [(Set.mem_Ico.mp hx0).2, hvpos])
    · intro x hx
      have hx0 : x 0 ∈ Set.Ico rigidEps (1 + rigidEps + v 0) := (Set.mem_pi.mp hx) 0 (by simp)
      have h1 : rigidEps ≤ (x - v) 0 := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hx0).1, hvpos]
      have h2 : (x - v) 0 < 1 + rigidEps := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hx0).2]
      exact fin1_mem_rigidTile h1 h2


/-- Case A, first half (`v_p >= 0`): a witness coordinate with `|v_p| < 1 - 4ε`
lets an explicit slice `[v_p+3ε, v_p+4ε)` clear all hole ranges for both `x` and `x-v`. -/
lemma rigid_overlap_caseA_ge0 {d : ℕ} {v : Fin d → ℝ} {p : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hvp : |v p| < 1 - 4 * rigidEps) (hvp0 : 0 ≤ v p) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let a : Fin d → ℝ := fun i => if i = p then v p + 3 * rigidEps else max 0 (v i)
  let b : Fin d → ℝ := fun i => if i = p then v p + 4 * rigidEps else min 1 (1 + v i)
  apply rigid_overlap_of_box (d := d) (v := v) (a := a) (b := b)
  · intro i
    by_cases hip : i = p
    · subst i
      simp [a, b]
      linarith [rigidEps_pos]
    · have hvlow : -1 < v i := (abs_lt.mp (hv i)).1
      have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
      have hmax : max 0 (v i) < min 1 (1 + v i) := by
        by_cases hvi0 : 0 ≤ v i
        · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
          have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
          rw [hmax', hmin']
          exact hvhi
        · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
          have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
          rw [hmax', hmin']
          linarith
      simpa [a, b, hip] using hmax
  · intro x hx
    apply mem_rigidTile_box (a := a) (b := b) (x := x)
    · exact hx
    · intro i
      by_cases hip : i = p
      · subst i
        simp [a]
        linarith [hvp0, rigidEps_pos]
      · have : 0 ≤ max 0 (v i) := le_max_left 0 (v i)
        simpa [a, hip] using this
    · intro i
      by_cases hip : i = p
      · subst i
        simp [b]
        have hvpl : v p < 1 - 4 * rigidEps := (abs_lt.mp hvp).2
        linarith
      · have : min 1 (1 + v i) ≤ 1 := min_le_left 1 (1 + v i)
        simpa [b, hip] using this
    · have hxp' : x p ∈ Set.Ico (v p + 3 * rigidEps) (v p + 4 * rigidEps) := by
        simpa [a, b] using (coord_in_pi_of_coord (a := a) (b := b) (i := p) hx)
      have hge : 3 * rigidEps ≤ x p := by linarith [hvp0, (Set.mem_Ico.mp hxp').1]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := a) (b := b) (x := x)
    · exact hx
    · intro i
      by_cases hip : i = p
      · subst i
        simp [a]
        linarith [rigidEps_pos]
      · by_cases hvi0 : 0 ≤ v i
        · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
          have : 0 ≤ v i - v i := by linarith
          simpa [a, hip, hmax'] using this
        · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
          have : 0 ≤ - v i := by linarith
          simpa [a, hip, hmax'] using this
    · intro i
      by_cases hip : i = p
      · subst i
        simp [b]
        norm_num [rigidEps]
      · by_cases hvi0 : 0 ≤ v i
        · have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
          have : 1 - v i ≤ 1 := by linarith
          simpa [b, hip, hmin'] using this
        · have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
          have : (1 + v i) - v i ≤ 1 := by linarith
          simpa [b, hip, hmin'] using this
    · have hxp' : x p ∈ Set.Ico (v p + 3 * rigidEps) (v p + 4 * rigidEps) := by
        simpa [a, b] using (coord_in_pi_of_coord (a := a) (b := b) (i := p) hx)
      have hge : 3 * rigidEps ≤ (x - v) p := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hxp').1]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)


/-- Case A, second half (`v_p < 0`): the mirror of `rigid_overlap_caseA_ge0`, with the slice
`Ico (3ε) (1+v_p)` clearing the hole ranges for both `x` and `x - v`. -/
lemma rigid_overlap_caseA_lt0 {d : ℕ} {v : Fin d → ℝ} {p : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hvp : |v p| < 1 - 4 * rigidEps) (hvneg : v p < 0) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let a : Fin d → ℝ := fun i => if i = p then 3 * rigidEps else max 0 (v i)
  let b : Fin d → ℝ := fun i => if i = p then 1 + v p else min 1 (1 + v i)
  apply rigid_overlap_of_box (d := d) (v := v) (a := a) (b := b)
  · intro i
    by_cases hip : i = p
    · subst i
      simp [a, b]
      have hvneg' : -(1 - 4 * rigidEps) < v p := (abs_lt.mp hvp).1
      linarith [rigidEps_pos]
    · have hvlow : -1 < v i := (abs_lt.mp (hv i)).1
      have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
      have hmax : max 0 (v i) < min 1 (1 + v i) := by
        by_cases hvi0 : 0 ≤ v i
        · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
          have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
          rw [hmax', hmin']
          exact hvhi
        · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
          have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
          rw [hmax', hmin']
          linarith
      simpa [a, b, hip] using hmax
  · intro x hx
    apply mem_rigidTile_box (a := a) (b := b) (x := x)
    · exact hx
    · intro i
      by_cases hip : i = p
      · subst i
        simp [a]
        linarith [rigidEps_pos]
      · have : 0 ≤ max 0 (v i) := le_max_left 0 (v i)
        simpa [a, hip] using this
    · intro i
      by_cases hip : i = p
      · subst i
        simp [b]
        linarith
      · have : min 1 (1 + v i) ≤ 1 := min_le_left 1 (1 + v i)
        simpa [b, hip] using this
    · have hxp' : x p ∈ Set.Ico (3 * rigidEps) (1 + v p) := by
        simpa [a, b] using (coord_in_pi_of_coord (a := a) (b := b) (i := p) hx)
      have hge : 3 * rigidEps ≤ x p := (Set.mem_Ico.mp hxp').1
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := a) (b := b) (x := x)
    · exact hx
    · intro i
      by_cases hip : i = p
      · subst i
        simp [a]
        linarith [rigidEps_pos, hvneg]
      · by_cases hvi0 : 0 ≤ v i
        · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
          have : 0 ≤ v i - v i := by linarith
          simpa [a, hip, hmax'] using this
        · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
          have : 0 ≤ - v i := by linarith
          simpa [a, hip, hmax'] using this
    · intro i
      by_cases hip : i = p
      · subst i
        simp [b]
      · by_cases hvi0 : 0 ≤ v i
        · have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
          have : 1 - v i ≤ 1 := by linarith
          simpa [b, hip, hmin'] using this
        · have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
          have : (1 + v i) - v i ≤ 1 := by linarith
          simpa [b, hip, hmin'] using this
    · have hxp' : x p ∈ Set.Ico (3 * rigidEps) (1 + v p) := by
        simpa [a, b] using (coord_in_pi_of_coord (a := a) (b := b) (i := p) hx)
      have hge : 3 * rigidEps ≤ (x - v) p := by
        simp [Pi.sub_apply]
        linarith [(Set.mem_Ico.mp hxp').1, hvneg]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)


/-- Case B, all-near-+1, with at least two coordinates in `M = {i | v_i >= 1 - 2ε}`:
the full box `∏ [v_i, 1)` avoids all holes (`x` via any coordinate `>= 1-2ε >= 3ε`,
`x - v` via two coordinates with `(x-v)_i < 2ε`). -/
lemma rigid_overlap_caseB_twoM {d : ℕ} {v : Fin d → ℝ} {a b : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hpos : ∀ i : Fin d, 1 - 4 * rigidEps ≤ v i)
    (hab2 : a ≠ b)
    (hvM1 : v a ≥ 1 - 2 * rigidEps) (hvM2 : v b ≥ 1 - 2 * rigidEps) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun i => v i
  let bb : Fin d → ℝ := fun i => 1
  have hpos0 : ∀ i : Fin d, 0 ≤ v i := by
    intro i
    have h1 : 1 - 4 * rigidEps ≥ 0 := by norm_num [rigidEps]
    linarith [hpos i]
  have h7 : 3 * rigidEps ≤ 1 - 2 * rigidEps := by norm_num [rigidEps]
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
    simpa [aa, bb] using hvhi
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      simpa [aa] using hpos0 i
    · intro i
      simpa [bb]
    · have hxa : x a ∈ Set.Ico (v a) 1 := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := a) hx)
      have hge : 3 * rigidEps ≤ x a := by linarith [h7, hvM1, (Set.mem_Ico.mp hxa).1]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      simpa [aa]
    · intro i
      have : 1 - v i ≤ 1 := by linarith [hpos0 i]
      simpa [bb] using this
    · have hxa : x a ∈ Set.Ico (v a) 1 := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := a) hx)
      have hxb : x b ∈ Set.Ico (v b) 1 := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := b) hx)
      have hsa : (x - v) a < 2 * rigidEps := by
        simp [Pi.sub_apply]
        linarith [hvM1, (Set.mem_Ico.mp hxa).2]
      have hsb : (x - v) b < 2 * rigidEps := by
        simp [Pi.sub_apply]
        linarith [hvM2, (Set.mem_Ico.mp hxb).2]
      exact not_mem_hole_union_of_two_small hab2 hsa hsb



/-- Case B, all-near-+1, `M = {p}`: slice a non-M coordinate `i0` by `[v_i0, v_i0+2ε)`;
then `(x-v)_p < 2ε` and `(x-v)_i0 < 2ε`, so two-small clears the holes for `x-v`,
while `x` is cleared by coordinate `p` (`>= 1-2ε >= 3ε`). -/
lemma rigid_overlap_caseB_Mp {d : ℕ} {v : Fin d → ℝ} {p i0 : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hpos : ∀ i : Fin d, 1 - 4 * rigidEps ≤ v i)
    (hip0 : i0 ≠ p)
    (hvMp : v p ≥ 1 - 2 * rigidEps) (hvM0 : v i0 < 1 - 2 * rigidEps) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun i => if i = i0 then v i0 else v i
  let bb : Fin d → ℝ := fun i => if i = i0 then v i0 + 2 * rigidEps else 1
  have hpne : p ≠ i0 := fun h => hip0 h.symm
  have haap : aa p = v p := by simp [aa, hpne]
  have hbbp : bb p = 1 := by simp [bb, hpne]
  have hai0 : aa i0 = v i0 := by simp [aa]
  have hbi0 : bb i0 = v i0 + 2 * rigidEps := by simp [bb]
  have hpos0 : ∀ i : Fin d, 0 ≤ v i := by
    intro i
    have h1 : 1 - 4 * rigidEps ≥ 0 := by norm_num [rigidEps]
    linarith [hpos i]
  have h7 : 3 * rigidEps ≤ 1 - 2 * rigidEps := by norm_num [rigidEps]
  have h2e : 2 * rigidEps ≤ 1 := by norm_num [rigidEps]
  have hxbox : ∀ (x : Fin d → ℝ), x ∈ Set.univ.pi (fun i => Set.Ico (aa i) (bb i)) →
      ∀ i : Fin d, x i ∈ Set.Ico (aa i) (bb i) := by
    intro x hx i
    exact (Set.mem_pi.mp hx) i (by simp)
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    by_cases hii : i = i0
    · subst i
      simp [aa, bb]
      linarith [rigidEps_pos]
    · have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
      simpa [aa, bb, hii] using hvhi
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hii : i = i0
      · subst i
        simpa [aa] using hpos0 i0
      · simpa [aa, hii] using hpos0 i
    · intro i
      by_cases hii : i = i0
      · subst i
        simp [bb]
        linarith [hvM0]
      · simpa [bb, hii]
    · have hlo0 : aa p ≤ x p := (Set.mem_Ico.mp (hxbox x hx p)).1
      have hlt0 : x p < bb p := (Set.mem_Ico.mp (hxbox x hx p)).2
      have hvp_le : v p ≤ x p := by simpa [haap] using hlo0
      have hx_lt : x p < 1 := by simpa [hbbp] using hlt0
      have hge : 3 * rigidEps ≤ x p := by linarith [h7, hvMp]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hii : i = i0
      · subst i
        simp [aa]
      · simp [aa, hii]
    · intro i
      by_cases hii : i = i0
      · subst i
        simp [bb]
        linarith [h2e]
      · have : 1 - v i ≤ 1 := by linarith [hpos0 i]
        simpa [bb, hii] using this
    · have hlo0 : aa p ≤ x p := (Set.mem_Ico.mp (hxbox x hx p)).1
      have hlt0 : x p < bb p := (Set.mem_Ico.mp (hxbox x hx p)).2
      have hlt0b : x i0 < bb i0 := (Set.mem_Ico.mp (hxbox x hx i0)).2
      have hsp : (x - v) p < 2 * rigidEps := by
        simp [Pi.sub_apply]
        have hx_lt : x p < 1 := by simpa [hbbp] using hlt0
        linarith [hvMp]
      have hsi : (x - v) i0 < 2 * rigidEps := by
        simp [Pi.sub_apply]
        have hx_lt : x i0 < v i0 + 2 * rigidEps := by simpa [hbi0] using hlt0b
        linarith
      exact not_mem_hole_union_of_two_small hpne hsp hsi


/-- A value in `[ε, 2ε)` avoids both hole ranges `[0,ε)` and `[2ε,3ε)`. -/
lemma coord_not_in_ranges_of_between {r : ℝ} (hlo : rigidEps ≤ r) (hlt : r < 2 * rigidEps) :
    r ∉ Set.Ico (0 : ℝ) rigidEps ∪ Set.Ico (2 * rigidEps) (3 * rigidEps) := by
  rintro (h1 | h2)
  · have : r < rigidEps := (Set.mem_Ico.mp h1).2
    linarith [rigidEps_pos]
  · have : 2 * rigidEps ≤ r := (Set.mem_Ico.mp h2).1
    linarith

/-- Case B, all-near-+1, `M = ∅`: slice one coordinate `a` by `[v_a+ε, v_a+2ε)`;
then `(x-v)_a ∈ [ε, 2ε)` avoids both hole ranges (single-coordinate clearing),
while `x` is cleared by any coordinate `>= 1-4ε >= 3ε`. -/
lemma rigid_overlap_caseB_Mempty {d : ℕ} {v : Fin d → ℝ} {a : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hpos : ∀ i : Fin d, 1 - 4 * rigidEps ≤ v i) (hvM0 : v a < 1 - 2 * rigidEps) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun i => if i = a then v a + rigidEps else v i
  let bb : Fin d → ℝ := fun i => if i = a then v a + 2 * rigidEps else 1
  have haa : aa a = v a + rigidEps := by simp [aa]
  have hbb : bb a = v a + 2 * rigidEps := by simp [bb]
  have hpos0 : ∀ i : Fin d, 0 ≤ v i := by
    intro i
    have h1 : 1 - 4 * rigidEps ≥ 0 := by norm_num [rigidEps]
    linarith [hpos i]
  have hge3 : 1 - 3 * rigidEps ≥ 3 * rigidEps := by norm_num [rigidEps]
  have h2e : 2 * rigidEps ≤ 1 := by norm_num [rigidEps]
  have hxbox : ∀ (x : Fin d → ℝ), x ∈ Set.univ.pi (fun i => Set.Ico (aa i) (bb i)) →
      ∀ i : Fin d, x i ∈ Set.Ico (aa i) (bb i) := by
    intro x hx i
    exact (Set.mem_pi.mp hx) i (by simp)
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    by_cases hia : i = a
    · subst i
      simp [aa, bb]
      linarith [rigidEps_pos]
    · have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
      simpa [aa, bb, hia] using hvhi
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hia : i = a
      · subst i
        simp [aa]
        linarith [hpos a, rigidEps_pos]
      · simpa [aa, hia] using hpos0 i
    · intro i
      by_cases hia : i = a
      · subst i
        simp [bb]
        linarith [hvM0]
      · simpa [bb, hia]
    · have hlo0 : aa a ≤ x a := (Set.mem_Ico.mp (hxbox x hx a)).1
      have hvp_le : v a + rigidEps ≤ x a := by simpa [haa] using hlo0
      have hge : 3 * rigidEps ≤ x a := by linarith [hge3, hpos a]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hia : i = a
      · subst i
        simp [aa]
        linarith [rigidEps_pos]
      · simp [aa, hia]
    · intro i
      by_cases hia : i = a
      · subst i
        simp [bb]
        linarith [h2e]
      · have : 1 - v i ≤ 1 := by linarith [hpos0 i]
        simpa [bb, hia] using this
    · have hlo0 : aa a ≤ x a := (Set.mem_Ico.mp (hxbox x hx a)).1
      have hlt0 : x a < bb a := (Set.mem_Ico.mp (hxbox x hx a)).2
      have hva_le : v a + rigidEps ≤ x a := by simpa [haa] using hlo0
      have hx_lt : x a < v a + 2 * rigidEps := by simpa [hbb] using hlt0
      have hlo : rigidEps ≤ (x - v) a := by
        simp [Pi.sub_apply]
        linarith
      have hhi : (x - v) a < 2 * rigidEps := by
        simp [Pi.sub_apply]
        linarith
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_between hlo hhi)



/-- Case B, both signs present: some coordinate near `+1` and some near `-1`.
The full `J`-box `∏ [max 0 (v_i), min 1 (1+v_i))` is hole-free: `x` is cleared by the
near-`+1` coordinate and `x-v` by the near-`-1` coordinate. -/
lemma rigid_overlap_caseB_both {d : ℕ} {v : Fin d → ℝ} {p q : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hp : 1 - 4 * rigidEps ≤ v p) (hq : v q ≤ -(1 - 4 * rigidEps)) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun i => max 0 (v i)
  let bb : Fin d → ℝ := fun i => min 1 (1 + v i)
  have hp_pos : 0 ≤ v p := by
    have h1 : 0 ≤ 1 - 4 * rigidEps := by norm_num [rigidEps]
    linarith [hp]
  have hq_neg : v q ≤ 0 := by
    have hnz : -(1 - 4 * rigidEps) ≤ (0 : ℝ) := by norm_num [rigidEps]
    linarith [hq, hnz]
  have h7 : 3 * rigidEps ≤ 1 - 4 * rigidEps := by norm_num [rigidEps]
  have haap : aa p = v p := by
    simpa [aa, max_eq_right hp_pos]
  have hbbp : bb p = 1 := by
    have hle : 1 ≤ 1 + v p := by linarith [hp_pos]
    simpa [bb, min_eq_left hle]
  have haaq : aa q = 0 := by
    simpa [aa, max_eq_left hq_neg]
  have hbbq : bb q = 1 + v q := by
    have hle : 1 + v q ≤ 1 := by linarith [hq_neg]
    simpa [bb, min_eq_right hle]
  have hxbox : ∀ (x : Fin d → ℝ), x ∈ Set.univ.pi (fun i => Set.Ico (aa i) (bb i)) →
      ∀ i : Fin d, x i ∈ Set.Ico (aa i) (bb i) := by
    intro x hx i
    exact (Set.mem_pi.mp hx) i (by simp)
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    have hvlow : -1 < v i := (abs_lt.mp (hv i)).1
    have hvhi : v i < 1 := (abs_lt.mp (hv i)).2
    by_cases hvi0 : 0 ≤ v i
    · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
      have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
      change max 0 (v i) < min 1 (1 + v i)
      rw [hmax', hmin']
      exact hvhi
    · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
      have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
      change max 0 (v i) < min 1 (1 + v i)
      rw [hmax', hmin']
      linarith
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      exact le_max_left 0 (v i)
    · intro i
      exact min_le_left 1 (1 + v i)
    · have hlo0 : aa p ≤ x p := (Set.mem_Ico.mp (hxbox x hx p)).1
      have hvp_le : v p ≤ x p := by simpa [haap] using hlo0
      have hge : 3 * rigidEps ≤ x p := by linarith [h7, hp]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hvi0 : 0 ≤ v i
      · have hmax' : max 0 (v i) = v i := max_eq_right hvi0
        have : 0 ≤ v i - v i := by linarith
        simpa [aa, hmax'] using this
      · have hmax' : max 0 (v i) = 0 := max_eq_left (le_of_not_ge hvi0)
        have : 0 ≤ - v i := by linarith
        simpa [aa, hmax'] using this
    · intro i
      by_cases hvi0 : 0 ≤ v i
      · have hmin' : min 1 (1 + v i) = 1 := by apply min_eq_left; linarith
        have : 1 - v i ≤ 1 := by linarith
        simpa [bb, hmin'] using this
      · have hmin' : min 1 (1 + v i) = 1 + v i := by apply min_eq_right; linarith
        have : (1 + v i) - v i ≤ 1 := by linarith
        simpa [bb, hmin'] using this
    · have hxq0 : aa q ≤ x q := (Set.mem_Ico.mp (hxbox x hx q)).1
      have hxq0' : 0 ≤ x q := by simpa [haaq] using hxq0
      have hge : 3 * rigidEps ≤ (x - v) q := by
        simp [Pi.sub_apply]
        have hvq : 1 - 4 * rigidEps ≤ -v q := by linarith [hq]
        linarith
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)

/-- Case B, all-near-`-1`, `M'` has at least two elements: box `∏ [0, 1+v_i)`;
holes of `x` cleared by two-small on `(a,b)`, holes of `x-v` cleared by any
coordinate (`(x-v)_i >= 1-4ε >= 3ε`). -/
lemma rigid_overlap_caseB_twoM_neg {d : ℕ} {v : Fin d → ℝ} {a b : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hneg : ∀ i : Fin d, v i ≤ -(1 - 4 * rigidEps))
    (hab2 : a ≠ b)
    (hvM1 : v a ≤ -(1 - 2 * rigidEps)) (hvM2 : v b ≤ -(1 - 2 * rigidEps)) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun _ => 0
  let bb : Fin d → ℝ := fun i => 1 + v i
  have hvle0 : ∀ i : Fin d, v i ≤ 0 := by
    intro i
    have hnz : -(1 - 4 * rigidEps) ≤ (0 : ℝ) := by norm_num [rigidEps]
    linarith [hneg i, hnz]
  have hvgt_neg1 : ∀ i : Fin d, -1 < v i := by
    intro i
    exact (abs_lt.mp (hv i)).1
  have h7 : 3 * rigidEps ≤ 1 - 4 * rigidEps := by norm_num [rigidEps]
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    have hpos : 0 < 1 + v i := by linarith [hvgt_neg1 i]
    simpa [aa, bb] using hpos
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      simp [aa]
    · intro i
      simpa [bb] using (by linarith [hvle0 i] : 1 + v i ≤ 1)
    · have hxa : x a ∈ Set.Ico (aa a) (bb a) := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := a) hx)
      have hxb : x b ∈ Set.Ico (aa b) (bb b) := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := b) hx)
      have hsa : x a < 2 * rigidEps := by
        have hx1 : x a < 1 + v a := (Set.mem_Ico.mp hxa).2
        linarith [hvM1]
      have hsb : x b < 2 * rigidEps := by
        have hx1 : x b < 1 + v b := (Set.mem_Ico.mp hxb).2
        linarith [hvM2]
      exact not_mem_hole_union_of_two_small hab2 hsa hsb
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      simp [aa]
      linarith [hvle0 i]
    · intro i
      simp [bb]
    · have hxa : x a ∈ Set.Ico (aa a) (bb a) := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := a) hx)
      have hlo0 : 0 ≤ x a := (Set.mem_Ico.mp hxa).1
      have hge : 3 * rigidEps ≤ (x - v) a := by
        simp [Pi.sub_apply]
        linarith [h7, hneg a, hlo0]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)

/-- Case B, all-near-`-1`, `M' != everything`: slice a coordinate `a` with
`-(1-2ε) < v a` by `[ε, 2ε)`; holes of `x` cleared by `a` via between, holes of
`x-v` cleared by `a` via `>= 1-3ε >= 3ε`. -/
lemma rigid_overlap_caseB_Mempty_neg {d : ℕ} {v : Fin d → ℝ} {a : Fin d}
    (hv : ∀ i : Fin d, |v i| < 1)
    (hneg : ∀ i : Fin d, v i ≤ -(1 - 4 * rigidEps))
    (hvM0 : -(1 - 2 * rigidEps) < v a) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  let aa : Fin d → ℝ := fun i => if i = a then rigidEps else 0
  let bb : Fin d → ℝ := fun i => if i = a then 2 * rigidEps else 1 + v i
  have haa : aa a = rigidEps := by simp [aa]
  have hbb : bb a = 2 * rigidEps := by simp [bb]
  have hvle0 : ∀ i : Fin d, v i ≤ 0 := by
    intro i
    have hnz : -(1 - 4 * rigidEps) ≤ (0 : ℝ) := by norm_num [rigidEps]
    linarith [hneg i, hnz]
  have hvgt_neg1 : ∀ i : Fin d, -1 < v i := by
    intro i
    exact (abs_lt.mp (hv i)).1
  have h7a : 3 * rigidEps ≤ rigidEps - v a := by
    have h7 : 3 * rigidEps ≤ 1 - 3 * rigidEps := by norm_num [rigidEps]
    linarith [hneg a, h7]
  have hxbox : ∀ (x : Fin d → ℝ), x ∈ Set.univ.pi (fun i => Set.Ico (aa i) (bb i)) →
      ∀ i : Fin d, x i ∈ Set.Ico (aa i) (bb i) := by
    intro x hx i
    exact (Set.mem_pi.mp hx) i (by simp)
  apply rigid_overlap_of_box (d := d) (v := v) (a := aa) (b := bb)
  · intro i
    by_cases hia : i = a
    · subst i
      simp [aa, bb]
      exact rigidEps_lt_two_rigidEps
    · have hpos : 0 < 1 + v i := by linarith [hvgt_neg1 i]
      simpa [aa, bb, hia] using hpos
  · intro x hx
    apply mem_rigidTile_box (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hia : i = a
      · subst i
        simp [aa]
        exact le_of_lt rigidEps_pos
      · simp [aa, hia]
    · intro i
      by_cases hia : i = a
      · subst i
        simp [bb]
        norm_num [rigidEps]
      · have h1 : 1 + v i ≤ 1 := by linarith [hvle0 i]
        simpa [bb, hia] using h1
    · have hlo0 : aa a ≤ x a := (Set.mem_Ico.mp (hxbox x hx a)).1
      have hlt0 : x a < bb a := (Set.mem_Ico.mp (hxbox x hx a)).2
      have hlo : rigidEps ≤ x a := by simpa [haa] using hlo0
      have hhi : x a < 2 * rigidEps := by simpa [hbb] using hlt0
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_between hlo hhi)
  · intro x hx
    apply mem_shift_rigidTile_box (v := v) (a := aa) (b := bb) (x := x)
    · exact hx
    · intro i
      by_cases hia : i = a
      · subst i
        simp [aa]
        linarith [hneg a]
      · simp [aa, hia]
        linarith [hvle0 i]
    · intro i
      by_cases hia : i = a
      · subst i
        simp [bb]
        linarith [hvM0]
      · have h1 : (1 + v i) - v i ≤ 1 := by linarith
        simpa [bb, hia] using h1
    · have hxa : x a ∈ Set.Ico (aa a) (bb a) := by
        simpa [aa, bb] using (coord_in_pi_of_coord (a := aa) (b := bb) (i := a) hx)
      have heps_x : rigidEps ≤ x a := by
        simpa [haa] using (Set.mem_Ico.mp hxa).1
      have hge : 3 * rigidEps ≤ (x - v) a := by
        simp [Pi.sub_apply]
        linarith [h7a, heps_x]
      exact not_mem_hole_union_of_coord_avoid (coord_not_in_ranges_of_ge hge)

lemma rigid_overlap_volume_pos {d : ℕ} (v : Fin d → ℝ)
    (hv : rigidClose v 0) :
    0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d} := by
  classical
  cases d with
  | zero =>
      have hset : {x : Fin 0 → ℝ | x ∈ rigidTile 0 ∧ x ∈ v +ᵥ rigidTile 0} = rigidTile 0 := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          constructor
          · exact hx
          · rw [Set.mem_vadd_set]
            refine ⟨x, hx, ?_⟩
            have hv0 : v = 0 := by
              ext i
              exact Fin.elim0 i
            apply funext
            intro i
            exact Fin.elim0 i
      rw [hset]
      exact rigidTile_volume_pos 0
  | succ d' =>
      cases d' with
      | zero =>
          -- d = 1
          exact rigid_overlap_fin1 v hv
            | succ d'' =>
          -- d >= 2 : general case
          have hvabs : ∀ i : Fin (Nat.succ (Nat.succ d'')), |v i| < 1 := by
            intro i
            simpa using hv i
          by_cases hA : ∃ p : Fin (Nat.succ (Nat.succ d'')), |v p| < 1 - 4 * rigidEps
          · rcases hA with ⟨p, hvp⟩
            by_cases hvp0 : 0 ≤ v p
            · exact rigid_overlap_caseA_ge0 (d := Nat.succ (Nat.succ d'')) (p := p) hvabs hvp hvp0
            · have hvneg : v p < 0 := lt_of_not_ge hvp0
              exact rigid_overlap_caseA_lt0 (d := Nat.succ (Nat.succ d'')) (p := p) hvabs hvp hvneg
          · -- Case B: all |v_i| >= 1 - 4ε
            have hB : ∀ i : Fin (Nat.succ (Nat.succ d'')), 1 - 4 * rigidEps ≤ |v i| := by
              intro i
              by_contra hc
              exact hA ⟨i, lt_of_not_ge hc⟩
            by_cases hN : ∃ q : Fin (Nat.succ (Nat.succ d'')), v q ≤ -(1 - 4 * rigidEps)
            · by_cases hP : ∃ p : Fin (Nat.succ (Nat.succ d'')), 1 - 4 * rigidEps ≤ v p
              · rcases hP with ⟨p, hp⟩
                rcases hN with ⟨q, hq⟩
                exact rigid_overlap_caseB_both (d := Nat.succ (Nat.succ d'')) (v := v) (p := p) (q := q) hvabs hp hq
              · -- all coordinates near -1
                have hneg : ∀ i : Fin (Nat.succ (Nat.succ d'')), v i ≤ -(1 - 4 * rigidEps) := by
                  intro i
                  by_cases hvi0 : 0 ≤ v i
                  · exfalso
                    apply hP
                    refine ⟨i, ?_⟩
                    have habs : |v i| = v i := abs_of_nonneg hvi0
                    simpa [habs] using hB i
                  · have hlt : v i < 0 := lt_of_not_ge hvi0
                    have habs : |v i| = -v i := abs_of_neg hlt
                    have hbig : 1 - 4 * rigidEps ≤ -v i := by simpa [habs] using hB i
                    linarith
                by_cases hall : ∀ i : Fin (Nat.succ (Nat.succ d'')), v i ≤ -(1 - 2 * rigidEps)
                · have htwo : ∃ a b : Fin (Nat.succ (Nat.succ d'')), a ≠ b := by
                    refine ⟨0, 1, ?_⟩
                    norm_num
                  rcases htwo with ⟨a, b, hab⟩
                  exact rigid_overlap_caseB_twoM_neg (d := Nat.succ (Nat.succ d'')) (v := v)
                    (a := a) (b := b) hvabs hneg hab (hall a) (hall b)
                · rcases (not_forall.mp hall) with ⟨a, ha⟩
                  have ha' : -(1 - 2 * rigidEps) < v a := lt_of_not_ge ha
                  exact rigid_overlap_caseB_Mempty_neg (d := Nat.succ (Nat.succ d'')) (v := v)
                    (a := a) hvabs hneg ha'
            · -- no coordinates near -1: all near +1
              have hpos : ∀ i : Fin (Nat.succ (Nat.succ d'')), 1 - 4 * rigidEps ≤ v i := by
                intro i
                by_cases hvi0 : 0 ≤ v i
                · have habs : |v i| = v i := abs_of_nonneg hvi0
                  simpa [habs] using hB i
                · exfalso
                  apply hN
                  refine ⟨i, ?_⟩
                  have hlt : v i < 0 := lt_of_not_ge hvi0
                  have habs : |v i| = -v i := abs_of_neg hlt
                  have hbig : 1 - 4 * rigidEps ≤ -v i := by simpa [habs] using hB i
                  linarith
              by_cases hall : ∀ i : Fin (Nat.succ (Nat.succ d'')), 1 - 2 * rigidEps ≤ v i
              · have htwo : ∃ a b : Fin (Nat.succ (Nat.succ d'')), a ≠ b := by
                  refine ⟨0, 1, ?_⟩
                  norm_num
                rcases htwo with ⟨a, b, hab⟩
                exact rigid_overlap_caseB_twoM (d := Nat.succ (Nat.succ d'')) (v := v)
                  (a := a) (b := b) hvabs hpos hab (hall a) (hall b)
              · rcases (not_forall.mp hall) with ⟨a, ha⟩
                have ha' : v a < 1 - 2 * rigidEps := lt_of_not_ge ha
                exact rigid_overlap_caseB_Mempty (d := Nat.succ (Nat.succ d'')) (v := v)
                  (a := a) hvabs hpos ha'

lemma rigid_separated_of_tiling {d : ℕ} {Λ : Set (Fin d → ℝ)}
    (hΛ : IsContinuousTiling (rigidTile d) Λ)
    {u w : Fin d → ℝ} (hu : u ∈ Λ) (hw : w ∈ Λ) (hne : u ≠ w) :
    ¬ rigidClose u w := by
  intro hclose
  let v : Fin d → ℝ := w - u
  have hv : rigidClose v 0 := by
    intro i
    have hi := hclose i
    simpa [v, rigidClose, abs_sub_comm] using hi
  let S : Set (Fin d → ℝ) := {x | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidTile d}
  have hposS : 0 < volume S := by
    simpa [S] using rigid_overlap_volume_pos v hv
  let T : Set (Fin d → ℝ) := {x | x - u ∈ rigidTile d ∧ x - w ∈ rigidTile d}
  have hTeq : T = (fun x : Fin d → ℝ => u + x) '' S := by
    ext x
    constructor
    · intro hx
      refine ⟨x - u, ?_, ?_⟩
      · constructor
        · exact hx.1
        · rw [Set.mem_vadd_set]
          refine ⟨x - w, hx.2, ?_⟩
          simp [v]
      · abel_nf
    · intro hx
      rcases hx with ⟨s, hs, hxs⟩
      have hxs' : x = u + s := hxs.symm
      have hs' : x - u = s := by rw [hxs']; abel_nf
      constructor
      · simpa [hs'] using hs.1
      · rcases (Set.mem_vadd_set.mp hs.2) with ⟨r, hr, hsr⟩
        have hsr' : s = v + r := by
          simpa [vadd_eq_add] using hsr.symm
        have hxw : x - w = r := by
          calc x - w = (u + s) - w := by rw [hxs']
              _ = (u + (v + r)) - w := by rw [hsr']
              _ = r := by dsimp [v]; abel_nf
        simpa [hxw] using hr
  have hvol : volume T = volume S := by
    rw [hTeq]
    rw [Set.image_add_left]
    simp [measure_preimage_add]
  have hbad : volume {x : Fin d → ℝ | ¬ ∃! v' ∈ Λ, x ∈ v' +ᵥ rigidTile d} = 0 := by
    exact (MeasureTheory.ae_iff (μ := volume)).1 hΛ
  have hsub : T ⊆ {x : Fin d → ℝ | ¬ ∃! v' ∈ Λ, x ∈ v' +ᵥ rigidTile d} := by
    intro x hx
    intro huniq
    have hxR : x ∈ u +ᵥ rigidTile d := by
      rw [Set.mem_vadd_set]
      exact ⟨x - u, hx.1, by simp⟩
    have hxRw : x ∈ w +ᵥ rigidTile d := by
      rw [Set.mem_vadd_set]
      exact ⟨x - w, hx.2, by simp⟩
    have hu' : u ∈ Λ ∧ x ∈ u +ᵥ rigidTile d := ⟨hu, hxR⟩
    have hw' : w ∈ Λ ∧ x ∈ w +ᵥ rigidTile d := ⟨hw, hxRw⟩
    exact hne (ExistsUnique.unique huniq hu' hw')
  have hle : volume T ≤ volume {x : Fin d → ℝ | ¬ ∃! v' ∈ Λ, x ∈ v' +ᵥ rigidTile d} := by
    exact measure_mono hsub
  rw [hvol, hbad] at hle
  exact (not_lt_of_ge hle) hposS



-- ============ Helpers ============

lemma rigidHole_volume_pos {d : ℕ} {k : Fin d} : 0 < volume (rigidHole d k) := by
  classical
  rw [rigidHole_eq_pi]
  let a : Fin d → ℝ := fun j => if j = k then 0 else 2 * rigidEps
  let b : Fin d → ℝ := fun j => if j = k then rigidEps else 3 * rigidEps
  have hpi : Set.univ.pi (fun j : Fin d => if j = k then Set.Ico (0 : ℝ) rigidEps
      else Set.Ico (2 * rigidEps) (3 * rigidEps)) =
      Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j)) := by
    apply congrArg (fun f : Fin d → Set ℝ => Set.univ.pi f)
    funext j
    by_cases hjk : j = k
    · subst j
      simp [a, b]
    · simp [a, b, hjk]
  rw [hpi, Real.volume_pi_Ico]
  have hfac : ∀ j : Fin d, ENNReal.ofReal (b j - a j) = ENNReal.ofReal rigidEps := by
    intro j
    by_cases hjk : j = k
    · subst j
      simp [a, b]
    · simp [a, b, hjk]
      congr 1
      ring
  rw [Finset.prod_congr rfl (by intro j hj; exact hfac j)]
  have hpos : 0 < (ENNReal.ofReal rigidEps) ^ Fintype.card (Fin d) := by
    exact ENNReal.pow_pos (by rw [ENNReal.ofReal_pos]; exact rigidEps_pos) _
  simpa [Finset.prod_const] using hpos

/-- Coordinates of points in the tile lie in `[0, 1+ε]`. -/
lemma rigidTile_mem_box0 {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ rigidTile d) (i : Fin d) :
    x i ∈ Set.Icc (0 : ℝ) (1 + rigidEps) := by
  rw [rigidTile_mem_iff] at hx
  rcases hx with hmain | hbump
  · rcases hmain with ⟨hQ, _⟩
    rcases Set.mem_Ico.mp (hQ i) with ⟨hlo, hlt⟩
    constructor <;> linarith [rigidEps_pos]
  · rcases hbump with ⟨l, q, hq, hxq⟩
    have hxq_i : x i = q i + rigidBasis l i := by
      simpa [Pi.add_apply] using congrFun hxq i
    by_cases hil : i = l
    · subst hil
      rcases Set.mem_Ico.mp hq.1 with ⟨h0, hlt⟩
      rw [hxq_i]
      have hbk : rigidBasis i i = 1 := by simp [rigidBasis]
      rw [hbk]
      constructor <;> linarith [rigidEps_pos]
    · have hqj := hq.2 i hil
      rcases Set.mem_Ico.mp hqj with ⟨h1, h2⟩
      rw [hxq_i]
      have hbk : rigidBasis l i = 0 := by simp [rigidBasis, hil]
      rw [hbk]
      constructor <;> norm_num [rigidEps] at h1 h2 ⊢ <;> linarith

/-- A tile point with `k`-th coordinate `>= 1` lies in the `k`-th bump. -/
lemma rigidTile_mem_bump_of_coord_ge_one {d : ℕ} {x : Fin d → ℝ} {k : Fin d}
    (hx : x ∈ rigidTile d) (hxk : 1 ≤ x k) :
    ∃ q : Fin d → ℝ, q ∈ rigidHole d k ∧ x = q + rigidBasis k := by
  rw [rigidTile_mem_iff] at hx
  rcases hx with hmain | hbump
  · exfalso
    rcases hmain with ⟨hQ, _⟩
    have hk : x k ∈ Set.Ico (0 : ℝ) 1 := hQ k
    linarith [(Set.mem_Ico.mp hk).2, hxk]
  · rcases hbump with ⟨l, q, hq, hxq⟩
    by_cases hlk : l = k
    · subst l
      exact ⟨q, hq, hxq⟩
    · exfalso
      have hqk : q k ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hq.2 k (Ne.symm hlk)
      have hxqk : x k = q k := by
        have hxqk' := congrFun hxq k
        simpa [Pi.add_apply, rigidBasis, Ne.symm hlk] using hxqk'
      linarith [(Set.mem_Ico.mp hqk).2, hxk, hxqk, three_rigidEps_lt_one]

/-- Every bump is a subset of the tile. -/
lemma rigidBump_subset_tile {d : ℕ} (l : Fin d) : rigidBump d l ⊆ rigidTile d := by
  intro x hx
  rw [rigidTile_mem_iff]
  right
  refine ⟨l, ?_⟩
  rw [rigidBump] at hx
  rcases hx with ⟨q, hq, hxq⟩
  refine ⟨q, hq, ?_⟩
  exact hxq.symm

lemma rigidHole_far_candidate {d : ℕ} {k : Fin d} (v : Fin d → ℝ)
    (hfar : ∃ i : Fin d, 1 ≤ |v i|)
    (hvol : 0 < volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidHole d k}) :
    (1 ≤ v k ∧ v k < 1 + rigidEps ∧ ∀ i : Fin d, i ≠ k → |v i| < rigidEps) := by
  classical
  let S : Set (Fin d → ℝ) := {x | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidHole d k}
  have hneS : S.Nonempty := by
    by_contra hc
    have hS0 : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hc
    have hvol0 : volume S = 0 := by simp [hS0]
    change 0 < volume S at hvol
    rw [hvol0] at hvol
    exact (lt_irrefl (0 : ENNReal)) hvol
  rcases hneS with ⟨x, hx⟩
  have hxR : x ∈ rigidTile d := hx.1
  rcases (Set.mem_vadd_set.mp hx.2) with ⟨c, hcC, hxc⟩
  have hxv : x = v + c := by simpa [vadd_eq_add] using hxc.symm
  have hck0 : c k ∈ Set.Ico (0 : ℝ) rigidEps := hcC.1
  have hcjk : ∀ j : Fin d, j ≠ k → c j ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hcC.2
  have hxbox : ∀ i : Fin d, x i ∈ Set.Icc (0 : ℝ) (1 + rigidEps) := fun i => rigidTile_mem_box0 hxR i
  have hxvi : ∀ i : Fin d, x i = v i + c i := by
    intro i
    have := congrFun hxv i
    simpa [Pi.add_apply] using this
  rcases hfar with ⟨j, hfj⟩
  have hjk : j = k := by
    by_contra hjne
    have hcj0 : 2 * rigidEps ≤ c j := (Set.mem_Ico.mp (hcjk j hjne)).1
    have hcj1 : c j < 3 * rigidEps := (Set.mem_Ico.mp (hcjk j hjne)).2
    by_cases hvj0 : 0 ≤ v j
    · have hvj1 : 1 ≤ v j := by
        have habs : |v j| = v j := abs_of_nonneg hvj0
        simpa [habs] using hfj
      have hxge : 1 + 2 * rigidEps ≤ x j := by
        rw [hxvi j]
        linarith [hcj0, hvj1]
      linarith [(Set.mem_Icc.mp (hxbox j)).2, hxge]
    · have hvjneg : v j ≤ -1 := by
        have habs : |v j| = -v j := abs_of_neg (lt_of_not_ge hvj0)
        have : 1 ≤ -v j := by simpa [habs] using hfj
        linarith
      have hxlt : x j < 0 := by
        rw [hxvi j]
        linarith [hcj1, hvjneg, three_rigidEps_lt_one]
      linarith [(Set.mem_Icc.mp (hxbox j)).1, hxlt]
  have hfk : 1 ≤ |v k| := by simpa [hjk] using hfj
  have hvk_nonneg : 0 ≤ v k := by
    by_contra hvkneg
    have hvk_le : v k ≤ -1 := by
      have habs : |v k| = -v k := abs_of_neg (lt_of_not_ge hvkneg)
      have : 1 ≤ -v k := by simpa [habs] using hfk
      linarith
    have hck : c k < rigidEps := (Set.mem_Ico.mp hck0).2
    linarith [hvk_le, hck, hxvi k, (Set.mem_Icc.mp (hxbox k)).1, rigidEps_lt_one]
  have hvk1 : 1 ≤ v k := by
    have habs : |v k| = v k := abs_of_nonneg hvk_nonneg
    simpa [habs] using hfk
  have hck_ge : 0 ≤ c k := (Set.mem_Ico.mp hck0).1
  have hxk_ge1 : 1 ≤ x k := by linarith [hvk1, hck_ge, hxvi k]
  rcases rigidTile_mem_bump_of_coord_ge_one hxR hxk_ge1 with ⟨q, hq, hxq⟩
  have hqk : q k ∈ Set.Ico (0 : ℝ) rigidEps := hq.1
  have hqjk : ∀ i : Fin d, i ≠ k → q i ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hq.2
  have hvk_lt : v k < 1 + rigidEps := by
    have hxkq : x k = q k + 1 := by
      have := congrFun hxq k
      simpa [Pi.add_apply, rigidBasis] using this
    linarith [(Set.mem_Ico.mp hqk).2, hck_ge, hxvi k, hxkq]
  have hvik : ∀ i : Fin d, i ≠ k → |v i| < rigidEps := by
    intro i hik
    have hqi0 : 2 * rigidEps ≤ q i := (Set.mem_Ico.mp (hqjk i hik)).1
    have hqi1 : q i < 3 * rigidEps := (Set.mem_Ico.mp (hqjk i hik)).2
    have hci0 : 2 * rigidEps ≤ c i := (Set.mem_Ico.mp (hcjk i hik)).1
    have hci1 : c i < 3 * rigidEps := (Set.mem_Ico.mp (hcjk i hik)).2
    have hvi_eq : v i = q i - c i := by
      have hxqi : x i = q i + rigidBasis k i := by
        have := congrFun hxq i
        simpa [Pi.add_apply] using this
      have hbk : rigidBasis k i = 0 := by simp [rigidBasis, hik]
      linarith [hxvi i, hxqi, hbk]
    rw [abs_lt]
    constructor <;> linarith [hvi_eq, hqi0, hqi1, hci0, hci1]
  exact ⟨hvk1, hvk_lt, hvik⟩

lemma rigidHole_volume_eq {d : ℕ} {k : Fin d} :
    volume (rigidHole d k) = ENNReal.ofReal rigidEps ^ Fintype.card (Fin d) := by
  classical
  rw [rigidHole_eq_pi]
  let a : Fin d → ℝ := fun j => if j = k then 0 else 2 * rigidEps
  let b : Fin d → ℝ := fun j => if j = k then rigidEps else 3 * rigidEps
  have hpi : Set.univ.pi (fun j : Fin d => if j = k then Set.Ico (0 : ℝ) rigidEps
      else Set.Ico (2 * rigidEps) (3 * rigidEps)) =
      Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j)) := by
    apply congrArg (fun f : Fin d → Set ℝ => Set.univ.pi f)
    funext j
    by_cases hjk : j = k
    · subst j
      simp [a, b]
    · simp [a, b, hjk]
  rw [hpi, Real.volume_pi_Ico]
  have hfac : ∀ j : Fin d, ENNReal.ofReal (b j - a j) = ENNReal.ofReal rigidEps := by
    intro j
    by_cases hjk : j = k
    · subst j
      simp [a, b]
    · simp [a, b, hjk]
      congr 1
      ring
  rw [Finset.prod_congr rfl (by intro j hj; exact hfac j)]
  simp [Finset.prod_const]

/-- `y ∈ w +ᵥ P` iff `y - w ∈ P`, for the pointwise additive structure. -/
lemma mem_vadd_sub_iff {d : ℕ} (P : Set (Fin d → ℝ)) (w y : Fin d → ℝ) :
    y ∈ w +ᵥ P ↔ y - w ∈ P := by
  constructor
  · intro h
    rcases (Set.mem_vadd_set.mp h) with ⟨c, hc, hwc⟩
    have hyc : y = w + c := by simpa [vadd_eq_add] using hwc.symm
    have : y - w = c := by rw [hyc]; abel
    simpa [this] using hc
  · intro h
    rw [Set.mem_vadd_set]
    refine ⟨y - w, h, ?_⟩
    simp [vadd_eq_add]

/-- Translation by `+a` preserves volume. -/
lemma volume_image_add_right {d : ℕ} (a : Fin d → ℝ) (S : Set (Fin d → ℝ)) :
    volume ((fun x : Fin d → ℝ => x + a) '' S) = volume S := by
  have hfun : (fun x : Fin d → ℝ => x + a) = (fun x : Fin d → ℝ => a + x) := by
    funext x
    simp [add_comm]
  rw [hfun]
  rw [Set.image_add_left]
  simp [measure_preimage_add]

/-- A `k`-hole box shifted by a small nonzero `w` overlaps itself with strictly smaller volume. -/
lemma volume_shift_hole_lt {d : ℕ} {k : Fin d} (w : Fin d → ℝ)
    (hw : ∀ i : Fin d, |w i| < rigidEps) (hw0 : w ≠ 0) :
    volume (rigidHole d k ∩ (w +ᵥ rigidHole d k)) < volume (rigidHole d k) := by
  classical
  let a : Fin d → ℝ := fun j => if j = k then (0 : ℝ) else 2 * rigidEps
  let b : Fin d → ℝ := fun j => if j = k then rigidEps else 3 * rigidEps
  have hpiC : rigidHole d k = Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j)) := by
    rw [rigidHole_eq_pi]
    apply congrArg (fun f : Fin d → Set ℝ => Set.univ.pi f)
    funext j
    by_cases hjk : j = k
    · subst j
      simp [a, b]
    · simp [a, b, hjk]
  let lo : Fin d → ℝ := fun j => max (a j) (a j + w j)
  let hi : Fin d → ℝ := fun j => min (b j) (b j + w j)
  have hinter : rigidHole d k ∩ (w +ᵥ rigidHole d k) =
      Set.univ.pi (fun j : Fin d => Set.Ico (lo j) (hi j)) := by
    rw [hpiC]
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyP, hyw⟩
      have hywP : y - w ∈ Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j)) :=
        (mem_vadd_sub_iff (Set.univ.pi (fun j : Fin d => Set.Ico (a j) (b j))) w y).1 hyw
      rw [Set.mem_pi] at hyP hywP
      rw [Set.mem_pi]
      intro j hj
      have hyj1 := hyP j hj
      have hyj2 := hywP j hj
      rcases Set.mem_Ico.mp hyj1 with ⟨h1lo, h1hi⟩
      rcases Set.mem_Ico.mp hyj2 with ⟨h2lo, h2hi⟩
      have h2lo' : a j + w j ≤ y j := by
        have h' : a j ≤ y j - w j := by simpa [Pi.sub_apply] using h2lo
        linarith
      have h2hi' : y j < b j + w j := by
        have h' : y j - w j < b j := by simpa [Pi.sub_apply] using h2hi
        linarith
      constructor
      · change max (a j) (a j + w j) ≤ y j
        rw [max_le_iff]
        exact ⟨h1lo, h2lo'⟩
      · change y j < min (b j) (b j + w j)
        rw [lt_min_iff]
        exact ⟨h1hi, h2hi'⟩
    · intro hy
      have hyj : ∀ j : Fin d, y j ∈ Set.Ico (lo j) (hi j) := fun j =>
        (Set.mem_pi.mp hy) j (by simp)
      constructor
      · rw [Set.mem_pi]
        intro j hj
        rcases Set.mem_Ico.mp (hyj j) with ⟨hlo, hhi⟩
        exact ⟨le_trans (le_max_left (a j) (a j + w j)) (by simpa [lo] using hlo),
          lt_of_lt_of_le hhi (by simpa [hi] using min_le_left (b j) (b j + w j))⟩
      · rw [Set.mem_vadd_set]
        refine ⟨y - w, ?_, ?_⟩
        · rw [Set.mem_pi]
          intro j hj
          rcases Set.mem_Ico.mp (hyj j) with ⟨hlo, hhi⟩
          constructor
          · change a j ≤ y j - w j
            have h2 : a j + w j ≤ y j :=
              le_trans (le_max_right (a j) (a j + w j)) (by simpa [lo] using hlo)
            linarith
          · change y j - w j < b j
            have h1 : y j < b j + w j :=
              lt_of_lt_of_le hhi (by simpa [hi] using min_le_right (b j) (b j + w j))
            linarith
        · simp [vadd_eq_add]
  have hvol_inter : volume (rigidHole d k ∩ (w +ᵥ rigidHole d k)) =
      ∏ j : Fin d, ENNReal.ofReal (hi j - lo j) := by
    rw [hinter, Real.volume_pi_Ico]
  have hwidth : ∀ j : Fin d, hi j - lo j = rigidEps - |w j| := by
    intro j
    have hbma : b j - a j = rigidEps := by
      by_cases hjk : j = k
      · subst j
        have hcalc : rigidEps - (0 : ℝ) = rigidEps := by ring
        simpa [a, b] using hcalc
      · have hcalc : (3 * rigidEps) - (2 * rigidEps) = rigidEps := by ring
        simpa [a, b, hjk] using hcalc
    by_cases hwj0 : 0 ≤ w j
    · have hmax' : max (a j) (a j + w j) = a j + w j := max_eq_right (by linarith)
      have hmin' : min (b j) (b j + w j) = b j := min_eq_left (by linarith)
      have habs : |w j| = w j := abs_of_nonneg hwj0
      simp [hi, lo, hmax', hmin', habs]
      nlinarith [hbma]
    · have hwneg : w j < 0 := lt_of_not_ge hwj0
      have hmax' : max (a j) (a j + w j) = a j := max_eq_left (by linarith)
      have hmin' : min (b j) (b j + w j) = b j + w j := min_eq_right (by linarith)
      have habs : |w j| = -w j := abs_of_neg hwneg
      simp [hi, lo, hmax', hmin', habs]
      nlinarith [hbma]
  have hvol_inter2 : volume (rigidHole d k ∩ (w +ᵥ rigidHole d k)) =
      ENNReal.ofReal (∏ j : Fin d, (rigidEps - |w j|)) := by
    calc
      volume (rigidHole d k ∩ (w +ᵥ rigidHole d k)) =
          ∏ j : Fin d, ENNReal.ofReal (rigidEps - |w j|) := by
        rw [hvol_inter]
        refine Finset.prod_congr rfl ?_
        intro j hj
        rw [hwidth j]
      _ = ENNReal.ofReal (∏ j : Fin d, (rigidEps - |w j|)) := by
        exact (ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
          (fun j hj => by linarith [hw j])).symm
  have hvolC : volume (rigidHole d k) = ENNReal.ofReal (rigidEps ^ Fintype.card (Fin d)) := by
    rw [rigidHole_volume_eq]
    exact (ENNReal.ofReal_pow (by norm_num [rigidEps] : 0 ≤ rigidEps)
      (Fintype.card (Fin d))).symm
  have hwpos : ∃ j : Fin d, 0 < |w j| := by
    by_contra hc
    apply hw0
    funext j
    by_contra hwj0
    exact hc ⟨j, abs_pos.mpr hwj0⟩
  rcases hwpos with ⟨j0, hj0⟩
  have hltprod : (∏ j : Fin d, (rigidEps - |w j|)) < rigidEps ^ Fintype.card (Fin d) := by
    have h1 : (∏ j : Fin d, (rigidEps - |w j|)) < (∏ j : Fin d, rigidEps) := by
      refine Finset.prod_lt_prod (s := Finset.univ) ?hf ?hfg ?hlt
      · intro i hi
        linarith [hw i]
      · intro i hi
        linarith [abs_nonneg (w i)]
      · refine ⟨j0, Finset.mem_univ j0, ?_⟩
        linarith [hj0]
    have hprodC : (∏ j : Fin d, rigidEps) = rigidEps ^ Fintype.card (Fin d) := by
      simp [Finset.prod_const]
    simpa [hprodC] using h1
  rw [hvol_inter2, hvolC]
  rw [ENNReal.ofReal_lt_ofReal_iff (pow_pos rigidEps_pos (Fintype.card (Fin d)))]
  exact hltprod

/-- The overlap of the tile with a translated hole equals a translate of the hole
overlapped with its own `(v - e_k)`-shift. -/
lemma rigidHole_tile_overlap_eq {d : ℕ} {k : Fin d} (v : Fin d → ℝ)
    (hvk : 1 ≤ v k) :
    {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidHole d k} =
      (fun y : Fin d → ℝ => y + rigidBasis k) ''
        (rigidHole d k ∩ ((v - rigidBasis k) +ᵥ rigidHole d k)) := by
  classical
  set w : Fin d → ℝ := v - rigidBasis k with hwdef
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxR, hxv⟩
    rcases (Set.mem_vadd_set.mp hxv) with ⟨c, hc, hvc⟩
    have hxv_eq : x = v + c := by simpa [vadd_eq_add] using hvc.symm
    have hck0 : 0 ≤ c k := (Set.mem_Ico.mp hc.1).1
    have hxk : x k = v k + c k := by
      have := congrFun hxv_eq k
      simpa [Pi.add_apply] using this
    have hxk1 : 1 ≤ x k := by linarith [hvk, hck0, hxk]
    rcases rigidTile_mem_bump_of_coord_ge_one hxR hxk1 with ⟨q, hq, hxq⟩
    have hqw : q - w = c := by
      calc
        q - w = q - (v - rigidBasis k) := by dsimp [w]
        _ = (q + rigidBasis k) - v := by abel
        _ = x - v := by rw [← hxq]
        _ = c := by rw [hxv_eq]; abel
    refine ⟨q, ?_, ?_⟩
    · constructor
      · exact hq
      · rw [mem_vadd_sub_iff]
        simpa [hqw] using hc
    · exact hxq.symm
  · intro hx
    rcases hx with ⟨y, hy, hxeq⟩
    constructor
    · have hxR : x ∈ rigidBump d k := by
        rw [rigidBump]
        rcases hy with ⟨hyC, _⟩
        exact ⟨y, hyC, hxeq⟩
      exact rigidBump_subset_tile k hxR
    · have hyw : y - w ∈ rigidHole d k :=
        (mem_vadd_sub_iff (rigidHole d k) w y).1 hy.2
      have hcalc : x - v = y - w := by
        calc
          x - v = (y + rigidBasis k) - v := by rw [hxeq.symm]
          _ = y - (v - rigidBasis k) := by abel
          _ = y - w := by dsimp [w]
      rw [Set.mem_vadd_set]
      refine ⟨x - v, ?_, ?_⟩
      · simpa [hcalc] using hyw
      · simp [vadd_eq_add]

lemma rigidHole_candidate_lt {d : ℕ} {k : Fin d} (v : Fin d → ℝ)
    (hvk : 1 ≤ v k) (hvk2 : v k < 1 + rigidEps)
    (hvi : ∀ i : Fin d, i ≠ k → |v i| < rigidEps)
    (hne : v ≠ rigidBasis k) :
    volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidHole d k} <
      volume (rigidHole d k) := by
  classical
  set w : Fin d → ℝ := v - rigidBasis k with hwdef
  have hw : ∀ i : Fin d, |w i| < rigidEps := by
    intro i
    by_cases hik : i = k
    · subst i
      have h1 : 0 ≤ v k - 1 := by linarith [hvk]
      have h2 : v k - 1 < rigidEps := by linarith [hvk2]
      change |(v - rigidBasis k) k| < rigidEps
      rw [Pi.sub_apply]
      simp only [rigidBasis]
      simp only [if_true]
      simpa [abs_of_nonneg h1] using h2
    · change |(v - rigidBasis k) i| < rigidEps
      rw [Pi.sub_apply]
      simp only [rigidBasis, if_neg hik]
      simpa using hvi i hik
  have hwne : w ≠ 0 := by
    intro hw0
    apply hne
    funext i
    have hwi : w i = 0 := congrFun hw0 i
    by_cases hik : i = k
    · subst i
      have hsub : (v - rigidBasis k) k = 0 := by simpa [w] using hwi
      have : v k - 1 = 0 := by
        simpa [Pi.sub_apply, rigidBasis] using hsub
      simp [rigidBasis]
      linarith
    · have hsub : (v - rigidBasis k) i = 0 := by simpa [w] using hwi
      have hvi0 : v i = 0 := by
        simpa [Pi.sub_apply, rigidBasis, hik] using hsub
      simp [rigidBasis, hik, hvi0]
  have hvol_lt := volume_shift_hole_lt (d := d) (k := k) w hw hwne
  have hvol_eq : volume {x : Fin d → ℝ | x ∈ rigidTile d ∧ x ∈ v +ᵥ rigidHole d k} =
      volume (rigidHole d k ∩ (w +ᵥ rigidHole d k)) := by
    rw [rigidHole_tile_overlap_eq (d := d) (k := k) v hvk]
    exact volume_image_add_right (rigidBasis k)
      (rigidHole d k ∩ ((v - rigidBasis k) +ᵥ rigidHole d k))
  rw [hvol_eq]
  simpa [w] using hvol_lt

lemma rigidTile_mem_box {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ rigidTile d) (i : Fin d) :
    x i ∈ Set.Icc (-rigidEps) (1 + rigidEps) := by
  rw [rigidTile_mem_iff] at hx
  rcases hx with hmain | hbump
  · rcases hmain with ⟨hQ, _⟩
    rcases Set.mem_Ico.mp (hQ i) with ⟨hlo, hlt⟩
    constructor <;> linarith [rigidEps_pos]
  · rcases hbump with ⟨l, q, hq, hxq⟩
    have hqk_i : x i = q i + rigidBasis l i := by
      simpa [Pi.add_apply] using congrFun hxq i
    by_cases hil : i = l
    · subst hil
      rcases Set.mem_Ico.mp hq.1 with ⟨h0, hlt⟩
      rw [hqk_i]
      have hbk : rigidBasis i i = 1 := by simp [rigidBasis]
      rw [hbk]
      constructor <;> linarith [rigidEps_pos]
    · have hqj := hq.2 i hil
      rcases Set.mem_Ico.mp hqj with ⟨h1, h2⟩
      rw [hqk_i]
      have hbk : rigidBasis l i = 0 := by simp [rigidBasis, hil]
      rw [hbk]
      constructor <;> norm_num [rigidEps] at h1 h2 ⊢ <;> linarith

lemma rigidHole_mem_box {d : ℕ} {k : Fin d} {x : Fin d → ℝ} (hx : x ∈ rigidHole d k) (i : Fin d) :
    x i ∈ Set.Ico (0 : ℝ) 1 := by
  exact rigidHole_subset_unitCube2 k hx i

lemma volume_add_image {d : ℕ} (a : Fin d → ℝ) (S : Set (Fin d → ℝ)) :
    volume ((fun x : Fin d → ℝ => a + x) '' S) = volume S := by
  rw [Set.image_add_left]
  simp [measure_preimage_add]

lemma rigidTile_disjoint_hole {d : ℕ} (k : Fin d) : Disjoint (rigidTile d) (rigidHole d k) := by
  rw [Set.disjoint_left]
  intro r hr hh
  rw [rigidTile_mem_iff] at hr
  rcases hr with hmain | hbump
  · rcases hmain with ⟨hQ, hnot⟩
    exact hnot (Set.mem_iUnion.mpr ⟨k, hh⟩)
  · rcases hbump with ⟨l, q, hq, rfl⟩
    have hcoord : (q + rigidBasis l) k ∈ Set.Ico (0 : ℝ) rigidEps := hh.1
    by_cases hlk : k = l
    · subst l
      have hb : (q + rigidBasis k) k = q k + 1 := by simp [Pi.add_apply, rigidBasis]
      have hlt : q k < rigidEps := (Set.mem_Ico.mp hq.1).2
      have hnonneg : 0 ≤ q k := (Set.mem_Ico.mp hq.1).1
      have : q k + 1 < rigidEps := by simpa [hb] using (Set.mem_Ico.mp hcoord).2
      linarith [rigidEps_lt_one]
    · have hb : (q + rigidBasis l) k = q k := by simp [Pi.add_apply, rigidBasis, hlk]
      have hqk2 : q k ∈ Set.Ico (2 * rigidEps) (3 * rigidEps) := hq.2 k hlk
      have hlow : 2 * rigidEps ≤ q k := (Set.mem_Ico.mp hqk2).1
      have : q k < rigidEps := by simpa [hb] using (Set.mem_Ico.mp hcoord).2
      linarith [two_rigidEps_pos]

lemma abs_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  have hx1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hy2 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have hy1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hx2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hxy1 : x - y < 1 := by
    calc x - y < ((⌊x⌋ : ℝ) + 1) - (⌊y⌋ : ℝ) := by linarith [hx2, hy1]
      _ = 1 := by rw [h]; ring
  have hyx1 : y - x < 1 := by
    calc y - x < ((⌊y⌋ : ℝ) + 1) - (⌊x⌋ : ℝ) := by linarith [hy2, hx1]
      _ = 1 := by rw [h]; ring
  exact abs_lt.mpr ⟨by linarith, hxy1⟩

lemma finite_of_sep_bounded {d : ℕ} {S : Set (Fin d → ℝ)}
    (hsep : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → ¬ ∀ i : Fin d, |u i - w i| < 1)
    (a : Fin d → ℝ) (N : ℕ) :
    (S ∩ {x | ∀ i, x i ∈ Set.Icc (a i) (a i + (N : ℝ))}).Finite := by
  classical
  let T := S ∩ {x | ∀ i, x i ∈ Set.Icc (a i) (a i + (N : ℝ))}
  have hfpos : ∀ (x : T) (i : Fin d), 0 ≤ ⌊x.1 i - a i⌋ := by
    intro x i
    exact Int.floor_nonneg.mpr (sub_nonneg.mpr (Set.mem_Icc.mp (x.2.2 i)).1)
  have hfle : ∀ (x : T) (i : Fin d), ⌊x.1 i - a i⌋ ≤ (N : ℤ) := by
    intro x i
    have hle : x.1 i - a i ≤ (N : ℝ) := by linarith [(Set.mem_Icc.mp (x.2.2 i)).2]
    have h := Int.floor_le_floor hle
    simpa using h
  let f : T → Fin d → Fin (N + 1) := fun x i =>
    ⟨Int.toNat (⌊x.1 i - a i⌋), by
      have h2 : Int.toNat (⌊x.1 i - a i⌋) ≤ N := by
        have h := Int.toNat_le_toNat (hfle x i)
        simpa using h
      omega⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hcloseAll : ∀ j : Fin d, |x.1 j - y.1 j| < 1 := by
      intro j
      have hvalj : Int.toNat (⌊x.1 j - a j⌋) = Int.toNat (⌊y.1 j - a j⌋) := by
        exact congrArg Fin.val (congrFun hxy j)
      have hflj : ⌊x.1 j - a j⌋ = ⌊y.1 j - a j⌋ := by
        have h1 : (⌊x.1 j - a j⌋ : ℤ) = Int.toNat (⌊x.1 j - a j⌋) := (Int.toNat_of_nonneg (hfpos x j)).symm
        have h2 : (⌊y.1 j - a j⌋ : ℤ) = Int.toNat (⌊y.1 j - a j⌋) := (Int.toNat_of_nonneg (hfpos y j)).symm
        rw [h1, h2, hvalj]
      have hd' : |(x.1 j - a j) - (y.1 j - a j)| < 1 := abs_lt_one_of_floor_eq hflj
      have h1 : (x.1 j - a j) - (y.1 j - a j) = x.1 j - y.1 j := by ring
      simpa [h1] using hd'
    apply Subtype.ext
    by_contra hne
    exact (hsep x.1 x.2.1 y.1 y.2.1 hne) hcloseAll
  haveI : Finite (Fin d → Fin (N + 1)) := inferInstance
  haveI : Finite T := Finite.of_injective f hinj
  exact Set.toFinite T



-- ============ Downward closure ============

lemma rigidTiling_downward {d : ℕ} (hd : 0 < d) {Λ : Set (Fin d → ℝ)}
    (hΛ : IsContinuousTiling (rigidTile d) Λ)
    {μ : Fin d → ℝ} (hμ : μ ∈ Λ) (k : Fin d) :
    μ - rigidBasis k ∈ Λ := by
  classical
  by_contra hnot
  let C : Set (Fin d → ℝ) := rigidHole d k
  let H : Set (Fin d → ℝ) := {x | x - μ ∈ C}
  let piece : (Fin d → ℝ) → Set (Fin d → ℝ) := fun lam => (lam +ᵥ rigidTile d) ∩ H
  have hvolC : 0 < volume C := by
    simpa [C] using (rigidHole_volume_pos (d := d) (k := k))
  have hvolH : 0 < volume H := by
    have hHeq : H = (fun x : Fin d → ℝ => μ + x) '' C := by
      ext x
      constructor
      · intro hx
        dsimp [H] at hx
        refine ⟨x - μ, ?_, ?_⟩
        · simpa [C] using hx
        · abel_nf
      · rintro ⟨c, hc, rfl⟩
        dsimp [H]
        change (μ + c) - μ ∈ C
        simpa using hc
    rw [hHeq]
    simpa [C] using hvolC
  have hvolH_eq : volume H = volume C := by
    have hHeq : H = (fun x : Fin d → ℝ => μ + x) '' C := by
      ext x
      constructor
      · intro hx
        dsimp [H] at hx
        refine ⟨x - μ, ?_, ?_⟩
        · simpa [C] using hx
        · abel_nf
      · rintro ⟨c, hc, rfl⟩
        dsimp [H]
        change (μ + c) - μ ∈ C
        simpa using hc
    rw [hHeq]
    rw [volume_add_image]
  let Bad : Set (Fin d → ℝ) := {x | ¬ ∃! v ∈ Λ, x ∈ v +ᵥ rigidTile d}
  have hBad : volume Bad = 0 := by
    simpa [Bad] using (MeasureTheory.ae_iff (μ := volume)).1 hΛ
  let S : Set (Fin d → ℝ) := {lam | lam ∈ Λ ∧ (piece lam).Nonempty}
  have hmem_C_of_H : ∀ x : Fin d → ℝ, x ∈ H → x - μ ∈ C := by
    intro x hx
    exact hx
  have hpiece_sub : ∀ lam : Fin d → ℝ, lam ∈ S → piece lam ⊆ (lam +ᵥ rigidTile d) := by
    intro lam hlam x hx
    exact hx.1
  -- measure of a piece equals measure of intersection of R with translated hole
  have hpiece_eq : ∀ lam : Fin d → ℝ,
      volume (piece lam) = volume ({x | x ∈ rigidTile d ∧ x ∈ (μ - lam) +ᵥ C}) := by
    intro lam
    let A : Set (Fin d → ℝ) := {x | x ∈ rigidTile d ∧ x ∈ (μ - lam) +ᵥ C}
    have htrans : (lam +ᵥ rigidTile d) ∩ H = (fun x : Fin d → ℝ => lam + x) '' A := by
      ext x
      constructor
      · intro hx
        rcases (Set.mem_vadd_set.mp hx.1) with ⟨r, hr, hxr⟩
        have hxr' : x = lam + r := by simpa [vadd_eq_add] using hxr.symm
        refine ⟨x - lam, ?_, ?_⟩
        · constructor
          · have hd : x - lam = r := by rw [hxr']; abel_nf
            simpa [hd] using hr
          · have hxH : x ∈ H := hx.2
            have hxmu : x - μ ∈ C := hxH
            rw [Set.mem_vadd_set]
            refine ⟨x - μ, hxmu, ?_⟩
            simp [vadd_eq_add]
        · abel_nf
      · rintro ⟨s, hs, hxs⟩
        have hxs' : x = lam + s := hxs.symm
        rcases hs with ⟨hsR, hsC⟩
        constructor
        · rw [Set.mem_vadd_set]
          exact ⟨s, hsR, by simpa [vadd_eq_add] using hxs'.symm⟩
        · rcases (Set.mem_vadd_set.mp hsC) with ⟨c, hc, hsc⟩
          have hsc' : s = (μ - lam) + c := by simpa [vadd_eq_add] using hsc.symm
          dsimp [H]
          have hxmu : x - μ = c := by
            calc x - μ = (lam + s) - μ := by rw [hxs']
              _ = (lam + ((μ - lam) + c)) - μ := by rw [hsc']
              _ = c := by abel_nf
          simpa [hxmu] using hc
    change volume ((lam +ᵥ rigidTile d) ∩ H) = volume ({x | x ∈ rigidTile d ∧ x ∈ (μ - lam) +ᵥ C})
    rw [htrans]
    rw [volume_add_image]
  have hSfinite : S.Finite := by
    have hfinbox : S ⊆ Λ ∩ {x | ∀ i, x i ∈ Set.Icc (μ i - 2) (μ i + 2)} := by
      intro lam hlam
      rcases hlam with ⟨hlamΛ, hne⟩
      constructor
      · exact hlamΛ
      · intro i
        rcases hne with ⟨y, hyR, hyH⟩
        rcases (Set.mem_vadd_set.mp hyR) with ⟨r, hr, hyr⟩
        have hyr' : y = lam + r := by simpa [vadd_eq_add] using hyr.symm
        have hlam_eq : lam = μ + (y - μ) - r := by
          rw [hyr']
          abel_nf
        have hri : r i ∈ Set.Icc (-rigidEps) (1 + rigidEps) := rigidTile_mem_box hr i
        have hci0 : 0 ≤ (y - μ) i := (Set.mem_Ico.mp (rigidHole_mem_box (k := k) hyH i)).1
        have hci1 : (y - μ) i ≤ 1 := le_of_lt (Set.mem_Ico.mp (rigidHole_mem_box (k := k) hyH i)).2
        have hlam_i : lam i = μ i + (y - μ) i - r i := congrFun hlam_eq i
        rw [hlam_i]
        rcases Set.mem_Icc.mp hri with ⟨hri0, hri1⟩
        constructor <;> linarith [rigidEps_pos, rigidEps_lt_one]
    let B : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Icc (μ i - 2) (μ i - 2 + (4 : ℝ))}
    have hsub' : {x | ∀ i, x i ∈ Set.Icc (μ i - 2) (μ i + 2)} ⊆ B := by
      intro x hx i
      rcases hx i with ⟨h1, h2⟩
      constructor
      · exact h1
      · linarith
    have hfin : (Λ ∩ {x | ∀ i, x i ∈ Set.Icc (μ i - 2) (μ i + 2)}).Finite := by
      have h1 : (Λ ∩ {x | ∀ i, x i ∈ Set.Icc (μ i - 2) (μ i + 2)}) ⊆ Λ ∩ B := by
        intro x hx
        exact ⟨hx.1, hsub' hx.2⟩
      exact Set.Finite.subset (finite_of_sep_bounded (d := d) (S := Λ)
        (fun u hu w hw hne2 => rigid_separated_of_tiling hΛ hu hw hne2)
        (fun i => μ i - 2) 4) h1
    exact Set.Finite.subset hfin hfinbox
  let U : Set (Fin d → ℝ) := {x | ∃ lam, lam ∈ S ∧ x ∈ piece lam}
  have hcover : H ⊆ U ∪ Bad := by
    intro x hx
    by_cases hxBad : x ∈ Bad
    · exact Or.inr hxBad
    · left
      have hxGood : ∃! v ∈ Λ, x ∈ v +ᵥ rigidTile d := by
        by_contra hc
        exact hxBad (by simpa [Bad] using hc)
      rcases hxGood with ⟨v, hvΛx, _⟩
      rcases hvΛx with ⟨hvΛ, hvx⟩
      have hmemS : v ∈ S := ⟨hvΛ, ⟨x, hvx, hx⟩⟩
      exact ⟨v, hmemS, ⟨hvx, hx⟩⟩
  have hvol_cover : volume H ≤ volume U := by
    calc
      volume H ≤ volume (U ∪ Bad) := measure_mono hcover
      _ ≤ volume U + volume Bad := measure_union_le _ _
      _ = volume U := by rw [hBad, add_zero]
  have hmu_not_S : μ ∉ S := by
    intro hmS
    rcases hmS.2 with ⟨y, hyR, hyH⟩
    rcases (Set.mem_vadd_set.mp hyR) with ⟨r, hr, hyr⟩
    have h1 : y - μ = r := by
      have hyr' : y = μ + r := hyr.symm
      rw [hyr']
      abel_nf
    have hyc : y - μ ∈ C := hyH
    have hdisj : Disjoint (rigidTile d) C := by simpa [C] using (rigidTile_disjoint_hole (d := d) k)
    rw [Set.disjoint_left] at hdisj
    exact hdisj (by simpa [h1] using hr) hyc
  have hfar_of : ∀ lam : Fin d → ℝ, lam ∈ Λ → lam ≠ μ → ∃ i : Fin d, 1 ≤ |μ i - lam i| := by
    intro lam hlam hne
    by_contra hc
    apply rigid_separated_of_tiling hΛ hμ hlam hne.symm
    intro i
    by_contra hni
    have : |μ i - lam i| < 1 := by
      apply lt_of_not_ge
      intro h1
      exact hc ⟨i, h1⟩
    exact hni this
  have hpiece_le_C : ∀ lam : Fin d → ℝ, lam ∈ S → volume (piece lam) ≤ volume C := by
    intro lam hlam
    rw [hpiece_eq lam]
    have hlamμ : lam ≠ μ := by
      intro hl
      exact hmu_not_S (by simpa [hl] using hlam)
    have hfar := hfar_of lam hlam.1 hlamμ
    let v : Fin d → ℝ := μ - lam
    by_cases hpos : 0 < volume ({x | x ∈ rigidTile d ∧ x ∈ v +ᵥ C})
    · have hcand := rigidHole_far_candidate (d := d) (k := k) v (by simpa [v] using hfar) (by simpa [v] using hpos)
      rcases hcand with ⟨hvk, hvk2, hvi⟩
      have hvne : v ≠ rigidBasis k := by
        intro hve
        apply hnot
        have : μ - rigidBasis k = lam := by
          calc μ - rigidBasis k = μ - v := by rw [hve]
            _ = lam := by simpa [v] using sub_sub_cancel μ lam
        rw [this]
        exact hlam.1
      have hlt := rigidHole_candidate_lt (d := d) (k := k) v hvk hvk2
        (by intro i hi; exact hvi i hi) hvne
      exact le_of_lt (by simpa [v] using hlt)
    · have hle0 : volume ({x | x ∈ rigidTile d ∧ x ∈ v +ᵥ C}) ≤ volume C := by
        have : volume ({x | x ∈ rigidTile d ∧ x ∈ v +ᵥ C}) = 0 :=
          le_antisymm (not_lt.mp hpos) zero_le
        rw [this]
        exact zero_le
      simpa [v] using hle0
  have hpos_at_most_one : ∀ lam1 : Fin d → ℝ, lam1 ∈ S → ∀ lam2 : Fin d → ℝ, lam2 ∈ S →
      0 < volume (piece lam1) → 0 < volume (piece lam2) → lam1 = lam2 := by
    intro lam1 h1 lam2 h2 hp1 hp2
    by_contra hne
    have h1μ : lam1 ≠ μ := by intro h; exact hmu_not_S (by simpa [h] using h1)
    have h2μ : lam2 ≠ μ := by intro h; exact hmu_not_S (by simpa [h] using h2)
    have hfar1 := hfar_of lam1 h1.1 h1μ
    have hfar2 := hfar_of lam2 h2.1 h2μ
    let v1 : Fin d → ℝ := μ - lam1
    let v2 : Fin d → ℝ := μ - lam2
    have hpos1 : 0 < volume ({x | x ∈ rigidTile d ∧ x ∈ v1 +ᵥ C}) := by
      rw [hpiece_eq lam1] at hp1
      simpa [v1] using hp1
    have hpos2 : 0 < volume ({x | x ∈ rigidTile d ∧ x ∈ v2 +ᵥ C}) := by
      rw [hpiece_eq lam2] at hp2
      simpa [v2] using hp2
    have hcand1 := rigidHole_far_candidate (d := d) (k := k) v1 (by simpa [v1] using hfar1) hpos1
    have hcand2 := rigidHole_far_candidate (d := d) (k := k) v2 (by simpa [v2] using hfar2) hpos2
    rcases hcand1 with ⟨hvk1, hvk21, hvi1⟩
    rcases hcand2 with ⟨hvk2, hvk22, hvi2⟩
    have h2e : 2 * rigidEps < 1 := by norm_num [rigidEps]
    have hclose : rigidClose lam1 lam2 := by
      intro i
      by_cases hik : i = k
      · subst i
        have hb : |lam1 k - lam2 k| = |v1 k - v2 k| := by
          dsimp [v1, v2]
          rw [abs_sub_comm]
          congr 1
          ring
        rw [hb]
        rw [abs_lt]
        constructor <;> linarith [hvk1, hvk21, hvk2, hvk22, rigidEps_lt_one]
      · have hb : |lam1 i - lam2 i| = |v1 i - v2 i| := by
          dsimp [v1, v2]
          rw [abs_sub_comm]
          congr 1
          ring
        rw [hb]
        have h1v : |v1 i| < rigidEps := hvi1 i hik
        have h2v : |v2 i| < rigidEps := hvi2 i hik
        have hv1a : -rigidEps < v1 i ∧ v1 i < rigidEps := abs_lt.mp h1v
        have hv2a : -rigidEps < v2 i ∧ v2 i < rigidEps := abs_lt.mp h2v
        rw [abs_lt]
        constructor <;> linarith
    exact (rigid_separated_of_tiling hΛ h1.1 h2.1 hne) hclose
  have hpiece_pos_lt_C : ∀ lam : Fin d → ℝ, lam ∈ S → 0 < volume (piece lam) →
      volume (piece lam) < volume C := by
    intro lam hlam hpos
    rw [hpiece_eq lam]
    have hlamμ : lam ≠ μ := by intro hl; exact hmu_not_S (by simpa [hl] using hlam)
    have hfar := hfar_of lam hlam.1 hlamμ
    let v : Fin d → ℝ := μ - lam
    have hposv : 0 < volume ({x | x ∈ rigidTile d ∧ x ∈ v +ᵥ C}) := by
      rw [hpiece_eq lam] at hpos
      simpa [v] using hpos
    have hcand := rigidHole_far_candidate (d := d) (k := k) v (by simpa [v] using hfar) hposv
    rcases hcand with ⟨hvk, hvk2, hvi⟩
    have hvne : v ≠ rigidBasis k := by
      intro hve
      apply hnot
      have : μ - rigidBasis k = lam := by
        calc μ - rigidBasis k = μ - v := by rw [hve]
          _ = lam := by simpa [v] using sub_sub_cancel μ lam
      rw [this]
      exact hlam.1
    have hlt := rigidHole_candidate_lt (d := d) (k := k) v hvk hvk2
      (by intro i hi; exact hvi i hi) hvne
    simpa [v] using hlt
  obtain ⟨fs, hfs⟩ := hSfinite.exists_finset
  have hfs_mem : ∀ lam : Fin d → ℝ, lam ∈ S ↔ lam ∈ (fs : Set (Fin d → ℝ)) := by
    intro lam
    exact (hfs lam).symm
  have hUeq : U = ⋃ lam ∈ (fs : Set (Fin d → ℝ)), piece lam := by
    ext x
    simp [U, hfs_mem]
  have hvol_sum : volume H ≤ ∑ lam ∈ fs, volume (piece lam) := by
    calc
      volume H ≤ volume U := hvol_cover
      _ = volume (⋃ lam ∈ (fs : Set (Fin d → ℝ)), piece lam) := by rw [hUeq]
      _ ≤ ∑ lam ∈ fs, volume (piece lam) := by
        simpa using (MeasureTheory.measure_biUnion_finset_le (μ := volume) fs (fun lam => piece lam))
  have hsum_lt : (∑ lam ∈ fs, volume (piece lam)) < volume C := by
    by_cases hpos : ∃ lam ∈ S, 0 < volume (piece lam)
    · rcases hpos with ⟨lam0, hlam0S, hpos0⟩
      have hlt0 := hpiece_pos_lt_C lam0 hlam0S hpos0
      have hsum_eq : (∑ lam ∈ fs, volume (piece lam)) = volume (piece lam0) := by
        refine Finset.sum_eq_single lam0 ?_ ?_
        · intro b hb hbne
          by_cases hbS : b ∈ S
          · have hzero : volume (piece b) = 0 := by
              have hnotpos : ¬ 0 < volume (piece b) := by
                intro hp
                have : b = lam0 := hpos_at_most_one b hbS lam0 hlam0S hp hpos0
                exact hbne this
              exact le_antisymm (not_lt.mp hnotpos) zero_le
            simpa [hzero]
          · have hz : volume (piece b) = 0 := by
              have hbS' : b ∈ S := (hfs_mem b).2 (by simpa using hb)
              exact False.elim (hbS hbS')
            simpa [hz]
        · intro hb
          have hmem : lam0 ∈ fs := (hfs_mem lam0).1 hlam0S
          exact False.elim (hb hmem)
      rw [hsum_eq]
      exact hlt0
    · have hall_zero : ∀ lam ∈ fs, volume (piece lam) = 0 := by
        intro lam hlam
        have hlamS : lam ∈ S := (hfs_mem lam).2 (by simpa using hlam)
        have hnotpos : ¬ 0 < volume (piece lam) := by
          intro hp
          exact hpos ⟨lam, hlamS, hp⟩
        exact le_antisymm (not_lt.mp hnotpos) zero_le
      have hsum0 : (∑ lam ∈ fs, volume (piece lam)) = 0 := by
        exact Finset.sum_eq_zero (by intro lam hlam; exact hall_zero lam hlam)
      calc
        (∑ lam ∈ fs, volume (piece lam)) = 0 := hsum0
        _ < volume C := hvolC
  have hvlt : volume H < volume C := lt_of_le_of_lt hvol_sum hsum_lt
  have : volume C < volume C := by simpa [hvolH_eq] using hvlt
  exact (lt_irrefl (volume C)) this



-- ============ single coset & equality ============

lemma rigid_down_nat {d : ℕ} {Λ : Set (Fin d → ℝ)}
    (hdown : ∀ μ : Fin d → ℝ, μ ∈ Λ → ∀ k : Fin d, μ - rigidBasis k ∈ Λ)
    (μ : Fin d → ℝ) (hμ : μ ∈ Λ) (m : Fin d → ℕ) :
    μ - (fun i : Fin d => (m i : ℝ)) ∈ Λ := by
  classical
  have hmain : ∀ (n : ℕ), ∀ (m : Fin d → ℕ),
      (∑ i, m i) ≤ n → μ - (fun i : Fin d => (m i : ℝ)) ∈ Λ := by
    intro n
    induction n with
    | zero =>
        intro m hm
        have hm0 : m = 0 := by
          apply funext
          intro i
          have hle : m i ≤ (∑ j, m j) := by
            exact Finset.single_le_sum (fun j hj => Nat.zero_le (m j)) (Finset.mem_univ i)
          exact Nat.eq_zero_of_le_zero (le_trans hle hm)
        have hfun : (fun i : Fin d => (m i : ℝ)) = 0 := by
          rw [hm0]
          funext i
          simp
        simpa [hfun] using hμ
    | succ n ih =>
        intro m hm
        by_cases hz : m = 0
        · have hfun : (fun i : Fin d => (m i : ℝ)) = 0 := by
            rw [hz]
            funext i
            simp
          simpa [hfun] using hμ
        · have hpos : ∃ j, 0 < m j := by
            by_contra hc
            apply hz
            funext j
            exact Nat.eq_zero_of_not_pos (fun hj => hc ⟨j, hj⟩)
          rcases hpos with ⟨j, hj⟩
          let m' : Fin d → ℕ := fun i => if i = j then m j - 1 else m i
          have hm_decomp : ∀ i : Fin d, m i = m' i + (if i = j then 1 else 0) := by
            intro i
            by_cases hij : i = j
            · subst i
              simp [m']
              omega
            · simp [m', hij]
          have hm_sum : (∑ i, m' i) ≤ n := by
            have h : (∑ i, m i) = (∑ i, m' i) + 1 := by
              calc (∑ i, m i) = ∑ i, (m' i + (if i = j then 1 else 0)) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact hm_decomp i
                _ = (∑ i, m' i) + 1 := by
                    rw [Finset.sum_add_distrib]
                    have h1 : (∑ i, (if i = j then 1 else 0)) = 1 := by
                      simp
                    rw [h1]
            omega
          have hmm : (fun i : Fin d => (m' i : ℝ)) + rigidBasis j =
              (fun i : Fin d => (m i : ℝ)) := by
            funext i
            by_cases hij : i = j
            · subst i
              simp [rigidBasis]
              have hmj : m j = m' j + 1 := by
                have := hm_decomp j
                simpa using this
              rw [hmj]
              simp
            · simp [rigidBasis, hij, m']
          have hm'Λ : μ - (fun i : Fin d => (m' i : ℝ)) ∈ Λ := ih m' hm_sum
          have hstep := hdown (μ - (fun i : Fin d => (m' i : ℝ))) hm'Λ j
          have hgoal : μ - (fun i : Fin d => (m i : ℝ)) =
              (μ - (fun i : Fin d => (m' i : ℝ))) - rigidBasis j := by
            funext i
            have hi : ((fun i0 : Fin d => (m' i0 : ℝ)) + rigidBasis j) i =
                (fun i0 : Fin d => (m i0 : ℝ)) i := congrFun hmm i
            have hi' : (m' i : ℝ) + rigidBasis j i = (m i : ℝ) := by
              simpa [Pi.add_apply] using hi
            simp only [Pi.sub_apply]
            rw [← hi']
            ring
          simpa [hgoal] using hstep
  exact hmain (∑ i, m i) m (le_rfl)

lemma rigidTiling_singleCoset {d : ℕ} (hd : 0 < d) {Λ : Set (Fin d → ℝ)}
    (hΛ : IsContinuousTiling (rigidTile d) Λ) {t : Fin d → ℝ} (ht : t ∈ Λ) :
    ∀ lam : Fin d → ℝ, lam ∈ Λ →
      ∃ z : Fin d → ℤ, lam - t = (fun i : Fin d => (z i : ℝ)) := by
  classical
  intro lam hlam
  have hdown : ∀ μ : Fin d → ℝ, μ ∈ Λ → ∀ k : Fin d, μ - rigidBasis k ∈ Λ := by
    intro μ hμ k
    exact rigidTiling_downward hd hΛ hμ k
  let c : Fin d → ℝ := fun i => min (lam i) (t i) - 1
  let n : Fin d → ℕ := fun i => Int.toNat ⌊lam i - c i⌋
  let m : Fin d → ℕ := fun i => Int.toNat ⌊t i - c i⌋
  have hn_def : ∀ i : Fin d, (⌊lam i - c i⌋ : ℤ) = (n i : ℤ) := by
    intro i
    have hz : 0 ≤ ⌊lam i - c i⌋ := by
      apply Int.floor_nonneg.mpr
      have : c i ≤ lam i := by
        dsimp [c]
        have hle : min (lam i) (t i) ≤ lam i := min_le_left _ _
        linarith
      linarith
    exact (Int.toNat_of_nonneg hz).symm
  have hm_def : ∀ i : Fin d, (⌊t i - c i⌋ : ℤ) = (m i : ℤ) := by
    intro i
    have hz : 0 ≤ ⌊t i - c i⌋ := by
      apply Int.floor_nonneg.mpr
      have hle : min (lam i) (t i) ≤ t i := min_le_right _ _
      dsimp [c]
      linarith
    exact (Int.toNat_of_nonneg hz).symm
  have hcl : ∀ i : Fin d, c i ≤ lam i - (n i : ℝ) ∧ lam i - (n i : ℝ) < c i + 1 := by
    intro i
    have h1 : (⌊lam i - c i⌋ : ℝ) ≤ lam i - c i := by exact_mod_cast Int.floor_le (lam i - c i)
    have h2 : lam i - c i < (⌊lam i - c i⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one (lam i - c i)
    have hn : (n i : ℝ) = ⌊lam i - c i⌋ := by
      exact_mod_cast (hn_def i).symm
    rw [hn]
    constructor <;> linarith
  have hcl2 : ∀ i : Fin d, c i ≤ t i - (m i : ℝ) ∧ t i - (m i : ℝ) < c i + 1 := by
    intro i
    have h1 : (⌊t i - c i⌋ : ℝ) ≤ t i - c i := by exact_mod_cast Int.floor_le (t i - c i)
    have h2 : t i - c i < (⌊t i - c i⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one (t i - c i)
    have hm : (m i : ℝ) = ⌊t i - c i⌋ := by
      exact_mod_cast (hm_def i).symm
    rw [hm]
    constructor <;> linarith
  let L : Fin d → ℝ := lam - (fun i : Fin d => (n i : ℝ))
  let T : Fin d → ℝ := t - (fun i : Fin d => (m i : ℝ))
  have hLΛ : L ∈ Λ := by
    simpa [L] using rigid_down_nat hdown lam hlam n
  have hTΛ : T ∈ Λ := by
    simpa [T] using rigid_down_nat hdown t ht m
  have hclose : rigidClose L T := by
    intro i
    rcases hcl i with ⟨h1a, h1b⟩
    rcases hcl2 i with ⟨h2a, h2b⟩
    have hlow : -(1 : ℝ) < L i - T i := by
      -- L i ≥ c i, T i < c i + 1: L - T > c - (c+1) = -1
      have : L i ≥ c i := by simpa [L] using h1a
      have : T i < c i + 1 := by simpa [T] using h2b
      linarith
    have hhigh : L i - T i < 1 := by
      have : L i < c i + 1 := by simpa [L] using h1b
      have : T i ≥ c i := by simpa [T] using h2a
      linarith
    rw [abs_lt]
    exact ⟨hlow, hhigh⟩
  by_cases hLT : L = T
  · refine ⟨fun i => (n i : ℤ) - (m i : ℤ), ?_⟩
    ext i
    have hc := congrFun hLT i
    dsimp [L, T] at hc
    have hc' : lam i - (n i : ℝ) = t i - (m i : ℝ) := by
      simpa [Pi.sub_apply] using hc
    have : lam i - t i = (n i : ℝ) - (m i : ℝ) := by
      linarith
    simp only [Pi.sub_apply]
    rw [this]
    norm_num
  · exfalso
    exact (rigid_separated_of_tiling hΛ hLΛ hTΛ hLT) hclose

lemma lattice_translate_disjoint {d : ℕ} {z1 z2 : Fin d → ℤ} (hne : z1 ≠ z2) :
    volume ((rigidIntVec z1 +ᵥ rigidTile d) ∩ (rigidIntVec z2 +ᵥ rigidTile d)) = 0 := by
  let R := rigidTile d
  have hbad : volume {x : Fin d → ℝ | ¬ ∃! w ∈ rigidLattice d, x ∈ w +ᵥ R} = 0 := by
    simpa [R] using (MeasureTheory.ae_iff (μ := volume)).1 (rigidTile_tiling d)
  have hsub : (rigidIntVec z1 +ᵥ R) ∩ (rigidIntVec z2 +ᵥ R) ⊆
      {x : Fin d → ℝ | ¬ ∃! w ∈ rigidLattice d, x ∈ w +ᵥ R} := by
    intro x hx
    intro huniq
    have h1 : rigidIntVec z1 ∈ rigidLattice d := ⟨z1, by intro i; rfl⟩
    have h2 : rigidIntVec z2 ∈ rigidLattice d := ⟨z2, by intro i; rfl⟩
    have hne' : rigidIntVec z1 ≠ rigidIntVec z2 := by
      intro h
      apply hne
      apply funext
      intro i
      have hi := congrFun h i
      exact Int.cast_injective hi
    exact hne' (ExistsUnique.unique huniq ⟨h1, hx.1⟩ ⟨h2, hx.2⟩)
  exact measure_mono_null hsub hbad

lemma rigidTiling_eq_lattice {d : ℕ} (hd : 0 < d) {Λ : Set (Fin d → ℝ)}
    (hΛ : IsContinuousTiling (rigidTile d) Λ) {t : Fin d → ℝ} (ht : t ∈ Λ) :
    Λ = (fun x : Fin d → ℝ => x + t) '' rigidLattice d := by
  classical
  have hsub_im : Λ ⊆ (fun x : Fin d → ℝ => x + t) '' rigidLattice d := by
    intro y hy
    rcases (rigidTiling_singleCoset hd hΛ ht) y hy with ⟨z, hz⟩
    have hvec : rigidIntVec z ∈ rigidLattice d := ⟨z, by intro i; rfl⟩
    refine ⟨rigidIntVec z, hvec, ?_⟩
    ext i
    have hi := congrFun hz i
    simp [rigidIntVec, Pi.sub_apply] at hi
    simp [rigidIntVec, Pi.add_apply]
    linarith
  have hcount_im : ((fun x : Fin d → ℝ => x + t) '' rigidLattice d).Countable := by
    have hL : rigidLattice d = Set.range (fun z : Fin d → ℤ => rigidIntVec z) := by
      ext x
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z, ?_⟩
        ext i
        exact (hz i).symm
      · rintro ⟨z, rfl⟩
        exact ⟨z, by intro i; rfl⟩
    rw [hL]
    exact Set.Countable.image (Set.countable_range (fun z : Fin d → ℤ => rigidIntVec z)) (fun x => x + t)
  have hcount : Λ.Countable := Set.Countable.mono hsub_im hcount_im
  haveI : Countable {v : Fin d → ℝ // v ∈ Λ} := hcount.to_subtype
  ext y
  constructor
  · exact fun hy => hsub_im hy
  · rintro ⟨z, hzL, hyz⟩
    rcases hzL with ⟨z0, hz0⟩
    have hyz' : y = t + rigidIntVec z0 := by
      ext i
      have hzi : z i = (z0 i : ℝ) := hz0 i
      have hyi : y i = z i + t i := by
        have hc := congrFun hyz i
        simpa [Pi.add_apply] using hc.symm
      rw [hyi, hzi]
      simp [rigidIntVec, Pi.add_apply]
      abel_nf
    by_contra hynot
    let lam0 : Fin d → ℝ := t + rigidIntVec z0
    have hlam0R : 0 < volume (lam0 +ᵥ rigidTile d) := by
      change volume ((fun x : Fin d → ℝ => lam0 + x) '' rigidTile d) > 0
      rw [Set.image_add_left]
      simp [measure_preimage_add]
      exact rigidTile_volume_pos d
    let Bad : Set (Fin d → ℝ) := {x | ¬ ∃! v ∈ Λ, x ∈ v +ᵥ rigidTile d}
    have hBad : volume Bad = 0 := by
      simpa [Bad] using (MeasureTheory.ae_iff (μ := volume)).1 hΛ
    let U : Set (Fin d → ℝ) := {x | ∃ v : Fin d → ℝ, v ∈ Λ ∧ x ∈ (v +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d)}
    have hcover : (lam0 +ᵥ rigidTile d) ⊆ U ∪ Bad := by
      intro x hx
      by_cases hxB : x ∈ Bad
      · exact Or.inr hxB
      · left
        have hxGood : ∃! v ∈ Λ, x ∈ v +ᵥ rigidTile d := by
          by_contra hc
          exact hxB (by simpa [Bad] using hc)
        rcases hxGood with ⟨v, hv1, _⟩
        rcases hv1 with ⟨hvΛ, hvx⟩
        exact ⟨v, hvΛ, ⟨hvx, hx⟩⟩
    have hvol0 : volume (lam0 +ᵥ rigidTile d) ≤ volume U := by
      calc
        volume (lam0 +ᵥ rigidTile d) ≤ volume (U ∪ Bad) := measure_mono hcover
        _ ≤ volume U + volume Bad := measure_union_le _ _
        _ = volume U := by rw [hBad, add_zero]
    have hne_all : ∀ v : Fin d → ℝ, v ∈ Λ → v ≠ lam0 := by
      intro v hv hEq
      apply hynot
      have hyv : y = v := by rw [hyz', hEq]
      rwa [hyv]
    have hvec_inj : Function.Injective (fun z : Fin d → ℤ => rigidIntVec z) := by
      intro a b h
      apply funext
      intro i
      exact Int.cast_injective (congrFun h i)
    have hpiecenull : ∀ v : Fin d → ℝ, v ∈ Λ →
        volume ((v +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d)) = 0 := by
      intro v hv
      rcases (rigidTiling_singleCoset hd hΛ ht) v hv with ⟨zv, hzv⟩
      have hz' : v = t + rigidIntVec zv := by
        ext i
        have hi := congrFun hzv i
        simp [rigidIntVec, Pi.sub_apply] at hi
        simp [rigidIntVec, Pi.add_apply]
        linarith
      have hzvne : zv ≠ z0 := by
        intro hzz
        have hvlam : v = lam0 := by
          rw [hz', hzz]
        exact hne_all v hv hvlam
      have hzero := lattice_translate_disjoint (z1 := zv) (z2 := z0) hzvne
      have hpre : ((v +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d)) =
          (fun x : Fin d → ℝ => x - t) ⁻¹'
            ((rigidIntVec zv +ᵥ rigidTile d) ∩ (rigidIntVec z0 +ᵥ rigidTile d)) := by
        ext x
        constructor
        · intro hx
          rcases (Set.mem_vadd_set.mp hx.1) with ⟨r1, hr1, hxr1⟩
          rcases (Set.mem_vadd_set.mp hx.2) with ⟨r2, hr2, hxr2⟩
          constructor
          · rw [Set.mem_vadd_set]
            refine ⟨r1, hr1, ?_⟩
            change rigidIntVec zv + r1 = x - t
            calc
              rigidIntVec zv + r1 = (v + r1) - t := by rw [hz']; abel_nf
              _ = x - t := by
                have hxr1' : v + r1 = x := by simpa [vadd_eq_add] using hxr1
                rw [hxr1']
          · rw [Set.mem_vadd_set]
            refine ⟨r2, hr2, ?_⟩
            change rigidIntVec z0 + r2 = x - t
            calc
              rigidIntVec z0 + r2 = (lam0 + r2) - t := by dsimp [lam0]; abel_nf
              _ = x - t := by
                have hxr2' : lam0 + r2 = x := by simpa [vadd_eq_add] using hxr2
                rw [hxr2']
        · intro hx
          rcases hx with ⟨hx1, hx2⟩
          rcases (Set.mem_vadd_set.mp hx1) with ⟨r1, hr1, hxr1⟩
          rcases (Set.mem_vadd_set.mp hx2) with ⟨r2, hr2, hxr2⟩
          constructor
          · rw [Set.mem_vadd_set]
            refine ⟨r1, hr1, ?_⟩
            have hxr1' : rigidIntVec zv + r1 = x - t := by simpa [vadd_eq_add] using hxr1
            change v + r1 = x
            calc v + r1 = t + (rigidIntVec zv + r1) := by rw [hz']; abel_nf
              _ = t + (x - t) := by rw [hxr1']
              _ = x := by abel_nf
          · rw [Set.mem_vadd_set]
            refine ⟨r2, hr2, ?_⟩
            have hxr2' : rigidIntVec z0 + r2 = x - t := by simpa [vadd_eq_add] using hxr2
            change lam0 + r2 = x
            calc lam0 + r2 = t + (rigidIntVec z0 + r2) := by dsimp [lam0]; abel_nf
              _ = t + (x - t) := by rw [hxr2']
              _ = x := by abel_nf
      rw [hpre]
      have hmeas : volume ((fun x : Fin d → ℝ => x - t) ⁻¹'
            ((rigidIntVec zv +ᵥ rigidTile d) ∩ (rigidIntVec z0 +ᵥ rigidTile d))) =
            volume ((rigidIntVec zv +ᵥ rigidTile d) ∩ (rigidIntVec z0 +ᵥ rigidTile d)) := by
        have hfun : (fun x : Fin d → ℝ => x - t) =
            (fun x : Fin d → ℝ => -t + x) := by
          funext x
          simp [sub_eq_add_neg, add_comm]
        rw [hfun]
        exact measure_preimage_add (μ := volume) (-t)
            ((rigidIntVec zv +ᵥ rigidTile d) ∩ (rigidIntVec z0 +ᵥ rigidTile d))
      rw [hmeas]
      exact hzero
    have hvol_U : volume U ≤ 0 := by
      have hU_sub : U ⊆ ⋃ v : {v : Fin d → ℝ // v ∈ Λ},
          ((v.1 +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d)) := by
        intro x hx
        rcases hx with ⟨v, hvΛ, hx2⟩
        rw [Set.mem_iUnion]
        exact ⟨⟨v, hvΛ⟩, hx2⟩
      have hle : volume U ≤ ∑' v : {v : Fin d → ℝ // v ∈ Λ},
          volume ((v.1 +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d)) := by
        exact le_trans (measure_mono hU_sub) (measure_iUnion_le _)
      have htsum : (∑' v : {v : Fin d → ℝ // v ∈ Λ},
          volume ((v.1 +ᵥ rigidTile d) ∩ (lam0 +ᵥ rigidTile d))) = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro v
        exact hpiecenull v.1 v.2
      rw [htsum] at hle
      exact hle
    have hvol_le0 : volume (lam0 +ᵥ rigidTile d) ≤ 0 := le_trans hvol0 hvol_U
    exact (not_lt_of_ge hvol_le0) hlam0R

theorem rigid_tile_rigid_aux
    {d : ℕ} (hd : 0 < d) :
    ∃ R : Set (Fin d → ℝ), Bornology.IsBounded R ∧ MeasurableSet R ∧
      0 < MeasureTheory.volume R ∧
      IsContinuousTiling R {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} ∧
      ∀ Λ : Set (Fin d → ℝ), IsContinuousTiling R Λ →
        ∃ t : Fin d → ℝ,
          Λ = (fun x : Fin d → ℝ => x + t) ''
            {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} := by
  refine ⟨rigidTile d, ?_, ?_, ?_, ?_, ?_⟩
  · exact rigidTile_bounded d
  · exact rigidTile_measurable d
  · exact rigidTile_volume_pos d
  · simpa [rigidLattice] using rigidTile_tiling d
  · intro Λ hΛ
    rcases Filter.Eventually.exists hΛ with ⟨x, hx⟩
    rcases hx with ⟨v, hv1, _⟩
    rcases hv1 with ⟨hvΛ, _⟩
    exact ⟨v, rigidTiling_eq_lattice hd hΛ hvΛ⟩


theorem rigid_tile_rigid
    {d : ℕ} (hd : 0 < d) :
    ∃ R : Set (Fin d → ℝ), Bornology.IsBounded R ∧ MeasurableSet R ∧
      0 < MeasureTheory.volume R ∧
      IsContinuousTiling R {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} ∧
      ∀ Λ : Set (Fin d → ℝ), IsContinuousTiling R Λ →
        ∃ t : Fin d → ℝ,
          Λ = (fun x : Fin d → ℝ => x + t) ''
            {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)} := by
  exact rigid_tile_rigid_aux hd
end

end Commons.PeriodicTiling