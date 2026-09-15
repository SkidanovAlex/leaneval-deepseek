import ChallengeDeps
import Submission.FUP.Cubes
import Submission.Commons.Measure.EuclideanSpace.cellAverageSupport_uniform

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-- An axis-parallel box `∏ᵢ [aᵢ, bᵢ]` in `ℝᵈ`. -/
def box (a b : Fin d → ℝ) : Set ℝᵈ :=
  (fun x : ℝᵈ => x.ofLp) ⁻¹' Set.univ.pi (fun i => Set.Icc (a i) (b i))

lemma mem_box {a b : Fin d → ℝ} {x : ℝᵈ} :
    x ∈ box a b ↔ ∀ i : Fin d, a i ≤ x i ∧ x i ≤ b i := by
  simp only [box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]

lemma box_subset_box {a b a' b' : Fin d → ℝ} (ha : ∀ i, a' i ≤ a i) (hb : ∀ i, b i ≤ b' i) :
    box a b ⊆ box a' b' := by
  intro x hx
  rw [mem_box] at hx ⊢
  intro i
  exact ⟨le_trans (ha i) (hx i).1, le_trans (hx i).2 (hb i)⟩

lemma volume_box (a b : Fin d → ℝ) :
    (volume (box a b) : ENNReal) = ∏ i : Fin d, ENNReal.ofReal (b i - a i) := by
  have hmp : MeasurePreserving (fun x : ℝᵈ => x.ofLp) volume volume := by
    simpa using (PiLp.volume_preserving_ofLp (Fin d))
  rw [box, hmp.measure_preimage]
  · rw [← Real.volume_Icc_pi (a := a) (b := b)]
    congr 1
    exact Set.pi_univ_Icc a b
  · exact (MeasurableSet.univ_pi (fun i => (measurableSet_Icc (a := a i) (b := b i)))).nullMeasurableSet

lemma volume_box_of_nonneg {a b : Fin d → ℝ} (h : ∀ i, a i ≤ b i) :
    (volume (box a b) : ENNReal) = ENNReal.ofReal (∏ i : Fin d, (b i - a i)) := by
  rw [volume_box]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (h i))).symm

/-- `cube a b` (constant per-coordinate bounds) is a box. -/
lemma cube_eq_box (a b : ℝ) :
    (cube a b : Set ℝᵈ) = box (fun _ => a) (fun _ => b) := by
  ext x
  rw [mem_cube, mem_box]

/-- Half-side of the `L`-adic grid cell at depth `n`. -/
noncomputable def hss (L n : ℕ) : ℝ := ((L : ℝ) ^ n)⁻¹

lemma hss_pos {L : ℕ} (hL : 0 < L) (n : ℕ) : 0 < hss L n := by
  rw [hss]; positivity

lemma hss_ne_zero {L : ℕ} (hL : 0 < L) (n : ℕ) : hss L n ≠ 0 := ne_of_gt (hss_pos hL n)

lemma hss_succ {L : ℕ} (hL : 0 < L) (n : ℕ) : hss L (n + 1) = hss L n / L := by
  rw [hss, hss, pow_succ, mul_inv]
  ring

lemma hss_eq_mul_succ {L : ℕ} (hL : 0 < L) (n : ℕ) : hss L n = (L : ℝ) * hss L (n + 1) := by
  rw [hss_succ hL n]
  field_simp

/-- The `L`-adic grid cell at depth `n` with multi-index `k`. -/
def gridBox (L n : ℕ) (k : Fin d → ℕ) : Set ℝᵈ :=
  box (fun i => -1 + 2 * (k i) * hss L n) (fun i => -1 + 2 * ((k i : ℝ) + 1) * hss L n)

lemma gridBox_zero (L : ℕ) : gridBox L 0 (fun _ => 0) = (cube (-1) 1 : Set ℝᵈ) := by
  rw [cube_eq_box]
  unfold gridBox
  congr 1 <;> · funext i; norm_num [hss]

/-- Index of a child cell: refine coordinate `i` by the offset `j i`. -/
def childIndex (L : ℕ) {d : ℕ} (k : Fin d → ℕ) (j : Fin d → Fin L) : Fin d → ℕ :=
  fun i => L * k i + (j i : ℕ)

lemma gridBox_child_subset {L n : ℕ} (hL : 0 < L) (k : Fin d → ℕ) (j : Fin d → Fin L) :
    gridBox L (n + 1) (childIndex L k j) ⊆ gridBox L n k := by
  refine box_subset_box ?_ ?_ <;> intro i
  · have hs : hss L (n+1) = hss L n / L := hss_succ hL n
    have hLr : (0:ℝ) < L := by exact_mod_cast hL
    have hh : 0 < hss L n := hss_pos hL n
    rw [hs]
    show -1 + 2 * (k i) * hss L n ≤ -1 + 2 * ((childIndex L k j i : ℕ) : ℝ) * (hss L n / L)
    have hK : ((childIndex L k j i : ℕ) : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      rw [childIndex]; push_cast; ring
    rw [hK]
    have hkn : (k i : ℝ) * (L:ℝ) ≤ (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      have : (0:ℝ) ≤ (j i : ℝ) := by positivity
      nlinarith
    have hle : 2 * (k i : ℝ) * hss L n
        ≤ 2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ)) * (hss L n / L) := by
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hLr]
      have hm := mul_le_mul_of_nonneg_right hkn (by positivity : (0:ℝ) ≤ 2 * hss L n)
      nlinarith [hm]
    linarith
  · have hs : hss L (n+1) = hss L n / L := hss_succ hL n
    have hLr : (0:ℝ) < L := by exact_mod_cast hL
    have hh : 0 < hss L n := hss_pos hL n
    rw [hs]
    show -1 + 2 * (((childIndex L k j i : ℕ) : ℝ) + 1) * (hss L n / L)
        ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n
    have hK : ((childIndex L k j i : ℕ) : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      rw [childIndex]; push_cast; ring
    rw [hK]
    have hj : (j i : ℝ) + 1 ≤ (L:ℝ) := by
      have h2 : ((j i : ℕ) + 1 : ℕ) ≤ L := Nat.succ_le_iff.mpr (j i).isLt
      exact_mod_cast h2
    have hle : 2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1) * (hss L n / L)
        ≤ 2 * ((k i : ℝ) + 1) * hss L n := by
      rw [← mul_div_assoc]
      rw [div_le_iff₀ hLr]
      have h1 : (2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1)) * hss L n
          ≤ (2 * ((L:ℝ) * ((k i:ℝ) + 1))) * hss L n := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
        nlinarith [hj]
      calc (2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1)) * hss L n
          ≤ (2 * ((L:ℝ) * ((k i:ℝ) + 1))) * hss L n := h1
        _ = (2 * ((k i:ℝ) + 1) * hss L n) * L := by ring
    linarith

/-- Covering an interval by `N` consecutive intervals of length `δ` starting at `a`. -/
lemma exists_child_coord {a δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) {r : ℝ}
    (hlo : a ≤ r) (hhi : r ≤ a + (N : ℝ) * δ) :
    ∃ j : ℕ, j < N ∧ a + (j : ℝ) * δ ≤ r ∧ r ≤ a + ((j : ℝ) + 1) * δ := by
  by_cases h : r < a + (N : ℝ) * δ
  · rcases Commons.Measure.EuclideanSpace.cell_cover_coord hδ hlo h with ⟨j, hjN, h1, h2⟩
    exact ⟨j, hjN, h1, le_of_lt h2⟩
  · push Not at h
    have hr : r = a + (N : ℝ) * δ := le_antisymm hhi h
    refine ⟨N - 1, by omega, ?_, ?_⟩
    · rw [hr]
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      rw [hcast]
      nlinarith [hδ]
    · rw [hr]
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      rw [hcast]
      nlinarith [hδ]

open Classical in
lemma gridBox_cover_children {L n : ℕ} (hL : 0 < L) (k : Fin d → ℕ) {x : ℝᵈ}
    (hx : x ∈ gridBox L n k) :
    ∃ j : Fin d → Fin L, x ∈ gridBox L (n + 1) (childIndex L k j) := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hspos : 0 < 2 * hss L (n + 1) := by
    have := hss_pos hL (n+1); positivity
  have hcoord : ∀ i : Fin d, ∃ j : Fin L,
      -1 + 2 * ((L:ℝ) * (k i : ℝ) + (j : ℝ)) * hss L (n + 1) ≤ x i ∧
      x i ≤ -1 + 2 * ((L:ℝ) * (k i : ℝ) + (j : ℝ) + 1) * hss L (n + 1) := by
    intro i
    rw [gridBox, mem_box] at hx
    have hlo : -1 + 2 * (k i : ℝ) * hss L n ≤ x i := (hx i).1
    have hhi : x i ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n := (hx i).2
    have hscale : hss L n = (L : ℝ) * hss L (n + 1) := hss_eq_mul_succ hL n
    rw [hscale] at hlo hhi
    have hhi' : x i ≤ (-1 + 2 * (k i : ℝ) * ((L : ℝ) * hss L (n + 1)))
        + (L : ℝ) * (2 * hss L (n + 1)) := by
      have heq : (-1 + 2 * (k i : ℝ) * ((L : ℝ) * hss L (n + 1)))
          + (L : ℝ) * (2 * hss L (n + 1))
          = -1 + 2 * ((k i : ℝ) + 1) * ((L : ℝ) * hss L (n + 1)) := by ring
      rw [heq]; exact hhi
    rcases exists_child_coord hspos hL hlo hhi' with ⟨j, hjL, hj1, hj2⟩
    refine ⟨⟨j, hjL⟩, ?_, ?_⟩
    · have heq : (-1 + 2 * (k i : ℝ) * ((L:ℝ) * hss L (n+1))) + (j : ℝ) * (2 * hss L (n+1))
          = -1 + 2 * ((L:ℝ) * (k i : ℝ) + (j : ℝ)) * hss L (n+1) := by ring
      rw [← heq]; exact hj1
    · have heq : (-1 + 2 * (k i : ℝ) * ((L:ℝ) * hss L (n+1))) + ((j : ℝ) + 1) * (2 * hss L (n+1))
          = -1 + 2 * ((L:ℝ) * (k i : ℝ) + (j : ℝ) + 1) * hss L (n+1) := by ring
      rw [← heq]; exact hj2
  choose j hj using hcoord
  refine ⟨j, ?_⟩
  rw [gridBox, mem_box]
  intro i
  have hK : ((childIndex L k j i : ℕ) : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
    rw [childIndex]; push_cast; ring
  constructor
  · rw [hK]
    exact (hj i).1
  · rw [hK]
    exact (hj i).2

lemma sub_apply' (x y : ℝᵈ) (i : Fin d) : (x - y) i = x i - y i := rfl

lemma hss_nonneg (L n : ℕ) : 0 ≤ hss L n := by rw [hss]; positivity

/-- The centre of a grid cell. -/
noncomputable def gridCenter (L n : ℕ) (k : Fin d → ℕ) : ℝᵈ :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm
    (fun i => -1 + 2 * ((k i : ℝ) + 1/2) * hss L n)

lemma gridCenter_apply (L n : ℕ) (k : Fin d → ℕ) (i : Fin d) :
    (gridCenter L n k) i = -1 + 2 * ((k i : ℝ) + 1/2) * hss L n := by
  have h : (EuclideanSpace.equiv (Fin d) ℝ) (gridCenter L n k)
      = fun i => -1 + 2 * ((k i : ℝ) + 1/2) * hss L n :=
    (EuclideanSpace.equiv (Fin d) ℝ).apply_symm_apply _
  have := congrFun h i
  simpa [equiv_apply] using this

/-- The ball inscribed in a grid cell is contained in the cell. -/
lemma closedBall_gridCenter_subset_gridBox {L n : ℕ} (k : Fin d → ℕ) :
    closedBall (gridCenter L n k) (hss L n) ⊆ gridBox L n k := by
  intro x hx
  rw [gridBox, mem_box]
  intro i
  rw [Metric.mem_closedBall] at hx
  have hcoord : ‖(x - gridCenter L n k) i‖ ≤ ‖x - gridCenter L n k‖ :=
    PiLp.norm_apply_le (x - gridCenter L n k) i
  have hdist : dist x (gridCenter L n k) = ‖x - gridCenter L n k‖ := dist_eq_norm x _
  rw [hdist] at hx
  have h1 : |x i - (gridCenter L n k) i| ≤ hss L n := by
    calc |x i - (gridCenter L n k) i| = ‖(x - gridCenter L n k) i‖ := by
          rw [sub_apply']; simp
      _ ≤ ‖x - gridCenter L n k‖ := hcoord
      _ ≤ hss L n := hx
  rw [gridCenter_apply] at h1
  constructor <;> linarith [abs_le.mp h1]

/-- Two points of a depth-`(n+1)` cell are at distance at most `√d · 2 hss(L,n+1)`. -/
lemma norm_sub_le_of_mem_gridBox {L n : ℕ} {k : Fin d → ℕ} {z x : ℝᵈ}
    (hz : z ∈ gridBox L (n+1) k) (hx : x ∈ gridBox L (n+1) k) :
    ‖z - x‖ ≤ Real.sqrt (d : ℝ) * (2 * hss L (n+1)) := by
  rw [gridBox, mem_box] at hz hx
  have hmem : z - x ∈ (cube (-(2 * hss L (n+1))) (2 * hss L (n+1)) : Set ℝᵈ) := by
    rw [mem_cube]
    intro i
    rw [sub_apply']
    constructor <;> linarith [(hz i).1, (hz i).2, (hx i).1, (hx i).2]
  exact norm_le_of_mem_cube_center (by linarith [hss_nonneg L (n+1)] : 0 ≤ 2 * hss L (n+1)) hmem

/-- Box porosity at scale `L` up to depth `N`, as in Han–Schlag. -/
def BoxPorous (L N : ℕ) (X : Set ℝᵈ) : Prop :=
  ∀ n < N, ∀ k : Fin d → ℕ, (X ∩ gridBox L n k).Nonempty →
    ∃ j : Fin d → Fin L, gridBox L (n + 1) (childIndex L k j) ∩ X = ∅

/-- Appendix lemma `compare_porosity`: a set porous on balls from scales `hmin` to `hmax` is
box porous at scale `L` at all depths `n < N` for which the cell side `2 L^{-n}` lies in
`(hmin, hmax)`.  (In the paper `hmax = 1` together with the convention that the grid at depth
`0` consists of a single cube of side `2`; here the range is kept explicit so that the lemma
is applicable at depth `0` as well.) -/
lemma boxPorous_of_porousOnBalls {ν hmin hmax : ℝ} {L N : ℕ} {X : Set ℝᵈ}
    (hL : 0 < L) (hνL : Real.sqrt (d : ℝ) ≤ ν * L)
    (hpor : PorousOnBalls ν hmin hmax X)
    (hscale : ∀ n < N, 2 * hss L n ∈ Set.Ioo hmin hmax) :
    BoxPorous L N X := by
  intro n hnN k _
  have hn := hscale n hnN
  rcases hpor (gridCenter L n k) (2 * hss L n) hn with ⟨x, hxball, hball⟩
  have hxbox : x ∈ gridBox L n k := by
    apply closedBall_gridCenter_subset_gridBox
    rw [Metric.mem_closedBall] at hxball ⊢
    rwa [show 2 * hss L n / 2 = hss L n by ring] at hxball
  rcases gridBox_cover_children hL k hxbox with ⟨j, hxj⟩
  refine ⟨j, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  have hzx : z ∈ closedBall x (ν * (2 * hss L n)) := by
    rw [Metric.mem_closedBall]
    have hdist : dist z x ≤ Real.sqrt (d : ℝ) * (2 * hss L (n+1)) :=
      norm_sub_le_of_mem_gridBox hz.1 hxj
    have hle : Real.sqrt (d : ℝ) * (2 * hss L (n+1)) ≤ ν * (2 * hss L n) := by
      have h1 : hss L n = (L : ℝ) * hss L (n + 1) := hss_eq_mul_succ hL n
      have h2 : 0 ≤ 2 * hss L (n+1) := by linarith [hss_nonneg L (n+1)]
      have h3 : Real.sqrt (d : ℝ) * (2 * hss L (n+1))
          ≤ (ν * L) * (2 * hss L (n+1)) := mul_le_mul_of_nonneg_right hνL h2
      rw [h1]
      nlinarith [h3]
    linarith [hdist]
  have hc : z ∈ closedBall x (ν * (2 * hss L n)) ∩ X := ⟨hzx, hz.2⟩
  simpa [hball] using hc

/-- Appendix lemma `compare_porosity` in the form used for the Han–Schlag comparison: a set
`ν`-porous on balls from scales `hmin` to `hmax` is box porous at scale `L` at all depths
`n < N` for which the cell half-side `L^{-n}` lies in `(hmin, hmax]`.  The porosity ball used
has diameter `(hmin + L^{-n})/2`, which keeps it strictly inside the cell and strictly below
`hmax`; the hypothesis `4√d ≤ ν L` makes the ball of radius `ν` times this diameter contain a
child cell. -/
lemma boxPorous_of_porousOnBalls_lt {ν hmin hmax : ℝ} {L N : ℕ} {X : Set ℝᵈ}
    (hL : 0 < L) (hνL : 4 * Real.sqrt (d : ℝ) ≤ ν * L) (hhmin : 0 < hmin)
    (hpor : PorousOnBalls ν hmin hmax X)
    (hscale : ∀ n < N, hmin < hss L n ∧ hss L n ≤ hmax) :
    BoxPorous L N X := by
  intro n hnN k _
  obtain ⟨hlo, hhi⟩ := hscale n hnN
  set R : ℝ := (hmin + hss L n) / 2 with hRdef
  have hRgt : hmin < R := by rw [hRdef]; linarith
  have hRlt : R < hmax := by rw [hRdef]; linarith
  rcases hpor (gridCenter L n k) R ⟨hRgt, hRlt⟩ with ⟨x, hxball, hhole⟩
  have hxbox : x ∈ gridBox L n k := by
    apply closedBall_gridCenter_subset_gridBox
    rw [Metric.mem_closedBall] at hxball ⊢
    have h2 : R / 2 ≤ hss L n := by rw [hRdef]; linarith
    linarith
  rcases gridBox_cover_children hL k hxbox with ⟨j, hxj⟩
  refine ⟨j, ?_⟩
  apply Set.subset_empty_iff.mp
  intro z hz
  have hzx : z ∈ closedBall x (ν * R) := by
    rw [Metric.mem_closedBall]
    have hdist : dist z x ≤ Real.sqrt (d : ℝ) * (2 * hss L (n + 1)) :=
      norm_sub_le_of_mem_gridBox hz.1 hxj
    have hle : Real.sqrt (d : ℝ) * (2 * hss L (n + 1)) ≤ ν * R := by
      have h1 : hss L n = (L : ℝ) * hss L (n + 1) := hss_eq_mul_succ hL n
      have h2 : (0 : ℝ) ≤ 2 * hss L (n + 1) := by linarith [hss_nonneg L (n + 1)]
      have h3 : Real.sqrt (d : ℝ) * (2 * hss L (n + 1))
          ≤ (ν * L / 4) * (2 * hss L (n + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ h2
        linarith
      have h4 : Real.sqrt (d : ℝ) * (2 * hss L (n+1)) ≤ ν * hss L n / 2 := by
        have : (ν * L / 4) * (2 * hss L (n + 1)) = ν * hss L n / 2 := by
          rw [h1]; ring
        rwa [this] at h3
      have h5 : ν * hss L n / 2 ≤ ν * R := by
        have hRge : hss L n / 2 ≤ R := by rw [hRdef]; linarith [le_of_lt hhmin]
        have hLr : (0 : ℝ) < L := by exact_mod_cast hL
        have hν0 : 0 ≤ ν := by
          have hpos : 0 ≤ (L : ℝ) * ν := by
            have hsqrt : (0 : ℝ) ≤ 4 * Real.sqrt (d : ℝ) := by positivity
            linarith
          exact nonneg_of_mul_nonneg_right hpos hLr
        nlinarith
      linarith
    linarith
  have hc : z ∈ closedBall x (ν * R) ∩ X := ⟨hzx, hz.2⟩
  simpa [hhole] using hc

lemma gridBox_subset_iUnion_children {L n : ℕ} (hL : 0 < L) (k : Fin d → ℕ) :
    gridBox L n k ⊆ ⋃ j : Fin d → Fin L, gridBox L (n + 1) (childIndex L k j) := by
  intro x hx
  rcases gridBox_cover_children hL k hx with ⟨j, hj⟩
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

lemma volume_gridBox (L n : ℕ) (k : Fin d → ℕ) :
    volume (gridBox L n k) = ∏ i : Fin d, ENNReal.ofReal (2 * hss L n) := by
  rw [gridBox, volume_box]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  ring

lemma volume_gridBox_eq (L n : ℕ) (k : Fin d → ℕ) :
    volume (gridBox L n k) = ENNReal.ofReal ((2 * hss L n) ^ d) := by
  rw [volume_gridBox, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith [hss_nonneg L n] : (0 : ℝ) ≤ 2 * hss L n)]

lemma volume_cube_unit :
    volume (cube (-1) 1 : Set ℝᵈ) = ENNReal.ofReal ((2 : ℝ) ^ d) := by
  rw [cube_eq_box]
  rw [volume_box_of_nonneg (fun i => by norm_num : ∀ i : Fin d, (-1:ℝ) ≤ 1)]
  congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma card_childIndex (L : ℕ) :
    Fintype.card (Fin d → Fin L) = L ^ d := by
  simp [Fintype.card_fun]

/-- The recursion step bounding the measure in a cell by the measures in the children,
dropping the empty child provided by box porosity. -/
lemma volume_inter_gridBox_le {L N : ℕ} {X : Set ℝᵈ} (hL : 0 < L) (hbox : BoxPorous L N X) :
    ∀ n < N, ∀ k : Fin d → ℕ,
      volume (X ∩ gridBox L n k) ≤
        ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) *
          (⨆ k' : Fin d → ℕ, volume (X ∩ gridBox L (n + 1) k')) := by
  intro n hnN k
  by_cases hne : (X ∩ gridBox L n k).Nonempty
  · rcases hbox n hnN k hne with ⟨j0, hj0⟩
    have hcover : X ∩ gridBox L n k ⊆
        ⋃ j : Fin d → Fin L, X ∩ gridBox L (n + 1) (childIndex L k j) := by
      intro z hz
      rcases Set.mem_iUnion.mp (gridBox_subset_iUnion_children hL k hz.2) with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, ⟨hz.1, hj⟩⟩
    have hterm : volume (X ∩ gridBox L (n + 1) (childIndex L k j0)) = 0 := by
      have h1 : X ∩ gridBox L (n + 1) (childIndex L k j0) = ∅ := by
        rw [Set.inter_comm]
        exact hj0
      rw [h1, measure_empty]
    calc volume (X ∩ gridBox L n k)
        ≤ volume (⋃ j : Fin d → Fin L, X ∩ gridBox L (n + 1) (childIndex L k j)) :=
          measure_mono hcover
      _ ≤ ∑' j : Fin d → Fin L, volume (X ∩ gridBox L (n + 1) (childIndex L k j)) :=
          measure_iUnion_le _
      _ = ∑ j : Fin d → Fin L, volume (X ∩ gridBox L (n + 1) (childIndex L k j)) :=
          tsum_fintype _
      _ = ∑ j ∈ (Finset.univ.erase j0), volume (X ∩ gridBox L (n + 1) (childIndex L k j)) := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j0), hterm, add_zero]
      _ ≤ ∑ _j ∈ (Finset.univ.erase j0),
            (⨆ k' : Fin d → ℕ, volume (X ∩ gridBox L (n + 1) k')) :=
          Finset.sum_le_sum (fun j _ => le_iSup (fun k' => volume (X ∩ gridBox L (n + 1) k')) (childIndex L k j))
      _ = ((Finset.univ.erase j0).card : ℝ≥0∞) *
            (⨆ k' : Fin d → ℕ, volume (X ∩ gridBox L (n + 1) k')) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) *
            (⨆ k' : Fin d → ℕ, volume (X ∩ gridBox L (n + 1) k')) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty]
    exact zero_le

/-- Box porosity gives a power-law bound on the measure (relative to the unit cube). -/
lemma volume_le_of_boxPorous {L N : ℕ} {X : Set ℝᵈ} (hL : 0 < L)
    (hXsub : X ⊆ cube (-1) 1) (hbox : BoxPorous L N X) :
    volume X ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ N *
      volume (gridBox L N (fun _ : Fin d => 0)) := by
  let J : ℕ → ℝ≥0∞ := fun n => ⨆ k : Fin d → ℕ, volume (X ∩ gridBox L n k)
  have h0 : volume X ≤ J 0 := by
    have hcube : X ∩ gridBox L 0 (fun _ => 0) = X := by
      rw [gridBox_zero]
      exact Set.inter_eq_left.mpr hXsub
    calc volume X = volume (X ∩ gridBox L 0 (fun _ => 0)) := by rw [hcube]
      _ ≤ J 0 := le_iSup (fun k => volume (X ∩ gridBox L 0 k)) (fun _ => 0)
  have hstep : ∀ n < N, J n ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) * J (n + 1) := by
    intro n hnN
    refine iSup_le (fun k => ?_)
    exact volume_inter_gridBox_le hL hbox n hnN k
  have hN : J N ≤ volume (gridBox L N (fun _ : Fin d => 0)) := by
    refine iSup_le (fun k => ?_)
    calc volume (X ∩ gridBox L N k) ≤ volume (gridBox L N k) := measure_mono Set.inter_subset_right
      _ = volume (gridBox L N (fun _ : Fin d => 0)) := by
        rw [volume_gridBox_eq, volume_gridBox_eq]
  have hiter : ∀ M ≤ N, J 0 ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ M * J M := by
    intro M
    induction M with
    | zero => intro _; simp
    | succ M ih =>
        intro hM
        have hs := hstep M (by omega)
        have ihM := ih (le_trans (Nat.le_succ M) hM)
        calc J 0 ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ M * J M := ihM
          _ ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ M *
                (((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) * J (M + 1)) := by gcongr
          _ = ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ (M + 1) * J (M + 1) := by
              rw [pow_succ]; ring
  calc volume X ≤ J 0 := h0
    _ ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ N * J N := hiter N le_rfl
    _ ≤ ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ N *
          volume (gridBox L N (fun _ : Fin d => 0)) := by gcongr

/-- Rewriting the box-porosity bound in terms of the unit cube measure. -/
lemma boxBounded_volume_eq {L N : ℕ} (hL : 1 ≤ L) :
    ((Fintype.card (Fin d → Fin L) - 1 : ℕ) : ℝ≥0∞) ^ N *
        volume (gridBox L N (fun _ : Fin d => 0))
      = ENNReal.ofReal ((1 - ((L : ℝ) ^ d)⁻¹) ^ N) * volume (cube (-1) 1 : Set ℝᵈ) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hLd_pos : (0 : ℝ) < (L : ℝ) ^ d := pow_pos hL0 d
  have hLd_ge_one : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL : (1:ℝ) ≤ L)
  have h1 : 1 ≤ L ^ d := by exact_mod_cast hLd_ge_one
  have hcast : (((L ^ d - 1 : ℕ)) : ℝ) = (L : ℝ) ^ d - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  have hpow : (2 * hss L N) ^ d = (2 : ℝ) ^ d * (((L : ℝ) ^ d)⁻¹) ^ N := by
    rw [mul_pow, hss]
    congr 1
    rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  have hcard : Fintype.card (Fin d → Fin L) = L ^ d := card_childIndex L
  have h0a : (0 : ℝ) ≤ (((L : ℝ) ^ d - 1) ^ N) := by positivity
  have h0b : (0 : ℝ) ≤ (L ^ d - 1 : ℕ) := by positivity
  rw [volume_gridBox_eq, volume_cube_unit, hcard, ← ENNReal.ofReal_natCast (L ^ d - 1)]
  rw [← ENNReal.ofReal_pow h0b, hcast]
  rw [← ENNReal.ofReal_mul (p := ((L:ℝ)^d - 1)^N) (q := (2 * hss L N)^d) (hp := by positivity)]
  have h0c : (0:ℝ) ≤ (1 - ((L:ℝ)^d)⁻¹)^N := by
    have : (0:ℝ) ≤ 1 - ((L:ℝ)^d)⁻¹ := by
      have h := inv_le_one_of_one_le₀ hLd_ge_one
      linarith
    positivity
  rw [← ENNReal.ofReal_mul (p := (1 - ((L:ℝ)^d)⁻¹)^N) (q := (2:ℝ)^d) (hp := h0c)]
  congr 1
  rw [hpow]
  have hne : ((L : ℝ) ^ d) ≠ 0 := ne_of_gt hLd_pos
  rw [show ((L:ℝ)^d - 1)^N * ((2:ℝ)^d * (((L:ℝ)^d)⁻¹)^N)
      = ((L:ℝ)^d - 1)^N * (((L:ℝ)^d)⁻¹)^N * (2:ℝ)^d by ring]
  have hfac : ((L:ℝ)^d - 1) * ((L:ℝ)^d)⁻¹ = 1 - ((L:ℝ)^d)⁻¹ := by
    rw [sub_mul, one_mul, mul_inv_cancel₀ hne]
  rw [← mul_pow ((L:ℝ)^d - 1) (((L:ℝ)^d)⁻¹) N, hfac]

/-- Box porosity gives a per-cell power-law measure bound. -/
lemma volume_le_of_boxPorous' {L N : ℕ} {X : Set ℝᵈ} (hL : 1 ≤ L)
    (hXsub : X ⊆ cube (-1) 1) (hbox : BoxPorous L N X) :
    volume X ≤ ENNReal.ofReal ((1 - ((L : ℝ) ^ d)⁻¹) ^ N) * volume (cube (-1) 1 : Set ℝᵈ) := by
  rw [← boxBounded_volume_eq hL]
  exact volume_le_of_boxPorous (by omega) hXsub hbox

end Submission.FUP
