import ChallengeDeps
import Submission.FUP.Dyadic
import Submission.FUP.BoxPorosity
import Submission.Commons.Measure.Real.exists_cell_Icc
import Submission.Commons.Measure.EuclideanSpace.iUnion_box_grid_pos

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The width-`W` cube covers of §6.1

This module starts the formalisation of the weight construction of §6.1 of Cohen's
*Fractal uncertainty in higher dimensions*: the families of axis-parallel cubes of width
`W_k = 2^k/k^s` covering the dyadic annulus `A_k`, the associated set `Y_k`, and the
one-dimensional intersection estimates following from the porosity of `Y`.
-/

/-- Lower corner of the `j`-th cube of the width-`W`, spacing-`W/2` grid anchored at `-R`. -/
noncomputable def coverCoef (R W : ℝ) (j : Fin d → ℕ) (i : Fin d) : ℝ :=
  -R + (j i : ℝ) * (W / 2)

/-- The `j`-th cube of the width-`W` grid (spacing `W/2`, so consecutive cubes overlap). -/
def coverBox (R W : ℝ) (j : Fin d → ℕ) : Set ℝᵈ :=
  box (coverCoef R W j) (fun i => coverCoef R W j i + W)

/-- The inner half of the `j`-th cube; these tile the space. -/
def coverBoxHalf (R W : ℝ) (j : Fin d → ℕ) : Set ℝᵈ :=
  box (fun i => coverCoef R W j i + W / 4) (fun i => coverCoef R W j i + 3 * W / 4)

lemma mem_coverBox {R W : ℝ} {j : Fin d → ℕ} {x : ℝᵈ} :
    x ∈ coverBox R W j ↔ ∀ i : Fin d, coverCoef R W j i ≤ x i ∧ x i ≤ coverCoef R W j i + W :=
  mem_box

lemma mem_coverBoxHalf {R W : ℝ} {j : Fin d → ℕ} {x : ℝᵈ} :
    x ∈ coverBoxHalf R W j ↔
      ∀ i : Fin d, coverCoef R W j i + W / 4 ≤ x i ∧ x i ≤ coverCoef R W j i + 3 * W / 4 :=
  mem_box

lemma coverBoxHalf_subset_coverBox {R W : ℝ} (hW : 0 ≤ W) (j : Fin d → ℕ) :
    coverBoxHalf R W j ⊆ coverBox R W j := by
  intro x hx
  rw [mem_coverBoxHalf] at hx
  rw [mem_coverBox]
  intro i
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

/-- Consecutive cubes of the cover are at distance at most `√d·W` from each other. -/
lemma norm_sub_le_of_mem_coverBox {R W : ℝ} (hW : 0 ≤ W) {j : Fin d → ℕ} {z x : ℝᵈ}
    (hz : z ∈ coverBox R W j) (hx : x ∈ coverBox R W j) :
    ‖z - x‖ ≤ Real.sqrt (d : ℝ) * W := by
  rw [mem_coverBox] at hz hx
  have hmem : z - x ∈ (cube (-W) W : Set ℝᵈ) := by
    rw [mem_cube]
    intro i
    rw [show (z - x) i = z i - x i from rfl]
    constructor <;> linarith [(hz i).1, (hz i).2, (hx i).1, (hx i).2]
  exact norm_le_of_mem_cube_center hW hmem

/-- The half-cubes of the grid cover the cube `[-b,b]^d` provided `b + W/4 ≤ R` and
`b + R - W/4 ≤ N·W/2`. -/
lemma pi_Icc_subset_iUnion_coverBoxHalf {R W b : ℝ} (hW : 0 < W) {N : ℕ} (hN : 0 < N)
    (h1 : b + W / 4 ≤ R) (h2 : b + R ≤ (N : ℝ) * (W / 2)) :
    (cube (-b) b : Set ℝᵈ) ⊆
      ⋃ j : Fin d → Fin N, coverBoxHalf R W (fun i => (j i : ℕ)) := by
  intro x hx
  rw [mem_cube] at hx
  have hcoord : ∀ i : Fin d, ∃ k : ℕ, k < N ∧
      x i ∈ Set.Icc (-R + (k : ℝ) * (W / 2) + W / 4)
        (-R + (k : ℝ) * (W / 2) + 3 * W / 4) := by
    intro i
    have hxi := hx i
    have hlo : -R + W / 4 ≤ x i := by linarith [hxi.1]
    have hhi : x i ≤ -R + W / 4 + (N : ℝ) * (W / 2) := by
      have : -R + (N : ℝ) * (W / 2) ≤ -R + W / 4 + (N : ℝ) * (W / 2) := by linarith
      linarith [hxi.2, h2, this]
    rcases Commons.Measure.Real.exists_cell_Icc N hN ⟨hlo, hhi⟩ with ⟨k, hkN, hk⟩
    refine ⟨k, hkN, ?_, ?_⟩
    · have : -R + W / 4 + (k : ℝ) * (W / 2) = -R + (k : ℝ) * (W / 2) + W / 4 := by ring
      linarith [hk.1, this.symm.le, this.le]
    · have : -R + W / 4 + ((k : ℝ) + 1) * (W / 2) = -R + (k : ℝ) * (W / 2) + 3 * W / 4 := by ring
      have hkk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hkk] at hk
      linarith [hk.2, this.symm.le, this.le]
  choose k hkN hk using hcoord
  refine Set.mem_iUnion.mpr ⟨fun i => ⟨k i, hkN i⟩, ?_⟩
  rw [mem_coverBoxHalf]
  intro i
  have hki := hk i
  have hcoef : coverCoef R W (fun i => (k i : ℕ)) i = -R + (k i : ℝ) * (W / 2) := rfl
  rw [hcoef]
  exact ⟨by linarith [hki.1], by linarith [hki.2]⟩

/-- The union of the width-`W` cubes of the grid (anchored at `-R`) that meet `Y ∩ A`.
This is the set `𝓢_{𝕐,k}` / `𝕐_k` of §6.1 of the paper. -/
def yCover (R W : ℝ) (N : ℕ) (Y A : Set ℝᵈ) : Set ℝᵈ :=
  {x | ∃ j : Fin d → Fin N,
    (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty ∧
      x ∈ coverBox R W (fun i => (j i : ℕ))}

lemma yCover_subset_iUnion (R W : ℝ) (N : ℕ) (Y A : Set ℝᵈ) :
    yCover R W N Y A ⊆ ⋃ j : Fin d → Fin N, coverBox R W (fun i => (j i : ℕ)) := by
  rintro x ⟨j, -, hx⟩
  exact Set.mem_iUnion.mpr ⟨j, hx⟩

/-- `Y_k` is contained in the closed `√d·W`-neighbourhood of `Y ∩ A`: every cube of the grid
through a point of `Y ∩ A` has diameter at most `√d·W`. -/
lemma yCover_subset_nbhd (R W : ℝ) (N : ℕ) (Y A : Set ℝᵈ) (hW : 0 ≤ W) :
    yCover R W N Y A ⊆ nbhd (Y ∩ A) (Real.sqrt (d : ℝ) * W) := by
  rintro x ⟨j, ⟨y, hybox, hyY, hyA⟩, hxj⟩
  refine subset_closure ⟨y, ⟨hyY, hyA⟩, x - y, ?_, by abel⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : ‖x - y‖ ≤ Real.sqrt (d : ℝ) * W := norm_sub_le_of_mem_coverBox hW hxj hybox
  simpa [dist_eq_norm, norm_sub_rev] using h

/-- If `A ⊆ [-a,a]^d` and the grid parameters satisfy `a + W/4 ≤ R`, `a + R ≤ N·W/2`, then
`Y ∩ A ⊆ Y_k`: the inner halves of the grid cubes tile the cube `[-a,a]^d`. -/
lemma inter_subset_yCover {R W a : ℝ} (hW : 0 < W) {N : ℕ} (hN : 0 < N)
    (h1 : a + W / 4 ≤ R) (h2 : a + R ≤ (N : ℝ) * (W / 2))
    {Y A : Set ℝᵈ} (hA : A ⊆ cube (-a) a) :
    Y ∩ A ⊆ yCover R W N Y A := by
  rintro x ⟨hxY, hxA⟩
  have hxpi : x ∈ cube (-a) a := hA hxA
  have hmem : x ∈ ⋃ j : Fin d → Fin N, coverBoxHalf R W (fun i => (j i : ℕ)) :=
    pi_Icc_subset_iUnion_coverBoxHalf hW hN h1 h2 hxpi
  rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
  have hxbox : x ∈ coverBox R W (fun i => (j i : ℕ)) :=
    coverBoxHalf_subset_coverBox (le_of_lt hW) _ hj
  exact ⟨j, ⟨x, hxbox, ⟨hxY, hxA⟩⟩, hxbox⟩

lemma card_coverBox_le (R W : ℝ) (hW : 0 < W) (N : ℕ) (x : ℝᵈ) :
    Nat.card {j : Fin d → Fin N // x ∈ coverBox R W (fun i => (j i : ℕ))} ≤ 3 ^ d := by
  classical
  set m : Fin d → ℕ := fun i => ⌈(x i + R) * 2 / W⌉₊ with hmdef
  have hm_apply : ∀ i, m i = ⌈(x i + R) * 2 / W⌉₊ := fun i => rfl
  have key : ∀ (i : Fin d) (j : Fin d → Fin N),
      x ∈ coverBox R W (fun i => (j i : ℕ)) →
      (j i : ℕ) ≤ m i ∧ m i ≤ (j i : ℕ) + 2 := by
    intro i j hx
    have h := (mem_coverBox.mp hx) i
    have hcoef : coverCoef R W (fun i => (j i : ℕ)) i = -R + (j i : ℝ) * (W / 2) := rfl
    rw [hcoef] at h
    have hj0 : (0 : ℝ) ≤ ((j i : ℕ) : ℝ) * (W / 2) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hle : ((j i : ℕ) : ℝ) ≤ (x i + R) * 2 / W := by
      have h1' : (j i : ℝ) * (W / 2) ≤ x i + R := by linarith [h.1]
      rw [le_div_iff₀ hW]
      nlinarith [h1']
    have hge : (x i + R) * 2 / W - 2 ≤ ((j i : ℕ) : ℝ) := by
      have h2' : x i + R - W ≤ (j i : ℝ) * (W / 2) := by linarith [h.2]
      have hmul : (x i + R - W) * 2 / W ≤ ((j i : ℕ) : ℝ) := by
        rw [div_le_iff₀ hW]
        nlinarith [h2']
      have heq : (x i + R - W) * 2 / W = (x i + R) * 2 / W - 2 := by
        field_simp
      linarith [hmul, heq.symm.le]
    have hceil : ((m i : ℕ) : ℝ) < (x i + R) * 2 / W + 1 := by
      rw [hm_apply i]
      have hxR : 0 ≤ x i + R := by linarith [h.1, hj0]
      exact Nat.ceil_lt_add_one (div_nonneg (by linarith : (0:ℝ) ≤ (x i + R) * 2) (le_of_lt hW))
    constructor
    · have : ((j i : ℕ) : ℝ) ≤ ((m i : ℕ) : ℝ) := by
        rw [hm_apply i]
        exact le_trans hle (Nat.le_ceil _)
      exact_mod_cast this
    · have hcast : ((m i : ℕ) : ℝ) < ((((j i : ℕ) + 3 : ℕ)) : ℝ) := by
        push_cast
        linarith
      have : (m i : ℕ) < ((j i : ℕ) + 3) := by exact_mod_cast hcast
      omega
  have hinj : Function.Injective
      (fun (jj : {j : Fin d → Fin N // x ∈ coverBox R W (fun i => (j i : ℕ))}) =>
        fun i : Fin d => (⟨(jj.1 i : ℕ) + 2 - m i, by
          have h := (key i jj.1 jj.2).1
          omega⟩ : Fin 3)) := by
    intro a b hab
    refine Subtype.ext (funext fun i => ?_)
    have h := congrFun hab i
    simp only [Fin.mk.injEq] at h
    have ha := key i a.1 a.2
    have hb := key i b.1 b.2
    have hab' : (a.1 i : ℕ) = (b.1 i : ℕ) := by omega
    exact Fin.ext hab'
  have hcard := Fintype.card_le_of_injective _ hinj
  have h3 : Nat.card {j : Fin d → Fin N // x ∈ coverBox R W (fun i => (j i : ℕ))}
      = Fintype.card {j : Fin d → Fin N // x ∈ coverBox R W (fun i => (j i : ℕ))} :=
    Nat.card_eq_fintype_card
  rw [h3]
  rwa [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard

/-- Axis-parallel boxes are closed. -/
lemma isClosed_box {a b : Fin d → ℝ} : IsClosed (box a b : Set ℝᵈ) := by
  have h : (box a b : Set ℝᵈ) = ⋂ i : Fin d, ({x : ℝᵈ | a i ≤ x i} ∩ {x : ℝᵈ | x i ≤ b i}) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, mem_box]
  rw [h]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
  · exact isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i) continuous_const

lemma isClosed_coverBox (R W : ℝ) (j : Fin d → ℕ) :
    IsClosed (coverBox R W j : Set ℝᵈ) := isClosed_box

/-- `Y_k` is closed (it is a finite union of closed boxes). -/
lemma isClosed_yCover (R W : ℝ) (N : ℕ) (Y A : Set ℝᵈ) :
    IsClosed (yCover R W N Y A) := by
  have h : yCover R W N Y A =
      ⋃ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
        (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
        coverBox R W (fun i => (j i : ℕ)) := by
    ext x
    rw [yCover, Set.mem_setOf_eq, Set.mem_iUnion₂]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, hx⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, (Finset.mem_filter.mp hj).2, hx⟩
  rw [h]
  exact isClosed_biUnion_finset fun j _ => isClosed_coverBox R W (fun i => (j i : ℕ))

/-- **Counting estimate for the cube cover.**  The sum, over the cubes of the width-`W` grid
that meet `Y ∩ A`, of the one-dimensional measure of their intersections with a unit-speed
segment is at most `3^d` times the measure of the intersection of the whole union `Y_k` with
that segment.  This is the step `∑_{𝓠 ∈ 𝓢_{𝕐,k}} |𝓠 ∩ ℓ| ≲ |𝕐_k ∩ ℓ|` of §6.1. -/
lemma sum_volume_coverBox_le (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) (p v : ℝᵈ)
    {L : ℝ} :
    (∑ j ∈ (Finset.univ.filter
        (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      volume ((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ)) ∩ Set.Icc 0 L))
      ≤ (3 ^ d : ℝ≥0∞) *
        volume ((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A ∩ Set.Icc 0 L) := by
  classical
  have hcont : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmeasQ : ∀ j : Fin d → Fin N,
      MeasurableSet ((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ)) ∩
        Set.Icc 0 L) := by
    intro j
    refine (MeasurableSet.preimage ?_ hcont.measurable).inter measurableSet_Icc
    exact (isClosed_box (a := coverCoef R W (fun i => (j i : ℕ)))
      (b := fun i => coverCoef R W (fun i => (j i : ℕ)) i + W)).measurableSet
  have hmeasY : MeasurableSet ((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A
      ∩ Set.Icc 0 L) :=
    (MeasurableSet.preimage (isClosed_yCover R W N Y A).measurableSet hcont.measurable).inter
      measurableSet_Icc
  have hmemQ : ∀ (j : Fin d → Fin N), (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty
      → coverBox R W (fun i => (j i : ℕ)) ⊆ yCover R W N Y A :=
    fun j hj x hx => ⟨j, hj, hx⟩
  -- the pointwise counting bound
  have hpoint : ∀ t : ℝ,
      (∑ j ∈ (Finset.univ.filter
          (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
        (((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ))
          ∩ Set.Icc 0 L).indicator (fun _ => 1) t))
      ≤ (3 ^ d : ℝ≥0∞) * (((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A
          ∩ Set.Icc 0 L).indicator (fun _ => 1) t) := by
    intro t
    by_cases ht : t ∈ (fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A ∩ Set.Icc 0 L
    · rw [Set.indicator_of_mem ht (fun _ => (1:ℝ≥0∞)), mul_one]
      -- each summand is `1` exactly when `γ t` lies in the cube
      have hg : ∀ j : Fin d → Fin N,
          (((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ))
            ∩ Set.Icc 0 L).indicator (fun _ => 1) t)
          = (if p + t • v ∈ coverBox R W (fun i => (j i : ℕ)) then (1:ℝ≥0∞) else 0) := by
        intro j
        by_cases hj : p + t • v ∈ coverBox R W (fun i => (j i : ℕ))
        · rw [if_pos hj]
          exact Set.indicator_of_mem (⟨hj, ht.2⟩ : t ∈ (fun t : ℝ => p + t • v) ⁻¹'
            coverBox R W (fun i => (j i : ℕ)) ∩ Set.Icc 0 L) (fun _ => (1:ℝ≥0∞))
        · rw [if_neg hj]
          exact Set.indicator_of_notMem (fun hmem => hj hmem.1) (fun _ => (1:ℝ≥0∞))
      rw [Finset.sum_congr rfl (fun j _ => hg j)]
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcard : ((Finset.univ.filter (fun j : Fin d → Fin N =>
              (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
              (fun j : Fin d → Fin N =>
                p + t • v ∈ coverBox R W (fun i => (j i : ℕ)))).card ≤ 3 ^ d := by
        refine le_trans (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.subset_univ _))) ?_
        have h4 : Finset.card (Finset.filter (fun j : Fin d → Fin N =>
              p + t • v ∈ coverBox R W (fun i => (j i : ℕ))) Finset.univ) ≤ 3 ^ d := by
          rw [← Fintype.card_subtype]
          have h5 := card_coverBox_le R W hW N (p + t • v)
          rwa [Nat.card_eq_fintype_card] at h5
        exact h4
      exact_mod_cast hcard
    · rw [Set.indicator_of_notMem ht (fun _ => (1:ℝ≥0∞)), mul_zero]
      refine le_of_eq (Finset.sum_eq_zero fun j hj => ?_)
      rw [Finset.mem_filter] at hj
      exact Set.indicator_of_notMem (fun hmem => ht ⟨hmemQ j hj.2 hmem.1, hmem.2⟩) _
  have hmeas1 : ∀ j : Fin d → Fin N,
      Measurable (((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ))
        ∩ Set.Icc 0 L).indicator (fun _ => (1 : ℝ≥0∞))) :=
    fun j => measurable_const.indicator (hmeasQ j)
  calc (∑ j ∈ (Finset.univ.filter
        (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      volume ((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ)) ∩ Set.Icc 0 L))
      = ∑ j ∈ (Finset.univ.filter
          (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          ∫⁻ t, (((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ))
            ∩ Set.Icc 0 L).indicator (fun _ => 1) t) :=
        Finset.sum_congr rfl fun j _ => (lintegral_indicator_one (hmeasQ j)).symm
    _ = ∫⁻ t, ∑ j ∈ (Finset.univ.filter
          (fun j : Fin d → Fin N => (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          (((fun t : ℝ => p + t • v) ⁻¹' coverBox R W (fun i => (j i : ℕ))
            ∩ Set.Icc 0 L).indicator (fun _ => 1) t) :=
        (MeasureTheory.lintegral_finsetSum _ (fun j _ => hmeas1 j)).symm
    _ ≤ ∫⁻ t, (3 ^ d : ℝ≥0∞) * (((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A
          ∩ Set.Icc 0 L).indicator (fun _ => 1) t) := lintegral_mono hpoint
    _ = (3 ^ d : ℝ≥0∞) * ∫⁻ t, (((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A
          ∩ Set.Icc 0 L).indicator (fun _ => 1) t) :=
        MeasureTheory.lintegral_const_mul _ (measurable_const.indicator hmeasY)
    _ = (3 ^ d : ℝ≥0∞) * volume ((fun t : ℝ => p + t • v) ⁻¹' yCover R W N Y A
          ∩ Set.Icc 0 L) := by
        congr 1
        exact lintegral_indicator_one hmeasY

end Submission.FUP
