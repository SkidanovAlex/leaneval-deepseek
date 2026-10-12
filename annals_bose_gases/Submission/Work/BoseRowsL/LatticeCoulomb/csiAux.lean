import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.csiAux` — cell geometry for `cellSumVsIntegral`

Vocabulary and elementary geometry for the proof of

  `|Σ_{n∈T} ∫_{q∈ucell n} cos(2π⟪q,z⟫)/‖q‖² − ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖²| ≤ 100`

where `ucell n` is the closed unit cube centred at the lattice point `nvec n` and `T` is exactly
the set of non-zero lattice points with `‖nvec n‖ ≤ R`.

The route is *volume-only* (no use of the oscillation of the cosine, and no use of `‖z‖ ≤ 1/2`):
`Σ_{n∈T} ∫_{ucell n} f = ∫_{U} f` with `U = ⋃_{n∈T} ucell n` (the cells are pairwise a.e.
disjoint), and then both symmetric differences `U \ B_R` and `B_R \ U` are *thin*: the first lies
in the shell `R ≤ ‖q‖ ≤ R+1`, the second in the shell `R-1 ≤ ‖q‖ ≤ R` together with the central
cell `ucell 0`.  Since `|f| ≤ ‖q‖⁻²` and `∫_{ball ρ} ‖q‖⁻² = 4πρ` (constant density `4π` per unit
radius), all pieces are bounded by `4π·(something ≤ 7/3)`, well below `100`.

This module contains only the cell geometry; the analytic input `∫_{ball ρ} ‖q‖⁻² = 4πρ` is the
separate module `ballInvNormSq`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- The **open** unit cube centred at the lattice point `nvec n`: the product over the
coordinates of the open intervals `(nᵢ - 1/2, nᵢ + 1/2)`.  Unlike the closed cells `ucell n`,
the open cells of distinct lattice points are *disjoint*. -/
def uopen (n : Fin 3 → ℤ) : Set E3 := {q | ∀ i : Fin 3, |(q.ofLp i) - (n i : ℝ)| < 1 / 2}

lemma uopen_eq_preimage (n : Fin 3 → ℤ) :
    uopen n = WithLp.ofLp ⁻¹' (Set.pi Set.univ
      (fun i : Fin 3 => Set.Ioo ((n i : ℝ) - 1 / 2) ((n i : ℝ) + 1 / 2))) := by
  ext q
  simp only [uopen, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies, Set.mem_Ioo]
  constructor
  · intro h i
    have h' := abs_lt.mp (h i)
    exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  · intro h i
    exact abs_lt.mpr ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

lemma uopen_measurableSet (n : Fin 3 → ℤ) : MeasurableSet (uopen n) := by
  rw [uopen_eq_preimage]
  exact (MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioo)).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

lemma uopen_subset_ucell (n : Fin 3 → ℤ) : uopen n ⊆ ucell n := by
  intro q hq
  simp only [uopen, Set.mem_ofPred_eq] at hq
  simp only [ucell, Set.mem_ofPred_eq]
  intro i
  obtain ⟨h1, h2⟩ := abs_lt.mp (hq i)
  exact abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩

/-- Two distinct closed cells meet only on their common faces; the open cells are disjoint. -/
lemma disjoint_uopen {m n : Fin 3 → ℤ} (h : m ≠ n) : Disjoint (uopen m) (uopen n) := by
  rw [Set.disjoint_left]
  intro q hm hn
  apply h
  funext i
  by_contra hi
  have hm' := (abs_lt.mp (hm i)).2
  have hn' := (abs_lt.mp (hn i)).1
  have hlt : (n i : ℝ) < (m i : ℝ) + 1 := by linarith
  have hlt' : (m i : ℝ) < (n i : ℝ) + 1 := by
    have := (abs_lt.mp (hm i)).1
    have := (abs_lt.mp (hn i)).2
    linarith
  have h1 : n i ≤ m i := Int.lt_add_one_iff.mp (by exact_mod_cast hlt)
  have h2 : m i ≤ n i := Int.lt_add_one_iff.mp (by exact_mod_cast hlt')
  exact hi (le_antisymm h2 h1)

/-- `WithLp.ofLp : E3 → (Fin 3 → ℝ)` is measure preserving. -/
private lemma vol_ofLp_preimage (s : Set (Fin 3 → ℝ)) (hs : MeasurableSet s) :
    volume (WithLp.ofLp ⁻¹' s : Set E3) = volume s := by
  have hmp := PiLp.volume_preserving_ofLp (Fin 3)
  rw [← MeasureTheory.Measure.map_apply hmp.measurable hs, hmp.map_eq]

/-- A coordinate hyperplane of `E3` is null. -/
lemma coordHyperplane_volume_zero (i : Fin 3) (c : ℝ) :
    volume {q : E3 | q.ofLp i = c} = 0 := by
  rw [show {q : E3 | q.ofLp i = c}
      = WithLp.ofLp ⁻¹' {x : Fin 3 → ℝ | x i = c} from rfl,
    vol_ofLp_preimage _ (by measurability)]
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (α := fun _ : Fin 3 => ℝ)
    (μ := fun _ : Fin 3 => volume) i c

/-- The closed cell of `n` differs from the open cell of `n` by its faces, which are null. -/
lemma volume_ucell_sdiff_uopen (n : Fin 3 → ℤ) : volume (ucell n \ uopen n) = 0 := by
  have hsub : ucell n \ uopen n ⊆ ⋃ i : Fin 3,
      ({q : E3 | q.ofLp i = (n i : ℝ) - 1 / 2} ∪ {q : E3 | q.ofLp i = (n i : ℝ) + 1 / 2}) := by
    intro q hq
    simp only [Set.mem_sdiff, ucell, uopen, Set.mem_ofPred_eq] at hq
    push_neg at hq
    obtain ⟨i, hi⟩ := hq.2
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hle : |q.ofLp i - (n i : ℝ)| ≤ 1 / 2 := hq.1 i
    have heq : |q.ofLp i - (n i : ℝ)| = 1 / 2 := le_antisymm hle hi
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1 / 2)).mp heq with h | h
    · exact Or.inr (by show q.ofLp i = (n i : ℝ) + 1 / 2; linarith [h])
    · exact Or.inl (by show q.ofLp i = (n i : ℝ) - 1 / 2; linarith [h])
  refine measure_mono_null hsub (measure_iUnion_null_iff.mpr fun i => ?_)
  exact measure_union_null (coordHyperplane_volume_zero i _) (coordHyperplane_volume_zero i _)

/-- A point of the closed cell of `n` is within distance `1` of `nvec n`. -/
lemma norm_sub_nvec_le_of_mem_ucell {n : Fin 3 → ℤ} {q : E3} (hq : q ∈ ucell n) :
    ‖q - nvec n‖ ≤ 1 := by
  have h1 : ∀ i : Fin 3, ‖(q - nvec n).ofLp i‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    intro i
    have hi : (q - nvec n).ofLp i = q.ofLp i - (n i : ℝ) := by
      rw [PiLp.sub_apply (fun _ : Fin 3 => ℝ), nvec_apply]
    rw [hi, Real.norm_eq_abs]
    exact sq_le_sq.mpr (by simpa using hq i)
  have h2 : ‖q - nvec n‖ ^ 2 ≤ 3 / 4 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    calc ∑ i : Fin 3, ‖(q - nvec n).ofLp i‖ ^ 2
        ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
      _ = 3 / 4 := by simp [Finset.sum_const, Finset.card_univ]; norm_num
  nlinarith [norm_nonneg (q - nvec n), h2]

/-- A point of the closed cell of `n` is within distance `1` of the origin's cell centre plus
one: `‖q‖ ≤ ‖nvec n‖ + 1`. -/
lemma norm_le_of_mem_ucell {n : Fin 3 → ℤ} {q : E3} (hq : q ∈ ucell n) :
    ‖q‖ ≤ ‖nvec n‖ + 1 := by
  calc ‖q‖ = ‖nvec n + (q - nvec n)‖ := by congr 1; abel
    _ ≤ ‖nvec n‖ + ‖q - nvec n‖ := norm_add_le _ _
    _ ≤ ‖nvec n‖ + 1 := by linarith [norm_sub_nvec_le_of_mem_ucell hq]

/-- Off the origin, the closed cell of a non-zero lattice point stays at distance at least `1/2`
from the origin. -/
lemma half_le_norm_of_mem_ucell {n : Fin 3 → ℤ} {q : E3} (hq : q ∈ ucell n) (hn : n ≠ 0) :
    1 / 2 ≤ ‖q‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    have h2 : ((|n i| : ℤ) : ℝ) = |(n i : ℝ)| := by simp
    exact_mod_cast this
  have h3 : |q.ofLp i| ≥ 1 / 2 := by
    have hle : |(n i : ℝ)| ≤ |q.ofLp i| + |q.ofLp i - (n i : ℝ)| := by
      calc |(n i : ℝ)| = |q.ofLp i - (q.ofLp i - (n i : ℝ))| := by ring_nf
        _ ≤ |q.ofLp i| + |q.ofLp i - (n i : ℝ)| := abs_sub _ _
    have h2 : |q.ofLp i - (n i : ℝ)| ≤ 1 / 2 := hq i
    linarith
  have h4 : |q.ofLp i| ≤ ‖q‖ := by
    have := PiLp.norm_apply_le (p := 2) q i
    simpa [Real.norm_eq_abs] using this
  linarith

/-- Every point of `ℝ³` lies in a closed unit cell. -/
lemma exists_mem_ucell (q : E3) : ∃ n : Fin 3 → ℤ, q ∈ ucell n := by
  refine ⟨fun i => ⌊q.ofLp i + 1 / 2⌋, fun i => ?_⟩
  have h1 := Int.floor_le (q.ofLp i + 1 / 2)
  have h2 := Int.lt_floor_add_one (q.ofLp i + 1 / 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two a.e.-equal sets have equal set integrals: the workhorse for replacing the closed cells
`ucell n` by the open cells `uopen n`. -/
lemma ae_eq_of_subset_of_null_sdiff {u v : Set E3} (h : v ⊆ u)
    (h0 : volume (u \ v) = 0) : u =ᵐ[volume] v := by
  have h1 : ∀ᵐ q ∂volume, q ∉ (u \ v) := measure_eq_zero_iff_ae_notMem.mp h0
  filter_upwards [h1] with q hq
  exact propext ⟨fun hu => by_contra fun hv => hq ⟨hu, hv⟩, fun hv => h hv⟩

/-- The union of the closed cells of `T` and the union of the open cells of `T` agree a.e. -/
lemma iUnion_ucell_ae_eq_iUnion_uopen (T : Finset (Fin 3 → ℤ)) :
    (⋃ n ∈ T, ucell n) =ᵐ[volume] (⋃ n ∈ T, uopen n) := by
  refine ae_eq_of_subset_of_null_sdiff ?_ ?_
  · exact Set.iUnion₂_mono fun n _ => uopen_subset_ucell n
  · have hsub : (⋃ n ∈ T, ucell n) \ (⋃ n ∈ T, uopen n) ⊆ ⋃ n ∈ T, (ucell n \ uopen n) := by
      intro q hq
      obtain ⟨hqU, hqnU⟩ := hq
      obtain ⟨n, hnT, hqn⟩ := Set.mem_iUnion₂.mp hqU
      exact Set.mem_iUnion₂.mpr ⟨n, hnT, ⟨hqn, fun hqu =>
        hqnU (Set.mem_iUnion₂.mpr ⟨n, hnT, hqu⟩)⟩⟩
    refine measure_mono_null hsub ?_
    exact (measure_biUnion_null_iff T.countable_toSet).mpr fun n _ => volume_ucell_sdiff_uopen n

/-- **The covering of the ball minus the union of the cells.**  A point of the ball of radius
`R` that is *not* covered by the cells of `T` either has norm at least `R - 1`, or lies in the
central cell `ucell 0`. -/
theorem closedBall_sdiff_cellUnion_subset (R : ℝ) (T : Finset (Fin 3 → ℤ))
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    Metric.closedBall (0 : E3) R \ (⋃ n ∈ T, ucell n) ⊆
      (Metric.closedBall (0 : E3) R \ Metric.ball (0 : E3) (R - 1)) ∪ ucell 0 := by
  intro q hq
  obtain ⟨hqB, hqU⟩ := hq
  have hqBn : ‖q‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_zero_right] at hqB
    exact hqB
  by_cases hsmall : ‖q‖ < R - 1
  · right
    obtain ⟨n, hn⟩ := exists_mem_ucell q
    have hlt : ‖nvec n‖ < R := by
      have hsub := norm_sub_nvec_le_of_mem_ucell hn
      have hsplit : ‖nvec n‖ ≤ ‖nvec n - q‖ + ‖q‖ := by
        calc ‖nvec n‖ = ‖(nvec n - q) + q‖ := by congr 1; abel
          _ ≤ ‖nvec n - q‖ + ‖q‖ := norm_add_le _ _
      have : ‖nvec n - q‖ = ‖q - nvec n‖ := norm_sub_rev _ _
      linarith [hsub, hsmall, hsplit, this]
    by_cases hn0 : n = 0
    · rwa [hn0] at hn
    · exact absurd (Set.mem_iUnion₂.mpr ⟨n, h4 n hn0 hlt.le, hn⟩) hqU
  · left
    refine ⟨hqB, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hsmall

/-- A point of the unit cube in the `ℓ^∞` sense has norm at most `√3/2`. -/
lemma norm_le_sqrt_three_div_two {q : E3} (hq : ∀ i : Fin 3, |q.ofLp i| ≤ (1 : ℝ) / 2) :
    ‖q‖ ≤ Real.sqrt 3 / 2 := by
  have h2 : ‖q‖ ^ 2 ≤ 3 / 4 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
    calc ∑ i : Fin 3, ‖q.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 / 2 : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun i _ => by
            rw [Real.norm_eq_abs]; exact sq_le_sq.mpr (by simpa using hq i))
      _ = 3 / 4 := by simp [Finset.sum_const, Finset.card_univ]; norm_num
  nlinarith [norm_nonneg q, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- The central cell is contained in the ball of radius `√3/2`. -/
lemma ucell_zero_subset_closedBall :
    ucell (0 : Fin 3 → ℤ) ⊆ Metric.closedBall (0 : E3) (Real.sqrt 3 / 2) := by
  intro q hq
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_sqrt_three_div_two fun i => by simpa using hq i

end Work.BoseRowsL.LatticeCoulomb
