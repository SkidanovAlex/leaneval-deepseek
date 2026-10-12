import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.sum_integral_ucell_eq_integral_iUnion`

The sum of the integrals of the Coulomb integrand `q ↦ cos (2π⟪q,z⟫) / ‖q‖²` over the closed
unit cells `ucell n`, `n ∈ T` (all `n ≠ 0`), equals the integral over their union:

`Σ_{n∈T} ∫_{q ∈ ucell n} … = ∫_{q ∈ ⋃_{n∈T} ucell n} …`.

## Proof

The closed cells of distinct lattice points are *not* disjoint: `ucell n ∩ ucell m` consists of
the common faces, on which some coordinate equals a half integer, so the intersection is
contained in a coordinate hyperplane and hence is null (`volume_coord_eq_zero`).  Therefore the
cells are pairwise a.e. disjoint (`aedisjoint_ucell`), and the set integral is *finitely*
additive along a.e. disjoint unions — this is assembled in `integral_biUnion_finset_of_aedisjoint`
by induction on the `Finset` using `setIntegral_union₀`; Mathlib itself only provides the
literally-disjoint version `MeasureTheory.integral_biUnion_finset`.

The integrand is integrable on every non-zero cell because such a cell stays at distance `≥ 1/2`
from the origin (`half_le_norm_of_mem_ucell`), so that the integrand is bounded by `4` there
(`integrableOn_cos_div_normSq`).  The hypothesis `n ≠ 0` is essential: the integrand has a
non-integrable singularity at the origin, which lies in `ucell 0`.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-- A coordinate hyperplane of `E3` is a null set. -/
private lemma volume_coord_eq_zero (i : Fin 3) (c : ℝ) :
    volume {q : E3 | q.ofLp i = c} = 0 := by
  have hs : MeasurableSet (Set.pi Set.univ
      (fun j : Fin 3 => if j = i then ({c} : Set ℝ) else Set.univ)) :=
    MeasurableSet.pi Set.countable_univ (fun j _ => by by_cases h : j = i <;> simp [h])
  have hpre : {q : E3 | q.ofLp i = c} = WithLp.ofLp ⁻¹'
      (Set.pi Set.univ (fun j : Fin 3 => if j = i then ({c} : Set ℝ) else Set.univ)) := by
    ext q
    simp [Set.mem_pi]
  have hmp := PiLp.volume_preserving_ofLp (Fin 3)
  rw [hpre, ← MeasureTheory.Measure.map_apply hmp.measurable hs, hmp.map_eq,
    MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The intersection of the closed cells of two distinct lattice points is contained in a
coordinate hyperplane: on the common face the differing coordinate is a half integer. -/
private lemma inter_ucell_subset_hyperplane {n m : Fin 3 → ℤ} (h : n ≠ m) :
    ∃ (i : Fin 3) (c : ℝ), ucell n ∩ ucell m ⊆ {q : E3 | q.ofLp i = c} := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ m i := by
    by_contra hc
    exact h (funext fun i => not_not.mp (not_exists.mp hc i))
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · refine ⟨i, (n i : ℝ) + 1 / 2, ?_⟩
    intro q hq
    have h1 : q.ofLp i ≤ (n i : ℝ) + 1 / 2 := by
      have := (abs_le.mp (hq.1 i)).2; linarith
    have h2 : (m i : ℝ) - 1 / 2 ≤ q.ofLp i := by
      have := (abs_le.mp (hq.2 i)).1; linarith
    have h3 : (n i : ℝ) + 1 ≤ (m i : ℝ) := by
      have : n i + 1 ≤ m i := Int.add_one_le_iff.mpr hlt
      exact_mod_cast this
    show q.ofLp i = (n i : ℝ) + 1 / 2
    linarith
  · refine ⟨i, (m i : ℝ) + 1 / 2, ?_⟩
    intro q hq
    have h1 : q.ofLp i ≤ (m i : ℝ) + 1 / 2 := by
      have := (abs_le.mp (hq.2 i)).2; linarith
    have h2 : (n i : ℝ) - 1 / 2 ≤ q.ofLp i := by
      have := (abs_le.mp (hq.1 i)).1; linarith
    have h3 : (m i : ℝ) + 1 ≤ (n i : ℝ) := by
      have : m i + 1 ≤ n i := Int.add_one_le_iff.mpr hlt
      exact_mod_cast this
    show q.ofLp i = (m i : ℝ) + 1 / 2
    linarith

/-- The closed cells of two distinct lattice points are a.e. disjoint. -/
private lemma aedisjoint_ucell {n m : Fin 3 → ℤ} (h : n ≠ m) :
    AEDisjoint volume (ucell n) (ucell m) := by
  obtain ⟨i, c, hsub⟩ := inter_ucell_subset_hyperplane h
  rw [MeasureTheory.AEDisjoint]
  exact measure_mono_null hsub (volume_coord_eq_zero i c)

/-- Off the origin, the closed cell of a non-zero lattice point stays at distance at least `1/2`
from the origin. -/
private lemma half_le_norm_of_mem_ucell {n : Fin 3 → ℤ} {q : E3} (hq : q ∈ ucell n)
    (hn : n ≠ 0) : (1 / 2 : ℝ) ≤ ‖q‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hc
    exact hn (funext fun i => not_not.mp (not_exists.mp hc i))
  have hi1 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have hq1 : q.ofLp i - (n i : ℝ) ≤ 1 / 2 := (abs_le.mp (hq i)).2
  have hq2 : -(1 / 2) ≤ q.ofLp i - (n i : ℝ) := (abs_le.mp (hq i)).1
  have h4 : |((n i : ℤ) : ℝ)| ≤ |q.ofLp i| + |((n i : ℤ) : ℝ) - q.ofLp i| := by
    have h := abs_add_le (q.ofLp i) (((n i : ℤ) : ℝ) - q.ofLp i)
    rwa [show q.ofLp i + (((n i : ℤ) : ℝ) - q.ofLp i) = ((n i : ℤ) : ℝ) from by ring] at h
  have h5 : |((n i : ℤ) : ℝ) - q.ofLp i| ≤ 1 / 2 := by
    rw [abs_sub_comm]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : |q.ofLp i| ≤ ‖q‖ := by
    have := PiLp.norm_apply_le q i
    simpa [Real.norm_eq_abs] using this
  linarith

/-- The Coulomb integrand is integrable on the cell of a non-zero lattice point (where it is
bounded by `4`). -/
private lemma integrableOn_cos_div_normSq {n : Fin 3 → ℤ} (hn : n ≠ 0) (z : E3) :
    IntegrableOn (fun q : E3 => Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2) (ucell n)
      volume := by
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ 4 ?_
  · rw [volume_ucell]; norm_num
  · refine ContinuousOn.aestronglyMeasurable ?_ (ucell_measurableSet n)
    refine ContinuousOn.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro q hq
      have h := half_le_norm_of_mem_ucell hq hn
      have hqne : q ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h; norm_num at h
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hqne)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict (ucell_measurableSet n)] with q hq
    have hqn : (1 / 2 : ℝ) ≤ ‖q‖ := half_le_norm_of_mem_ucell hq hn
    have hcos : |Real.cos (2 * Real.pi * inner ℝ q z)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hq2 : (1 / 4 : ℝ) ≤ ‖q‖ ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖q‖ ^ 2)]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖q‖ ^ 2)]
    linarith

/-- Finite additivity of the set integral along an a.e.-disjoint finite family of measurable
sets.  (Mathlib's `MeasureTheory.integral_biUnion_finset` assumes literal disjointness.) -/
private lemma integral_biUnion_finset_of_aedisjoint {ι X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (T : Finset ι) {s : ι → Set X}
    (hmeas : ∀ i ∈ T, MeasurableSet (s i))
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → AEDisjoint μ (s i) (s j))
    (hint : ∀ i ∈ T, IntegrableOn f (s i) μ) :
    ∫ x in (⋃ i ∈ T, s i), f x ∂μ = ∑ i ∈ T, ∫ x in s i, f x ∂μ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha IH =>
    have hmeasT : ∀ i ∈ T, MeasurableSet (s i) := fun i hi => hmeas i (Finset.mem_insert_of_mem hi)
    have hdisjT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → AEDisjoint μ (s i) (s j) :=
      fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hintT : ∀ i ∈ T, IntegrableOn f (s i) μ := fun i hi => hint i (Finset.mem_insert_of_mem hi)
    have hdisj_a : AEDisjoint μ (s a) (⋃ i ∈ T, s i) := by
      rw [AEDisjoint]
      have hset : s a ∩ (⋃ i ∈ T, s i) = ⋃ i ∈ T, (s a ∩ s i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion]
        constructor
        · rintro ⟨hxa, i, hi, hxi⟩; exact ⟨i, hi, hxa, hxi⟩
        · rintro ⟨i, hi, hxa, hxi⟩; exact ⟨hxa, i, hi, hxi⟩
      rw [hset]
      have hle : μ (⋃ i ∈ T, (s a ∩ s i)) ≤ ∑ i ∈ T, μ (s a ∩ s i) :=
        MeasureTheory.measure_biUnion_finset_le T (fun i => s a ∩ s i)
      have hzero : ∑ i ∈ T, μ (s a ∩ s i) = 0 :=
        Finset.sum_eq_zero fun i hi =>
          hdisj a (Finset.mem_insert_self a T) i (Finset.mem_insert_of_mem hi)
            (by rintro rfl; exact ha hi)
      rw [hzero] at hle
      exact le_antisymm hle bot_le
    have hIntUnion : IntegrableOn f (⋃ i ∈ T, s i) μ :=
      (integrableOn_finset_iUnion (s := T) (t := s)).2 hintT
    rw [Finset.set_biUnion_insert]
    rw [MeasureTheory.setIntegral_union₀ hdisj_a
        (Finset.measurableSet_biUnion T hmeasT).nullMeasurableSet
        (hint a (Finset.mem_insert_self a T)) hIntUnion,
      Finset.sum_insert ha, ← IH hmeasT hdisjT hintT]

theorem sum_integral_ucell_eq_integral_iUnion (T : Finset (Fin 3 → ℤ))
    (z : EuclideanSpace ℝ (Fin 3)) (hne : ∀ n ∈ T, n ≠ 0) :
    (∑ n ∈ T, ∫ q in Work.BoseRowsL.LatticeCoulomb.ucell n,
        Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2)
      = ∫ q in (⋃ n ∈ T, Work.BoseRowsL.LatticeCoulomb.ucell n),
          Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 := by
  refine (integral_biUnion_finset_of_aedisjoint
    (f := fun q : E3 => Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2) T
    (fun n _ => ucell_measurableSet n) ?_ ?_).symm
  · intro n _ m _ hnm
    exact aedisjoint_ucell hnm
  · intro n hn
    exact integrableOn_cos_div_normSq (hne n hn) z

end Work.BoseRowsL.LatticeCoulomb
