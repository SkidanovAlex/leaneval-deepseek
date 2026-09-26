import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# The period lattice is separated near a compact set with no lattice periods

Let `Λ = 2πℤ²` be the period lattice of the parameter plane and let `K ⊆ ℝ × ℝ` be
compact.  Assume that `K` contains no two distinct points whose difference lies in `Λ`
(equivalently, `K → (ℝ × ℝ)/Λ` is injective).  Then `K` can be fattened a little without
creating a pair of distinct points whose difference lies in `Λ`:

  `∃ δ > 0, ∀ p q, (∃ p' ∈ K, dist p p' < δ) → (∃ q' ∈ K, dist q q' < δ) →
     p - q ∈ Λ → p = q.`

The proof is the classical compactness argument.  The difference set `A = K - K` is compact
and meets `Λ` only in `0`; a nonzero lattice point therefore has positive `infDist` from `A`, and
since `A` is bounded only finitely many nonzero lattice points can be close to it, so the
infimum is attained and positive.
-/

namespace Work.BoxShrink.PinchOff

open Metric

/-- The difference set `K - K` of a subset of the plane. -/
def diffSet (K : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1 - z.2) '' (K ×ˢ K)

lemma mem_diffSet {K : Set (ℝ × ℝ)} {x : ℝ × ℝ} :
    x ∈ diffSet K ↔ ∃ p ∈ K, ∃ q ∈ K, p - q = x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1, hz.1, z.2, hz.2, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨(p, q), ⟨hp, hq⟩, rfl⟩

lemma isCompact_diffSet {K : Set (ℝ × ℝ)} (hK : IsCompact K) : IsCompact (diffSet K) :=
  (hK.prod hK).image (continuous_fst.sub continuous_snd)

lemma diffSet_nonempty {K : Set (ℝ × ℝ)} (hK : K.Nonempty) : (diffSet K).Nonempty := by
  obtain ⟨p, hp⟩ := hK
  exact ⟨p - p, mem_diffSet.mpr ⟨p, hp, p, hp, rfl⟩⟩

lemma zero_mem_diffSet {K : Set (ℝ × ℝ)} (hK : K.Nonempty) : (0 : ℝ × ℝ) ∈ diffSet K := by
  obtain ⟨p, hp⟩ := hK
  exact mem_diffSet.mpr ⟨p, hp, p, hp, sub_self p⟩

theorem lattice_separated_of_isCompact {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    (hinj : ∀ p ∈ K, ∀ q ∈ K, p - q ∈ Work.TorusCover.lattice → p = q) :
    ∃ δ > 0, ∀ p q : ℝ × ℝ,
      (∃ p' ∈ K, dist p p' < δ) → (∃ q' ∈ K, dist q q' < δ) →
      p - q ∈ Work.TorusCover.lattice → p = q := by
  set A : Set (ℝ × ℝ) := diffSet K with hA
  have hAmem : ∀ x : ℝ × ℝ, x ∈ A ↔ ∃ p ∈ K, ∃ q ∈ K, p - q = x := by
    intro x; rw [hA]; exact mem_diffSet
  have hAcomp : IsCompact A := by rw [hA]; exact isCompact_diffSet hK
  have hAne : A.Nonempty := by rw [hA]; exact diffSet_nonempty hKne
  have hAclosed : IsClosed A := hAcomp.isClosed
  -- `A` meets the lattice only in `0`
  have hAinter : A ∩ (Work.TorusCover.lattice : Set (ℝ × ℝ)) = {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxlat⟩ := hx
      obtain ⟨p, hpK, q, hqK, hpq⟩ := (hAmem x).mp hxA
      rw [Set.mem_singleton_iff]
      have hlat : p - q ∈ Work.TorusCover.lattice := hpq ▸ hxlat
      have hpqeq : p = q := hinj p hpK q hqK hlat
      rw [← hpq, hpqeq, sub_self]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨by rw [hA]; exact zero_mem_diffSet hKne, Work.TorusCover.lattice.zero_mem⟩
  -- a bound for `A`
  obtain ⟨a₀, _, ha₀max⟩ := hAcomp.exists_isMaxOn hAne continuous_norm.continuousOn
  set R : ℝ := ‖a₀‖ with hRdef
  have hR : ∀ a ∈ A, ‖a‖ ≤ R := fun a ha => by rw [hRdef]; exact ha₀max ha
  -- the lattice is closed, being a discrete subgroup
  have hClosedLattice : IsClosed (Work.TorusCover.lattice : Set (ℝ × ℝ)) :=
    letI : DiscreteTopology (Work.TorusCover.lattice) :=
      isDiscrete_iff_discreteTopology.mp Work.TorusCover.isDiscrete_lattice
    AddSubgroup.isClosed_of_discreteTopology (U := Work.TorusCover.lattice)
  -- nonzero lattice points near `A` form a finite set
  set S : Set (ℝ × ℝ) :=
    Metric.closedBall (0 : ℝ × ℝ) (R + 1) ∩ (Work.TorusCover.lattice : Set (ℝ × ℝ)) with hSdef
  have hSfin : S.Finite := by
    rw [hSdef]
    exact Metric.finite_isBounded_inter_isClosed Work.TorusCover.isDiscrete_lattice
      (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := R + 1)) hClosedLattice
  set T : Finset (ℝ × ℝ) := hSfin.toFinset.erase 0 with hTdef
  have hTmem : ∀ w : ℝ × ℝ, w ∈ T ↔ w ≠ 0 ∧ w ∈ S := by
    intro w
    rw [hTdef, Finset.mem_erase, hSfin.mem_toFinset]
  have hTlat : ∀ w ∈ T, w ∈ Work.TorusCover.lattice := by
    intro w hw
    have hwS : w ∈ S := ((hTmem w).mp hw).2
    rw [hSdef] at hwS
    exact hwS.2
  have hTpos : ∀ w ∈ T, 0 < Metric.infDist w A := by
    intro w hw
    have hwne : w ≠ 0 := ((hTmem w).mp hw).1
    have hwlat : w ∈ Work.TorusCover.lattice := hTlat w hw
    have hwnotA : w ∉ A := by
      intro hAw
      have hmem : w ∈ A ∩ (Work.TorusCover.lattice : Set (ℝ × ℝ)) := ⟨hAw, hwlat⟩
      rw [hAinter, Set.mem_singleton_iff] at hmem
      exact hwne hmem
    have hnotcl : w ∉ closure A := by rwa [hAclosed.closure_eq]
    exact (Metric.infDist_pos_iff_notMem_closure hAne).mp hnotcl
  -- far away lattice points are already at distance at least `1`
  have hnotT : ∀ w ∈ Work.TorusCover.lattice, w ≠ 0 → w ∉ T → 1 ≤ Metric.infDist w A := by
    intro w hwlat hwne hwT
    have hwS : w ∉ S := fun hS => hwT ((hTmem w).mpr ⟨hwne, hS⟩)
    have hnorm : R + 1 < ‖w‖ := by
      have hnotball : w ∉ Metric.closedBall (0 : ℝ × ℝ) (R + 1) := by
        intro h; exact hwS (by rw [hSdef]; exact ⟨h, hwlat⟩)
      rw [Metric.mem_closedBall, dist_zero_right] at hnotball
      exact not_le.mp hnotball
    rw [Metric.le_infDist hAne]
    intro a ha
    have haR : ‖a‖ ≤ R := hR a ha
    have h1 : (1 : ℝ) ≤ ‖w‖ - R := by linarith
    calc (1 : ℝ) ≤ ‖w‖ - R := h1
      _ ≤ ‖w‖ - ‖a‖ := by linarith
      _ ≤ dist w a := by rw [dist_eq_norm]; exact norm_sub_norm_le w a
  -- the uniform positive lower bound
  have hinf : ∃ ε > 0, ∀ w ∈ Work.TorusCover.lattice, w ≠ 0 → ε ≤ Metric.infDist w A := by
    by_cases hT : T.Nonempty
    · refine ⟨min 1 (T.inf' hT (fun w => Metric.infDist w A)), lt_min one_pos ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro w hw
        exact hTpos w hw
      · intro w hwlat hwne
        by_cases hwT : w ∈ T
        · exact le_trans (min_le_right _ _)
            (Finset.inf'_le (fun w => Metric.infDist w A) hwT)
        · exact le_trans (min_le_left _ _) (hnotT w hwlat hwne hwT)
    · refine ⟨1, one_pos, ?_⟩
      intro w hwlat hwne
      exact hnotT w hwlat hwne (fun hwT => hT ⟨w, hwT⟩)
  obtain ⟨ε, hεpos, hεbound⟩ := hinf
  refine ⟨ε / 4, by linarith, ?_⟩
  intro p q hp hq hpq
  by_contra hne
  obtain ⟨p', hp'K, hp'd⟩ := hp
  obtain ⟨q', hq'K, hq'd⟩ := hq
  have hwne : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hle : ε ≤ Metric.infDist (p - q) A := hεbound (p - q) hpq hwne
  have hmem : p' - q' ∈ A := (hAmem (p' - q')).mpr ⟨p', hp'K, q', hq'K, rfl⟩
  have hdist : Metric.infDist (p - q) A ≤ dist p p' + dist q q' := by
    calc Metric.infDist (p - q) A ≤ dist (p - q) (p' - q') := Metric.infDist_le_dist_of_mem hmem
      _ = ‖(p - q) - (p' - q')‖ := dist_eq_norm _ _
      _ = ‖(p - p') - (q - q')‖ := by congr 1; abel
      _ ≤ ‖p - p'‖ + ‖q - q'‖ := norm_sub_le _ _
      _ = dist p p' + dist q q' := by rw [dist_eq_norm, dist_eq_norm]
  linarith

end Work.BoxShrink.PinchOff
