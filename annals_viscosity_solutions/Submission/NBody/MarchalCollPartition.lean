import Submission.NBody.MarchalCollClass
import Submission.NBody.MarchalMultiEnergy

/-!
# The collision partition at an interior collision time

The geometry of the Marchal chapter (F1), second layer.  At an interior time `t₀` of a continuous
curve `γ` the bodies split into *collision classes* (the equivalence classes of "coincide at `t₀`").
This file packages that partition and the separation estimates needed by the multi-cluster Sundman
analysis (`MarchalMultiBound.exists_multiRelEnergy_bound`).

The one-sided separation is the only form available in the multi-cluster case: two bodies in
*different* collision classes need not stay separated (both classes collapse).

* `collClasses γ t₀` — the distinct collision classes of cardinality `≥ 2`;
* `collUnion γ t₀` — the bodies involved in a collision at `t₀`;
* `exists_separation_of_collClasses` — a common `ν > 0` and neighbourhood on which every pair not
  lying in a *common* collision class is `ν`-separated (hence `ClusterSeparatedWeak k` for every
  class `k`, and the separation of the bodies outside the union);
* `exists_clusterInertia_bound_of_collClasses` — a constant `γ > 0` dominating all the class
  inertias near `t₀` (used as the `hI`/`hγm` interface of `exists_multiCrossWork_bound`).
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The collision classes of cardinality at least two at the time `t₀`.** -/
noncomputable def collClasses (γ : ℝ → EN E N) (t₀ : ℝ) : Finset (Finset (Fin N)) :=
  (Finset.univ.image (fun i => collClass γ t₀ i)).filter (fun k => 2 ≤ k.card)

/-- **The bodies involved in a collision at the time `t₀`.** -/
noncomputable def collUnion (γ : ℝ → EN E N) (t₀ : ℝ) : Finset (Fin N) :=
  (collClasses γ t₀).biUnion id

lemma mem_collClasses {γ : ℝ → EN E N} {t₀ : ℝ} {k : Finset (Fin N)} :
    k ∈ collClasses γ t₀ ↔ ∃ i, k = collClass γ t₀ i ∧ 2 ≤ k.card := by
  classical
  rw [collClasses, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, -, hi⟩, h2⟩
    exact ⟨i, hi.symm, h2⟩
  · rintro ⟨i, rfl, h2⟩
    exact ⟨⟨i, Finset.mem_univ i, rfl⟩, h2⟩

/-- A collision class of cardinality at least two contains a body different from `i`. -/
lemma exists_ne_of_two_le_card_collClass {γ : ℝ → EN E N} {t₀ : ℝ} {i : Fin N}
    (h : 2 ≤ (collClass γ t₀ i).card) : ∃ j ≠ i, γ t₀ j = γ t₀ i := by
  have h1 : 1 < (collClass γ t₀ i).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
  rw [mem_collClass] at ha hb
  by_cases hbi : b = i
  · exact ⟨a, fun hai => hab (hai.trans hbi.symm), ha⟩
  · exact ⟨b, hbi, hb⟩

lemma two_le_card_collClass_of_exists {γ : ℝ → EN E N} {t₀ : ℝ} {i j : Fin N}
    (hij : j ≠ i) (h : γ t₀ j = γ t₀ i) : 2 ≤ (collClass γ t₀ i).card := by
  classical
  have hsub : ({i, j} : Finset (Fin N)) ⊆ collClass γ t₀ i := by
    intro a ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact mem_collClass.mpr rfl
    · exact mem_collClass.mpr h
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hij.symm] at this

/-- Two collision classes which have a common element are equal. -/
lemma collClass_eq_of_collide {γ : ℝ → EN E N} {t₀ : ℝ} {i j : Fin N}
    (h : γ t₀ j = γ t₀ i) : collClass γ t₀ j = collClass γ t₀ i := by
  classical
  refine Finset.ext fun a => ?_
  rw [mem_collClass, mem_collClass]
  exact ⟨fun ha => ha.trans h, fun ha => ha.trans h.symm⟩

lemma collClasses_card {γ : ℝ → EN E N} {t₀ : ℝ} {k : Finset (Fin N)}
    (hk : k ∈ collClasses γ t₀) : 2 ≤ k.card := ((mem_collClasses.mp hk).choose_spec).2

lemma collClasses_nonempty {γ : ℝ → EN E N} {t₀ : ℝ} {k : Finset (Fin N)}
    (hk : k ∈ collClasses γ t₀) : k.Nonempty :=
  Finset.card_pos.mp (by have := collClasses_card hk; omega)

/-- **The collision classes are pairwise disjoint.** -/
lemma disjoint_collClasses {γ : ℝ → EN E N} {t₀ : ℝ} :
    ∀ k ∈ collClasses γ t₀, ∀ k' ∈ collClasses γ t₀, k ≠ k' → Disjoint k k' := by
  classical
  intro k hk k' hk' hne
  obtain ⟨i, rfl, -⟩ := mem_collClasses.mp hk
  obtain ⟨i', rfl, -⟩ := mem_collClasses.mp hk'
  refine Finset.disjoint_left.mpr fun a ha ha' => ?_
  rw [mem_collClass] at ha ha'
  exact hne ((collClass_eq_of_collide ha).symm.trans (collClass_eq_of_collide ha'))

/-- **Membership in the collision union.** -/
lemma mem_collUnion {γ : ℝ → EN E N} {t₀ : ℝ} {i : Fin N} :
    i ∈ collUnion γ t₀ ↔ ∃ j ≠ i, γ t₀ j = γ t₀ i := by
  classical
  rw [collUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨k, hk, hik⟩
    obtain ⟨i', rfl, h2⟩ := mem_collClasses.mp hk
    obtain ⟨j, hji, hjeq⟩ := exists_ne_of_two_le_card_collClass (γ := γ) h2
    simp only [id] at hik
    rw [mem_collClass] at hik
    by_cases hc : j = i
    · exact ⟨i', fun h => hji (hc.trans h.symm), by rw [← hjeq, hc]⟩
    · exact ⟨j, hc, by rw [hjeq, ← hik]⟩
  · rintro ⟨j, hji, hj⟩
    exact ⟨collClass γ t₀ i, mem_collClasses.mpr ⟨i, rfl, two_le_card_collClass_of_exists hji hj⟩,
      mem_collClass.mpr rfl⟩

/-- The bodies which do not collide with anybody at `t₀`. -/
lemma not_mem_collUnion {γ : ℝ → EN E N} {t₀ : ℝ} {i : Fin N} :
    i ∉ collUnion γ t₀ ↔ ∀ j, j ≠ i → γ t₀ j ≠ γ t₀ i := by
  rw [mem_collUnion]
  constructor
  · intro h j hj hji
    exact h ⟨j, hj, hji⟩
  · rintro h ⟨j, hj, hji⟩
    exact h j hj hji

/-- The pairs which do not lie in a common collision class. -/
noncomputable def sepPairs (γ : ℝ → EN E N) (t₀ : ℝ) : Finset (Fin N × Fin N) :=
  (Finset.univ.product Finset.univ).filter
    (fun p => p.1 ≠ p.2 ∧ ¬ ∃ k ∈ collClasses γ t₀, p.1 ∈ k ∧ p.2 ∈ k)

lemma mem_sepPairs {γ : ℝ → EN E N} {t₀ : ℝ} {i j : Fin N} :
    (i, j) ∈ sepPairs γ t₀ ↔ i ≠ j ∧ ¬ ∃ k ∈ collClasses γ t₀, i ∈ k ∧ j ∈ k := by
  classical
  constructor
  · intro h
    obtain ⟨-, h2, h3⟩ := Finset.mem_filter.mp h
    exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h1, h2⟩

/-- Pairs with one body in a collision class and the other outside it do not lie in a common
collision class. -/
lemma mem_sepPairs_of_mem_of_notMem {γ : ℝ → EN E N} {t₀ : ℝ} {i j : Fin N} {k : Finset (Fin N)}
    (hk : k ∈ collClasses γ t₀) (hi : i ∈ k) (hj : j ∉ k) : (i, j) ∈ sepPairs γ t₀ := by
  classical
  obtain ⟨i₀, hk_eq, -⟩ := mem_collClasses.mp hk
  refine mem_sepPairs.mpr ⟨?_, ?_⟩
  · rintro rfl
    exact hj hi
  · rintro ⟨k', hk', hik', hjk'⟩
    obtain ⟨j₀, hk'_eq, -⟩ := mem_collClasses.mp hk'
    rw [hk_eq] at hi
    rw [hk'_eq] at hik'
    rw [mem_collClass] at hi hik'
    have heq : collClass γ t₀ i₀ = collClass γ t₀ j₀ :=
      (collClass_eq_of_collide (i := i₀) (j := j₀) (by rw [← hi, hik'])).symm
    refine hj ?_
    rw [hk_eq, heq, ← hk'_eq]
    exact hjk'

/-- Pairs of bodies outside the collision union do not lie in a common collision class. -/
lemma mem_sepPairs_of_notMem_collUnion {γ : ℝ → EN E N} {t₀ : ℝ} {i j : Fin N}
    (hi : i ∉ collUnion γ t₀) (hj : j ∉ collUnion γ t₀) (hij : i ≠ j) :
    (i, j) ∈ sepPairs γ t₀ := by
  classical
  refine mem_sepPairs.mpr ⟨hij, ?_⟩
  rintro ⟨k, hk, hik, -⟩
  exact hi (Finset.mem_biUnion.mpr ⟨k, hk, hik⟩)

/-- **The main separation theorem.**  Near an interior time `t₀` of a continuous curve, every pair
of bodies which does not lie in a common collision class stays `ν`-separated. -/
theorem exists_separation_of_sepPairs {γ : ℝ → EN E N} {a b t₀ : ℝ}
    (hcont : ContinuousOn γ (Icc a b)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ ν > 0, ∃ ε > 0, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      ∀ p ∈ sepPairs γ t₀, ν ≤ r (γ t) p.1 p.2 := by
  classical
  have hpos : ∀ p ∈ sepPairs γ t₀, 0 < r (γ t₀) p.1 p.2 := by
    intro p hp
    obtain ⟨hne, hnc⟩ := mem_sepPairs.mp hp
    rw [r_eq_norm_sub]
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hnc ?_)
    exact ⟨collClass γ t₀ p.1,
      mem_collClasses.mpr ⟨p.1, rfl,
        two_le_card_collClass_of_exists (i := p.1) (j := p.2) hne.symm h.symm⟩,
      mem_collClass.mpr rfl, mem_collClass.mpr h.symm⟩
  obtain ⟨ν, hνpos, hν⟩ : ∃ ν > 0, ∀ p ∈ sepPairs γ t₀, ν ≤ r (γ t₀) p.1 p.2 := by
    by_cases hSne : (sepPairs γ t₀).Nonempty
    · obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image (sepPairs γ t₀) (fun p => r (γ t₀) p.1 p.2) hSne
      exact ⟨r (γ t₀) p.1 p.2, hpos p hp, fun q hq => hpmin q hq⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hSne⟩
  have hcontAt : ContinuousAt γ t₀ := hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hcontp : ∀ p : Fin N × Fin N, ContinuousAt (fun t => r (γ t) p.1 p.2) t₀ := by
    intro p
    have h1 : ContinuousAt (fun t : ℝ => γ t p.1) t₀ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.1).continuousAt).comp hcontAt
    have h2 : ContinuousAt (fun t : ℝ => γ t p.2) t₀ :=
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) p.2).continuousAt).comp hcontAt
    have hfun : (fun t : ℝ => r (γ t) p.1 p.2) = fun t : ℝ => ‖γ t p.1 - γ t p.2‖ := by
      funext t; rw [r_eq_norm_sub]
    rw [hfun]
    exact (h1.sub h2).norm
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ p ∈ sepPairs γ t₀, ν / 2 ≤ r (γ t) p.1 p.2 := by
    refine (Finset.eventually_all (sepPairs γ t₀)).mpr fun p hp => ?_
    filter_upwards [(hcontp p).eventually (eventually_ge_nhds
      (show ν / 2 < r (γ t₀) p.1 p.2 from by linarith [hν p hp]))] with t ht
    exact ht
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ν / 2, by linarith, ε, hεpos, ?_⟩
  intro t ht p hp
  have hball : t ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact hε t hball p hp

/-- **The one-sided separation of the collision classes and of the outside bodies.** -/
theorem exists_separation_of_collClasses {γ : ℝ → EN E N} {a b t₀ : ℝ}
    (hcont : ContinuousOn γ (Icc a b)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ ν > 0, ∃ ε > 0, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      (∀ k ∈ collClasses γ t₀, ClusterSeparatedWeak k (γ t) ν) ∧
      (∀ i ∉ collUnion γ t₀, ∀ j ∉ collUnion γ t₀, i ≠ j → ν ≤ r (γ t) i j) := by
  obtain ⟨ν, hνpos, ε, hεpos, hε⟩ := exists_separation_of_sepPairs (γ := γ) hcont ht₀
  exact ⟨ν, hνpos, ε, hεpos, fun t ht =>
    ⟨fun k hk i hi j hj => hε t ht (i, j) (mem_sepPairs_of_mem_of_notMem hk hi hj),
     fun i hi j hj hij => hε t ht (i, j) (mem_sepPairs_of_notMem_collUnion hi hj hij)⟩⟩

/-- **The class inertias are uniformly small near the collision time.** -/
theorem exists_clusterInertia_bound_of_collClasses {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {γ : ℝ → EN E N} {a b t₀ : ℝ} (hcont : ContinuousOn γ (Icc a b)) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ γc : ℝ, 0 < γc ∧ (∀ p, γc ≤ m p) ∧ ∃ ε > 0, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      ∀ k ∈ collClasses γ t₀, clusterInertia m k (γ t) ≤ γc := by
  classical
  have hcontAt : ContinuousAt γ t₀ := hcont.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have htend : ∀ k ∈ collClasses γ t₀,
      Tendsto (fun t : ℝ => clusterInertia m k (γ t)) (𝓝 t₀) (𝓝 0) := by
    intro k hk
    obtain ⟨i, rfl, -⟩ := mem_collClasses.mp hk
    have hmk : clusterMass m (collClass γ t₀ i) ≠ 0 :=
      ne_of_gt (clusterMass_pos hm ⟨i, mem_collClass_self γ t₀ i⟩)
    exact tendsto_clusterInertia_collClass hmk hcontAt
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin N)) with hem | hne
  · refine ⟨1, one_pos, fun p => absurd (Finset.mem_univ p) (Finset.eq_empty_iff_forall_notMem.mp hem p),
      1, one_pos, ?_⟩
    intro t ht k hk
    exfalso
    have h2 := collClasses_card hk
    have hc : k.card = 0 := by
      have hk0 : k = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a _ =>
        Finset.eq_empty_iff_forall_notMem.mp hem a (Finset.mem_univ a)
      rw [hk0, Finset.card_empty]
    omega
  · set γc : ℝ := Finset.univ.inf' hne m with hγc
    have hγcpos : 0 < γc := by
      rw [hγc]
      exact (Finset.lt_inf'_iff hne).mpr fun p _ => hm p
    have hγcle : ∀ p, γc ≤ m p := fun p => by
      rw [hγc]; exact Finset.inf'_le m (Finset.mem_univ p)
    refine ⟨γc, hγcpos, hγcle, ?_⟩
    have hev : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ collClasses γ t₀, clusterInertia m k (γ t) < γc := by
      refine (Finset.eventually_all (collClasses γ t₀)).mpr fun k hk => ?_
      exact (htend k hk).eventually (isOpen_Iio.mem_nhds hγcpos)
    obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff_ball.mp hev
    refine ⟨ε, hεpos, fun t ht k hk => ?_⟩
    have hball : t ∈ Metric.ball t₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact le_of_lt (hε t hball k hk)

end Submission.NBody
