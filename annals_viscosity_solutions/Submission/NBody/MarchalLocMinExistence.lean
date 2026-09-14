import Submission.NBody.MarchalCollPartition

/-!
# Uniformising the collision set: an interval where all collisions involve a fixed cluster

The geometry of the Marchal chapter (F1), third layer.  Ferrario--Terracini's `propo:isolated`
starts from the following purely topological fact: *if a continuous curve has a collision, then
there is a time interval in which every collision makes a fixed cluster `k` (of at least two
bodies) collide entirely*.  This is Baire's theorem applied to the closed set `S` of collision
times, covered by the finitely many closed sets `{t : all of k collide at t}`.

The content used later is: let `F = I_k ∘ γ` be the inertia of that cluster.  If `F t > 0` then
not all of `k` collide at `t`, so by the property `t ∉ S`: the configuration is collision free,
the curve is a genuine solution at `t`, and the Lagrange--Jacobi identity for `I_k` applies.
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

/-- The set of times in `[a,b]` at which the curve `γ` has a collision. -/
def collisionSet (γ : ℝ → EN E N) (a b : ℝ) : Set ℝ :=
  {t | t ∈ Icc a b ∧ ¬ WithoutCollisions (γ t)}

/-- **Colliding configurations form a closed set.** -/
lemma isClosed_collisionConfigs :
    IsClosed {x : EN E N | ¬ WithoutCollisions x} := by
  have hset : {x : EN E N | ¬ WithoutCollisions x}
      = ⋃ p : Fin N × Fin N, {x : EN E N | p.1 ≠ p.2 ∧ x p.1 = x p.2} := by
    ext x
    constructor
    · intro hx
      simp only [WithoutCollisions, not_forall] at hx
      push_neg at hx
      obtain ⟨i, j, hij, heq⟩ := hx
      have h2 : x i = x j := by
        have h := heq
        rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at h
        exact h
      exact Set.mem_iUnion.mpr ⟨(i, j), hij, h2⟩
    · intro hx hnc
      obtain ⟨p, hp1, hp2⟩ := Set.mem_iUnion.mp hx
      exact (hnc p.1 p.2 hp1) (by rw [r_eq_norm_sub, hp2, sub_self, norm_zero])
  rw [hset]
  refine isClosed_iUnion_of_finite fun p => ?_
  by_cases hp : p.1 = p.2
  · have h0 : {x : EN E N | p.1 ≠ p.2 ∧ x p.1 = x p.2} = ∅ := by
      ext x; simp [hp]
    rw [h0]; exact isClosed_empty
  · have h0 : {x : EN E N | p.1 ≠ p.2 ∧ x p.1 = x p.2}
        = {x : EN E N | x p.1 = x p.2} := by
      ext x; simp [hp]
    rw [h0]
    exact isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin N => E) p.1)
      (PiLp.continuous_apply 2 (fun _ : Fin N => E) p.2)

lemma isClosed_collisionSet {γ : ℝ → EN E N} {a b : ℝ} (hcont : ContinuousOn γ (Icc a b)) :
    IsClosed (collisionSet γ a b) :=
  ContinuousOn.preimage_isClosed_of_isClosed hcont isClosed_Icc isClosed_collisionConfigs

/-- **Baire's theorem for a closed subset of `ℝ`.**  If countably many closed sets cover a closed
nonempty subset of `ℝ`, then one of them contains a whole relative neighbourhood of a point of the
set. -/
lemma exists_interval_subset_of_isClosed_cover {S : Set ℝ} (hS : IsClosed S) (hSne : S.Nonempty)
    {ι : Type*} [Countable ι] {f : ι → Set ℝ} (hcl : ∀ i, IsClosed (f i)) (hcov : S ⊆ ⋃ i, f i) :
    ∃ i, ∃ t ∈ S, ∃ ε > 0, ∀ s ∈ S, |s - t| < ε → s ∈ f i := by
  classical
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace S :=
    hS.isCompletelyPseudoMetrizableSpace
  haveI : BaireSpace S := inferInstance
  haveI : Nonempty S := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  have hcl' : ∀ i, IsClosed ((Subtype.val ⁻¹' f i : Set S)) :=
    fun i => (hcl i).preimage continuous_subtype_val
  have hcov' : (⋃ i, (Subtype.val ⁻¹' f i : Set S)) = Set.univ := by
    ext x
    refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov x.property)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hcl' hcov'
  obtain ⟨x, hx⟩ := hi
  have hx' : (Subtype.val ⁻¹' f i : Set S) ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  rw [nhds_induced Subtype.val x] at hx'
  obtain ⟨U, hU, hUsub⟩ := Filter.mem_comap.mp hx'
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨i, x.val, x.property, ε, hεpos, fun s hs hlt => ?_⟩
  have hsU : s ∈ U := by
    refine hε ?_
    rw [Metric.mem_ball, Real.dist_eq]
    exact hlt
  exact hUsub (show (⟨s, hs⟩ : S) ∈ Subtype.val ⁻¹' U from hsU)

/-- The times at which all the bodies of `k` collide. -/
def allCollSet (γ : ℝ → EN E N) (k : Finset (Fin N)) : Set ℝ :=
  {t | ∀ i ∈ k, ∀ j ∈ k, γ t i = γ t j}

lemma isClosed_allCollSet {γ : ℝ → EN E N} {a b : ℝ} (hcont : ContinuousOn γ (Icc a b))
    (k : Finset (Fin N)) : IsClosed (Icc a b ∩ allCollSet γ k) := by
  have hset : Icc a b ∩ allCollSet γ k
      = Icc a b ∩ ⋂ i, ⋂ (_ : i ∈ k), ⋂ j, ⋂ (_ : j ∈ k),
          (Icc a b ∩ γ ⁻¹' {x : EN E N | x i = x j}) := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun hi =>
        Set.mem_iInter.mpr fun j => Set.mem_iInter.mpr fun hj => ⟨h1, h2 i hi j hj⟩⟩
    · intro ht
      refine ⟨ht.1, fun i hi j hj => ?_⟩
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp
        (Set.mem_iInter.mp ht.2 i) hi) j) hj).2
  rw [hset]
  refine isClosed_Icc.inter (isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_iInter fun j => isClosed_iInter fun _ => ?_)
  exact ContinuousOn.preimage_isClosed_of_isClosed hcont isClosed_Icc
    (isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin N => E) i)
      (PiLp.continuous_apply 2 (fun _ : Fin N => E) j))

/-- **An interval on which every collision is a full collision of a fixed cluster.**
If the continuous curve `γ` has a collision in `[c,d] ⊆ (a,b)`, then there are a cluster `k`
(`2 ≤ #k`), a time `t₀ ∈ [c,d]` and `ε > 0` such that every collision time within `ε` of `t₀`
(and inside `[c,d]`) has *all* the bodies of `k` colliding. -/
theorem exists_collision_interval {γ : ℝ → EN E N} {a b c d : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b) (hcont : ContinuousOn γ (Icc a b))
    (hcoll : ∃ t ∈ Icc c d, ¬ WithoutCollisions (γ t)) :
    ∃ k : Finset (Fin N), 2 ≤ k.card ∧ ∃ t₀ ∈ Icc c d, ∃ ε > 0,
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε) ∩ Icc c d,
        (∃ i j : Fin N, i ≠ j ∧ γ t i = γ t j) → ∀ i ∈ k, ∀ j ∈ k, γ t i = γ t j := by
  classical
  have hcont' : ContinuousOn γ (Icc c d) := hcont.mono (Icc_subset_Icc hac.le hdb.le)
  have hS : IsClosed (collisionSet γ c d) := isClosed_collisionSet hcont'
  obtain ⟨t₁, ht₁, hnc₁⟩ := hcoll
  have hSne : (collisionSet γ c d).Nonempty := ⟨t₁, ht₁, hnc₁⟩
  set F : {k : Finset (Fin N) // 2 ≤ k.card} → Set ℝ :=
    fun k => collisionSet γ c d ∩ (Icc c d ∩ allCollSet γ k.1) with hF
  have hFcl : ∀ k, IsClosed (F k) := fun k => hS.inter (isClosed_allCollSet hcont' k.1)
  have hcov : collisionSet γ c d ⊆ ⋃ k, F k := by
    intro t ht
    have hnc : ¬ WithoutCollisions (γ t) := ht.2
    simp only [WithoutCollisions, not_forall] at hnc
    push_neg at hnc
    obtain ⟨i, j, hij, heq⟩ := hnc
    have heq' : γ t i = γ t j := by
      have hh := heq
      rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hh
      exact hh
    have h2 : 2 ≤ (collClass γ t i).card :=
      two_le_card_collClass_of_exists (i := i) (j := j) hij.symm heq'.symm
    refine Set.mem_iUnion.mpr ⟨⟨collClass γ t i, h2⟩, ht, ht.1, ?_⟩
    intro i' hi' j' hj'
    rw [mem_collClass] at hi' hj'
    rw [hi', hj']
  obtain ⟨k, t₀, ht₀, ε, hεpos, hε⟩ :=
    exists_interval_subset_of_isClosed_cover hS hSne hFcl hcov
  refine ⟨k.1, k.2, t₀, ht₀.1, ε, hεpos, fun t ht hcol => ?_⟩
  have htS : t ∈ collisionSet γ c d := by
    refine ⟨ht.2, ?_⟩
    obtain ⟨i, j, hij, heq⟩ := hcol
    intro hnc
    exact (hnc i j hij) (by rw [r_eq_norm_sub, heq, sub_self, norm_zero])
  have hnear : |t - t₀| < ε := by
    rw [abs_lt]
    exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
  exact (hε t htS hnear).2.2

end Submission.NBody
