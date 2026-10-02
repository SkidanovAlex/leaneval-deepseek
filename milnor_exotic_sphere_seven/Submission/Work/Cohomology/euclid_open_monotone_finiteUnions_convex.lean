import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An open set in `ℝ^N` is an increasing union of finite unions of convex open sets

Every open `U ⊆ EuclideanSpace ℝ (Fin N)` is the union of a monotone sequence `W` of open sets,
each of which is a *finite* union of open convex subsets of `U`.  The proof uses a compact
exhaustion of `U` (the sets `{‖x‖ ≤ k} ∩ {x | ball x (1/(k+1)) ⊆ U}`, which are closed and
bounded, hence compact) and, for each of these compact sets, the covering by finitely many balls
contained in `U`.

This is the point-set-topological input for the assembly of Poincaré duality: it allows one to
write an arbitrary open subset of a coordinate chart as an increasing union of finite unions of
convex coordinate pieces, to which the gluing lemma and the base case can be applied.
-/

open Set Metric

namespace Work.Cohomology

/-- **A compact set in an open subset of `ℝ^N` is covered by finitely many open convex sets
contained in the open set.** -/
theorem isCompact_subset_finset_convex {N : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U) {K : Set (EuclideanSpace ℝ (Fin N))}
    (hKc : IsCompact K) (hKU : K ⊆ U) :
    ∃ s : Finset (Set (EuclideanSpace ℝ (Fin N))),
      (∀ Q ∈ s, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ U) ∧ K ⊆ ⋃ Q ∈ s, Q := by
  have hcov : ∀ x : ↥K, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (x : EuclideanSpace ℝ (Fin N)) ε ⊆ U :=
    fun x => Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU x.2))
  choose ε hεpos hεU using hcov
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun x : ↥K => Metric.ball (x : EuclideanSpace ℝ (Fin N)) (ε x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hεpos ⟨x, hx⟩)⟩)
  refine ⟨t.image (fun x : ↥K => Metric.ball (x : EuclideanSpace ℝ (Fin N)) (ε x)), ?_, ?_⟩
  · intro Q hQ
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hQ
    exact ⟨Metric.isOpen_ball, convex_ball _ _, hεU x⟩
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := by
      simpa only [Set.mem_iUnion] using ht hx
    exact Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image.mpr ⟨y, hyt, rfl⟩, hxy⟩

/-- **An open set in `ℝ^N` is an increasing union of finite unions of open convex subsets.** -/
theorem euclid_open_monotone_finiteUnions_convex (N : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) :
    ∃ W : ℕ → Set (EuclideanSpace ℝ (Fin N)),
      Monotone W ∧ (∀ k, W k ⊆ U) ∧ (⋃ k, W k) = U ∧
      ∀ k, ∃ s : Finset (Set (EuclideanSpace ℝ (Fin N))),
        (∀ Q ∈ s, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ U) ∧ W k = ⋃ Q ∈ s, Q := by
  -- the compact exhaustion of `U`
  set K : ℕ → Set (EuclideanSpace ℝ (Fin N)) :=
    fun k => {x | ‖x‖ ≤ (k : ℝ)} ∩ {x | Metric.ball x (1 / ((k : ℝ) + 1)) ⊆ U} with hKdef
  have hKclosed : ∀ k, IsClosed (K k) := by
    intro k
    have h1 : IsClosed {x : EuclideanSpace ℝ (Fin N) | ‖x‖ ≤ (k : ℝ)} :=
      isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {x : EuclideanSpace ℝ (Fin N) | Metric.ball x (1 / ((k : ℝ) + 1)) ⊆ U} := by
      rw [show {x : EuclideanSpace ℝ (Fin N) | Metric.ball x (1 / ((k : ℝ) + 1)) ⊆ U}
          = (⋃ y : ↥Uᶜ, Metric.ball (y : EuclideanSpace ℝ (Fin N)) (1 / ((k : ℝ) + 1)))ᶜ by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion]
        constructor
        · rintro h ⟨y, hyx⟩
          exact y.2 (h (Metric.mem_ball_comm.mp hyx))
        · intro h z hz
          by_contra hzU
          exact h ⟨⟨z, hzU⟩, Metric.mem_ball_comm.mpr hz⟩]
      exact (isOpen_iUnion (fun y : ↥Uᶜ => Metric.isOpen_ball)).isClosed_compl
    rw [hKdef]
    exact h1.inter h2
  have hKbd : ∀ k, Bornology.IsBounded (K k) := by
    intro k
    have h1 : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (k : ℝ)) :=
      Metric.isBounded_closedBall
    refine h1.subset ?_
    intro x hx
    simpa using hx.1
  have hKc : ∀ k, IsCompact (K k) := fun k =>
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed k, hKbd k⟩
  have hKU : ∀ k, K k ⊆ U := by
    intro k x hx
    exact hx.2 (Metric.mem_ball_self (by positivity))
  have hcover : ∀ k, ∃ s : Finset (Set (EuclideanSpace ℝ (Fin N))),
      (∀ Q ∈ s, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ U) ∧ K k ⊆ ⋃ Q ∈ s, Q :=
    fun k => isCompact_subset_finset_convex hU (hKc k) (hKU k)
  choose s hs hKs using hcover
  refine ⟨fun k => ⋃ Q ∈ (Finset.range (k + 1)).biUnion s, Q, ?_, ?_, ?_, ?_⟩
  · -- monotone
    intro k l hkl x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨Q, hQ, hxQ⟩ := hx
    obtain ⟨j, hj, hQj⟩ := Finset.mem_biUnion.mp hQ
    simp only [Set.mem_iUnion]
    exact ⟨Q, Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hkl)), hQj⟩, hxQ⟩
  · -- contained in `U`
    intro k x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨Q, hQ, hxQ⟩ := hx
    obtain ⟨j, -, hQj⟩ := Finset.mem_biUnion.mp hQ
    exact (hs j Q hQj).2.2 hxQ
  · -- the union is `U`
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨k, Q, hQ, hxQ⟩ := hx
      obtain ⟨j, -, hQj⟩ := Finset.mem_biUnion.mp hQ
      exact (hs j Q hQj).2.2 hxQ
    · intro x hxU
      obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
      obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖x‖ ≤ (k : ℝ) ∧ 1 / ((k : ℝ) + 1) ≤ r := by
        refine ⟨max (Nat.ceil ‖x‖) (Nat.ceil (1 / r)), ?_, ?_⟩
        · have h1 : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil _
          have h2 : (Nat.ceil ‖x‖ : ℝ) ≤ (max (Nat.ceil ‖x‖) (Nat.ceil (1 / r)) : ℕ) := by
            push_cast
            exact le_max_left _ _
          linarith
        · have h2 : 1 / r ≤ (Nat.ceil (1 / r) : ℝ) := Nat.le_ceil _
          have h3 : (Nat.ceil (1 / r) : ℝ) ≤ (max (Nat.ceil ‖x‖) (Nat.ceil (1 / r)) : ℕ) := by
            push_cast
            exact le_max_right _ _
          have h4 : 1 / r ≤ (max (Nat.ceil ‖x‖) (Nat.ceil (1 / r)) : ℕ) := le_trans h2 h3
          have h6 : 1 ≤ r * (max (Nat.ceil ‖x‖) (Nat.ceil (1 / r)) : ℕ) := by
            have h7 := mul_le_mul_of_nonneg_left h4 (le_of_lt hr)
            have h8 : r * (1 / r) = 1 := by field_simp
            linarith
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hr]
      have hxK : x ∈ K k := by
        refine ⟨hk.1, fun y hy => hrU ?_⟩
        rw [Metric.mem_ball] at hy ⊢
        exact lt_of_lt_of_le hy hk.2
      have hx' : x ∈ ⋃ Q ∈ s k, Q := hKs k hxK
      simp only [Set.mem_iUnion] at hx'
      obtain ⟨Q, hQ, hxQ⟩ := hx'
      simp only [Set.mem_iUnion]
      exact ⟨k, Q, Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), hQ⟩, hxQ⟩
  · -- each `W k` is a finite union of convex open pieces
    intro k
    refine ⟨(Finset.range (k + 1)).biUnion s, ?_, rfl⟩
    intro Q hQ
    obtain ⟨j, -, hQj⟩ := Finset.mem_biUnion.mp hQ
    exact hs j Q hQj

end Work.Cohomology
