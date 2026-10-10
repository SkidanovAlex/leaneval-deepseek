import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Submission.Work.SSGRoute.prop5.magnusFramework
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus map carries the lower central series into `1 + fil`

This file proves the "easy half" of the Magnus embedding:  if `y` lies in the `k`-th term of the
lower central series of a free group `FreeGroup X`, then the Magnus image of `y` in the truncated
free associative algebra `FreeAssoc X ⧸ fil X N` satisfies

`magnus X N y - 1 ∈ ideal image of fil X (k+1)`.

The proof is the standard filtered-ring argument.  Write `F k` for the image of `fil X k` in the
quotient; it is a (two-sided) ideal with `F a * F b ≤ F (a+b)`.  The set
`T k = {u : Rˣ // ↑u - 1 ∈ F k}` is a subgroup of the unit group, and for `u ∈ T a`, `v ∈ T b` the
commutator lies in `T (a+b)` because

`↑⁅u,v⁆ - 1 = ((↑u - 1)(↑v - 1) - (↑v - 1)(↑u - 1)) * (↑u⁻¹ * ↑v⁻¹)`.

Since every image of a generator of the free group is `≡ 1` modulo `F 1`, induction on `k` using
`γ_{k+1} = ⁅γ_k, ⊤⁆` gives the claim.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The filtration ideals of the truncated free algebra -/

/-- `filq X N k` is the image of the `k`-th filtration ideal `fil X k` in the quotient
`FreeAssoc X ⧸ fil X N`. -/
def filq (X : Type*) (N k : ℕ) : Ideal (FreeAssoc X ⧸ fil X N) :=
  Ideal.map (Ideal.Quotient.mk (fil X N)) (fil X k)

theorem filq_antitone (X : Type*) (N : ℕ) : Antitone (filq X N) :=
  fun _ _ hmn => Ideal.map_mono (fil_antitone X hmn)

/-- The product of two filtration pieces lands in the filtration piece of the sum of the
indices. -/
theorem mul_mem_filq (X : Type*) (N a b : ℕ) {x y : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N a) (hy : y ∈ filq X N b) : x * y ∈ filq X N (a + b) := by
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    (Ideal.Quotient.mk_surjective)).1 hx
  obtain ⟨y', hy', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    (Ideal.Quotient.mk_surjective)).1 hy
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (fil_mul_le X a b (Ideal.mul_mem_mul hx' hy'))

/-- A filtration piece is a two-sided ideal of the quotient. -/
theorem mul_mem_filq_right (X : Type*) (N a : ℕ) {x : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N a) (c : FreeAssoc X ⧸ fil X N) : x * c ∈ filq X N a := by
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    (Ideal.Quotient.mk_surjective)).1 hx
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (Ideal.IsTwoSided.mul_mem_of_left c' hx')

/-! ## The subgroup of units congruent to `1` modulo a filtration piece -/

/-- The subgroup of the unit group of `FreeAssoc X ⧸ fil X N` consisting of the units whose image
in the ring is congruent to `1` modulo the `k`-th filtration piece. -/
def unitCongr (X : Type*) (N k : ℕ) : Subgroup (FreeAssoc X ⧸ fil X N)ˣ where
  carrier := {u | ((u : FreeAssoc X ⧸ fil X N) - 1) ∈ filq X N k}
  mul_mem' := by
    intro u v hu hv
    change ((↑(u * v) : FreeAssoc X ⧸ fil X N) - 1) ∈ filq X N k
    have h : (↑(u * v) : FreeAssoc X ⧸ fil X N) - 1
        = (↑u : FreeAssoc X ⧸ fil X N) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
          + ((↑u : FreeAssoc X ⧸ fil X N) - 1) := by
      rw [Units.val_mul]
      noncomm_ring
    rw [h]
    exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ hv) hu
  one_mem' := by
    change ((↑(1 : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1) ∈ filq X N k
    rw [Units.val_one]
    simp
  inv_mem' := by
    intro u hu
    change ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1) ∈ filq X N k
    have h1 : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ↑u = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h : (↑(u⁻¹) : FreeAssoc X ⧸ fil X N) - 1
        = - ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)) := by
      rw [mul_sub, h1, mul_one, neg_sub]
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ hu)

/-! ## The commutator of two congruent units -/

/-- If `u ≡ 1` modulo `F a` and `v ≡ 1` modulo `F b`, then `⁅u,v⁆ ≡ 1` modulo `F (a+b)`. -/
theorem commutator_mem_unitCongr (X : Type*) (N a b : ℕ)
    {u v : (FreeAssoc X ⧸ fil X N)ˣ} (hu : u ∈ unitCongr X N a)
    (hv : v ∈ unitCongr X N b) : ⁅u, v⁆ ∈ unitCongr X N (a + b) := by
  change ((↑(⁅u, v⁆) : FreeAssoc X ⧸ fil X N) - 1) ∈ filq X N (a + b)
  have key : (↑u : FreeAssoc X ⧸ fil X N) * ↑v - ↑v * ↑u =
      ((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        - ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1) := by
    noncomm_ring
  have hcomm : ((↑(⁅u, v⁆) : FreeAssoc X ⧸ fil X N)) - 1 =
      (((↑u : FreeAssoc X ⧸ fil X N) - 1) * ((↑v : FreeAssoc X ⧸ fil X N) - 1)
        - ((↑v : FreeAssoc X ⧸ fil X N) - 1) * ((↑u : FreeAssoc X ⧸ fil X N) - 1)) *
        ((↑(u⁻¹) : FreeAssoc X ⧸ fil X N) * ↑(v⁻¹)) := by
    rw [← key, sub_mul, commutatorElement_def]
    simp only [Units.val_mul, mul_assoc]
    have h3 : (↑v : FreeAssoc X ⧸ fil X N) *
        ((↑u : FreeAssoc X ⧸ fil X N) * (↑(u⁻¹) * ↑(v⁻¹))) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      simp
    rw [h3]
  rw [hcomm]
  refine mul_mem_filq_right X N (a + b) (Submodule.sub_mem _ ?_ ?_) _
  · exact mul_mem_filq X N a b hu hv
  · have h := mul_mem_filq X N b a hv hu
    rwa [Nat.add_comm b a] at h

theorem commutator_unitCongr_le (X : Type*) (N a b : ℕ) :
    ⁅unitCongr X N a, unitCongr X N b⁆ ≤ unitCongr X N (a + b) := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  exact commutator_mem_unitCongr X N a b hu hv

/-! ## The induction -/

/-- Every element of the free group is carried by the Magnus map to a unit congruent to `1`
modulo the first filtration piece. -/
theorem map_magnus_le_unitCongr_one (X : Type*) (N : ℕ) :
    Subgroup.map (magnus X N) (⊤ : Subgroup (FreeGroup X)) ≤ unitCongr X N 1 := by
  rw [Subgroup.map_le_iff_le_comap, ← FreeGroup.closure_range_of X, Subgroup.closure_le]
  rintro y ⟨x, rfl⟩
  change FreeGroup.of x ∈ Subgroup.comap (magnus X N) (unitCongr X N 1)
  rw [Subgroup.mem_comap]
  change ((magnus X N (FreeGroup.of x) : (FreeAssoc X ⧸ fil X N)ˣ) :
      FreeAssoc X ⧸ fil X N) - 1 ∈ filq X N 1
  rw [magnus_of]
  have h : (1 + Ideal.Quotient.mk (fil X N)
        (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ))) - 1
      = Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ)) := by
    noncomm_ring
  rw [h]
  refine Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨FreeMonoid.of x, ?_, rfl⟩)
  rw [FreeMonoid.length_of]

/-- The Magnus image of the `k`-th term of the lower central series lies in the group of units
congruent to `1` modulo `fil X (k+1)`. -/
theorem map_magnus_lowerCentralSeries_le (X : Type*) (N k : ℕ) :
    Subgroup.map (magnus X N) ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k) ≤
      unitCongr X N (k + 1) := by
  induction k with
  | zero =>
      rw [Subgroup.lowerCentralSeries_zero]
      exact map_magnus_le_unitCongr_one X N
  | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.map_commutator]
      refine le_trans (Subgroup.commutator_mono ih (le_refl _)) ?_
      exact le_trans (Subgroup.commutator_mono le_rfl (map_magnus_le_unitCongr_one X N))
        (commutator_unitCongr_le X N (k + 1) 1)

theorem magnus_mem_one_add (X : Type*) (N k : ℕ) (hk : k + 1 ≤ N) :
    ∀ y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k,
      ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
        Ideal.map (Ideal.Quotient.mk (fil X N)) (fil X (k + 1)) := by
  intro y hy
  exact map_magnus_lowerCentralSeries_le X N k (Subgroup.mem_map_of_mem (magnus X N) hy)

end Work.SSGRoute.prop5
