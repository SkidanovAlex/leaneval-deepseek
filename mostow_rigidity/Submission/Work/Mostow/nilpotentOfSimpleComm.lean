import Mathlib
import Submission.Work.Mostow.zassDefs

/-!
# Nilpotency from vanishing of simple commutators

If all left-normed simple commutators of weight at least `N` in the elements of a set `X` of a
group `G` are trivial, then `⟨X⟩` is nilpotent.

The proof builds the descending family `Z k = CommSubgroup X k` (the closure of the
`⟨X⟩`-conjugates of the simple commutators of weight at least `k`), proves the key step
`⁅Z k, ⟨X⟩⁆ ≤ Z (k+1)`, and reads off a descending central series of `⟨X⟩` whose `N`-th term
is trivial.
-/

open scoped commutatorElement

namespace Work.Mostow

variable {G : Type*} [Group G]

lemma SimpleCommSet_subset_closure (X : Set G) (k : ℕ) :
    SimpleCommSet X k ⊆ Subgroup.closure X := by
  induction k with
  | zero => intro x hx; exact Subgroup.subset_closure hx
  | succ k ih =>
    rintro c ⟨a, ha, x, hx, rfl⟩
    have h1 : a ∈ Subgroup.closure X := ih ha
    have h2 : x ∈ Subgroup.closure X := Subgroup.subset_closure hx
    rw [commutatorElement_def]
    exact (Subgroup.closure X).mul_mem
      ((Subgroup.closure X).mul_mem ((Subgroup.closure X).mul_mem h1 h2)
        ((Subgroup.closure X).inv_mem h1))
      ((Subgroup.closure X).inv_mem h2)

lemma CommGens_subset_closure (X : Set G) (k : ℕ) :
    CommGens X k ⊆ Subgroup.closure X := by
  rintro g ⟨j, _hj, c, hc, h, hh, rfl⟩
  exact (Subgroup.closure X).mul_mem
    ((Subgroup.closure X).mul_mem hh (SimpleCommSet_subset_closure X j hc))
    ((Subgroup.closure X).inv_mem hh)

/-- Every term of the series is contained in `⟨X⟩`. -/
lemma CommSubgroup_le_closure (X : Set G) (k : ℕ) :
    CommSubgroup X k ≤ Subgroup.closure X := by
  rw [CommSubgroup]
  exact (Subgroup.closure_le _).mpr (CommGens_subset_closure X k)

/-- The zeroth term of the series is exactly `⟨X⟩`. -/
lemma closure_le_CommSubgroup_zero (X : Set G) :
    Subgroup.closure X ≤ CommSubgroup X 0 := by
  rw [CommSubgroup]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  exact Subgroup.subset_closure ⟨0, le_rfl, x, hx, 1, Subgroup.one_mem _, by simp⟩

lemma CommSubgroup_zero_eq (X : Set G) : CommSubgroup X 0 = Subgroup.closure X :=
  le_antisymm (CommSubgroup_le_closure X 0) (closure_le_CommSubgroup_zero X)

/-- If all simple commutators of weight at least `N` vanish then the `N`-th term of the series
is trivial. -/
lemma CommSubgroup_eq_bot_of_trivial (X : Set G) (N : ℕ)
    (hN : ∀ k, N ≤ k → ∀ c ∈ SimpleCommSet X k, c = 1) : CommSubgroup X N = ⊥ := by
  rw [CommSubgroup, eq_bot_iff]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨j, hj, c, hc, h, _hh, rfl⟩
  rw [hN j hj c hc]
  simp

/-- For a fixed simple commutator `c` of weight `j ≥ k`, the commutators `⁅c, g⁆` with `g ∈ ⟨X⟩`
all lie in `CommSubgroup X (k+1)`. -/
lemma SimpleCommSet_commutator_mem (X : Set G) (k : ℕ) {j : ℕ} {c : G}
    (hc : c ∈ SimpleCommSet X j) (hjk : k ≤ j) :
    ∀ g ∈ Subgroup.closure X, ⁅c, g⁆ ∈ CommSubgroup X (k+1) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => ⁅c, g⁆ ∈ CommSubgroup X (k+1))
    (fun x hx => ?_) ?_ ?_ ?_ hg
  · exact Subgroup.subset_closure
      ⟨j + 1, by omega, ⁅c, x⁆, ⟨c, hc, x, hx, rfl⟩, 1, Subgroup.one_mem _, by simp⟩
  · simp
  · intro a b ha _hb hpa hpb
    have hmul : ⁅c, a * b⁆ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    rw [hmul]
    exact Subgroup.mul_mem _ hpa (CommSubgroup_conj_mem X (k+1) hpb ha)
  · intro a ha hpa
    have hconj : a⁻¹ * ⁅c, a⁆ * a ∈ CommSubgroup X (k+1) := by
      simpa using CommSubgroup_conj_mem X (k+1) hpa (Subgroup.inv_mem _ ha)
    have hinv : ⁅c, a⁻¹⁆ = (a⁻¹ * ⁅c, a⁆ * a)⁻¹ := by
      rw [commutatorElement_inv_right, ← commutatorElement_inv]
      group
    rw [hinv]
    exact Subgroup.inv_mem _ hconj

/-- The subgroup of elements of `H = ⟨X⟩` whose commutators with all of `H` lie in
`CommSubgroup X k`. -/
private def commQ (X : Set G) (k : ℕ) : Subgroup G where
  carrier := {x : G | x ∈ Subgroup.closure X ∧
    ∀ g ∈ Subgroup.closure X, ⁅x, g⁆ ∈ CommSubgroup X k}
  one_mem' := ⟨Subgroup.one_mem _, by intro g _; simp⟩
  mul_mem' := by
    rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
    refine ⟨Subgroup.mul_mem _ hxH hyH, ?_⟩
    intro g hg
    have hconj : x * ⁅y, g⁆ * x⁻¹ ∈ CommSubgroup X k := CommSubgroup_conj_mem X k (hy g hg) hxH
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact Subgroup.mul_mem _ hconj (hx g hg)
  inv_mem' := by
    rintro x ⟨hxH, hx⟩
    refine ⟨Subgroup.inv_mem _ hxH, ?_⟩
    intro g hg
    have h1 : ⁅g, x⁆ ∈ CommSubgroup X k := by
      simpa using Subgroup.inv_mem _ (hx g hg)
    have h2 : x⁻¹ * ⁅g, x⁆ * (x⁻¹)⁻¹ ∈ CommSubgroup X k :=
      CommSubgroup_conj_mem X k h1 (Subgroup.inv_mem _ hxH)
    rw [commutatorElement_inv_left]
    simpa using h2

/-- **Key step**: the commutator of an element of `CommSubgroup X k` with an element of `⟨X⟩`
lies in `CommSubgroup X (k+1)`. -/
lemma commutator_mem_CommSubgroup_succ (X : Set G) (k : ℕ) :
    ∀ x ∈ CommSubgroup X k, ∀ g ∈ Subgroup.closure X, ⁅x, g⁆ ∈ CommSubgroup X (k+1) := by
  have hQ : CommSubgroup X k ≤ commQ X (k+1) := by
    rw [CommSubgroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨j, hjk, c, hc, h, hh, rfl⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (SimpleCommSet_subset_closure X j hc))
      (Subgroup.inv_mem _ hh), ?_⟩
    intro g hg
    have hinner : ⁅c, h⁻¹ * g * h⁆ ∈ CommSubgroup X (k+1) :=
      SimpleCommSet_commutator_mem X k hc hjk _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg) hh)
    have hconj : h * ⁅c, h⁻¹ * g * h⁆ * h⁻¹ ∈ CommSubgroup X (k+1) :=
      CommSubgroup_conj_mem X (k+1) hinner hh
    have hcomm : ⁅h * c * h⁻¹, g⁆ = h * ⁅c, h⁻¹ * g * h⁆ * h⁻¹ := by
      rw [conjugate_commutatorElement]
      congr 1
      group
    rwa [hcomm]
  intro x hx g hg
  exact (hQ hx).2 g hg

theorem nilpotentOfSimpleComm {G : Type*} [Group G] (X : Set G) (N : ℕ)
    (hN : ∀ k, N ≤ k → ∀ c ∈ Work.Mostow.SimpleCommSet X k, c = 1) :
    Group.IsNilpotent (Subgroup.closure X) := by
  let H := Subgroup.closure X
  let D : ℕ → Subgroup H := fun k => (CommSubgroup X k).comap H.subtype
  refine (Subgroup.nilpotent_iff_finite_descending_central_series H).mpr ⟨N, D, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · ext x
      simp only [D, Subgroup.mem_comap, Subgroup.mem_top, iff_true]
      rw [CommSubgroup_zero_eq]
      exact x.2
    · intro x n hx g
      have hx' : (x : G) ∈ CommSubgroup X n := hx
      have hg' : (g : G) ∈ Subgroup.closure X := g.2
      have hkey : ⁅(x : G), (g : G)⁆ ∈ CommSubgroup X (n + 1) :=
        commutator_mem_CommSubgroup_succ X n (x : G) hx' (g : G) hg'
      simp only [D, Subgroup.mem_comap]
      rw [map_commutatorElement]
      exact hkey
  · simp only [D]
    rw [CommSubgroup_eq_bot_of_trivial X N hN]
    ext x
    simp

end Work.Mostow
