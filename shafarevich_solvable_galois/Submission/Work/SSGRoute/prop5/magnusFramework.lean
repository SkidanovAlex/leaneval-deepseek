import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Torsion-freeness of the lower central factors of a free group

The lower central factors `γ_n/γ_{n+1}` of a free group are torsion free (Magnus / Witt).

The proof goes through the *Magnus embedding*: `FreeGroup X` is mapped into the units of the
free associative `ℤ`-algebra `FreeAssoc X = ℤ[FreeMonoid X]` by `x ↦ 1 + X_x`; modulo the `N`-th
term of the word-length filtration this map is well defined.  The "easy half" of the dimension
subgroup theorem shows that `γ_n` maps into `1 + fil n`; the "hard half" (Witt's theorem on the
faithfulness of the free Lie ring, proved separately) provides injectivity, which yields
torsion-freeness because `fil n / fil (n+1)` is free abelian.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The free associative `ℤ`-algebra on `X`, modelled as the monoid algebra of the free monoid. -/
abbrev FreeAssoc (X : Type*) := MonoidAlgebra ℤ (FreeMonoid X)

/-- The generating set (over `ℤ`) of the `N`-th filtration piece: the words of length at least
`N`. -/
def filgen (X : Type*) (N : ℕ) : Set (FreeAssoc X) :=
  {a : FreeAssoc X | ∃ w : FreeMonoid X, N ≤ w.length ∧ a = MonoidAlgebra.single w 1}

/-- The `N`-th filtration piece as a `ℤ`-submodule. -/
def filz (X : Type*) (N : ℕ) : Submodule ℤ (FreeAssoc X) := Submodule.span ℤ (filgen X N)

/-- The `N`-th filtration ideal. -/
def fil (X : Type*) (N : ℕ) : Ideal (FreeAssoc X) := Ideal.span (filgen X N)

theorem mem_filgen {N : ℕ} {a : FreeAssoc X} :
    a ∈ filgen X N ↔ ∃ w : FreeMonoid X, N ≤ w.length ∧ a = MonoidAlgebra.single w 1 := Iff.rfl

theorem single_mem_filz {N : ℕ} {w : FreeMonoid X} (hw : N ≤ w.length) (c : ℤ) :
    MonoidAlgebra.single w c ∈ filz X N := by
  rw [show MonoidAlgebra.single w c = c • MonoidAlgebra.single w (1 : ℤ) by
    rw [MonoidAlgebra.smul_single']; simp]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem filz_le_fil (X : Type*) (N : ℕ) : (filz X N : Set (FreeAssoc X)) ⊆ (fil X N : Set _) :=
  show (filz X N) ≤ (fil X N).restrictScalars ℤ from
    Submodule.span_le.2 fun _ ha => Ideal.subset_span ha

theorem mul_mem_filz (X : Type*) (N : ℕ) (c : FreeAssoc X) {x : FreeAssoc X}
    (hx : x ∈ filz X N) : c * x ∈ filz X N := by
  refine Submodule.span_induction (p := fun x _ => c * x ∈ filz X N) ?_ ?_ ?_ ?_ hx
  · rintro a ⟨w, hw, rfl⟩
    rw [← MonoidAlgebra.sum_coeff_single c, Finsupp.sum_mul]
    refine Submodule.sum_mem _ fun v _ => ?_
    simp only
    simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
    exact single_mem_filz (by rw [FreeMonoid.length_mul]; omega) _
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b ha hb h₁ h₂; rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c' a ha h₁; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' h₁

theorem mul_mem_filz' (X : Type*) (N : ℕ) (c : FreeAssoc X) {x : FreeAssoc X}
    (hx : x ∈ filz X N) : x * c ∈ filz X N := by
  refine Submodule.span_induction (p := fun x _ => x * c ∈ filz X N) ?_ ?_ ?_ ?_ hx
  · rintro a ⟨w, hw, rfl⟩
    rw [← MonoidAlgebra.sum_coeff_single c, Finsupp.mul_sum]
    refine Submodule.sum_mem _ fun v _ => ?_
    simp only
    simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
    exact single_mem_filz (by rw [FreeMonoid.length_mul]; omega) _
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b ha hb h₁ h₂; rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  · intro c' a ha h₁; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c' h₁

/-- `filz X N` viewed as an ideal. -/
def filI (X : Type*) (N : ℕ) : Ideal (FreeAssoc X) :=
  { carrier := filz X N
    zero_mem' := Submodule.zero_mem _
    add_mem' := fun ha hb => Submodule.add_mem _ ha hb
    smul_mem' := fun c _ hx => by
      show c * _ ∈ filz X N
      exact mul_mem_filz X N _ hx }

theorem fil_eq_filI (X : Type*) (N : ℕ) : fil X N = filI X N := by
  refine le_antisymm ?_ ?_
  · refine Ideal.span_le.2 fun a ha => Submodule.subset_span ha
  · intro a ha
    exact filz_le_fil X N ha

theorem fil_antitone (X : Type*) : Antitone (fil X) := by
  intro m n hmn
  refine Ideal.span_le.2 ?_
  rintro a ⟨w, hw, rfl⟩
  exact Ideal.subset_span ⟨w, le_trans hmn hw, rfl⟩

theorem fil_succ_le (X : Type*) (N : ℕ) : fil X (N + 1) ≤ fil X N :=
  fil_antitone X (Nat.le_succ N)

theorem fil_mul_le (X : Type*) (M N : ℕ) : fil X M * fil X N ≤ fil X (M + N) := by
  rw [fil_eq_filI X M, fil_eq_filI X N, fil_eq_filI X (M + N)]
  refine Ideal.mul_le.2 fun r hr s hs => ?_
  refine Submodule.span_induction₂ (R := ℤ) (p := fun r s _ _ => r * s ∈ filz X (M + N))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hr hs
  · rintro x y ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
    exact single_mem_filz (by rw [FreeMonoid.length_mul]; omega) 1
  · intro y _; rw [zero_mul]; exact Submodule.zero_mem _
  · intro x _; rw [mul_zero]; exact Submodule.zero_mem _
  · intro x y z hx hy hz h₁ h₂; rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  · intro x y z hx hy hz h₁ h₂; rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
  · intro c x y hx hy h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  · intro c x y hx hy h; rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

instance (X : Type*) (N : ℕ) : (fil X N).IsTwoSided where
  mul_mem_of_left := fun {a} b ha => by
    rw [fil_eq_filI X N] at ha ⊢
    exact mul_mem_filz' X N b ha

theorem length_pow_of (x : X) (n : ℕ) : ((FreeMonoid.of x) ^ n).length = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, FreeMonoid.length_mul, ih]; simp

theorem isNilpotent_mk_single (X : Type*) (N : ℕ) (x : X) :
    IsNilpotent (Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ))) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, MonoidAlgebra.single_pow, one_pow, Ideal.Quotient.eq_zero_iff_mem]
  rw [fil_eq_filI]
  exact single_mem_filz (le_of_eq (length_pow_of x N).symm) 1

/-- **The Magnus map mod `fil N`.**  The generator `x` of the free group is sent to the unit
`1 + X_x` of the truncated free associative algebra. -/
def magnus (X : Type*) (N : ℕ) : FreeGroup X →* (FreeAssoc X ⧸ fil X N)ˣ :=
  FreeGroup.lift fun x =>
    (IsNilpotent.isUnit_one_add (isNilpotent_mk_single X N x)).unit

theorem magnus_of (X : Type*) (N : ℕ) (x : X) :
    ((magnus X N (FreeGroup.of x) : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) =
      1 + Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ)) := by
  rw [magnus, FreeGroup.lift_apply_of, IsUnit.unit_spec]

end Work.SSGRoute.prop5
