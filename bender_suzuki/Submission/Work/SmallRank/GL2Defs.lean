/-
# `GL(2, p)`: algebraic preliminaries for "odd `p'`-subgroups of `GL(2,p)` are abelian"

Setting: `p` is a prime, `K = ZMod p`, `M₂(K) = Matrix (Fin 2) (Fin 2) K`, `G = M₂(K)ˣ = GL(2,p)`.

For `a : M₂(K)`, `polySet a` is the `K`-span of `1` and `a` (the "polynomials in `a`").  For a
non-scalar `a` this is a commutative subalgebra isomorphic to `𝔽_p[a]`, and it is the centraliser of
`a` in `M₂(K)`; this is the basic structural input for the proof of
`Work.SmallRank.isMulCommutative_of_odd_coprime_le_GL2`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped Classical
open Matrix

noncomputable section

namespace Work.SmallRank

/-- The algebra `M₂(𝔽_p)` of `2 × 2` matrices over `ZMod p`. -/
abbrev M2 (p : ℕ) : Type := Matrix (Fin 2) (Fin 2) (ZMod p)

/-- `polySet a` is the `𝔽_p`-linear span of `1` and `a`: the "polynomials in `a`". -/
def polySet {p : ℕ} (a : M2 p) : Set (M2 p) := {x | ∃ α β : ZMod p, x = α • 1 + β • a}

lemma one_mem_polySet {p : ℕ} (a : M2 p) : (1 : M2 p) ∈ polySet a := ⟨1, 0, by simp⟩

lemma self_mem_polySet {p : ℕ} (a : M2 p) : a ∈ polySet a := ⟨0, 1, by simp⟩

lemma smul_one_mem_polySet {p : ℕ} (a : M2 p) (α : ZMod p) : α • 1 ∈ polySet a :=
  ⟨α, 0, by simp⟩

/-- `a` is a scalar matrix. -/
def IsScalar {p : ℕ} (a : M2 p) : Prop := ∃ α : ZMod p, a = α • 1

/-- `a` is a non-scalar matrix: the interesting case, where `polySet a` is a genuine subalgebra. -/
def NonScalar {p : ℕ} (a : M2 p) : Prop := ¬ IsScalar a

lemma not_isScalar_iff {p : ℕ} (a : M2 p) : NonScalar a ↔ ¬ ∃ α : ZMod p, a = α • 1 := Iff.rfl

/-- Cayley–Hamilton for `2 × 2` matrices. -/
lemma sq_eq_trace_smul_sub_det_smul {p : ℕ} [Fact p.Prime] (a : M2 p) :
    a ^ 2 = Matrix.trace a • a - a.det • 1 := by
  rw [pow_two, Matrix.eta_fin_two a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

/-- Trace of `α + β a`. -/
lemma trace_smul_one_add_smul {p : ℕ} (α β : ZMod p) (a : M2 p) :
    Matrix.trace (α • 1 + β • a) = 2 * α + β * Matrix.trace a := by
  simp [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply]
  ring

/-- Determinant of `α + β a`. -/
lemma det_smul_one_add_smul {p : ℕ} (α β : ZMod p) (a : M2 p) :
    (α • 1 + β • a).det = α ^ 2 + α * β * Matrix.trace a + β ^ 2 * a.det := by
  rw [Matrix.eta_fin_two a]
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply]
  ring

/-- Expanded product of two elements of `polySet a`. -/
lemma mul_smul_one_add_smul {p : ℕ} [Fact p.Prime] (α β γ δ : ZMod p) (a : M2 p) :
    (α • 1 + β • a) * (γ • 1 + δ • a)
      = (α * γ - β * δ * a.det) • 1 + (α * δ + β * γ + β * δ * Matrix.trace a) • a := by
  rw [Matrix.eta_fin_two a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Matrix.add_mul, Matrix.mul_add, Matrix.trace_fin_two,
      Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_mul,
      Matrix.mul_one]
  all_goals ring

/-- `polySet a` is closed under multiplication. -/
lemma mul_mem_polySet {p : ℕ} [Fact p.Prime] {a x y : M2 p} (hx : x ∈ polySet a)
    (hy : y ∈ polySet a) : x * y ∈ polySet a := by
  obtain ⟨α, β, rfl⟩ := hx
  obtain ⟨γ, δ, rfl⟩ := hy
  exact ⟨α * γ - β * δ * a.det, α * δ + β * γ + β * δ * Matrix.trace a,
    mul_smul_one_add_smul α β γ δ a⟩

/-- `polySet a` is a commutative set. -/
lemma mul_comm_of_mem_polySet {p : ℕ} [Fact p.Prime] {a x y : M2 p} (hx : x ∈ polySet a)
    (hy : y ∈ polySet a) : x * y = y * x := by
  obtain ⟨α, β, rfl⟩ := hx
  obtain ⟨γ, δ, rfl⟩ := hy
  rw [mul_smul_one_add_smul, mul_smul_one_add_smul]
  congr 2 <;> ring

/-- `polySet a` is closed under addition. -/
lemma add_mem_polySet {p : ℕ} {a x y : M2 p} (hx : x ∈ polySet a) (hy : y ∈ polySet a) :
    x + y ∈ polySet a := by
  obtain ⟨α, β, rfl⟩ := hx
  obtain ⟨γ, δ, rfl⟩ := hy
  exact ⟨α + γ, β + δ, by module⟩

/-- `polySet a` is closed under scalar multiplication. -/
lemma smul_mem_polySet {p : ℕ} {a x : M2 p} (hx : x ∈ polySet a) (c : ZMod p) :
    c • x ∈ polySet a := by
  obtain ⟨α, β, rfl⟩ := hx
  exact ⟨c * α, c * β, by module⟩

/-- `polySet a ⊆ polySet x` when `x ∈ polySet a`. -/
lemma polySet_subset_of_mem {p : ℕ} {a x : M2 p} (hx : x ∈ polySet a) :
    polySet x ⊆ polySet a := by
  rintro y ⟨γ, δ, rfl⟩
  obtain ⟨α, β, rfl⟩ := hx
  exact ⟨γ + δ * α, δ * β, by module⟩

/-- If `x = α + β a ∈ polySet a` with `β ≠ 0` then `polySet a ⊆ polySet x`. -/
lemma polySet_subset_of_mem_of_ne {p : ℕ} [Fact p.Prime] {a x : M2 p} {α β : ZMod p}
    (hx : x = α • 1 + β • a) (hβ : β ≠ 0) : polySet a ⊆ polySet x := by
  intro y hy
  obtain ⟨γ, δ, rfl⟩ := hy
  subst hx
  have hb : δ * β⁻¹ * β = δ := by rw [mul_assoc, inv_mul_cancel₀ hβ, mul_one]
  refine ⟨γ - δ * β⁻¹ * α, δ * β⁻¹, ?_⟩
  calc γ • 1 + δ • a
      = (γ - δ * β⁻¹ * α) • 1 + ((δ * β⁻¹ * α) • 1 + (δ * β⁻¹ * β) • a) := by rw [hb]; module
    _ = (γ - δ * β⁻¹ * α) • 1 + (δ * β⁻¹) • (α • 1 + β • a) := by module

/-- `polySet a` is a submonoid of `M₂(𝔽_p)`. -/
def polyMon {p : ℕ} [Fact p.Prime] (a : M2 p) : Submonoid (M2 p) where
  carrier := polySet a
  mul_mem' hx hy := mul_mem_polySet hx hy
  one_mem' := one_mem_polySet a

/-- The inverse of a unit of `M₂(𝔽_p)` in terms of trace, determinant and adjugate. -/
lemma inv_eq_det_inv_smul_adjugate {p : ℕ} [Fact p.Prime] (u : (M2 p)ˣ) :
    ((u⁻¹ : (M2 p)ˣ) : M2 p)
      = (Matrix.det (u : M2 p))⁻¹ • (Matrix.trace (u : M2 p) • 1 - (u : M2 p)) := by
  have hdet : Matrix.det ((u : (M2 p)ˣ) : M2 p) ≠ 0 := by
    have h : IsUnit ((u : (M2 p)ˣ) : M2 p) := u.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at h
    exact h.ne_zero
  have hadj : ((u : (M2 p)ˣ) : M2 p).adjugate
      = Matrix.trace ((u : (M2 p)ˣ) : M2 p) • 1 - (u : M2 p) := by
    rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  have hmul : ((u : (M2 p)ˣ) : M2 p) *
      ((Matrix.det ((u : (M2 p)ˣ) : M2 p))⁻¹ •
        (Matrix.trace ((u : (M2 p)ˣ) : M2 p) • 1 - (u : M2 p))) = 1 := by
    rw [← hadj, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  have key : ∀ w : M2 p, ((u : (M2 p)ˣ) : M2 p) * w = 1 → ((u⁻¹ : (M2 p)ˣ) : M2 p) = w := by
    intro w hw
    calc ((u⁻¹ : (M2 p)ˣ) : M2 p)
        = ((u⁻¹ : (M2 p)ˣ) : M2 p) * 1 := (mul_one _).symm
      _ = ((u⁻¹ : (M2 p)ˣ) : M2 p) * (((u : (M2 p)ˣ) : M2 p) * w) := by rw [hw]
      _ = (((u⁻¹ : (M2 p)ˣ) : M2 p) * ((u : (M2 p)ˣ) : M2 p)) * w := (mul_assoc _ _ _).symm
      _ = 1 * w := by rw [Units.inv_mul]
      _ = w := one_mul w
  exact key _ hmul

/-- `trace u • 1 - u ∈ polySet a` for `u ∈ polySet a`. -/
lemma trace_smul_one_sub_mem_polySet {p : ℕ} [Fact p.Prime] {a u : M2 p}
    (hu : u ∈ polySet a) : Matrix.trace u • 1 - u ∈ polySet a := by
  obtain ⟨α, β, rfl⟩ := hu
  refine ⟨2 * α + β * Matrix.trace a - α, -β, ?_⟩
  rw [trace_smul_one_add_smul]
  module

/-- The subgroup of units of `M₂(𝔽_p)` lying in `polySet a`.  When `a` is non-scalar this is a
commutative subgroup of `GL(2,p)` (the unit group of the commutative algebra `𝔽_p[a]`). -/
def polyUnitSub {p : ℕ} [Fact p.Prime] (a : M2 p) : Subgroup (M2 p)ˣ where
  carrier := {u | (u : M2 p) ∈ polySet a}
  one_mem' := one_mem_polySet a
  mul_mem' := by
    intro u v hu hv
    show ((u * v : (M2 p)ˣ) : M2 p) ∈ polySet a
    rw [Units.val_mul]
    exact mul_mem_polySet hu hv
  inv_mem' := by
    intro u hu
    show ((u⁻¹ : (M2 p)ˣ) : M2 p) ∈ polySet a
    rw [inv_eq_det_inv_smul_adjugate]
    exact smul_mem_polySet (trace_smul_one_sub_mem_polySet hu) _

/-- Membership in `polyUnitSub` is membership of the underlying matrix in `polySet`. -/
@[simp]
lemma mem_polyUnitSub_iff {p : ℕ} [Fact p.Prime] {a : M2 p} {u : (M2 p)ˣ} :
    u ∈ polyUnitSub a ↔ (u : M2 p) ∈ polySet a := Iff.rfl

/-- Two elements of `polySet a` with the same trace and determinant satisfy the discriminant
identity: if `b = α + β a` and `b` has the same characteristic polynomial as `a`, then
`(β² - 1) (4 det a - (tr a)²) = 0`. -/
lemma sq_sub_one_mul_disc_eq_zero {p : ℕ} [Fact p.Prime] (a : M2 p) (α β : ZMod p)
    (htr : 2 * α + β * Matrix.trace a = Matrix.trace a)
    (hdet : α ^ 2 + α * β * Matrix.trace a + β ^ 2 * a.det = a.det) :
    (β ^ 2 - 1) * (4 * a.det - (Matrix.trace a) ^ 2) = 0 := by
  have h1 : 2 * α - Matrix.trace a * (1 - β) = 0 := by linear_combination htr
  have h2 : α ^ 2 + α * β * Matrix.trace a + β ^ 2 * a.det - a.det = 0 := by
    linear_combination hdet
  linear_combination (4 : ZMod p) * h2 - (2 * α + Matrix.trace a * (1 + β)) * h1

/-- Intersection of two `polySet`s: if a *non-scalar* element lies in `polySet a ∩ polySet b`, then
`polySet a = polySet b`.  (Otherwise the intersection is the set of scalars.) -/
theorem polySet_eq_of_mem_inter {p : ℕ} [Fact p.Prime] {a b x : M2 p} (ha : x ∈ polySet a)
    (hb : x ∈ polySet b) (hx : NonScalar x) : polySet a = polySet b := by
  obtain ⟨α, β, hxab⟩ := ha
  have hβ : β ≠ 0 := by
    rintro rfl
    exact hx ⟨α, by rw [hxab]; simp⟩
  have h1 : polySet a = polySet x :=
    le_antisymm (polySet_subset_of_mem_of_ne hxab hβ) (polySet_subset_of_mem ⟨α, β, hxab⟩)
  obtain ⟨γ, δ, hxbb⟩ := hb
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hx ⟨γ, by rw [hxbb]; simp⟩
  have h2 : polySet b = polySet x :=
    le_antisymm (polySet_subset_of_mem_of_ne hxbb hδ) (polySet_subset_of_mem ⟨γ, δ, hxbb⟩)
  rw [h1, h2]

end Work.SmallRank
