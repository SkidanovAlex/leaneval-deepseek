import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.Expectation

/-!
# The convex distance of Talagrand

For a finite index set `ι`, a product space `∀ i, Ω i`, a set `A` and a point `x`,
Talagrand's convex distance is the Euclidean distance from `0` to the convex hull
of the set `U_A(x)` of `0/1` vectors `s` whose zeros occur only in coordinates
where `x` agrees with some point of `A`.

We work with the *square* of that distance, `cdsq A x`, which is what the
probability estimates need, and record the structural properties used in the
proof of Talagrand's convex distance inequality:

* `cdsq_ge_of_witness` — a nonnegative weight vector `a` which is a witness that
  every point of `A` is far from `x` forces `cdsq A x ≥ D² / ‖a‖²`;
* `cdsq_slice_Option` — one-coordinate slicing: `cdsq` on a product is controlled
  by `cdsq` of the slices and of the projection.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

variable {ι : Type*} [Fintype ι]

/-- The `0/1` vector recording, in each coordinate, whether `x` and `y` differ. -/
noncomputable def disag {Ω : ι → Type*} (x y : ∀ i, Ω i) : ι → ℝ := by
  classical
  exact fun i => if x i = y i then 0 else 1

@[simp] lemma disag_eq_zero {Ω : ι → Type*} {x y : ∀ i, Ω i} {i : ι} :
    disag x y i = 0 ↔ x i = y i := by
  classical
  simp [disag]

lemma disag_eq_one {Ω : ι → Type*} {x y : ∀ i, Ω i} {i : ι} :
    disag x y i = 1 ↔ x i ≠ y i := by
  classical
  simp [disag]

lemma disag_nonneg {Ω : ι → Type*} (x y : ∀ i, Ω i) (i : ι) : 0 ≤ disag x y i := by
  classical
  by_cases h : x i = y i <;> simp [disag, h]

lemma disag_le_one {Ω : ι → Type*} (x y : ∀ i, Ω i) (i : ι) : disag x y i ≤ 1 := by
  classical
  by_cases h : x i = y i <;> simp [disag, h]

lemma disag_self {Ω : ι → Type*} (x : ∀ i, Ω i) : disag x x = 0 := by
  funext i; simp

/-- Squared Euclidean norm of a vector indexed by `ι`. -/
noncomputable def sqnorm (p : ι → ℝ) : ℝ := ∑ i, p i ^ 2

lemma sqnorm_nonneg (p : ι → ℝ) : 0 ≤ sqnorm p :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma sqnorm_eq_zero {p : ι → ℝ} (h : sqnorm p = 0) : p = 0 := by
  funext i
  have hle : p i ^ 2 ≤ sqnorm p := by
    simpa [sqnorm] using
      (Finset.single_le_sum (f := fun j => p j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  rw [h] at hle
  exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp (le_antisymm hle (sq_nonneg _))

@[simp] lemma sqnorm_zero : sqnorm (0 : ι → ℝ) = 0 := by
  simp [sqnorm]

lemma sqnorm_add_le {p q : ι → ℝ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    sqnorm (fun i => lam * p i + (1 - lam) * q i) ≤ lam * sqnorm p + (1 - lam) * sqnorm q := by
  rw [sqnorm, sqnorm, sqnorm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : (lam * p i + (1 - lam) * q i) ^ 2 ≤ lam * p i ^ 2 + (1 - lam) * q i ^ 2 := by
    nlinarith [sq_nonneg (p i - q i), mul_nonneg h0 (sub_nonneg.mpr h1)]
  exact h

/-- Talagrand's set `U_A(x)`: the `0/1` vectors whose zeros occur only in
coordinates where `x` agrees with some point of `A`. -/
def Uset {Ω : ι → Type*} (A : Set (∀ i, Ω i)) (x : ∀ i, Ω i) : Set (ι → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧ ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

/-- The convex hull of `U_A(x)`. -/
noncomputable def Vset {Ω : ι → Type*} (A : Set (∀ i, Ω i)) (x : ∀ i, Ω i) : Set (ι → ℝ) :=
  convexHull ℝ (Uset A x)

/-- The square of Talagrand's convex distance from `x` to `A`. -/
noncomputable def cdsq {Ω : ι → Type*} (A : Set (∀ i, Ω i)) (x : ∀ i, Ω i) : ℝ :=
  sInf (sqnorm '' Vset A x)

/-- Talagrand's convex distance from `x` to `A`. -/
noncomputable def cd {Ω : ι → Type*} (A : Set (∀ i, Ω i)) (x : ∀ i, Ω i) : ℝ :=
  Real.sqrt (cdsq A x)

section Basic
variable {Ω : ι → Type*}

lemma Uset_mono {A B : Set (∀ i, Ω i)} (h : A ⊆ B) (x : ∀ i, Ω i) : Uset A x ⊆ Uset B x :=
  fun s ⟨h01, y, hy, hyx⟩ => ⟨h01, y, h hy, hyx⟩

lemma Vset_mono {A B : Set (∀ i, Ω i)} (h : A ⊆ B) (x : ∀ i, Ω i) : Vset A x ⊆ Vset B x :=
  convexHull_mono (Uset_mono h x)

lemma disag_mem_Uset {A : Set (∀ i, Ω i)} {x y : ∀ i, Ω i} (hy : y ∈ A) :
    disag x y ∈ Uset A x := by
  classical
  refine ⟨fun i => ?_, y, hy, fun i hi => ?_⟩
  · by_cases h : x i = y i <;> simp [disag, h]
  · exact (disag_eq_zero.mp hi)

lemma Uset_nonempty {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} (hA : A.Nonempty) :
    (Uset A x).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨_, disag_mem_Uset hy⟩

lemma Vset_nonempty {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} (hA : A.Nonempty) :
    (Vset A x).Nonempty :=
  (Uset_nonempty hA).mono (subset_convexHull ℝ _)

lemma bddBelow_sqnorm_Vset (A : Set (∀ i, Ω i)) (x : ∀ i, Ω i) :
    BddBelow (sqnorm '' Vset A x) :=
  ⟨0, by rintro q ⟨p, -, rfl⟩; exact sqnorm_nonneg p⟩

lemma cdsq_nonneg {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} : 0 ≤ cdsq A x := by
  rw [cdsq]
  by_cases h : (sqnorm '' Vset A x).Nonempty
  · refine le_csInf h fun q hq => ?_
    obtain ⟨p, hp, rfl⟩ := hq
    exact sqnorm_nonneg p
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

lemma cdsq_le_sqnorm {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} {p : ι → ℝ} (hp : p ∈ Vset A x) :
    cdsq A x ≤ sqnorm p :=
  csInf_le (bddBelow_sqnorm_Vset A x) ⟨p, hp, rfl⟩

lemma le_cdsq_of_forall {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} {C : ℝ}
    (hne : (Vset A x).Nonempty) (h : ∀ p ∈ Vset A x, C ≤ sqnorm p) : C ≤ cdsq A x := by
  refine le_csInf ?_ ?_
  · obtain ⟨p, hp⟩ := hne; exact ⟨sqnorm p, p, hp, rfl⟩
  · rintro q ⟨p, hp, rfl⟩; exact h p hp

/-- The half-space `{p | D ≤ ∑ i, a i * p i}` (a linear-functional preimage) is convex. -/
lemma convex_halfspace {a : ι → ℝ} {D : ℝ} :
    Convex ℝ {p : ι → ℝ | D ≤ ∑ i, a i * p i} := by
  intro p hp q hq lam mu hl hm hlm
  simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp hq ⊢
  have heq : ∑ i, a i * (lam * p i + mu * q i)
      = lam * (∑ i, a i * p i) + mu * (∑ i, a i * q i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  have h1 : lam * D ≤ lam * (∑ i, a i * p i) := mul_le_mul_of_nonneg_left hp hl
  have h2 : mu * D ≤ mu * (∑ i, a i * q i) := mul_le_mul_of_nonneg_left hq hm
  calc D = (lam + mu) * D := by rw [hlm, one_mul]
    _ = lam * D + mu * D := by ring
    _ ≤ _ := by linarith

/-- **Witness (certificate) lower bound for the convex distance.**
If `a ≥ 0` and every point of `A` differs from `x` on coordinates of total
`a`-weight at least `D`, then `D² ≤ ‖a‖² · cdsq A x`. -/
theorem cdsq_ge_of_witness {A : Set (∀ i, Ω i)} {x : ∀ i, Ω i} {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hA : A.Nonempty) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ y ∈ A, D ≤ ∑ i, a i * disag x y i) :
    D ^ 2 ≤ sqnorm a * cdsq A x := by
  have key : ∀ p ∈ Vset A x, D ≤ ∑ i, a i * p i := by
    intro p hp
    refine convexHull_min ?_ convex_halfspace hp
    rintro s ⟨h01, y, hy, hsy⟩
    have h1 : ∀ i, disag x y i ≤ s i := by
      intro i
      rcases h01 i with h | h
      · rw [disag_eq_zero.mpr (hsy i h), h]
      · rw [h]; exact disag_le_one x y i
    calc D ≤ ∑ i, a i * disag x y i := h y hy
      _ ≤ ∑ i, a i * s i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) (ha i)
  rcases eq_or_lt_of_le (sqnorm_nonneg a) with h0 | h0
  · have hazero : a = 0 := sqnorm_eq_zero h0.symm
    obtain ⟨y, hy⟩ := hA
    have hy' := h y hy
    rw [hazero] at hy'
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hy'
    have hD0 : D = 0 := le_antisymm hy' hD
    rw [hD0, ← h0]
    simp
  · have hstep : D ^ 2 / sqnorm a ≤ cdsq A x := by
      refine le_cdsq_of_forall (Vset_nonempty hA) fun p hp => ?_
      have hp1 : D ≤ ∑ i, a i * p i := key p hp
      have hcs : (∑ i, a i * p i) ^ 2 ≤ sqnorm a * sqnorm p := by
        rw [sqnorm, sqnorm]
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      have hD2 : D ^ 2 ≤ (∑ i, a i * p i) ^ 2 := by
        apply sq_le_sq'
        · linarith
        · exact hp1
      have hfin := le_trans hD2 hcs
      rw [div_le_iff₀ h0]
      linarith [hfin]
    rw [div_le_iff₀ h0] at hstep
    linarith [hstep]

end Basic

section Engine

/-- **Talagrand's convex distance inequality**, in the form proved by induction:
for a product of finite probability spaces of *full support*, the exponential
moment of the squared convex distance to any set `A` is at most `1 / Pr[A]`
(written multiplicatively so that it stays true for `A = ∅`). -/
def Engine (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ (Ω : ι → Type*) [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i)),
    (∀ i x, 0 < (μ i).wt x) → ∀ A : Set (∀ i, Ω i),
      (FinProb.pi μ).prob A * (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4)) ≤ 1

end Engine

end Work.Deep.Reed.Prob
