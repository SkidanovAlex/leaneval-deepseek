/-
# Cyclic lifts and the parametrization of a ray polygon

The ray polygon `Work.EL.polyCurve ps R` of an admissible list of co-landing pairs is the
boundary of the region `Work.EL.polyRegion ps R`.  This module fixes the language in which
the polygon is parametrized as a closed curve:

* `Work.ELTop.CycLift hN` is a **cyclic lift** of the data of the list `ps`: functions
  `A B : ℤ → ℝ` and `Y : ℤ → ℂ` with `A (k+m) = A k + 1`, `B (k+m) = B k + 1`,
  `Y (k+m) = Y k` and `A k < B k < A (k+1)`.  So `A k, B k` are the two angles of the `k`-th
  pair, lifted to the line so that the sequence `… < A k < B k < A (k+1) < …` is strictly
  increasing, and `Y k` is the common landing point of the two rays;
* `CycLift.Matches D ps`: `ps` is the list whose `i`-th pair is `k = i + m q` of the lift;
* `rayArc hN β y`: the (closed) ray piece of angle `β`, parametrized by the *potential level*
  `t ∈ [1,R]`: `t = 1` is the landing point `y`, `t > 1` the ray point;
* `eqArcPt hN β₁ β₂ R`: the equipotential arc of level `R` between the angles `β₁` and `β₂`,
  parametrized by `u ∈ [0,1]`: the angle `β₁ + u (β₂ - β₁)`;
* `cycBlock hN D R k`: the `k`-th block of the parametrization, on `σ ∈ [0,1]`: the ray `A k`
  up to level `R` (first third), the equipotential arc from `A k` back to `B (k-1)` (second
  third), the ray `B (k-1)` back to `Y (k-1)` (last third);
* `cycParam hN D R`: the resulting parametrization of the whole polygon by `s ∈ [0,1]`, with
  `cycParam hN D R '' Ico 0 1 = polyCurve ps R` for `D.Matches ps`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.closure_rayPiece
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Cyclic lifts -/

/-- A **cyclic lift** of the angle data of a list of co-landing pairs: the angles `A k`, `B k`
of the `k`-th pair and its landing point `Y k`, lifted to `ℤ` so that the angles are strictly
increasing in `k` and periodic of period `m` up to the translation `θ ↦ θ + 1`. -/
structure CycLift (hN : Work.EL.DynB c φ) where
  /-- the number of pairs. -/
  m : ℕ
  /-- the list of pairs is nonempty. -/
  hm : 0 < m
  /-- the first angle of the `k`-th pair, lifted. -/
  A : ℤ → ℝ
  /-- the second angle of the `k`-th pair, lifted. -/
  B : ℤ → ℝ
  /-- the landing point of the `k`-th pair. -/
  Y : ℤ → ℂ
  /-- the angle `A` is periodic up to `θ ↦ θ + 1`. -/
  A_add : ∀ k : ℤ, A (k + (m : ℤ)) = A k + 1
  /-- the angle `B` is periodic up to `θ ↦ θ + 1`. -/
  B_add : ∀ k : ℤ, B (k + (m : ℤ)) = B k + 1
  /-- the landing point is periodic. -/
  Y_add : ∀ k : ℤ, Y (k + (m : ℤ)) = Y k
  /-- the first angle of a pair precedes the second. -/
  A_lt_B : ∀ k : ℤ, A k < B k
  /-- the second angle of a pair precedes the first angle of the next pair. -/
  B_lt_A : ∀ k : ℤ, B k < A (k + 1)
  /-- the landing points of different pairs are different (`ps` is `Pairwise` distinct). -/
  Y_inj : ∀ k k' : ℤ, Y k = Y k' → ∃ q : ℤ, k' = k + (m : ℤ) * q
  /-- the landing points lie in the filled Julia set. -/
  Y_mem_K : ∀ k : ℤ, Y k ∈ Work.EL.K c

/-- `D.Matches ps` says that the cyclic lift `D` is a lift of the list `ps`: the `i`-th pair of
the list is the pair of index `i + m q` of the lift, for some `q : ℤ`. -/
def CycLift.Matches {hN : Work.EL.DynB c φ} (D : CycLift hN) (ps : List (Work.EL.CoPair hN)) :
    Prop :=
  D.m = ps.length ∧ ∀ i : Fin ps.length, ∃ k : ℤ, ∃ q : ℤ,
    k = (i : ℤ) + (ps.length : ℤ) * q ∧ D.A k = (ps.get i).a + (q : ℝ) ∧
      D.B k = (ps.get i).b + (q : ℝ) ∧ D.Y k = (ps.get i).y

namespace CycLift

variable {hN : Work.EL.DynB c φ} (D : CycLift hN)

theorem m_pos : 0 < (D.m : ℤ) := by exact_mod_cast D.hm

/-- Periodicity of `A` under a single backward shift. -/
theorem A_sub_m (k : ℤ) : D.A (k - (D.m : ℤ)) = D.A k - 1 := by
  have h := D.A_add (k - (D.m : ℤ))
  rw [sub_add_cancel] at h
  linarith

theorem B_sub_m (k : ℤ) : D.B (k - (D.m : ℤ)) = D.B k - 1 := by
  have h := D.B_add (k - (D.m : ℤ))
  rw [sub_add_cancel] at h
  linarith

theorem Y_sub_m (k : ℤ) : D.Y (k - (D.m : ℤ)) = D.Y k := by
  have h := D.Y_add (k - (D.m : ℤ))
  rw [sub_add_cancel] at h
  exact h.symm

theorem A_one_sub_m : D.A (1 - (D.m : ℤ)) = D.A 1 - 1 := by
  have h := D.A_sub_m 1
  simpa using h

theorem B_zero_sub_m : D.B (-(D.m : ℤ)) = D.B 0 - 1 := by
  have h := D.B_sub_m 0
  simpa using h

/-- Periodicity of `A` under any integer shift of the index. -/
theorem A_shift (k q : ℤ) : D.A (k + (D.m : ℤ) * q) = D.A k + (q : ℝ) := by
  induction q using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h1 : k + (D.m : ℤ) * (↑i + 1) = (k + (D.m : ℤ) * ↑i) + (D.m : ℤ) := by ring
      rw [h1, D.A_add, ih]
      push_cast
      ring
  | pred i ih =>
      have h1 : k + (D.m : ℤ) * (-↑i - 1) = (k + (D.m : ℤ) * (-↑i)) - (D.m : ℤ) := by ring
      rw [h1, D.A_sub_m, ih]
      push_cast
      ring

theorem B_shift (k q : ℤ) : D.B (k + (D.m : ℤ) * q) = D.B k + (q : ℝ) := by
  induction q using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h1 : k + (D.m : ℤ) * (↑i + 1) = (k + (D.m : ℤ) * ↑i) + (D.m : ℤ) := by ring
      rw [h1, D.B_add, ih]
      push_cast
      ring
  | pred i ih =>
      have h1 : k + (D.m : ℤ) * (-↑i - 1) = (k + (D.m : ℤ) * (-↑i)) - (D.m : ℤ) := by ring
      rw [h1, D.B_sub_m, ih]
      push_cast
      ring

theorem Y_shift (k q : ℤ) : D.Y (k + (D.m : ℤ) * q) = D.Y k := by
  induction q using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h1 : k + (D.m : ℤ) * (↑i + 1) = (k + (D.m : ℤ) * ↑i) + (D.m : ℤ) := by ring
      rw [h1, D.Y_add, ih]
  | pred i ih =>
      have h1 : k + (D.m : ℤ) * (-↑i - 1) = (k + (D.m : ℤ) * (-↑i)) - (D.m : ℤ) := by ring
      rw [h1, D.Y_sub_m, ih]

/-! ## Monotonicity of the lifted angles -/

theorem A_lt_A_succ (k : ℤ) : D.A k < D.A (k + 1) := by
  have h1 := D.A_lt_B k
  have h2 := D.B_lt_A k
  linarith

theorem B_lt_B_succ (k : ℤ) : D.B k < D.B (k + 1) := by
  have h1 := D.B_lt_A k
  have h2 := D.A_lt_B (k + 1)
  linarith

theorem A_le_add_nat (k : ℤ) (n : ℕ) : D.A k ≤ D.A (k + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 : D.A (k + (n : ℤ)) < D.A (k + (n : ℤ) + 1) := D.A_lt_A_succ _
      have h3 : k + (n : ℤ) + 1 = k + (((n : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h3] at h2
      linarith

theorem B_le_add_nat (k : ℤ) (n : ℕ) : D.B k ≤ D.B (k + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h2 : D.B (k + (n : ℤ)) < D.B (k + (n : ℤ) + 1) := D.B_lt_B_succ _
      have h3 : k + (n : ℤ) + 1 = k + (((n : ℕ) + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h3] at h2
      linarith

theorem A_le_of_le {k k' : ℤ} (h : k ≤ k') : D.A k ≤ D.A k' := by
  have hnn : 0 ≤ k' - k := by linarith
  have hcast : (((k' - k).toNat : ℕ) : ℤ) = k' - k := Int.toNat_of_nonneg hnn
  have hk : k' = k + (((k' - k).toNat : ℕ) : ℤ) := by
    rw [hcast]
    ring
  rw [hk]
  exact D.A_le_add_nat k (k' - k).toNat

theorem B_le_of_le {k k' : ℤ} (h : k ≤ k') : D.B k ≤ D.B k' := by
  have hnn : 0 ≤ k' - k := by linarith
  have hcast : (((k' - k).toNat : ℕ) : ℤ) = k' - k := Int.toNat_of_nonneg hnn
  have hk : k' = k + (((k' - k).toNat : ℕ) : ℤ) := by
    rw [hcast]
    ring
  rw [hk]
  exact D.B_le_add_nat k (k' - k).toNat

theorem A_lt_of_lt {k k' : ℤ} (h : k < k') : D.A k < D.A k' := by
  have h1 : k + 1 ≤ k' := by omega
  have h2 := D.A_lt_A_succ k
  have h3 := D.A_le_of_le h1
  linarith

theorem B_lt_of_lt {k k' : ℤ} (h : k < k') : D.B k < D.B k' := by
  have h1 : k + 1 ≤ k' := by omega
  have h2 := D.B_lt_B_succ k
  have h3 := D.B_le_of_le h1
  linarith

theorem A_lt_A_zero {k : ℤ} (h : k < 0) : D.A k < D.A 0 := D.A_lt_of_lt h

/-! ## The interleaving inequalities -/

theorem A_lt_B_of_lt {k k' : ℤ} (h : k < k') : D.A k < D.B k' := by
  have h1 : k + 1 ≤ k' := by omega
  have h2 := D.A_lt_A_succ k
  have h3 := D.A_le_of_le h1
  have h4 := D.A_lt_B k'
  linarith

theorem B_lt_A_of_lt {k k' : ℤ} (h : k < k') : D.B k < D.A k' := by
  have h1 : k + 1 ≤ k' := by omega
  have h2 := D.B_lt_A k
  have h3 := D.A_le_of_le h1
  linarith

theorem A_lt_B_of_le {k k' : ℤ} (h : k ≤ k') : D.A k < D.B k' := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact D.A_lt_B k
  · exact D.A_lt_B_of_lt hlt

/-- The second angle of a pair is less than the first angle of that pair plus `1`. -/
theorem B_lt_A_add_one (k : ℤ) : D.B k < D.A k + 1 := by
  have h1 : k + 1 ≤ k + (D.m : ℤ) := by
    have := D.m_pos
    linarith
  have h2 : D.A (k + 1) ≤ D.A (k + (D.m : ℤ)) := D.A_le_of_le h1
  rw [D.A_add] at h2
  have h3 : D.B k < D.A (k + 1) := D.B_lt_A k
  linarith

/-! ## The window in which the congruence arguments take place -/

/-- All the angles `A k` of the pairs `k ∈ [1-m, 0]` lie in the window `[A 0 - 1, A 0]`,
which has length `< 1`. -/
theorem A_window {k : ℤ} (h1 : 1 - (D.m : ℤ) ≤ k) (h2 : k ≤ 0) :
    D.A 0 - 1 < D.A k ∧ D.A k ≤ D.A 0 := by
  have hA1 : D.A 0 < D.A 1 := D.A_lt_of_lt (by norm_num)
  have hk : D.A (1 - (D.m : ℤ)) ≤ D.A k := D.A_le_of_le h1
  rw [D.A_one_sub_m] at hk
  exact ⟨by linarith, D.A_le_of_le h2⟩

/-- The angles `B k` of the pairs `k ∈ [-m, -1]` lie in the window `[B 0 - 1, B 0)`. -/
theorem B_window {k : ℤ} (h1 : -(D.m : ℤ) ≤ k) (h2 : k ≤ -1) :
    D.B 0 - 1 ≤ D.B k ∧ D.B k < D.B 0 := by
  have hk : D.B (-(D.m : ℤ)) ≤ D.B k := D.B_le_of_le h1
  rw [D.B_zero_sub_m] at hk
  exact ⟨hk, D.B_lt_of_lt (by omega)⟩

/-- The window `[B 0 - 1, A 0]` has length `< 1`. -/
theorem window_lt_one : D.A 0 - (D.B 0 - 1) < 1 := by
  have h := D.A_lt_B 0
  linarith

/-- Two angles of the window `[B 0 - 1, A 0]` which are congruent modulo `1` are equal. -/
theorem angle_eq_of_int_sub {x y : ℝ} (hx : D.B 0 - 1 ≤ x) (hx' : x ≤ D.A 0)
    (hy : D.B 0 - 1 ≤ y) (hy' : y ≤ D.A 0) (h : ∃ n : ℤ, y = x + (n : ℝ)) : y = x := by
  obtain ⟨n, hn⟩ := h
  have h1 : y - x = (n : ℝ) := by linarith
  have h2 : |y - x| < 1 := by
    rw [abs_lt]
    exact ⟨by linarith [D.window_lt_one], by linarith [D.window_lt_one]⟩
  obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
  have h5 : (n : ℝ) < 1 := by linarith
  have h6 : (-1 : ℤ) < n := by
    have h6' : (-1 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h6'
  have h7 : n < 1 := by exact_mod_cast h5
  have h8 : n = 0 := by omega
  rw [h8] at h1
  simp at h1
  linarith

end CycLift

/-! ## The ray arcs, the equipotential arcs and the blocks -/

/-- The closed ray piece of angle `β`, parametrized by the *potential level* `t ∈ [1,R]`:
at level `1` it is the landing point `y`, above level `1` the ray point. -/
def rayArc (hN : Work.EL.DynB c φ) (β : ℝ) (y : ℂ) (t : ℝ) : ℂ :=
  if t = 1 then y else Work.EL.rayPt hN β t

/-- The equipotential arc of level `R` between the angles `β₁` and `β₂`, parametrized by
`u ∈ [0,1]`. -/
def eqArcPt (hN : Work.EL.DynB c φ) (β₁ β₂ R : ℝ) (u : ℝ) : ℂ :=
  Work.EL.rayPt hN (β₁ + u * (β₂ - β₁)) R

/-- The potential level at which the point of the polygon of parameter `σ ∈ [0,1]` on the
block `k` is taken: the ray `A k` is traversed from level `1` up to `R` on the first third,
the equipotential arc at level `R` on the second third, and the ray `B (k-1)` back down to
level `1` on the last third. -/
def blkLev (R σ : ℝ) : ℝ :=
  if σ ≤ 1 / 3 then 1 + 3 * σ * (R - 1) else if σ ≤ 2 / 3 then R else 1 + (3 - 3 * σ) * (R - 1)

/-- The external angle of the point of the polygon of parameter `σ ∈ [0,1]` on the block `k`:
the angle is `A k` on the first third, runs from `A k` down to `B (k-1)` on the second
third, and is `B (k-1)` on the last third. -/
def blkAng {hN : Work.EL.DynB c φ} (D : CycLift hN) (k : ℤ) (σ : ℝ) : ℝ :=
  if σ ≤ 1 / 3 then D.A k
  else if σ ≤ 2 / 3 then D.A k + (3 * σ - 1) * (D.B (k - 1) - D.A k)
  else D.B (k - 1)

/-- The `k`-th block of the parametrization of the polygon, on `σ ∈ [0,1]`: the ray `A k` is
traversed from its landing point `Y k` up to level `R` on the first third (in particular at
`σ = 0` the block starts at `Y k`), the equipotential arc from `A k` back to `B (k-1)` is
traversed on the second third, and the ray `B (k-1)` is traversed back down to `Y (k-1)` on
the last third (at `σ = 1` the block ends at `Y (k-1)`). -/
def cycBlock {hN : Work.EL.DynB c φ} (D : CycLift hN) (R : ℝ) (k : ℤ) (σ : ℝ) : ℂ :=
  if σ ≤ 1 / 3 then rayArc hN (D.A k) (D.Y k) (1 + 3 * σ * (R - 1))
  else if σ ≤ 2 / 3 then eqArcPt hN (D.A k) (D.B (k - 1)) R (3 * σ - 1)
  else rayArc hN (D.B (k - 1)) (D.Y (k - 1)) (1 + (3 - 3 * σ) * (R - 1))

/-- The parametrization of the polygon by `s ∈ [0,1]`: on the `ℓ`-th subinterval the block
number `-ℓ` is traversed from `Y (-ℓ)` to `Y (-ℓ-1)`. -/
def cycParam {hN : Work.EL.DynB c φ} (D : CycLift hN) (R : ℝ) (s : ℝ) : ℂ :=
  cycBlock D R (-⌊(D.m : ℝ) * s⌋) ((D.m : ℝ) * s - ⌊(D.m : ℝ) * s⌋)

/-! ## Elementary properties of the block parameters -/

theorem blkLev_branch1 {R σ : ℝ} (h : σ ≤ 1 / 3) : blkLev R σ = 1 + 3 * σ * (R - 1) := by
  rw [blkLev, if_pos h]

theorem blkLev_branch2 {R σ : ℝ} (h1 : ¬ σ ≤ 1 / 3) (h2 : σ ≤ 2 / 3) : blkLev R σ = R := by
  rw [blkLev, if_neg h1, if_pos h2]

theorem blkLev_branch3 {R σ : ℝ} (h1 : ¬ σ ≤ 1 / 3) (h2 : ¬ σ ≤ 2 / 3) :
    blkLev R σ = 1 + (3 - 3 * σ) * (R - 1) := by
  rw [blkLev, if_neg h1, if_neg h2]

theorem blkAng_branch1 {hN : Work.EL.DynB c φ} {D : CycLift hN} {k : ℤ} {σ : ℝ}
    (h : σ ≤ 1 / 3) : blkAng D k σ = D.A k := by
  rw [blkAng, if_pos h]

theorem blkAng_branch2 {hN : Work.EL.DynB c φ} {D : CycLift hN} {k : ℤ} {σ : ℝ}
    (h1 : ¬ σ ≤ 1 / 3) (h2 : σ ≤ 2 / 3) :
    blkAng D k σ = D.A k + (3 * σ - 1) * (D.B (k - 1) - D.A k) := by
  rw [blkAng, if_neg h1, if_pos h2]

theorem blkAng_branch3 {hN : Work.EL.DynB c φ} {D : CycLift hN} {k : ℤ} {σ : ℝ}
    (h1 : ¬ σ ≤ 1 / 3) (h2 : ¬ σ ≤ 2 / 3) : blkAng D k σ = D.B (k - 1) := by
  rw [blkAng, if_neg h1, if_neg h2]

/-- On the fundamental domain `σ ∈ [0,1)` the block is given by the external angle `blkAng`
and the potential level `blkLev`; at `σ = 0` it is the landing point of the pair. -/
theorem cycBlock_eq_blk {hN : Work.EL.DynB c φ} (D : CycLift hN) {R : ℝ} (hR : 1 < R)
    {k : ℤ} {σ : ℝ} (hσ : σ ∈ Set.Ico 0 1) :
    cycBlock D R k σ = if σ = 0 then D.Y k else Work.EL.rayPt hN (blkAng D k σ) (blkLev R σ) := by
  by_cases h1 : σ ≤ 1 / 3
  · rw [cycBlock, if_pos h1, rayArc, blkAng_branch1 h1, blkLev_branch1 h1]
    by_cases h0 : σ = 0
    · simp [h0]
    · have ht : 1 + 3 * σ * (R - 1) ≠ 1 := by
        intro hh
        have h2 : σ * (3 * (R - 1)) = 0 := by linarith
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact h0 h3
        · linarith
      rw [if_neg ht, if_neg h0]
  · by_cases h2 : σ ≤ 2 / 3
    · have h0 : σ ≠ 0 := by linarith
      rw [cycBlock, if_neg h1, if_pos h2, eqArcPt, blkAng_branch2 h1 h2, blkLev_branch2 h1 h2,
        if_neg h0]
    · have h0 : σ ≠ 0 := by linarith
      rw [cycBlock, if_neg h1, if_neg h2, rayArc, blkAng_branch3 h1 h2, blkLev_branch3 h1 h2]
      have ht : 1 + (3 - 3 * σ) * (R - 1) ≠ 1 := by
        intro hh
        have h3 : (σ - 1) * (3 * (R - 1)) = 0 := by nlinarith [hh]
        rcases mul_eq_zero.mp h3 with h4 | h4
        · linarith [hσ.2]
        · linarith
      rw [if_neg ht, if_neg h0]

/-- The angle of the point of the block `k` of parameter `σ ∈ [0,1]` lies in the closed
interval `[B (k-1), A k]`. -/
theorem blkAng_mem {hN : Work.EL.DynB c φ} (D : CycLift hN) {k : ℤ} {σ : ℝ}
    (hσ : σ ∈ Set.Icc 0 1) : blkAng D k σ ∈ Set.Icc (D.B (k - 1)) (D.A k) := by
  have hAB : D.B (k - 1) < D.A k := by
    have h := D.B_lt_A (k - 1)
    simpa using h
  by_cases h1 : σ ≤ 1 / 3
  · rw [blkAng_branch1 h1]
    exact ⟨le_of_lt hAB, le_refl _⟩
  · by_cases h2 : σ ≤ 2 / 3
    · rw [blkAng_branch2 h1 h2]
      constructor
      · nlinarith [hσ.1, hAB]
      · nlinarith [hσ.2, hAB]
    · rw [blkAng_branch3 h1 h2]
      exact ⟨le_refl _, le_of_lt hAB⟩

/-- The potential level of the point of the block of parameter `σ ∈ (0,1)` lies in `(1,R]`. -/
theorem blkLev_mem {R σ : ℝ} (hR : 1 < R) (hσ : σ ∈ Set.Ico 0 1) (h0 : σ ≠ 0) :
    1 < blkLev R σ ∧ blkLev R σ ≤ R := by
  have hpos : 0 < σ := lt_of_le_of_ne hσ.1 (Ne.symm h0)
  have hRm1 : 0 < R - 1 := by linarith
  by_cases h1 : σ ≤ 1 / 3
  · rw [blkLev_branch1 h1]
    have h3 : 0 ≤ (1 - 3 * σ) * (R - 1) := by
      have : 0 ≤ 1 - 3 * σ := by linarith
      exact mul_nonneg this (le_of_lt hRm1)
    have h4 : 0 < 3 * σ * (R - 1) := by
      have : 0 < 3 * σ := by linarith
      exact mul_pos this hRm1
    constructor <;> linarith
  · by_cases h2 : σ ≤ 2 / 3
    · rw [blkLev_branch2 h1 h2]
      exact ⟨hR, le_refl _⟩
    · rw [blkLev_branch3 h1 h2]
      have hσ' : σ < 1 := hσ.2
      have h5 : 0 < (3 - 3 * σ) * (R - 1) := by
        have : 0 < 3 - 3 * σ := by linarith
        exact mul_pos this hRm1
      have h6 : (3 * σ - 2) * (R - 1) ≥ 0 := by
        have : 0 ≤ 3 * σ - 2 := by linarith
        exact mul_nonneg this (le_of_lt hRm1)
      constructor <;> linarith

end Work.ELTop
