import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic

/-!
# Grid covering for the measure-zero set `Lset` (`Work.HP.Lset_zero`)

The unit sphere `S^n ⊆ ℝ^{n+1}` is covered by the rescaled grid points `z/N` of the lattice
`(1/N)ℤ^{n+1}` (restricted to the integer box `∏ᵢ [-N,N]`).  This is the finite net used to prove
that the set `Lset d n` of coefficient vectors of degree-`d` forms in the unit ball that have a
*degenerate* real zero has measure zero: at such a zero `x`, the Taylor and Lipschitz hypotheses
show that a nearby net point `w` (a unit vector, hence with a coordinate `≥ 1/(n+1)`) is a point
where both `f_a(w)` and `∇f_a(w)` are small; the slab estimate `hslab` bounds the volume of the
corresponding coefficient region by `≍ ε δ^n ≍ N^{-(n+2)}`, while there are only `≍ N^{n+1}` net
points.

Definitions here:

* `gbox n N` : the integer box `∏ᵢ [-N, N]`, the index set of the grid;
* `gy n N z` : the grid point `z / N`;
* `gw n N z` : `gy n N z` rescaled to the unit sphere;
* `gEps n N C2`, `gDel n N C1` : the values of `ε` and `δ` used at such a point;
* `gS d n N C1 C2 z` : the "slab-type" coefficient set attached to a grid point.
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP.LsetAux

/-- The coordinate box `∏ᵢ [-N, N] ⊆ ℤ^{n+1}`. -/
def gbox (n N : ℕ) : Finset (Fin (n + 1) → ℤ) :=
  Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc (-(N : ℤ)) (N : ℤ))

/-- The point `z / N ∈ ℝ^{n+1}` of the grid `(1/N) ℤ^{n+1}`. -/
def gy (n N : ℕ) (z : Fin (n + 1) → ℤ) : Fin (n + 1) → ℝ :=
  fun i => (z i : ℝ) / (N : ℝ)

/-- The grid point `z/N` rescaled to the unit sphere. -/
def gw (n N : ℕ) (z : Fin (n + 1) → ℤ) : Fin (n + 1) → ℝ :=
  (1 / Work.HP.rNorm (gy n N z)) • gy n N z

/-- The value of `ε` at a grid point: `4 C (n+1) / N²` (the Taylor error at distance `2√(n+1)/N`). -/
def gEps (n N : ℕ) (C2 : ℝ) : ℝ := 4 * C2 * ((n : ℝ) + 1) / (N : ℝ) ^ 2

/-- The value of `δ` at a grid point: `2 C √(n+1) / N` (the Lipschitz gradient error). -/
def gDel (n N : ℕ) (C1 : ℝ) : ℝ := 2 * C1 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)

/-- The "slab-type" coefficient set attached to a grid point `z`: coefficient vectors in the unit
ball where `f_a` and `∇f_a` are both small at the unit vector `gw n N z`. -/
def gS (d n N : ℕ) (C1 C2 : ℝ) (z : Fin (n + 1) → ℤ) : Set (Work.HP.Mon d n → ℝ) :=
  {a | Work.HP.rNorm a ≤ 1 ∧ |Work.HP.formEvalR d n a (gw n N z)| ≤ gEps n N C2 ∧
    ∀ j : Fin (n + 1), |Work.HP.gradVec d n a (gw n N z) j| ≤ gDel n N C1}

lemma gy_eq_zero_iff {n N : ℕ} (hN : N ≠ 0) (z : Fin (n + 1) → ℤ) :
    gy n N z = 0 ↔ z = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  constructor
  · intro h
    funext i
    have hi : (z i : ℝ) / (N : ℝ) = 0 := by
      have := congrFun h i
      simpa [gy] using this
    have hzi : (z i : ℝ) = 0 := by
      rcases (div_eq_zero_iff).mp hi with h' | h'
      · exact h'
      · exact absurd h' hN'
    exact_mod_cast hzi
  · rintro rfl
    funext i
    simp [gy]

lemma gy_ne_zero {n N : ℕ} (hN : N ≠ 0) {z : Fin (n + 1) → ℤ} (hz : z ≠ 0) :
    gy n N z ≠ 0 := fun h => hz ((gy_eq_zero_iff hN z).mp h)

/-- The grid point `z/N` has a nonzero norm as long as `z ≠ 0` and `N ≠ 0`. -/
lemma rNorm_gy_ne_zero {n N : ℕ} (hN : N ≠ 0) {z : Fin (n + 1) → ℤ} (hz : z ≠ 0) :
    Work.HP.rNorm (gy n N z) ≠ 0 :=
  fun h => gy_ne_zero hN hz (Work.HP.rNorm_eq_zero.mp h)

/-- Rescaling a nonzero grid point to the unit sphere gives a unit vector. -/
lemma rNorm_gw {n N : ℕ} (hN : N ≠ 0) {z : Fin (n + 1) → ℤ} (hz : z ≠ 0) :
    Work.HP.rNorm (gw n N z) = 1 := by
  have hne := rNorm_gy_ne_zero hN hz
  have hpos : 0 < Work.HP.rNorm (gy n N z) :=
    lt_of_le_of_ne (Work.HP.rNorm_nonneg _) (Ne.symm hne)
  rw [gw, Work.HP.rNorm_smul', abs_of_pos (one_div_pos.mpr hpos), one_div,
    inv_mul_cancel₀ hne]

/-- On the unit sphere some coordinate has absolute value at least `1/(n+1)`.  This is the side
condition required by the slab estimate `hslab`. -/
lemma exists_coord_ge_one_div (n : ℕ) {w : Fin (n + 1) → ℝ} (hw : Work.HP.rNorm w = 1) :
    ∃ i, 1 / ((n : ℝ) + 1) ≤ |w i| := by
  by_contra h
  push Not at h
  have hterm : ∀ i : Fin (n + 1), (w i) ^ 2 < (1 / ((n : ℝ) + 1)) ^ 2 := fun i => by
    rw [← sq_abs (w i)]
    exact pow_lt_pow_left₀ (h i) (abs_nonneg (w i)) (by norm_num)
  have hsum : ∑ i : Fin (n + 1), (w i) ^ 2 <
      ∑ _i : Fin (n + 1), (1 / ((n : ℝ) + 1)) ^ 2 := by
    simpa using Finset.sum_lt_sum_of_nonempty
      (s := (Finset.univ : Finset (Fin (n + 1))))
      ⟨⟨0, Nat.succ_pos n⟩, Finset.mem_univ _⟩ (fun i _ => hterm i)
  have h2 : ∑ _i : Fin (n + 1), (1 / ((n : ℝ) + 1)) ^ 2 = 1 / ((n : ℝ) + 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  rw [h2] at hsum
  have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h4 : ∑ i : Fin (n + 1), (w i) ^ 2 = 1 := by
    rw [← Work.HP.rNorm_sq w, hw]
    norm_num
  linarith

end Work.HP.LsetAux
