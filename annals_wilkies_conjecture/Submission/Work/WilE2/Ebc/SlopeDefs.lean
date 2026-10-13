/-
  `Work.WilE2.Ebc.SlopeDefs` — vocabulary for `Work.WilE2.Ebc.exists_generic_slope`.

  Given `F : ℝ^k → ℝ` we write `pderiv F i x` for the partial derivative `∂_i F (x)`,
  realised as `fderiv ℝ F x (Pi.single i 1)` — exactly the expression appearing in the
  statement of `exists_generic_slope`.

  The interesting statements are indexed by the *number* `m` of coordinates different from a
  fixed `i : Fin (m+1)`, so the "other coordinates" form `Fin m` (`i.succAbove`).

  Fixing such an `i`, the *slope* of the level set `{F = 0}` in the `j`-th direction is the
  quotient `∂_j F / ∂_i F`.  A point `x` of the level set is *bad* for a slope `c` if the
  first-order conditions `∂_j F (x) = c_j ∂_i F (x)` (all `j ≠ i`) hold and there is a nonzero
  tangent vector `v` at `x` which is also annihilated by the derivative of all the differences
  `∂_j F - c_j ∂_i F`.  `badSlope` is the set of such `c`; the content of
  `exists_generic_slope` is that `badSlope` is Lebesgue-null, so that `c` can be chosen in any
  prescribed ball.

  We also package the local graph parametrisation of the level set: `graphMap i h u` is the
  point `insertNth i (h u) u`, and `graphSlope F i h` is the slope map computed on that graph.
-/
import Mathlib
import Submission.Work.WilE2.Ebc.Defs

set_option autoImplicit false

noncomputable section

open Classical
open scoped Topology

namespace Work.WilE2.Ebc

/-- The `i`-th partial derivative of `F`, as a function of the base point. -/
def pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i : Fin k) (x : Fin k → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

@[simp] theorem pderiv_apply {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i : Fin k) (x : Fin k → ℝ) :
    pderiv F i x = fderiv ℝ F x (Pi.single i 1) := rfl

/-- If `F` is `C²` then each of its partial derivatives is `C¹`. -/
theorem contDiff_one_pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin k) :
    ContDiff ℝ 1 (pderiv F i) := by
  change ContDiff ℝ 1 (fun x : Fin k → ℝ => fderiv ℝ F x (Pi.single i 1))
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

/-- A `C²` function has `C¹` partial derivatives, hence they are differentiable everywhere. -/
theorem differentiable_pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin k) :
    Differentiable ℝ (pderiv F i) :=
  (contDiff_one_pderiv F hF i).differentiable (by norm_num)

/-- A `C²` function has `C¹` partial derivatives, hence differentiable at every point. -/
theorem differentiableAt_pderiv {k : ℕ} (F : (Fin k → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin k) (x : Fin k → ℝ) : DifferentiableAt ℝ (pderiv F i) x :=
  (differentiable_pderiv F hF i) x

/-- A differential vanishes when all partial derivatives vanish. -/
theorem fderiv_eq_zero_of_forall_pderiv_eq_zero {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    {x : Fin k → ℝ} (h : ∀ i, pderiv F i x = 0) : fderiv ℝ F x = 0 := by
  ext v
  rw [zero_apply]
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℝ) : Fin k → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, smul_eq_mul,
    show (fderiv ℝ F x) (Pi.single i 1) = 0 from h i, mul_zero]

/-- The slope condition at a point `x`: the slope of the level set in the directions `≠ i` is
`c`. -/
def SlopeCond {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (c : Fin m → ℝ)
    (x : Fin (m+1) → ℝ) : Prop :=
  ∀ l : Fin m, pderiv F (i.succAbove l) x = c l * pderiv F i x

/-- The degeneracy condition at a point `x` with slope `c`: some nonzero tangent vector to the
level set is annihilated by the derivative of all the differences `∂_j F - c_j ∂_i F`. -/
def BadAt {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (c : Fin m → ℝ)
    (x : Fin (m+1) → ℝ) : Prop :=
  SlopeCond F i c x ∧ ∃ v : Fin (m+1) → ℝ, v ≠ 0 ∧ fderiv ℝ F x v = 0 ∧
    ∀ l : Fin m,
      fderiv ℝ (fun y => pderiv F (i.succAbove l) y - c l * pderiv F i y) x v = 0

/-- The set of "bad" slopes: those `c` for which the level set `{F = 0}` has a degenerate point
of slope `c`.  This is the set that `exists_generic_slope` has to avoid. -/
def badSlope {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) : Set (Fin m → ℝ) :=
  {c | ∃ x : Fin (m+1) → ℝ, F x = 0 ∧ BadAt F i c x}

/-- The part of the bad set generated in a ball of radius `R` around `x₀`. -/
def locBad {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1)) (x₀ : Fin (m+1) → ℝ)
    (R : ℝ) : Set (Fin m → ℝ) :=
  {c | ∃ x : Fin (m+1) → ℝ, dist x x₀ < R ∧ F x = 0 ∧ BadAt F i c x}

theorem mem_badSlope {m : ℕ} {F : (Fin (m+1) → ℝ) → ℝ} {i : Fin (m+1)} {c : Fin m → ℝ} :
    c ∈ badSlope F i ↔ ∃ x : Fin (m+1) → ℝ, F x = 0 ∧ BadAt F i c x := Iff.rfl

theorem mem_locBad {m : ℕ} {F : (Fin (m+1) → ℝ) → ℝ} {i : Fin (m+1)}
    {x₀ : Fin (m+1) → ℝ} {R : ℝ} {c : Fin m → ℝ} :
    c ∈ locBad F i x₀ R ↔
      ∃ x : Fin (m+1) → ℝ, dist x x₀ < R ∧ F x = 0 ∧ BadAt F i c x := Iff.rfl

/-- **The slope condition determines the slope.**  If `x` is a zero of `F` at which the slope
condition for `c` holds, then `∂_i F x ≠ 0`, so that `c` is the slope of `x`. -/
theorem pderiv_ne_zero_of_slopeCond {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0) {i : Fin (m+1)} {x : Fin (m+1) → ℝ}
    (hx : F x = 0) {c : Fin m → ℝ} (hc : SlopeCond F i c x) : pderiv F i x ≠ 0 := by
  intro h0
  refine hreg x hx (fderiv_eq_zero_of_forall_pderiv_eq_zero fun j => ?_)
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
  · rw [h]; exact h0
  · rw [hl, hc l, h0, mul_zero]

/-- The graph of the local solution `h` of `F = 0`. -/
def graphMap {m : ℕ} (i : Fin (m+1)) (h : (Fin m → ℝ) → ℝ) :
    (Fin m → ℝ) → (Fin (m+1) → ℝ) :=
  fun u => Fin.insertNth i (h u) u

@[simp] theorem graphMap_apply {m : ℕ} (i : Fin (m+1)) (h : (Fin m → ℝ) → ℝ)
    (u : Fin m → ℝ) : graphMap i h u = Fin.insertNth i (h u) u := rfl

/-- The slope map computed on the graph of `h`. -/
def graphSlope {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1))
    (h : (Fin m → ℝ) → ℝ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun u l => pderiv F (i.succAbove l) (graphMap i h u) / pderiv F i (graphMap i h u)

@[simp] theorem graphSlope_apply {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (i : Fin (m+1))
    (h : (Fin m → ℝ) → ℝ) (u : Fin m → ℝ) (l : Fin m) :
    graphSlope F i h u l = pderiv F (i.succAbove l) (graphMap i h u)
      / pderiv F i (graphMap i h u) := rfl

end Work.WilE2.Ebc
