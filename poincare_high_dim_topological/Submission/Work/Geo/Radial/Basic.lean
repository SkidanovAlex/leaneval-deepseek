import Mathlib
import Submission.Work.PL.Defs

/-!
# Radial geometry of sup-norm cubes in `ℝⁿ`

Area `A7` of the blueprint `Submission/Work/NOTES_LEAD_poincare_blueprint.md`
(`Geo/Radial+Conn-rel`).  This file owns the vocabulary of "sup-norm cubes centred at an
arbitrary point" and the elementary geometry of the radial push used by the cell-count
reduction (blueprint §3, C1 / G9).

Everything here is about `PL.E n = ℝⁿ` with the sup-norm cubes of the frozen vocabulary
`PL.closedCube r`, `PL.openCube r`:

* `ocubeAround q r` : `{y | ∀ i, |y i - q i| < r}` (so `ocubeAround 0 r = PL.openCube r`);
* `ccubeAround q r` : the closed version (so `ccubeAround 0 r = PL.closedCube r`).

The main structural results are the ones the radial push needs: a point outside a closed cube,
pushed radially outward from a point of the cube, stays outside the cube
(`scale_notMem_closedCube`), together with the openness/compactness/convexity API.

The radial pushes themselves (blueprint G9 `radial_expand`, and the sup-norm family
`exists_radial_push` which is what the cube-chart argument uses) live in
`Submission/Work/Geo/Radial/Push/`.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Radial

variable {n : ℕ}

/-- The open sup-norm cube of radius `r` centred at `q`. -/
def ocubeAround (q : PL.E n) (r : ℝ) : Set (PL.E n) := {y | ∀ i, |y i - q i| < r}

/-- The closed sup-norm cube of radius `r` centred at `q`. -/
def ccubeAround (q : PL.E n) (r : ℝ) : Set (PL.E n) := {y | ∀ i, |y i - q i| ≤ r}

@[simp] theorem mem_ocubeAround {q y : PL.E n} {r : ℝ} :
    y ∈ ocubeAround q r ↔ ∀ i, |y i - q i| < r := Iff.rfl

@[simp] theorem mem_ccubeAround {q y : PL.E n} {r : ℝ} :
    y ∈ ccubeAround q r ↔ ∀ i, |y i - q i| ≤ r := Iff.rfl

@[simp] theorem ocubeAround_zero (r : ℝ) :
    ocubeAround (0 : PL.E n) r = PL.openCube r := by
  ext y; simp [PL.openCube, ocubeAround]

@[simp] theorem ccubeAround_zero (r : ℝ) :
    ccubeAround (0 : PL.E n) r = PL.closedCube r := by
  ext y; simp [PL.closedCube, ccubeAround]

theorem ocubeAround_subset_ccubeAround {q : PL.E n} {r : ℝ} :
    ocubeAround q r ⊆ ccubeAround q r := fun _ hy i => le_of_lt (hy i)

theorem ccubeAround_mono {q : PL.E n} {r r' : ℝ} (h : r ≤ r') :
    ccubeAround q r ⊆ ccubeAround q r' := fun _ hy i => le_trans (hy i) h

theorem ocubeAround_mono {q : PL.E n} {r r' : ℝ} (h : r ≤ r') :
    ocubeAround q r ⊆ ocubeAround q r' := fun _ hy i => lt_of_lt_of_le (hy i) h

theorem ccubeAround_subset_ocubeAround {q : PL.E n} {r r' : ℝ} (h : r < r') :
    ccubeAround q r ⊆ ocubeAround q r' := fun _ hy i => lt_of_le_of_lt (hy i) h

/-- Coordinatewise sup-norm bound: a vector all of whose coordinates are bounded by `δ` has
norm at most `√n · δ`. -/
theorem norm_le_sqrt_mul_of_abs_le {z : PL.E n} {δ : ℝ} (h : ∀ i, |z i| ≤ δ) :
    ‖z‖ ≤ Real.sqrt n * δ := by
  have h2 : ‖z‖ ^ 2 ≤ n * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (z i) ^ 2 ≤ ∑ _i : Fin n, δ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = n * δ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsqrt : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hz : ‖z‖ = 0 := by
      have hle : ‖z‖ ^ 2 ≤ 0 := by simpa using h2
      nlinarith [norm_nonneg z]
    rw [hz]
    simp
  · have hδ0 : 0 ≤ δ := le_trans (abs_nonneg (z ⟨0, hpos⟩)) (h ⟨0, hpos⟩)
    have h3 : ‖z‖ ^ 2 ≤ (Real.sqrt n * δ) ^ 2 := by
      rw [mul_pow, hsqrt]; exact h2
    nlinarith [norm_nonneg z, mul_nonneg (Real.sqrt_nonneg n) hδ0]

theorem isCompact_ccubeAround (q : PL.E n) (r : ℝ) : IsCompact (ccubeAround q r) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall q (Real.sqrt n * r)) ?_ ?_
  · have h : ccubeAround q r
        = ⋂ i : Fin n, (fun y : PL.E n => y i) ⁻¹' Icc (q i - r) (q i + r) := by
      ext y
      rw [ccubeAround, mem_ofPred_eq, mem_iInter]
      constructor
      · intro hy i
        rw [mem_preimage, mem_Icc]
        exact ⟨by linarith [(abs_le.mp (hy i)).1], by linarith [(abs_le.mp (hy i)).2]⟩
      · intro hy i
        simp only [mem_preimage, mem_Icc] at hy
        exact abs_le.mpr ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
    rw [h]
    exact isClosed_iInter fun i =>
      isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
  · intro y hy
    rw [mem_closedBall, dist_eq_norm]
    exact norm_le_sqrt_mul_of_abs_le fun i => by simpa using hy i

theorem isClosed_ccubeAround (q : PL.E n) (r : ℝ) : IsClosed (ccubeAround q r) :=
  (isCompact_ccubeAround q r).isClosed

theorem isOpen_ocubeAround (q : PL.E n) (r : ℝ) : IsOpen (ocubeAround q r) := by
  have h : ocubeAround q r
      = ⋂ i : Fin n, (fun y : PL.E n => |y i - q i|) ⁻¹' Ioo (-r) r := by
    ext y
    rw [ocubeAround, mem_ofPred_eq, mem_iInter]
    exact ⟨fun hy i => mem_preimage.mpr ⟨by linarith [abs_nonneg (y i - q i), hy i], hy i⟩,
      fun hy i => (mem_preimage.mp (hy i)).2⟩
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).sub
      continuous_const).abs)

theorem convex_ccubeAround (q : PL.E n) (r : ℝ) : Convex ℝ (ccubeAround q r) := by
  intro x hx y hy a b ha hb hab i
  have hsub : (a • x + b • y) i - q i = a * (x i - q i) + b * (y i - q i) := by
    have h : (a • x + b • y) i = a * x i + b * y i := by simp
    rw [h]
    have hq : a * q i + b * q i = q i := by rw [← add_mul, hab, one_mul]
    linarith
  rw [hsub]
  calc |a * (x i - q i) + b * (y i - q i)|
      ≤ |a * (x i - q i)| + |b * (y i - q i)| := abs_add_le _ _
    _ = a * |x i - q i| + b * |y i - q i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := by
        have h1 : |x i - q i| ≤ r := hx i
        have h2 : |y i - q i| ≤ r := hy i
        linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    _ = r := by rw [← add_mul, hab, one_mul]

/-- One-dimensional core of the radial push: a point beyond `β` on one side, pushed radially
outward away from a point `q` with `|q| ≤ m ≤ β`, stays beyond `β`. -/
theorem abs_scale_gt {β m q y lam : ℝ} (hβ : 0 ≤ β) (hq : |q| ≤ m) (hmβ : m ≤ β)
    (hy : β < |y|) (hlam : 1 ≤ lam) : β < |q + lam * (y - q)| := by
  have hqβ : |q| ≤ β := le_trans hq hmβ
  have hqle : -β ≤ q ∧ q ≤ β := abs_le.mp hqβ
  have hlam0 : 0 < lam := by linarith
  rcases lt_abs.mp hy with hy | hy
  · have hmono : β < lam * y + (1 - lam) * q := by
      have h2 : lam * β < lam * y := mul_lt_mul_of_pos_left hy hlam0
      have h3 : (1 - lam) * β ≤ (1 - lam) * q :=
        mul_le_mul_of_nonpos_left hqle.2 (by linarith)
      have h4 : lam * β + (1 - lam) * β = β := by ring
      linarith
    rw [show q + lam * (y - q) = lam * y + (1 - lam) * q by ring]
    rw [abs_of_pos (by linarith)]
    linarith
  · have hmono : lam * y + (1 - lam) * q < -β := by
      have h2 : lam * y < lam * (-β) := mul_lt_mul_of_pos_left (by linarith : y < -β) hlam0
      have h3 : (1 - lam) * q ≤ (1 - lam) * (-β) :=
        mul_le_mul_of_nonpos_left hqle.1 (by linarith)
      have h4 : lam * (-β) + (1 - lam) * (-β) = -β := by ring
      linarith
    rw [show q + lam * (y - q) = lam * y + (1 - lam) * q by ring]
    rw [abs_of_neg (by linarith)]
    linarith

/-- A point outside the closed cube `PL.closedCube β`, pushed radially outward from a point `q`
of the cube (with `1 ≤ λ`), stays outside the cube.  This is the geometric core of "the radial
push keeps the complement of the cube inside itself". -/
theorem scale_notMem_closedCube {β m : ℝ} (hβ0 : 0 ≤ β) {q y z : PL.E n}
    (hq : ∀ i, |q i| ≤ m) (hmβ : m ≤ β) (hy : y ∉ PL.closedCube β) {lam : ℝ} (hlam : 1 ≤ lam)
    (hz : ∀ i, z i - q i = lam * (y i - q i)) : z ∉ PL.closedCube β := by
  rw [PL.closedCube, mem_ofPred_eq, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  have hyi : β < |y i| := lt_of_not_ge hi
  rw [PL.closedCube, mem_ofPred_eq, not_forall]
  refine ⟨i, ?_⟩
  rw [not_le]
  have hzi : z i = q i + lam * (y i - q i) := by
    have := hz i; linarith
  rw [hzi]
  exact abs_scale_gt hβ0 (hq i) hmβ hyi hlam

/-- The open cube of radius `β₂` is contained in the open cube of radius `β₂ + m` around any
point `q` with `|q i| ≤ m`. -/
theorem openCube_subset_ocubeAround {β₂ m : ℝ} {q : PL.E n} (hq : ∀ i, |q i| ≤ m) :
    PL.openCube β₂ ⊆ ocubeAround q (β₂ + m) := by
  intro y hy i
  have hyi : |y i| < β₂ := hy i
  have hqi : |q i| ≤ m := hq i
  calc |y i - q i| = |y i + (-q i)| := by rw [sub_eq_add_neg]
    _ ≤ |y i| + |-q i| := abs_add_le _ _
    _ = |y i| + |q i| := by rw [abs_neg]
    _ < β₂ + m := by linarith

/-- The closed cube of radius `β` is contained in the open cube of radius `β + m` around any
point `q` with `|q i| ≤ m`. -/
theorem closedCube_subset_ocubeAround {β m R : ℝ} {q : PL.E n} (hq : ∀ i, |q i| ≤ m)
    (hR : β + m < R) : PL.closedCube β ⊆ ocubeAround q R := by
  intro y hy i
  have hyi : |y i| ≤ β := hy i
  have hqi : |q i| ≤ m := hq i
  calc |y i - q i| = |y i + (-q i)| := by rw [sub_eq_add_neg]
    _ ≤ |y i| + |-q i| := abs_add_le _ _
    _ = |y i| + |q i| := by rw [abs_neg]
    _ ≤ β + m := by linarith
    _ < R := hR

/-- The open cube of radius `r` around `q` is contained in the sup-norm cube of radius `r + m`
about the origin when `|q i| ≤ m`. -/
theorem ocubeAround_subset_openCube {r m : ℝ} {q : PL.E n} (hq : ∀ i, |q i| ≤ m) :
    ocubeAround q r ⊆ PL.openCube (r + m) := by
  intro y hy i
  have hyi : |y i - q i| < r := hy i
  have hqi : |q i| ≤ m := hq i
  calc |y i| = |(y i - q i) + q i| := by rw [sub_add_cancel]
    _ ≤ |y i - q i| + |q i| := abs_add_le _ _
    _ < r + m := by linarith

/-- A point outside the open cube of radius `R` around `q` is outside the sup-norm cube of
radius `τ` about the origin, provided `τ + m ≤ R` and `|q i| ≤ m`. -/
theorem notMem_openCube_of_notMem_ocubeAround {τ m R : ℝ} {q y : PL.E n}
    (hq : ∀ i, |q i| ≤ m) (h : τ + m ≤ R) (hy : y ∉ ocubeAround q R) :
    y ∉ PL.openCube τ := by
  intro hc
  refine hy fun i => ?_
  have h1 : |y i| < τ := hc i
  have h2 : |q i| ≤ m := hq i
  calc |y i - q i| = |y i + (-q i)| := by rw [sub_eq_add_neg]
    _ ≤ |y i| + |-q i| := abs_add_le _ _
    _ = |y i| + |q i| := by rw [abs_neg]
    _ < τ + m := by linarith
    _ ≤ R := h

end Work.Geo.Radial
