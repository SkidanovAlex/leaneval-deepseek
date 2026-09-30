import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.E2dEngine

/-!
# The compression facts of the model cell

For `0 < s < 1/2` each of the six pairs of concentric model subsets of the closed model cell
`D^{n+2}` is compressed by the radial homotopy `x ↦ ((1 - t) + t · c x) • x`, where `c` is a
continuous `ℝ`-valued clamp which is `1` exactly on the smaller set.  The homotopy is a deformation
retraction of the ambient set onto the smaller one fixing the smaller set pointwise, so each pair is
compressible in every dimension (`Work.RatHurewicz.CompressRel`) by
`Work.Serre.compressRel_of_deformation`.
-/

set_option maxHeartbeats 800000

open scoped Topology unitInterval

namespace Work.Serre.Csr

noncomputable section

/-! ## The radial clamps -/

/-- The clamp `r ↦ min 1 (s / max r s)` of the ball pairs: it is `1` for `r ≤ s` and `s / r`
afterwards, so `r * clampBall s r` is the radius `r` clamped at `s`. -/
def clampBall (s r : ℝ) : ℝ := min 1 (s / max r s)

theorem clampBall_nonneg {s r : ℝ} (hs : 0 < s) : 0 ≤ clampBall s r :=
  le_min zero_le_one (div_nonneg hs.le (le_of_lt (lt_of_lt_of_le hs (le_max_right r s))))

theorem clampBall_le_one (s r : ℝ) : clampBall s r ≤ 1 := min_le_left _ _

theorem clampBall_pos {s r : ℝ} (hs : 0 < s) : 0 < clampBall s r :=
  lt_min one_pos (div_pos hs (lt_of_lt_of_le hs (le_max_right r s)))

theorem clampBall_mul_le {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) : clampBall s r * r ≤ s := by
  have hM : 0 < max r s := lt_of_lt_of_le hs (le_max_right r s)
  rw [clampBall]
  calc min 1 (s / max r s) * r ≤ (s / max r s) * r :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hr
    _ ≤ (s / max r s) * max r s :=
        mul_le_mul_of_nonneg_left (le_max_left r s) (div_nonneg hs.le hM.le)
    _ = s := div_mul_cancel₀ s (ne_of_gt hM)

theorem clampBall_eq_one {s r : ℝ} (hs : 0 < s) (hr : r ≤ s) : clampBall s r = 1 := by
  rw [clampBall, max_eq_right hr, div_self (ne_of_gt hs), min_self]

theorem continuous_clampBall (s : ℝ) (hs : 0 < s) : Continuous (clampBall s) :=
  continuous_const.min (continuous_const.div (continuous_id.max continuous_const)
    (fun r => ne_of_gt (lt_of_lt_of_le hs (le_max_right r s))))

/-! ## Two elementary tools -/

/-- A point of a subtype of the model cell has norm at most `1`. -/
theorem norm_coe_le_one {n : ℕ} {B : Set (Work.RatHurewicz.cellDisk n)} (x : ↥B) :
    ‖((x : ↥B) : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp ((x : ↥B) : Work.RatHurewicz.cellDisk n).2
  simpa [dist_eq_norm] using h

/-- Scaling a vector by a nonnegative scalar whose product with the norm is at most `1` stays in
the unit ball. -/
theorem smul_mem_closedBall_of_mul_le {n : ℕ} {v : Work.RatHurewicz.CellVec n} {a : ℝ}
    (h0 : 0 ≤ a) (h : a * ‖v‖ ≤ 1) :
    a • v ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_of_nonneg h0]
  exact h

/-! ## The general radial compression -/

/-- **Compression from a radial scaling homotopy.**  Let `B` be a set of points of the model cell
and `A ⊆ ↥B`.  If `c : ↥B → ℝ` is continuous, the homotopy `x ↦ ((1 - t) + t · c x) • x` stays in
`B`, ends in `A` at `t = 1` and fixes `A` pointwise, then the pair `(B, A)` is compressible in every
dimension. -/
theorem compressRel_of_radial {n : ℕ} {B : Set (Work.RatHurewicz.cellDisk n)}
    {A : Set ↥B} (c : ↥B → ℝ) (hc : Continuous c)
    (hFdisk : ∀ (x : ↥B) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * c x) • ((x : ↥B) : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1)
    (hFB : ∀ (x : ↥B) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * c x) • ((x : ↥B) : Work.RatHurewicz.CellVec n),
        hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈ B)
    (h1disk : ∀ x : ↥B, c x • ((x : ↥B) : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1)
    (h1B : ∀ x : ↥B, (⟨c x • ((x : ↥B) : Work.RatHurewicz.CellVec n), h1disk x⟩ :
        Work.RatHurewicz.cellDisk n) ∈ B)
    (h1A : ∀ x : ↥B,
      (⟨⟨c x • ((x : ↥B) : Work.RatHurewicz.CellVec n), h1disk x⟩, h1B x⟩ : ↥B) ∈ A)
    (hfix : ∀ x : ↥B, x ∈ A → c x = 1) : ∀ d, Work.RatHurewicz.CompressRel ↥B A d := by
  classical
  let F : ↥B × I → ↥B := fun p =>
    ⟨(⟨((1 - (p.2 : ℝ)) + (p.2 : ℝ) * c p.1) • ((p.1 : ↥B) : Work.RatHurewicz.CellVec n),
      hFdisk p.1 p.2⟩ : Work.RatHurewicz.cellDisk n), hFB p.1 p.2⟩
  have hFcont : Continuous F := by
    have h1 : Continuous fun p : ↥B × I =>
        ((1 - (p.2 : ℝ)) + (p.2 : ℝ) * c p.1) • ((p.1 : ↥B) : Work.RatHurewicz.CellVec n) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_snd).mul (hc.comp continuous_fst))).smul
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    exact Continuous.subtype_mk (Continuous.subtype_mk h1 (fun p => hFdisk p.1 p.2))
      (fun p => hFB p.1 p.2)
  have hF0 : ∀ x : ↥B, F (x, 0) = x := by
    intro x
    have h : (1 - ((0 : I) : ℝ)) + ((0 : I) : ℝ) * c x = 1 := by norm_num
    refine Subtype.ext (Subtype.ext ?_)
    show ((1 - ((0 : I) : ℝ)) + ((0 : I) : ℝ) * c x) •
        ((x : ↥B) : Work.RatHurewicz.CellVec n) = ((x : ↥B) : Work.RatHurewicz.CellVec n)
    rw [h, one_smul]
  have hF1 : ∀ x : ↥B, F (x, 1) ∈ A := by
    intro x
    convert h1A x using 1
    refine Subtype.ext (Subtype.ext ?_)
    have h : (1 - ((1 : I) : ℝ)) + ((1 : I) : ℝ) * c x = c x := by norm_num
    show ((1 - ((1 : I) : ℝ)) + ((1 : I) : ℝ) * c x) •
        ((x : ↥B) : Work.RatHurewicz.CellVec n) = c x • ((x : ↥B) : Work.RatHurewicz.CellVec n)
    rw [h]
  have hFfix : ∀ y ∈ A, ∀ t : I, F (y, t) = y := by
    intro y hy t
    have h : (1 - (t : ℝ)) + (t : ℝ) * c y = 1 := by
      rw [hfix y hy]
      ring
    refine Subtype.ext (Subtype.ext ?_)
    show ((1 - (t : ℝ)) + (t : ℝ) * c y) •
        ((y : ↥B) : Work.RatHurewicz.CellVec n) = ((y : ↥B) : Work.RatHurewicz.CellVec n)
    rw [h, one_smul]
  intro d
  exact Work.Serre.compressRel_of_deformation ⟨F, hFcont⟩ hF0 hF1 hFfix d

/-! ## The six pairs -/

/-- The pair `(dOpen n (1/2), dClosed n s)`. -/
theorem compressRel_dOpen (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dOpen n (1/2))
      {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d := by
  have hc : Continuous fun x : ↥(dOpen n (1/2)) =>
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    (continuous_clampBall s hs).comp (by fun_prop)
  have hFdisk : ∀ (x : ↥(dOpen n (1/2))) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    refine smul_mem_closedBall_of_mul_le hlam0 ?_
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
          ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
          mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
      _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
      _ ≤ 1 := norm_coe_le_one x
  have hFB : ∀ (x : ↥(dOpen n (1/2))) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dOpen n (1/2) := by
    intro x t
    have hx1 : ‖(x : Work.RatHurewicz.CellVec n)‖ < 1/2 := mem_dOpen.mp x.2
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    have hlt : ‖((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n)‖ < 1/2 := by
      rw [norm_smul, Real.norm_of_nonneg hlam0]
      calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
            ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ < 1/2 := hx1
    exact hlt
  have h1disk : ∀ x : ↥(dOpen n (1/2)),
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le
      (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs) ?_
    calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ s := clampBall_mul_le hs (norm_nonneg _)
      _ ≤ 1 := by linarith [hs2]
  have h1B : ∀ x : ↥(dOpen n (1/2)),
      (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dOpen n (1/2) := by
    intro x
    have hx1 : ‖(x : Work.RatHurewicz.CellVec n)‖ < 1/2 := mem_dOpen.mp x.2
    have hlt : ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
        (x : Work.RatHurewicz.CellVec n)‖ < 1/2 := by
      rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
      calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right (clampBall_le_one s _) (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ < 1/2 := hx1
    exact hlt
  have h1A : ∀ x : ↥(dOpen n (1/2)),
      (⟨⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
          (x : Work.RatHurewicz.CellVec n), h1disk x⟩, h1B x⟩ : ↥(dOpen n (1/2))) ∈
        {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} := by
    intro x
    show (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
      (x : Work.RatHurewicz.CellVec n), h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dClosed n s
    rw [mem_dClosed]
    show ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)‖ ≤ s
    rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
    exact clampBall_mul_le hs (norm_nonneg _)
  have hfix : ∀ x : ↥(dOpen n (1/2)),
      x ∈ {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} →
        clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    exact clampBall_eq_one hs (mem_dClosed.mp hx)
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- The pair `(dPunct n (1/2), dClosed n s)`. -/
theorem compressRel_dPunct (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dPunct n (1/2))
      {x : ↥(dPunct n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d := by
  have hc : Continuous fun x : ↥(dPunct n (1/2)) =>
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    (continuous_clampBall s hs).comp (by fun_prop)
  have hFdisk : ∀ (x : ↥(dPunct n (1/2))) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    refine smul_mem_closedBall_of_mul_le hlam0 ?_
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
          ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
          mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
      _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
      _ ≤ 1 := norm_coe_le_one x
  have hFB : ∀ (x : ↥(dPunct n (1/2))) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dPunct n (1/2) := by
    intro x t
    have hx := mem_dPunct.mp x.2
    have hx1 : ‖(x : Work.RatHurewicz.CellVec n)‖ < 1/2 := mem_dOpen.mp hx.1
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    have hle : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤
        (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h3 : (1 - (t : ℝ)) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ +
          (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ =
          clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by ring
      have h4 : (1 - (t : ℝ)) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤
          (1 - (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hc1 (by linarith [t.2.2])
      linarith
    refine mem_dPunct.mpr ⟨?_, ?_⟩
    · have hlt : ‖((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
          (x : Work.RatHurewicz.CellVec n)‖ < 1/2 := by
        rw [norm_smul, Real.norm_of_nonneg hlam0]
        calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
              ‖(x : Work.RatHurewicz.CellVec n)‖
            ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
              mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
          _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
          _ < 1/2 := hx1
      exact hlt
    · exact smul_ne_zero
        (ne_of_gt (lt_of_lt_of_le
          (clampBall_pos (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs) hle)) hx.2
  have h1disk : ∀ x : ↥(dPunct n (1/2)),
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le
      (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs) ?_
    calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ s := clampBall_mul_le hs (norm_nonneg _)
      _ ≤ 1 := by linarith [hs2]
  have h1B : ∀ x : ↥(dPunct n (1/2)),
      (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dPunct n (1/2) := by
    intro x
    have hx := mem_dPunct.mp x.2
    have hx1 : ‖(x : Work.RatHurewicz.CellVec n)‖ < 1/2 := mem_dOpen.mp hx.1
    have hlt : ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
        (x : Work.RatHurewicz.CellVec n)‖ < 1/2 := by
      rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
      calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right (clampBall_le_one s _) (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ < 1/2 := hx1
    exact mem_dPunct.mpr ⟨hlt,
      smul_ne_zero (ne_of_gt (clampBall_pos (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)) hx.2⟩
  have h1A : ∀ x : ↥(dPunct n (1/2)),
      (⟨⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
          (x : Work.RatHurewicz.CellVec n), h1disk x⟩, h1B x⟩ : ↥(dPunct n (1/2))) ∈
        {x : ↥(dPunct n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} := by
    intro x
    show (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
      (x : Work.RatHurewicz.CellVec n), h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dClosed n s
    rw [mem_dClosed]
    show ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)‖ ≤ s
    rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
    exact clampBall_mul_le hs (norm_nonneg _)
  have hfix : ∀ x : ↥(dPunct n (1/2)),
      x ∈ {x : ↥(dPunct n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} →
        clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    exact clampBall_eq_one hs (mem_dClosed.mp hx)
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- The pair `(dPunctClosed n s, dSph n s)`. -/
theorem compressRel_dPunctClosed (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dPunctClosed n s)
      {x : ↥(dPunctClosed n s) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} d := by
  have hne : ∀ x : ↥(dPunctClosed n s), (x : Work.RatHurewicz.CellVec n) ≠ 0 :=
    fun x => (mem_dPunctClosed.mp x.2).2
  have hrpos : ∀ x : ↥(dPunctClosed n s), 0 < ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    fun x => norm_pos_iff.mpr (hne x)
  have hrle : ∀ x : ↥(dPunctClosed n s), ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ s :=
    fun x => (mem_dPunctClosed.mp x.2).1
  have hc : Continuous fun x : ↥(dPunctClosed n s) => s / ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    continuous_const.div (by fun_prop) (fun x => ne_of_gt (hrpos x))
  have hkey : ∀ (x : ↥(dPunctClosed n s)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) *
        ‖(x : Work.RatHurewicz.CellVec n)‖
        = (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ + (t : ℝ) * s := by
    intro x t
    rw [add_mul, mul_assoc, div_mul_cancel₀ s (ne_of_gt (hrpos x))]
  have hFdisk : ∀ (x : ↥(dPunctClosed n s)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖) := by
      have h := mul_nonneg t.2.1 (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n)))
      linarith [t.2.2]
    refine smul_mem_closedBall_of_mul_le hlam0 ?_
    rw [hkey x t]
    have h4 : (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ ≤
        (1 - (t : ℝ)) * s :=
      mul_le_mul_of_nonneg_left (hrle x) (by linarith [t.2.2])
    have h3 : (1 - (t : ℝ)) * s + (t : ℝ) * s = s := by ring
    linarith
  have hlam1 : ∀ (x : ↥(dPunctClosed n s)) (t : I),
      1 ≤ (1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖) := by
    intro x t
    have hsr1 : 1 ≤ s / ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      rw [one_le_div (hrpos x)]
      exact hrle x
    have h := mul_le_mul_of_nonneg_left hsr1 t.2.1
    have h2 : (1 - (t : ℝ)) + (t : ℝ) * 1 = 1 := by ring
    linarith
  have hFB : ∀ (x : ↥(dPunctClosed n s)) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dPunctClosed n s := by
    intro x t
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖) := by
      have h := mul_nonneg t.2.1 (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n)))
      linarith [t.2.2]
    refine mem_dPunctClosed.mpr ⟨?_, ?_⟩
    · show ‖((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
          (x : Work.RatHurewicz.CellVec n)‖ ≤ s
      rw [norm_smul, Real.norm_of_nonneg hlam0, hkey x t]
      have h4 : (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ ≤
          (1 - (t : ℝ)) * s :=
        mul_le_mul_of_nonneg_left (hrle x) (by linarith [t.2.2])
      have h3 : (1 - (t : ℝ)) * s + (t : ℝ) * s = s := by ring
      linarith
    · exact smul_ne_zero (ne_of_gt (lt_of_lt_of_le one_pos (hlam1 x t))) (hne x)
  have h1disk : ∀ x : ↥(dPunctClosed n s),
      (s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))) ?_
    rw [div_mul_cancel₀ s (ne_of_gt (hrpos x))]
    linarith [hs2]
  have h1B : ∀ x : ↥(dPunctClosed n s),
      (⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dPunctClosed n s := by
    intro x
    refine mem_dPunctClosed.mpr ⟨?_, ?_⟩
    · show ‖(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ ≤ s
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
        div_mul_cancel₀ s (ne_of_gt (hrpos x))]
    · exact smul_ne_zero (ne_of_gt (div_pos hs (hrpos x))) (hne x)
  have h1A : ∀ x : ↥(dPunctClosed n s),
      (⟨⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩, h1B x⟩ : ↥(dPunctClosed n s)) ∈
        {x : ↥(dPunctClosed n s) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} := by
    intro x
    show (⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
      h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dSph n s
    rw [mem_dSph]
    show ‖(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ = s
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
      div_mul_cancel₀ s (ne_of_gt (hrpos x))]
  have hfix : ∀ x : ↥(dPunctClosed n s),
      x ∈ {x : ↥(dPunctClosed n s) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} →
        s / ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    rw [mem_dSph.mp hx, div_self (ne_of_gt hs)]
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- The pair `(dClosed n 1, dClosed n s)`. -/
theorem compressRel_dClosed (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dClosed n 1)
      {x : ↥(dClosed n 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d := by
  have hc : Continuous fun x : ↥(dClosed n 1) =>
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    (continuous_clampBall s hs).comp (by fun_prop)
  have hFdisk : ∀ (x : ↥(dClosed n 1)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    refine smul_mem_closedBall_of_mul_le hlam0 ?_
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
          ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
          mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
      _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
      _ ≤ 1 := mem_dClosed.mp x.2
  have hFB : ∀ (x : ↥(dClosed n 1)) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dClosed n 1 := by
    intro x t
    have hc0 : 0 ≤ clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ :=
      clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs
    have hc1 : clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := clampBall_le_one s _
    have hlam0 : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ := by
      have h := mul_nonneg t.2.1 hc0
      linarith [t.2.2]
    have hlam1 : (1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hc1 t.2.1
      linarith [h, t.2.2]
    have hle : ‖((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) •
        (x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg hlam0]
      calc ((1 - (t : ℝ)) + (t : ℝ) * clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖) *
            ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right hlam1 (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ ≤ 1 := mem_dClosed.mp x.2
    exact hle
  have h1disk : ∀ x : ↥(dClosed n 1),
      clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le
      (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs) ?_
    calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ s := clampBall_mul_le hs (norm_nonneg _)
      _ ≤ 1 := by linarith [hs2]
  have h1B : ∀ x : ↥(dClosed n 1),
      (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dClosed n 1 := by
    intro x
    have hle : ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
        (x : Work.RatHurewicz.CellVec n)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
      calc clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ * ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right (clampBall_le_one s _) (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ ≤ 1 := mem_dClosed.mp x.2
    exact hle
  have h1A : ∀ x : ↥(dClosed n 1),
      (⟨⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
          (x : Work.RatHurewicz.CellVec n), h1disk x⟩, h1B x⟩ : ↥(dClosed n 1)) ∈
        {x : ↥(dClosed n 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} := by
    intro x
    show (⟨clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ •
      (x : Work.RatHurewicz.CellVec n), h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dClosed n s
    rw [mem_dClosed]
    show ‖clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ • (x : Work.RatHurewicz.CellVec n)‖ ≤ s
    rw [norm_smul, Real.norm_of_nonneg (clampBall_nonneg (r := ‖(x : Work.RatHurewicz.CellVec n)‖) hs)]
    exact clampBall_mul_le hs (norm_nonneg _)
  have hfix : ∀ x : ↥(dClosed n 1),
      x ∈ {x : ↥(dClosed n 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} →
        clampBall s ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    exact clampBall_eq_one hs (mem_dClosed.mp hx)
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- The pair `(dAnn n s 1, dSph n s)`. -/
theorem compressRel_dAnnSph (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dAnn n s 1)
      {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} d := by
  have hpos : ∀ x : ↥(dAnn n s 1), 0 < ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    fun x => lt_of_lt_of_le hs (mem_dAnn.mp x.2).1
  have hle1 : ∀ x : ↥(dAnn n s 1), ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 :=
    fun x => (mem_dAnn.mp x.2).2
  have hc : Continuous fun x : ↥(dAnn n s 1) => s / ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    continuous_const.div (by fun_prop) (fun x => ne_of_gt (hpos x))
  have hkey : ∀ (x : ↥(dAnn n s 1)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) *
        ‖(x : Work.RatHurewicz.CellVec n)‖
        = (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ + (t : ℝ) * s := by
    intro x t
    rw [add_mul, mul_assoc, div_mul_cancel₀ s (ne_of_gt (hpos x))]
  have hlam0 : ∀ (x : ↥(dAnn n s 1)) (t : I),
      0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖) := by
    intro x t
    have h := mul_nonneg t.2.1 (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n)))
    linarith [t.2.2]
  have hlam1 : ∀ (x : ↥(dAnn n s 1)) (t : I),
      (1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖) ≤ 1 := by
    intro x t
    have hsr1 : s / ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 :=
      div_le_one_of_le₀ (mem_dAnn.mp x.2).1 (norm_nonneg _)
    have h := mul_le_mul_of_nonneg_left hsr1 t.2.1
    linarith [h, t.2.2]
  have hFdisk : ∀ (x : ↥(dAnn n s 1)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    refine smul_mem_closedBall_of_mul_le (hlam0 x t) ?_
    calc ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) *
          ‖(x : Work.RatHurewicz.CellVec n)‖
        ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
          mul_le_mul_of_nonneg_right (hlam1 x t) (norm_nonneg _)
      _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
      _ ≤ 1 := hle1 x
  have hFB : ∀ (x : ↥(dAnn n s 1)) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dAnn n s 1 := by
    intro x t
    refine mem_dAnn.mpr ⟨?_, ?_⟩
    · show s ≤ ‖((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
          (x : Work.RatHurewicz.CellVec n)‖
      rw [norm_smul, Real.norm_of_nonneg (hlam0 x t), hkey x t]
      have h4 : (1 - (t : ℝ)) * s ≤ (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
        mul_le_mul_of_nonneg_left (mem_dAnn.mp x.2).1 (by linarith [t.2.2])
      have h3 : (1 - (t : ℝ)) * s + (t : ℝ) * s = s := by ring
      linarith
    · show ‖((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
          (x : Work.RatHurewicz.CellVec n)‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (hlam0 x t)]
      calc ((1 - (t : ℝ)) + (t : ℝ) * (s / ‖(x : Work.RatHurewicz.CellVec n)‖)) *
            ‖(x : Work.RatHurewicz.CellVec n)‖
          ≤ 1 * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
            mul_le_mul_of_nonneg_right (hlam1 x t) (norm_nonneg _)
        _ = ‖(x : Work.RatHurewicz.CellVec n)‖ := one_mul _
        _ ≤ 1 := hle1 x
  have h1disk : ∀ x : ↥(dAnn n s 1),
      (s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))) ?_
    rw [div_mul_cancel₀ s (ne_of_gt (hpos x))]
    linarith [hle1 x, hs2]
  have h1B : ∀ x : ↥(dAnn n s 1),
      (⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dAnn n s 1 := by
    intro x
    refine mem_dAnn.mpr ⟨?_, ?_⟩
    · show s ≤ ‖(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
        div_mul_cancel₀ s (ne_of_gt (hpos x))]
    · show ‖(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
        div_mul_cancel₀ s (ne_of_gt (hpos x))]
      linarith [hs2]
  have h1A : ∀ x : ↥(dAnn n s 1),
      (⟨⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩, h1B x⟩ : ↥(dAnn n s 1)) ∈
        {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} := by
    intro x
    show (⟨(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
      h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dSph n s
    rw [mem_dSph]
    show ‖(s / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ = s
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
      div_mul_cancel₀ s (ne_of_gt (hpos x))]
  have hfix : ∀ x : ↥(dAnn n s 1),
      x ∈ {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} →
        s / ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    rw [mem_dSph.mp hx, div_self (ne_of_gt hs)]
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- The pair `(dAnn n s 1, dSph n 1)`. -/
theorem compressRel_dAnnSphOne (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    ∀ d, Work.RatHurewicz.CompressRel ↥(dAnn n s 1)
      {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n 1} d := by
  have hpos : ∀ x : ↥(dAnn n s 1), 0 < ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    fun x => lt_of_lt_of_le hs (mem_dAnn.mp x.2).1
  have hle1 : ∀ x : ↥(dAnn n s 1), ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ 1 :=
    fun x => (mem_dAnn.mp x.2).2
  have hc : Continuous fun x : ↥(dAnn n s 1) => 1 / ‖(x : Work.RatHurewicz.CellVec n)‖ :=
    continuous_const.div (by fun_prop) (fun x => ne_of_gt (hpos x))
  have hkey : ∀ (x : ↥(dAnn n s 1)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖)) *
        ‖(x : Work.RatHurewicz.CellVec n)‖
        = (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ + (t : ℝ) * 1 := by
    intro x t
    rw [add_mul, mul_assoc, div_mul_cancel₀ 1 (ne_of_gt (hpos x))]
  have hlam0 : ∀ (x : ↥(dAnn n s 1)) (t : I),
      0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖) := by
    intro x t
    have h := mul_nonneg t.2.1 (div_nonneg zero_le_one (norm_nonneg (x : Work.RatHurewicz.CellVec n)))
    linarith [t.2.2]
  have hFdisk : ∀ (x : ↥(dAnn n s 1)) (t : I),
      ((1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n) ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x t
    refine smul_mem_closedBall_of_mul_le (hlam0 x t) ?_
    rw [hkey x t]
    have h4 : (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ (1 - (t : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (hle1 x) (by linarith [t.2.2])
    have h3 : (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 = 1 := by ring
    linarith
  have hFB : ∀ (x : ↥(dAnn n s 1)) (t : I),
      (⟨((1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
        (x : Work.RatHurewicz.CellVec n), hFdisk x t⟩ : Work.RatHurewicz.cellDisk n) ∈
        dAnn n s 1 := by
    intro x t
    refine mem_dAnn.mpr ⟨?_, ?_⟩
    · show s ≤ ‖((1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
          (x : Work.RatHurewicz.CellVec n)‖
      rw [norm_smul, Real.norm_of_nonneg (hlam0 x t), hkey x t]
      have h4 : (1 - (t : ℝ)) * s ≤ (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ :=
        mul_le_mul_of_nonneg_left (mem_dAnn.mp x.2).1 (by linarith [t.2.2])
      have h5 : (1 - (t : ℝ)) * s + (t : ℝ) * 1 = s + (t : ℝ) * (1 - s) := by ring
      have h6 : 0 ≤ (t : ℝ) * (1 - s) := mul_nonneg t.2.1 (by linarith [hs2])
      linarith
    · show ‖((1 - (t : ℝ)) + (t : ℝ) * (1 / ‖(x : Work.RatHurewicz.CellVec n)‖)) •
          (x : Work.RatHurewicz.CellVec n)‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (hlam0 x t), hkey x t]
      have h4 : (1 - (t : ℝ)) * ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ (1 - (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (hle1 x) (by linarith [t.2.2])
      have h3 : (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 = 1 := by ring
      linarith
  have h1disk : ∀ x : ↥(dAnn n s 1),
      (1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)
        ∈ Metric.closedBall (0 : Work.RatHurewicz.CellVec n) 1 := by
    intro x
    refine smul_mem_closedBall_of_mul_le (div_nonneg zero_le_one (norm_nonneg (x : Work.RatHurewicz.CellVec n))) ?_
    rw [div_mul_cancel₀ 1 (ne_of_gt (hpos x))]
  have h1B : ∀ x : ↥(dAnn n s 1),
      (⟨(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dAnn n s 1 := by
    intro x
    refine mem_dAnn.mpr ⟨?_, ?_⟩
    · show s ≤ ‖(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
        div_mul_cancel₀ 1 (ne_of_gt (hpos x))]
      linarith [hs2]
    · show ‖(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
        div_mul_cancel₀ 1 (ne_of_gt (hpos x))]
  have h1A : ∀ x : ↥(dAnn n s 1),
      (⟨⟨(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
        h1disk x⟩, h1B x⟩ : ↥(dAnn n s 1)) ∈
        {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n 1} := by
    intro x
    show (⟨(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n),
      h1disk x⟩ : Work.RatHurewicz.cellDisk n) ∈ dSph n 1
    rw [mem_dSph]
    show ‖(1 / ‖(x : Work.RatHurewicz.CellVec n)‖) • (x : Work.RatHurewicz.CellVec n)‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (norm_nonneg (x : Work.RatHurewicz.CellVec n))),
      div_mul_cancel₀ 1 (ne_of_gt (hpos x))]
  have hfix : ∀ x : ↥(dAnn n s 1),
      x ∈ {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n 1} →
        1 / ‖(x : Work.RatHurewicz.CellVec n)‖ = 1 := by
    intro x hx
    rw [mem_dSph.mp hx, one_div_one]
  exact compressRel_of_radial _ hc hFdisk hFB h1disk h1B h1A hfix

/-- **The compression facts of the model cell.**  For `0 < s < 1/2`, each of the six pairs of
concentric model subsets of the closed model cell `D^{n+2}` is compressible in every dimension: the
larger set deformation-retracts onto the smaller one along the rays from the centre `0`, fixing the
smaller set pointwise.  The six pairs (ambient, relative part) are
`(dOpen n (1/2), dClosed n s)`, `(dPunct n (1/2), dClosed n s)`, `(dPunctClosed n s, dSph n s)`,
`(dClosed n 1, dClosed n s)`, `(dAnn n s 1, dSph n s)` and `(dAnn n s 1, dSph n 1)`.
Note that in the second pair the ambient is the *punctured* open ball `dPunct n (1/2)`, so its
relative part `dPunct n (1/2) ∩ dClosed n s` is the punctured closed ball (the centre `0` is not in
the ambient), and the radial clamp `x ↦ x · min (1) (s/‖x‖)` is a deformation retraction of the
ambient onto it which fixes it pointwise. -/
theorem csrCompressBase (n : ℕ) (s : ℝ) (hs : 0 < s) (hs2 : s < 1/2) :
    Work.Serre.CsrCompress n s := by
  unfold Work.Serre.CsrCompress
  exact ⟨compressRel_dOpen n s hs hs2, compressRel_dPunct n s hs hs2,
    compressRel_dPunctClosed n s hs hs2, compressRel_dClosed n s hs hs2,
    compressRel_dAnnSph n s hs hs2, compressRel_dAnnSphOne n s hs hs2⟩

end

end Work.Serre.Csr
