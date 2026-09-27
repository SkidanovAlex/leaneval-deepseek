import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.horSpec

/-!
# The flat (horospherical) action `flatAct` on `ξ^⊥`

`flatAct ξ g y = yc ξ (g • horoPt ξ y)` is the action of `g : PO n 1` on the flat coordinate `y`
of the horosphere of `ξ`, transported from the horosphere of level `1`.

This file collects the elementary calculus of `flatAct` that everything else in the `flatMapSpec`
development uses:

* `horoPt` is `hptOf` at level `1`, and `hdist (horoPt ξ y) (horoPt ξ y') = arccosh (1+‖y-y'‖²/2)`;
* `flatAct` lands in `ξ^⊥`, commutes with the horosphere parametrisation, is a Euclidean
  isometry there, and composes;
* `bd` is multiplicative/invertible on the stabiliser of `ξ`;
* the flat norm of the `flatAct` of a product of stabiliser elements is bounded by the sum of the
  flat norms of the factors (`flatAct_prod_norm_le`).
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-! ## `horoPt` is `hptOf` at level one -/

theorem horoPt_eq_hptOf (ξ y : E n) : horoPt ξ y = hptOf ξ y 1 := by
  have h : (‖y‖ ^ 2 / 2 : ℝ) = (1 + 1 ^ 2 * ‖y‖ ^ 2) / (2 * 1) - 1 / 2 := by ring
  rw [horoPt, hptOf, h, one_smul]

theorem horoPt_zero (ξ : E n) : horoPt ξ (0 : E n) = 0 := by
  simp [horoPt]

theorem norm_Sph {ξ : E n} (hξ : ξ ∈ Sph n) : ‖ξ‖ = 1 := by
  simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ

theorem inner_self_Sph {ξ : E n} (hξ : ξ ∈ Sph n) : inner ℝ ξ ξ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_Sph hξ, one_pow]

theorem lev_horoPt {ξ : E n} (hξ : ξ ∈ Sph n) (y : E n) (hy : inner ℝ y ξ = 0) :
    lev ξ (horoPt ξ y) = 1 := by
  rw [horoPt_eq_hptOf]
  exact (hptOf_level ξ hξ 1 one_pos y hy).1

theorem yc_horoPt {ξ : E n} (hξ : ξ ∈ Sph n) (y : E n) (hy : inner ℝ y ξ = 0) :
    yc ξ (horoPt ξ y) = y := by
  rw [horoPt_eq_hptOf]
  exact (hptOf_level ξ hξ 1 one_pos y hy).2

theorem hdist_horoPt {ξ : E n} (hξ : ξ ∈ Sph n) (y y' : E n)
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    hdist (horoPt ξ y) (horoPt ξ y') = Real.arcosh (1 + ‖y - y'‖ ^ 2 / 2) := by
  rw [horoPt_eq_hptOf ξ y, horoPt_eq_hptOf ξ y',
    hptOf_hdist ξ hξ 1 one_pos y y' hy hy', one_mul]

/-! ## The flat coordinate of a point of the level-one horosphere -/

/-- `wc ξ u = lev ξ u • yc ξ u` (for `lev ξ u ≠ 0`). -/
theorem wc_eq_lev_smul_yc (ξ u : E n) (h : lev ξ u ≠ 0) :
    wc ξ u = lev ξ u • yc ξ u := by
  rw [yc, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- `‖wc ξ u‖² = ‖u‖² - ⟪u,ξ⟫²`. -/
theorem norm_wc_sq {ξ u : E n} (hξ : ξ ∈ Sph n) :
    ‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := by
  have hw : wc ξ u = u - (inner ℝ u ξ) • ξ := rfl
  rw [hw, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, norm_Sph hξ,
    mul_one, sq_abs]
  ring

/-- The `ξ`-coordinate of a point of the level-one horosphere, in terms of its flat coordinate. -/
theorem inner_eq_norm_yc_sq {ξ u : E n} (hξ : ξ ∈ Sph n) (hu : lev ξ u = 1) :
    inner ℝ u ξ = ‖yc ξ u‖ ^ 2 / 2 := by
  have hwc : wc ξ u = lev ξ u • yc ξ u := wc_eq_lev_smul_yc ξ u (by rw [hu]; norm_num)
  have h1 : ‖wc ξ u‖ = ‖yc ξ u‖ := by rw [hwc, hu, one_smul]
  have h2 : ‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := norm_wc_sq hξ
  have ht : tpart u = 1 + inner ℝ u ξ := by
    have := hu; rw [lev] at this; linarith
  have hsq : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
    rw [tpart]; exact Real.sq_sqrt (by positivity)
  have h3 : ‖yc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := by rw [← h1, h2]
  nlinarith [hsq, ht, h3]

/-- The hyperbolic distance from `0` to a point of the level-one horosphere of `ξ`, in terms of
its flat coordinate. -/
theorem hdist_zero_eq_yc {ξ u : E n} (hξ : ξ ∈ Sph n) (hu : lev ξ u = 1) :
    hdist (0 : E n) u = Real.arcosh (1 + ‖yc ξ u‖ ^ 2 / 2) := by
  have ht : tpart u = 1 + inner ℝ u ξ := by
    have := hu; rw [lev] at this; linarith
  have h0 : hdist (0 : E n) u = Real.arcosh (tpart u) := by
    rw [hdist, tpart]
    simp
  rw [h0, ht, inner_eq_norm_yc_sq hξ hu]

/-- The flat coordinate of a point of the level-one horosphere is bounded by its norm. -/
theorem yc_norm_le_norm {ξ u : E n} (hξ : ξ ∈ Sph n) (hu : lev ξ u = 1) :
    ‖yc ξ u‖ ≤ ‖u‖ := by
  have hwc : wc ξ u = lev ξ u • yc ξ u := wc_eq_lev_smul_yc ξ u (by rw [hu]; norm_num)
  have h1 : ‖wc ξ u‖ = ‖yc ξ u‖ := by rw [hwc, hu, one_smul]
  have h2 : ‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := norm_wc_sq hξ
  have h3 : ‖wc ξ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have : 0 ≤ (inner ℝ u ξ) ^ 2 := sq_nonneg _
    linarith [h2]
  have h4 : ‖yc ξ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by rw [← h1]; exact h3
  have := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-! ## `flatAct` -/

/-- `flatAct` lands in `ξ^⊥`. -/
theorem flatAct_mem {ξ : E n} (hξ : ξ ∈ Sph n) (g : PO n 1) (y : E n) :
    inner ℝ (flatAct ξ g y) ξ = 0 := yc_inner_orth hξ

/-- For `g` fixing `ξ` and preserving the level, `flatAct` is the horosphere action in flat
coordinates. -/
theorem flatAct_horoPt {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {g : PO n 1} (hg : bd g ξ = ξ) (h0 : lev ξ (g • (0 : E n)) = 1)
    {y : E n} (hy : inner ℝ y ξ = 0) :
    g • horoPt ξ y = horoPt ξ (flatAct ξ g y) := by
  have hlev' : lev ξ (g • horoPt ξ y) = 1 := by
    rw [lev_smul_self hI hA ξ hξ g (horoPt ξ y) hg, lev_horoPt hξ y hy, h0, one_mul]
  show g • horoPt ξ y = horoPt ξ (yc ξ (g • horoPt ξ y))
  conv_rhs => rw [horoPt_eq_hptOf]
  exact (hptOf_yc ξ hξ 1 one_pos (g • horoPt ξ y) hlev').symm

/-- `flatAct` of an element fixing `ξ` and preserving the level is a Euclidean isometry of `ξ^⊥`. -/
theorem flatAct_isometry {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {g : PO n 1} (hg : bd g ξ = ξ) (h0 : lev ξ (g • (0 : E n)) = 1)
    {y y' : E n} (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    ‖flatAct ξ g y - flatAct ξ g y'‖ = ‖y - y'‖ := by
  have hL := hdist_horoPt hξ (flatAct ξ g y) (flatAct ξ g y')
    (flatAct_mem hξ g y) (flatAct_mem hξ g y')
  have hR := hdist_horoPt hξ y y' hy hy'
  have hsim : hdist (horoPt ξ (flatAct ξ g y)) (horoPt ξ (flatAct ξ g y'))
      = hdist (horoPt ξ y) (horoPt ξ y') := by
    rw [← flatAct_horoPt hξ hA hI hg h0 hy, ← flatAct_horoPt hξ hA hI hg h0 hy']
    exact hI.isom_smul g _ _
  rw [hL, hR] at hsim
  have harg : 1 + ‖flatAct ξ g y - flatAct ξ g y'‖ ^ 2 / 2 = 1 + ‖y - y'‖ ^ 2 / 2 := by
    have h1 : (1 : ℝ) ≤ 1 + ‖flatAct ξ g y - flatAct ξ g y'‖ ^ 2 / 2 := by
      have : (0 : ℝ) ≤ ‖flatAct ξ g y - flatAct ξ g y'‖ ^ 2 / 2 := by positivity
      linarith
    have h2 : (1 : ℝ) ≤ 1 + ‖y - y'‖ ^ 2 / 2 := by
      have : (0 : ℝ) ≤ ‖y - y'‖ ^ 2 / 2 := by positivity
      linarith
    have h := congrArg Real.cosh hsim
    rwa [Real.cosh_arcosh h1, Real.cosh_arcosh h2] at h
  have hsq : ‖flatAct ξ g y - flatAct ξ g y'‖ ^ 2 = ‖y - y'‖ ^ 2 := by linarith
  have h2 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

theorem flatAct_one {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) {y : E n}
    (hy : inner ℝ y ξ = 0) : flatAct ξ (1 : PO n 1) y = y := by
  show yc ξ ((1 : PO n 1) • horoPt ξ y) = y
  rw [hA.one_smul, yc_horoPt hξ y hy]

theorem flatAct_comp {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {g h : PO n 1} (hg : bd g ξ = ξ) (hh : bd h ξ = ξ)
    (h0g : lev ξ (g • (0 : E n)) = 1) (h0h : lev ξ (h • (0 : E n)) = 1)
    {y : E n} (hy : inner ℝ y ξ = 0) :
    flatAct ξ (g * h) y = flatAct ξ g (flatAct ξ h y) := by
  show yc ξ ((g * h) • horoPt ξ y) = yc ξ (g • horoPt ξ (flatAct ξ h y))
  rw [hA.mul_smul, flatAct_horoPt hξ hA hI hh h0h hy]

/-- `flatAct ξ g 0 = yc ξ (g • 0)` for `g` fixing `ξ`. -/
theorem flatAct_zero_eq_yc {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1} :
    flatAct ξ g (0 : E n) = yc ξ (g • (0 : E n)) := by
  show yc ξ (g • horoPt ξ (0 : E n)) = yc ξ (g • (0 : E n))
  rw [horoPt_zero]

/-! ## The stabiliser of `ξ` -/

theorem bd_mul_of {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n)
    {g h : PO n 1} (hg : bd g ξ = ξ) (hh : bd h ξ = ξ) : bd (g * h) ξ = ξ := by
  rw [hA.bd_mul g h ξ hξ, hh, hg]

theorem bd_inv_of {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n)
    {g : PO n 1} (hg : bd g ξ = ξ) : bd g⁻¹ ξ = ξ := by
  have hinj : ∀ a b : E n, a ∈ Sph n → b ∈ Sph n → bd g a = bd g b → a = b := by
    intro a b ha hb hab
    have h2 : bd g⁻¹ (bd g a) = a := by
      rw [← hA.bd_mul g⁻¹ g a ha, inv_mul_cancel, hA.bd_one a ha]
    have h3 : bd g⁻¹ (bd g b) = b := by
      rw [← hA.bd_mul g⁻¹ g b hb, inv_mul_cancel, hA.bd_one b hb]
    rw [hab] at h2
    rw [h2] at h3
    exact h3
  have h1 : bd g (bd g⁻¹ ξ) = bd g ξ := by
    have h := hA.bd_mul g g⁻¹ ξ hξ
    rw [mul_inv_cancel, hA.bd_one ξ hξ] at h
    exact h.symm.trans hg.symm
  exact hinj (bd g⁻¹ ξ) ξ (hA.bd_mem g⁻¹ ξ hξ) hξ h1

theorem bd_prod_of {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n)
    {l : List (PO n 1)} (h : ∀ g ∈ l, bd g ξ = ξ) : bd l.prod ξ = ξ := by
  induction l with
  | nil => rw [List.prod_nil]; exact hA.bd_one ξ hξ
  | cons g t ih =>
    rw [List.prod_cons]
    exact bd_mul_of hξ hA (h g (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem lev_prod_of {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {l : List (PO n 1)} (h : ∀ g ∈ l, bd g ξ = ξ ∧ lev ξ (g • (0 : E n)) = 1) :
    lev ξ (l.prod • (0 : E n)) = 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, hA.one_smul]
    simp [lev, tpart]
  | cons g t ih =>
    rw [List.prod_cons, hA.mul_smul,
      lev_smul_self hI hA ξ hξ g (t.prod • (0 : E n)) (h g (by simp)).1,
      (h g (by simp)).2,
      ih (fun x hx => h x (by simp [hx]))]
    simp

/-- The flat norm of the `flatAct` of a product is at most the sum of the flat norms. -/
theorem flatAct_prod_norm_le {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {l : List (PO n 1)} (hbd : ∀ g ∈ l, bd g ξ = ξ) (h0 : ∀ g ∈ l, lev ξ (g • (0 : E n)) = 1) :
    ‖flatAct ξ l.prod (0 : E n)‖ ≤ (l.map (fun g => ‖flatAct ξ g (0 : E n)‖)).sum := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.sum_nil,
      flatAct_one hξ hA (by simp : inner ℝ (0 : E n) ξ = 0)]
    exact norm_zero.le
  | cons g t ih =>
    have hgt : bd g ξ = ξ := hbd g (by simp)
    have h0g : lev ξ (g • (0 : E n)) = 1 := h0 g (by simp)
    have hbt : bd t.prod ξ = ξ := bd_prod_of hξ hA (fun x hx => hbd x (by simp [hx]))
    have h0t : lev ξ (t.prod • (0 : E n)) = 1 :=
      lev_prod_of hξ hA hI (fun x hx => ⟨hbd x (by simp [hx]), h0 x (by simp [hx])⟩)
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    have hcomp : flatAct ξ (g * t.prod) (0 : E n)
        = flatAct ξ g (flatAct ξ t.prod (0 : E n)) :=
      flatAct_comp hξ hA hI hgt hbt h0g h0t (by simp : inner ℝ (0 : E n) ξ = 0)
    rw [hcomp]
    calc ‖flatAct ξ g (flatAct ξ t.prod (0 : E n))‖
        ≤ ‖flatAct ξ g (flatAct ξ t.prod (0 : E n)) - flatAct ξ g (0 : E n)‖
            + ‖flatAct ξ g (0 : E n)‖ := by
          have h := norm_add_le
            (flatAct ξ g (flatAct ξ t.prod (0 : E n)) - flatAct ξ g (0 : E n))
            (flatAct ξ g (0 : E n))
          rwa [sub_add_cancel] at h
      _ = ‖flatAct ξ t.prod (0 : E n)‖ + ‖flatAct ξ g (0 : E n)‖ := by
          have h := flatAct_isometry (y := flatAct ξ t.prod (0 : E n)) (y' := (0 : E n))
            hξ hA hI hgt h0g (flatAct_mem hξ t.prod (0 : E n))
            (by simp : inner ℝ (0 : E n) ξ = 0)
          rw [h, sub_zero]
      _ ≤ (t.map (fun g => ‖flatAct ξ g (0 : E n)‖)).sum + ‖flatAct ξ g (0 : E n)‖ := by
          linarith [ih (fun x hx => hbd x (by simp [hx])) (fun x hx => h0 x (by simp [hx]))]
      _ = ‖flatAct ξ g (0 : E n)‖ + (t.map (fun g => ‖flatAct ξ g (0 : E n)‖)).sum := by
          ring

end Work.Mostow
