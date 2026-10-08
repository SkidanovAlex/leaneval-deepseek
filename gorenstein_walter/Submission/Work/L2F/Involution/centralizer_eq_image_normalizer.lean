import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Involution.mem_normalizer_zpowers

open scoped MatrixGroups

namespace Work.L2F.Involution

/-! ## Auxiliary facts about `pslMap` and about `⟨x⟩` for `x² = -1`

The main theorem below describes the centralizer of the image of `x` in `PSL(2,F)` as the image
of the normalizer of `⟨x⟩`.  Two independent pieces of bookkeeping are needed:

* the kernel of `SL(2,F) → PSL(2,F)` is `{±1}` in *every* characteristic
  (`pslMap_eq_one_iff_nochar`, the characteristic-free version of
  `Work.L2F.Mat2.pslMap_eq_one_iff`);
* every element of `⟨x⟩` (which is `{1, x, -1, -x}`) has image `1` or `pslMap x`
  (`pslMap_zpowers_eq_or`).
-/

/-- The kernel of `SL(2,F) → PSL(2,F)` is `{1, -1}` in every characteristic: `pslMap` is
`QuotientGroup.mk' (center _)`, and a central element of `SL(2,F)` is the scalar matrix
`r • 1` with `r ^ 2 = 1`, so `r = ±1` (in characteristic `2` the two coincide).  This is
`Work.L2F.Mat2.pslMap_eq_one_iff` with its unused hypothesis `(2 : F) ≠ 0` dropped. -/
theorem pslMap_eq_one_iff_nochar (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.PSL2.pslMap F x = 1 ↔ x = 1 ∨ x = Work.L2F.negOne F := by
  have hcenter : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
      x = 1 ∨ x = Work.L2F.negOne F := by
    constructor
    · intro hx
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hx
      obtain ⟨r, hr, hrA⟩ := hx
      have hr2 : r ^ 2 = 1 := by simpa using hr
      have hfac : (r - 1) * (r + 1) = 0 := by
        have h : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
        rw [h, hr2]; ring
      rcases mul_eq_zero.mp hfac with h | h
      · left
        have hr1 : r = 1 := sub_eq_zero.mp h
        subst hr1
        apply Subtype.ext
        rw [← hrA, map_one]
        rfl
      · right
        have hr1 : r = -1 := add_eq_zero_iff_eq_neg.mp h
        subst hr1
        apply Subtype.ext
        rw [← hrA, map_neg, map_one]
        rfl
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · rw [Matrix.SpecialLinearGroup.mem_center_iff]
        exact ⟨-1, by norm_num, by rw [map_neg, map_one]; rfl⟩
  change QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x = 1 ↔
    x = 1 ∨ x = Work.L2F.negOne F
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact hcenter

/-- The image of `-1` in `PSL(2,F)` is trivial, in every characteristic. -/
theorem pslMap_negOne_nochar (F : Type*) [Field F] :
    Work.PSL2.pslMap F (Work.L2F.negOne F) = 1 :=
  (pslMap_eq_one_iff_nochar F (Work.L2F.negOne F)).mpr (Or.inr rfl)

/-- `x ^ 2 = -1` as an element of `SL(2,F)`, when `x * x = -1` as a matrix. -/
theorem sq_eq_negOne (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    x ^ 2 = Work.L2F.negOne F := by
  rw [pow_two]
  apply Subtype.ext
  change (((x * x) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1
  exact hx

/-- Every element of `⟨x⟩` (for `x² = -1`, so `⟨x⟩ = {1, x, -1, -x}`) has image `1` or
`pslMap x` in `PSL(2,F)`: the four elements of `⟨x⟩` are `1`, `x`, `x² = -1` and
`x³ = -1 · x`, whose images are `1`, `pslMap x`, `1` and `pslMap x`. -/
theorem pslMap_zpowers_eq_or (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1)
    (w : Matrix.SpecialLinearGroup (Fin 2) F) (hw : w ∈ Subgroup.zpowers x) :
    Work.PSL2.pslMap F w = 1 ∨ Work.PSL2.pslMap F w = Work.PSL2.pslMap F x := by
  have hx2 : x ^ 2 = Work.L2F.negOne F := sq_eq_negOne F x hx
  have hx4 : x ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx2, negOne_pow_two F]
  rcases zpowers_of_pow_four hx4 hw with h | h | h | h
  · left; rw [h, map_one]
  · right; rw [h]
  · left; rw [h, hx2]; exact pslMap_negOne_nochar F
  · right
    have h3 : x ^ 3 = Work.L2F.negOne F * x := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, hx2, pow_one]
    rw [h, h3, map_mul, pslMap_negOne_nochar F, one_mul]

/-! ## The main theorem -/

/-- For `x ∈ SL(2,F)` with `x² = -1` (so `⟨x⟩ = {1,x,-1,-x}`), the centralizer of the image of
`x` in `PSL(2,F)` is the image of the normalizer of `⟨x⟩`:
`y` lies in the centralizer iff `y x y⁻¹ = ±x` (the image of `yxy⁻¹` in `PSL` is the image of `x`
iff `yxy⁻¹ ∈ xZ = {±x}`), and `y x y⁻¹ = ±x` iff `y` normalizes `⟨x⟩`.  Uses the quotient
description of `Subgroup.map` / `QuotientGroup.mk'`. -/
theorem centralizer_eq_image_normalizer (F : Type*) [Field F]
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1) :
    Subgroup.centralizer ({Work.PSL2.pslMap F x} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (Subgroup.normalizer (Subgroup.zpowers x)).map (Work.PSL2.pslMap F) := by
  -- `z` by `-z` and `x` by `x³ = -x`: `⟨x⟩ = {1, x, -1, -x}`.
  ext g
  constructor
  · -- `g` centralizes `pslMap x`: lift it to `y ∈ SL(2,F)` and show that `y` normalizes `⟨x⟩`,
    -- because `y x y⁻¹ x⁻¹ ∈ ker pslMap = {±1}`.
    intro hg
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
    have hyg : Work.PSL2.pslMap F y = g := hy
    refine Subgroup.mem_map.mpr ⟨y, ?_, hyg⟩
    refine (mem_normalizer_zpowers F x hx y).mpr ?_
    have hcomm : Work.PSL2.pslMap F x * Work.PSL2.pslMap F y =
        Work.PSL2.pslMap F y * Work.PSL2.pslMap F x := by
      have h := (Subgroup.mem_centralizer_iff.mp hg) (Work.PSL2.pslMap F x) (by simp)
      rwa [← hyg] at h
    have hker : Work.PSL2.pslMap F (y * x * y⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    rcases (pslMap_eq_one_iff_nochar F (y * x * y⁻¹ * x⁻¹)).mp hker with h1 | h1
    · left
      rwa [mul_inv_eq_one] at h1
    · right
      have h2 : y * x * y⁻¹ = Work.L2F.negOne F * x := by
        have h3 := congrArg (fun t => t * x) h1
        rw [show (y * x * y⁻¹ * x⁻¹) * x = y * x * y⁻¹ from by group] at h3
        exact h3
      exact h2
  · -- Conversely, `y ∈ N(⟨x⟩)` forces `pslMap y` to centralize `pslMap x`: `y x y⁻¹ ∈ ⟨x⟩`, and
    -- the image of anything in `⟨x⟩` is `1` or `pslMap x`; in the first case `x` is conjugate to
    -- `1` or to `-1`, so `pslMap x = 1` as well.
    intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨y, hyN, rfl⟩ := hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hyx : y * x * y⁻¹ ∈ Subgroup.zpowers x :=
      ((Subgroup.mem_normalizer_iff.mp hyN) x).mp (Subgroup.mem_zpowers x)
    have hconj : Work.PSL2.pslMap F (y * x * y⁻¹) = Work.PSL2.pslMap F x := by
      rcases pslMap_zpowers_eq_or F x hx (y * x * y⁻¹) hyx with h | h
      · rcases (pslMap_eq_one_iff_nochar F (y * x * y⁻¹)).mp h with h1 | h1
        · have h2 : x = 1 := by
            have h3 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
            rw [h1] at h3
            rw [← h3]
            group
          rw [h, h2, map_one]
        · have h2 : x = Work.L2F.negOne F := by
            have h3 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
            rw [h1] at h3
            rw [← h3, ← negOne_mul_comm F y⁻¹]
            group
          rw [h, h2, pslMap_negOne_nochar F]
      · exact h
    calc Work.PSL2.pslMap F x * Work.PSL2.pslMap F y
        = Work.PSL2.pslMap F (y * x * y⁻¹) * Work.PSL2.pslMap F y := by rw [hconj]
      _ = Work.PSL2.pslMap F (y * x * y⁻¹ * y) := by
            rw [map_mul (Work.PSL2.pslMap F) (y * x * y⁻¹) y]
      _ = Work.PSL2.pslMap F (y * x) := by
            rw [show y * x * y⁻¹ * y = y * x from by group]
      _ = Work.PSL2.pslMap F y * Work.PSL2.pslMap F x := by
            rw [map_mul (Work.PSL2.pslMap F) y x]

end Work.L2F.Involution
