/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Injectivity and range of the general Magnus map `rhoC`

For a weight function `c : α → ℤ` with `c t = 1` the Magnus map

`rhoC (of t) c : F(α × ℤ) →* F α`,   `(x, i) ↦ t ^ i * x * t ^ (-i - c x)`

sends the symbol `(x, i)` to the conjugate `t ^ i * x * t ^ (-i - c x)`, whose weight under
`cohom c` is `1`.  Restricted to the symbols `(x, i)` with `x ≠ t` this map is injective and its
range is exactly `ker (cohom c)`.

The point of the present file is that this is *not* an independent fact: the conjugating
automorphism

`thetaInv (x) = x * t ^ (-(c x))`  (`x ≠ t`),  `thetaInv t = t`

(preserving `t`, with inverse `thetaHom x = x * t ^ (c x)`) intertwines `rhoC (of t) c` with the
classical Magnus map `magnusMap t : (x, i) ↦ t ^ i * x * t ^ (-i)`, whose injectivity and whose
range (the kernel of the exponent sum in `t`) are `Work.OROneRel.magnusMap_injective_range`.  Since
`c t = 1`, moreover `cohom c ∘ thetaInv = expSum t`, so the kernel is transported correctly.
-/
import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.magnusMap_injective_range

set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The conjugating automorphism of `F α` -/

/-- The homomorphism `F α →* F α` fixing `t` and sending `x ≠ t` to `x * t ^ (c x)`. -/
noncomputable def thetaHom (t : α) (c : α → ℤ) : FreeGroup α →* FreeGroup α := by
  classical
  exact FreeGroup.lift fun x =>
    if x = t then FreeGroup.of t else FreeGroup.of x * FreeGroup.of t ^ (c x)

/-- The homomorphism `F α →* F α` fixing `t` and sending `x ≠ t` to `x * t ^ (-(c x))`; the inverse
of `thetaHom`.  It conjugates the classical Magnus map `magnusMap t` into `rhoC (of t) c`. -/
noncomputable def thetaInv (t : α) (c : α → ℤ) : FreeGroup α →* FreeGroup α := by
  classical
  exact FreeGroup.lift fun x =>
    if x = t then FreeGroup.of t else FreeGroup.of x * FreeGroup.of t ^ (-(c x))

theorem thetaHom_of_t (t : α) (c : α → ℤ) :
    thetaHom t c (FreeGroup.of t) = FreeGroup.of t := by
  classical
  rw [thetaHom, FreeGroup.lift_apply_of, if_pos rfl]

theorem thetaInv_of_t (t : α) (c : α → ℤ) :
    thetaInv t c (FreeGroup.of t) = FreeGroup.of t := by
  classical
  rw [thetaInv, FreeGroup.lift_apply_of, if_pos rfl]

theorem thetaHom_of_ne (t : α) (c : α → ℤ) {x : α} (hx : x ≠ t) :
    thetaHom t c (FreeGroup.of x) = FreeGroup.of x * FreeGroup.of t ^ (c x) := by
  classical
  rw [thetaHom, FreeGroup.lift_apply_of, if_neg hx]

theorem thetaInv_of_ne (t : α) (c : α → ℤ) {x : α} (hx : x ≠ t) :
    thetaInv t c (FreeGroup.of x) = FreeGroup.of x * FreeGroup.of t ^ (-(c x)) := by
  classical
  rw [thetaInv, FreeGroup.lift_apply_of, if_neg hx]

theorem thetaHom_comp_thetaInv (t : α) (c : α → ℤ) :
    (thetaHom t c).comp (thetaInv t c) = MonoidHom.id (FreeGroup α) := by
  classical
  refine FreeGroup.ext_hom _ _ fun x => ?_
  by_cases hx : x = t
  · subst hx
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, thetaInv_of_t, thetaHom_of_t]
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply, thetaInv_of_ne t c hx, map_mul, map_zpow,
      thetaHom_of_ne t c hx, thetaHom_of_t]
    group

theorem thetaInv_comp_thetaHom (t : α) (c : α → ℤ) :
    (thetaInv t c).comp (thetaHom t c) = MonoidHom.id (FreeGroup α) := by
  classical
  refine FreeGroup.ext_hom _ _ fun x => ?_
  by_cases hx : x = t
  · subst hx
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, thetaHom_of_t, thetaInv_of_t]
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply, thetaHom_of_ne t c hx, map_mul, map_zpow,
      thetaInv_of_ne t c hx, thetaInv_of_t]
    group

theorem thetaHom_thetaInv (t : α) (c : α → ℤ) (x : FreeGroup α) :
    thetaHom t c (thetaInv t c x) = x :=
  DFunLike.congr_fun (thetaHom_comp_thetaInv t c) x

theorem thetaInv_thetaHom (t : α) (c : α → ℤ) (x : FreeGroup α) :
    thetaInv t c (thetaHom t c x) = x :=
  DFunLike.congr_fun (thetaInv_comp_thetaHom t c) x

theorem thetaInv_injective (t : α) (c : α → ℤ) : Function.Injective (thetaInv t c) := by
  intro x y hxy
  rw [← thetaHom_thetaInv t c x, hxy, thetaHom_thetaInv t c y]

theorem thetaInv_surjective (t : α) (c : α → ℤ) : Function.Surjective (thetaInv t c) :=
  fun y => ⟨thetaHom t c y, thetaInv_thetaHom t c y⟩

/-! ## `rhoC (of t) c` is `thetaInv` conjugated into the classical Magnus map -/

/-- The defining value of `rhoC` on a single symbol. -/
theorem rhoC_of (τ : FreeGroup α) (c : α → ℤ) (p : α × ℤ) :
    rhoC τ c (FreeGroup.of p) = τ ^ p.2 * FreeGroup.of p.1 * τ ^ (-(p.2) - c p.1) := by
  rw [rhoC, FreeGroup.lift_apply_of]

/-- The general Magnus map `rhoC (of t) c`, restricted to the symbols `(x, i)` with `x ≠ t`, is
`thetaInv` applied to the classical Magnus map `magnusMap t`. -/
theorem rhoC_map_apply (t : α) (c : α → ℤ) (v : FreeGroup ({x : α // x ≠ t} × ℤ)) :
    Work.OROneRel.rhoC (FreeGroup.of t) c
        (FreeGroup.map (fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2)) v)
      = thetaInv t c (magnusMap t v) := by
  classical
  refine FreeGroup.induction_on v ?_ ?_ ?_ ?_
  · simp only [map_one]
  · intro s
    obtain ⟨y, i⟩ := s
    rw [FreeGroup.map.of, rhoC_of, magnusMap_apply, map_mul, map_mul, map_zpow, map_zpow,
      thetaInv_of_t, thetaInv_of_ne t c y.2]
    group
  · intro s ih
    simp only [map_inv, ih]
  · intro u w ihu ihw
    simp only [map_mul, ihu, ihw]

/-- The general Magnus map and the classical Magnus map agree after conjugation by `thetaInv`. -/
theorem rhoC_comp_map_eq (t : α) (c : α → ℤ) :
    (Work.OROneRel.rhoC (FreeGroup.of t) c).comp
        (FreeGroup.map (fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2)))
      = (thetaInv t c).comp (magnusMap t) := by
  classical
  refine FreeGroup.ext_hom _ _ fun s => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact rhoC_map_apply t c (FreeGroup.of s)

/-! ## The kernel is transported by `thetaInv` -/

theorem cohom_comp_thetaInv (t : α) (c : α → ℤ) (hc : c t = 1) :
    (cohom c).comp (thetaInv t c) = expSum t := by
  classical
  refine FreeGroup.ext_hom _ _ fun x => ?_
  by_cases hx : x = t
  · subst hx
    rw [MonoidHom.comp_apply, thetaInv_of_t, cohom_of, hc, expSum, FreeGroup.lift_apply_of,
      if_pos rfl]
  · rw [MonoidHom.comp_apply, thetaInv_of_ne t c hx, map_mul, map_zpow, cohom_of, cohom_of,
      expSum, FreeGroup.lift_apply_of, if_neg hx, hc]
    rw [← Int.ofAdd_mul, one_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero]

theorem cohom_thetaInv (t : α) (c : α → ℤ) (hc : c t = 1) (x : FreeGroup α) :
    cohom c (thetaInv t c x) = expSum t x :=
  DFunLike.congr_fun (cohom_comp_thetaInv t c hc) x

theorem map_thetaInv_ker (t : α) (c : α → ℤ) (hc : c t = 1) :
    Subgroup.map (thetaInv t c) (expSum t).ker = (cohom c).ker := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [cohom_thetaInv t c hc x]
    exact hx
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨thetaHom t c y, ?_, thetaInv_thetaHom t c y⟩
    rw [MonoidHom.mem_ker] at hy
    rw [MonoidHom.mem_ker, ← cohom_thetaInv t c hc (thetaHom t c y), thetaInv_thetaHom]
    exact hy

/-! ## The statement -/

theorem rhoC_injective_range {α : Type u} (t : α) (c : α → ℤ) (hc : c t = 1) :
    Function.Injective (fun v : FreeGroup ({x : α // x ≠ t} × ℤ) =>
        Work.OROneRel.rhoC (FreeGroup.of t) c
          (FreeGroup.map (fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2)) v)) ∧
      ((Work.OROneRel.rhoC (FreeGroup.of t) c).comp
        (FreeGroup.map (fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2)))).range
        = (Work.OROneRel.cohom c).ker := by
  classical
  refine ⟨?_, ?_⟩
  · change Function.Injective ⇑((Work.OROneRel.rhoC (FreeGroup.of t) c).comp
      (FreeGroup.map (fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2))))
    rw [rhoC_comp_map_eq t c]
    intro a b hab
    exact magMagnusMap_injective t (thetaInv_injective t c hab)
  · rw [rhoC_comp_map_eq t c, MonoidHom.range_comp, magRange_eq_ker t, map_thetaInv_ker t c hc]

end Work.OROneRel
