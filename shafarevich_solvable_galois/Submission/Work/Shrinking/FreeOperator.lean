/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Free `G`-operator groups and the shrinking retraction (discrete version)

In the shrinking procedure (Schmidt–Wingberg, Section 2) one uses the free pro-`p`
`G`-operator group `F(d) = G ⋉ F_d` of rank `d`: a free pro-`p` group with a continuous
action of the finite group `G`, with a basis `x_{i,g}` on which `G` acts by
`g' • x_{i,g} = x_{i,g' g}`.  The key point of the procedure is that for `m ≥ n` there is a
surjective `G`-operator homomorphism `F(m) → F(n)`, and the shrinking lemma lets one choose
this map so that all obstructions for the `ν`-th induction step vanish.

This file provides the *discrete* analogue: the free group on `Fin d × G` with the `G`-action
permuting the generators, together with the `G`-equivariant surjection `F(m) → F(n)` for
`n ≤ m` which kills the generators `x_{i,g}` for `n ≤ i`.  (The pro-`p` version would
additionally require the pro-`p` completion; it is not formalized here.)

## Main results

* `Work.Shrinking.freeOperatorGroup` : the discrete free `G`-operator group of rank `d`.
* `Work.Shrinking.instMulDistribMulActionFreeOperatorGroup` : the `G`-action permuting the
  generators, `g • x_{i,g'} = x_{i,g * g'}`.
* `Work.Shrinking.freeOperatorRetract` : for `n ≤ m`, the homomorphism
  `F(m) → F(n)` killing the generators of index `≥ n`.
* `Work.Shrinking.freeOperatorRetract_surjective`,
  `Work.Shrinking.freeOperatorRetract_smul` : it is surjective and `G`-equivariant.
* `Work.Shrinking.map_pCentralSeries_retract` : it maps the `ν`-th term of the descending
  `p`-central series onto the corresponding term (functoriality).
-/

import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

universe u

variable {G : Type*} [Group G]

/-- The discrete free `G`-operator group of rank `d`: the free group on `Fin d × G`, on whose
generators `G` acts by `g • x_{i,g'} = x_{i,g * g'}`. -/
abbrev freeOperatorGroup (G : Type*) [Group G] (d : ℕ) : Type _ := FreeGroup (Fin d × G)

/-- The permutation `x_{i,g'} ↦ x_{i,g * g'}` of the generating set of the free `G`-operator
group. -/
def freeOperatorGenPerm (d : ℕ) (g : G) : (Fin d × G) ≃ (Fin d × G) where
  toFun x := (x.1, g * x.2)
  invFun x := (x.1, g⁻¹ * x.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp]
lemma freeOperatorGenPerm_apply (d : ℕ) (g : G) (x : Fin d × G) :
    freeOperatorGenPerm d g x = (x.1, g * x.2) := rfl

@[simp]
lemma freeOperatorGenPerm_symm_apply (d : ℕ) (g : G) (x : Fin d × G) :
    (freeOperatorGenPerm (G := G) d g).symm x = (x.1, g⁻¹ * x.2) := rfl

lemma freeOperatorGenPerm_one (d : ℕ) : freeOperatorGenPerm (G := G) d 1 = Equiv.refl _ := by
  refine Equiv.ext fun x => ?_
  simp [freeOperatorGenPerm]

lemma freeOperatorGenPerm_mul (d : ℕ) (g h : G) :
    freeOperatorGenPerm (G := G) d (g * h)
      = (freeOperatorGenPerm (G := G) d h).trans (freeOperatorGenPerm (G := G) d g) := by
  refine Equiv.ext fun x => ?_
  simp [freeOperatorGenPerm, mul_assoc]

/-- The monoid homomorphism `G →* MulAut (F(d))` giving the action on the free `G`-operator
group. -/
noncomputable def freeOperatorActionHom (d : ℕ) : G →* MulAut (freeOperatorGroup G d) where
  toFun g := FreeGroup.freeGroupCongr (freeOperatorGenPerm (G := G) d g)
  map_one' := by
    rw [freeOperatorGenPerm_one, FreeGroup.freeGroupCongr_refl]
    rfl
  map_mul' g h := by
    rw [freeOperatorGenPerm_mul, ← FreeGroup.freeGroupCongr_trans]
    rfl

/-- The action of `G` on the free `G`-operator group of rank `d` by permuting generators. -/
noncomputable instance instMulDistribMulActionFreeOperatorGroup (d : ℕ) :
    MulDistribMulAction G (freeOperatorGroup G d) where
  smul g x := freeOperatorActionHom (G := G) d g x
  one_smul x := by
    show freeOperatorActionHom (G := G) d 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    show freeOperatorActionHom (G := G) d (g * h) x
      = freeOperatorActionHom (G := G) d g (freeOperatorActionHom (G := G) d h x)
    rw [map_mul]
    rfl
  smul_mul g x y := map_mul _ _ _
  smul_one g := map_one _

/-- The action on the generators. -/
@[simp]
lemma smul_freeOperator_of (d : ℕ) (g : G) (x : Fin d × G) :
    g • FreeGroup.of x = FreeGroup.of (x.1, g * x.2) := by
  change FreeGroup.freeGroupCongr (freeOperatorGenPerm (G := G) d g) (FreeGroup.of x) = _
  rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
  rfl

@[simp]
lemma smul_freeOperatorGroup_eq (d : ℕ) (g : G) (x : freeOperatorGroup G d) :
    g • x = freeOperatorActionHom (G := G) d g x := rfl

/-- The map on generators defining the retraction `F(m) → F(n)`: the generators `x_{i,g}`
with `i < n` are kept, the others are sent to `1`. -/
def freeOperatorRetractGen {m n : ℕ} (_h : n ≤ m) : Fin m × G → FreeGroup (Fin n × G) :=
  fun x => if hx : (x.1 : ℕ) < n then FreeGroup.of (⟨x.1, hx⟩, x.2) else 1

/-- For `n ≤ m` the homomorphism `F(m) → F(n)` of free `G`-operator groups which is the
identity on the generators `x_{i,g}` with `i < n` and kills the remaining generators. -/
noncomputable def freeOperatorRetract {m n : ℕ} (h : n ≤ m) :
    freeOperatorGroup G m →* freeOperatorGroup G n :=
  FreeGroup.lift (freeOperatorRetractGen (G := G) h)

lemma freeOperatorRetract_eq_lift {m n : ℕ} (h : n ≤ m) :
    freeOperatorRetract (G := G) h = FreeGroup.lift (freeOperatorRetractGen (G := G) h) := rfl

@[simp]
lemma freeOperatorRetract_of {m n : ℕ} (_h : n ≤ m) (x : Fin m × G) :
    freeOperatorRetract (G := G) _h (FreeGroup.of x)
      = if hx : (x.1 : ℕ) < n then FreeGroup.of (⟨x.1, hx⟩, x.2) else 1 :=
  FreeGroup.lift_apply_of

/-- On the generators of the smaller operator group, the retraction is the identity. -/
lemma freeOperatorRetract_gen {m n : ℕ} (h : n ≤ m) (i : Fin n) (g : G) :
    freeOperatorRetract (G := G) h
        (FreeGroup.of ((⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin m), g))
      = FreeGroup.of (i, g) := by
  rw [freeOperatorRetract_of, dif_pos i.2]

/-- The retraction `F(m) → F(n)` is surjective. -/
theorem freeOperatorRetract_surjective {m n : ℕ} (h : n ≤ m) :
    Function.Surjective (freeOperatorRetract (G := G) h) := by
  rw [← MonoidHom.range_eq_top, freeOperatorRetract_eq_lift, FreeGroup.range_lift_eq_closure]
  apply le_antisymm le_top
  rw [← FreeGroup.closure_range_of (Fin n × G)]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨((⟨x.1.1, lt_of_lt_of_le x.1.2 h⟩ : Fin m), x.2),
    by simp [freeOperatorRetractGen]⟩

/-- The retraction `F(m) → F(n)` is `G`-equivariant. -/
theorem freeOperatorRetract_smul {m n : ℕ} (h : n ≤ m) (g : G) (x : freeOperatorGroup G m) :
    freeOperatorRetract (G := G) h (g • x) = g • freeOperatorRetract (G := G) h x := by
  have key : ∀ y : Fin m × G,
      freeOperatorRetract (G := G) h (g • FreeGroup.of y)
        = g • freeOperatorRetract (G := G) h (FreeGroup.of y) := by
    intro y
    rw [smul_freeOperator_of, freeOperatorRetract_of, freeOperatorRetract_of]
    by_cases hy : (y.1 : ℕ) < n
    · rw [dif_pos hy, dif_pos hy, smul_freeOperator_of]
    · rw [dif_neg hy, dif_neg (by simpa using hy), smul_one]
  induction x using FreeGroup.induction_on with
  | one => simp
  | of y => exact key y
  | inv_of y ih =>
      simp only [smul_freeOperatorGroup_eq] at ih ⊢
      simp only [map_inv, ih]
  | mul x y ihx ihy =>
      simp only [smul_freeOperatorGroup_eq] at ihx ihy ⊢
      simp only [map_mul, ihx, ihy]

end Work.Shrinking
