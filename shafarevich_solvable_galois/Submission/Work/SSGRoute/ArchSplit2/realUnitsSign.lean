import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchSplit2

open Additive

/-- The sign of a real unit, `0` for a positive unit and `1` for a negative one, as a function
valued in `ZMod 2`.  Its additivity (for the multiplicative structure on `ℝˣ`) is the content of
`sgnFun_mul`. -/
private noncomputable def sgnFun (u : ℝˣ) : ZMod 2 := if (0 : ℝ) < (u : ℝ) then 0 else 1

private lemma sgnFun_mul (u v : ℝˣ) : sgnFun (u * v) = sgnFun u + sgnFun v := by
  unfold sgnFun
  rw [Units.val_mul]
  rcases lt_or_gt_of_ne (Ne.symm u.ne_zero) with hu | hu
  · rcases lt_or_gt_of_ne (Ne.symm v.ne_zero) with hv | hv
    · rw [if_pos (mul_pos hu hv), if_pos hu, if_pos hv]; simp
    · rw [if_neg (not_lt.mpr (mul_neg_of_pos_of_neg hu hv).le), if_pos hu,
        if_neg (not_lt.mpr hv.le)]; simp
  · rcases lt_or_gt_of_ne (Ne.symm v.ne_zero) with hv | hv
    · rw [if_neg (not_lt.mpr (mul_neg_of_neg_of_pos hu hv).le), if_neg (not_lt.mpr hu.le),
        if_pos hv]; simp
    · rw [if_pos (mul_pos_of_neg_of_neg hu hv), if_neg (not_lt.mpr hu.le),
        if_neg (not_lt.mpr hv.le)]; decide

private lemma sgnFun_eq_zero_iff (u : ℝˣ) : sgnFun u = 0 ↔ (0 : ℝ) < (u : ℝ) := by
  unfold sgnFun
  constructor
  · intro h
    by_contra hlt
    rw [if_neg hlt] at h
    exact one_ne_zero h
  · intro h; exact if_pos h

/-- The sign presented as a homomorphism `Additive ℝˣ →+ ZMod 2`. -/
private noncomputable def sgnHom : Additive ℝˣ →+ ZMod 2 :=
  AddMonoidHom.mk' (fun x => sgnFun x.toMul) (by
    intro x y
    rw [toMul_add]
    exact sgnFun_mul x.toMul y.toMul)

private lemma sgnHom_ofMul (u : ℝˣ) : sgnHom (Additive.ofMul u) = sgnFun u := rfl

/-- The section of `sgnFun` on `±1`, presented as a function `ZMod 2 → Additive ℝˣ`. -/
private noncomputable def liftFun (c : ZMod 2) : Additive ℝˣ :=
  if c = 0 then 0 else Additive.ofMul (-1 : ℝˣ)

/-- The only nonzero element of `ZMod 2` is `1`. -/
private lemma zmod2_eq_one_of_ne_zero (c : ZMod 2) (h : c ≠ 0) : c = 1 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with h0 | h1
  · exact absurd h0 h
  · exact h1

private lemma liftFun_add (a b : ZMod 2) : liftFun (a + b) = liftFun a + liftFun b := by
  by_cases ha : a = 0
  · subst ha; simp [liftFun]
  · by_cases hb : b = 0
    · subst hb; simp [liftFun, ha]
    · have hab : a + b = 0 := by
        rw [zmod2_eq_one_of_ne_zero a ha, zmod2_eq_one_of_ne_zero b hb]; decide
      rw [hab]
      unfold liftFun
      rw [if_pos rfl, if_neg ha, if_neg hb]
      rw [← ofMul_mul, show (-1 : ℝˣ) * (-1) = 1 by simp, ofMul_one]

/-- The section of `sgn` on `±1`, presented as a homomorphism `ZMod 2 →+ Additive ℝˣ`. -/
private noncomputable def liftHom : ZMod 2 →+ Additive ℝˣ :=
  AddMonoidHom.mk' liftFun liftFun_add

private lemma liftHom_apply (c : ZMod 2) : liftHom c = liftFun c := rfl

private lemma liftHom_one : liftHom (1 : ZMod 2) = Additive.ofMul (-1 : ℝˣ) := by
  rw [liftHom_apply]
  show liftFun (1 : ZMod 2) = Additive.ofMul (-1 : ℝˣ)
  simp [liftFun]

private lemma sgnHom_liftHom (c : ZMod 2) : sgnHom (liftHom c) = c := by
  rw [liftHom_apply]
  by_cases hc : c = 0
  · rw [hc]
    show sgnHom (liftFun 0) = 0
    rw [show liftFun (0 : ZMod 2) = 0 by simp [liftFun]]
    exact map_zero sgnHom
  · rw [zmod2_eq_one_of_ne_zero c hc]
    show sgnHom (liftFun 1) = 1
    rw [show liftFun (1 : ZMod 2) = Additive.ofMul (-1 : ℝˣ) by simp [liftFun]]
    rw [sgnHom_ofMul]
    exact show sgnFun (-1 : ℝˣ) = 1 by unfold sgnFun; simp

/-- The sign data of `ℝˣ`: `sgn : Additive ℝˣ →+ ZMod 2` with kernel the squares (`2 • y`), and a
section `lift : ZMod 2 →+ Additive ℝˣ` onto `±1` which is injective and hits the `2`-torsion. -/
theorem realUnitsSign :
    ∃ (sgn : Additive ℝˣ →+ ZMod 2) (lift : ZMod 2 →+ Additive ℝˣ),
      (∀ c : ZMod 2, sgn (lift c) = c) ∧
      Function.Injective lift ∧
      (∀ x : Additive ℝˣ, sgn x = 0 ↔ ∃ y : Additive ℝˣ, 2 • y = x) ∧
      (∀ x : Additive ℝˣ, 2 • x = 0 → ∃ c : ZMod 2, x = lift c) := by
  refine ⟨sgnHom, liftHom, sgnHom_liftHom, ?_, ?_, ?_⟩
  · intro a b h
    have hh := congrArg sgnHom h
    rwa [sgnHom_liftHom a, sgnHom_liftHom b] at hh
  · intro x
    constructor
    · intro hx
      have hxpos : (0 : ℝ) < (x.toMul : ℝ) := (sgnFun_eq_zero_iff x.toMul).mp hx
      let u : ℝˣ := Units.mk0 (Real.sqrt (x.toMul : ℝ)) (ne_of_gt (Real.sqrt_pos_of_pos hxpos))
      refine ⟨Additive.ofMul u, ?_⟩
      have hu : (u : ℝ) = Real.sqrt (x.toMul : ℝ) := Units.val_mk0 _
      have huu : u * u = x.toMul := by
        refine Units.ext ?_
        rw [Units.val_mul, hu, ← sq, Real.sq_sqrt (le_of_lt hxpos)]
      have h2 : (2 : ℕ) • (Additive.ofMul u) = Additive.ofMul (u * u) := by
        rw [two_nsmul, ofMul_mul]
      rw [h2, huu]
      exact (ofMul_toMul x).symm
    · intro hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy, map_nsmul, nsmul_eq_mul, ZMod.natCast_self 2, zero_mul]
  · intro x hx
    have h1 : x.toMul ^ 2 = (1 : ℝˣ) := by
      have hh := congrArg Additive.toMul hx
      rwa [toMul_nsmul, toMul_zero] at hh
    have h2 : ((x.toMul : ℝˣ) : ℝ) ^ 2 = 1 := by
      have hh := congrArg (fun u : ℝˣ => (u : ℝ)) h1
      simpa using hh
    rcases sq_eq_one_iff.mp h2 with hpos | hneg
    · refine ⟨0, ?_⟩
      have hx1 : x.toMul = 1 := Units.ext hpos
      have hx0 : x = 0 := toMul_eq_one.mp hx1
      rw [hx0, map_zero]
    · refine ⟨1, ?_⟩
      have hxm1 : x.toMul = (-1 : ℝˣ) := Units.ext (by simpa using hneg)
      rw [liftHom_one, ← hxm1]
      exact (ofMul_toMul x).symm

end Work.SSGRoute.ArchSplit2
