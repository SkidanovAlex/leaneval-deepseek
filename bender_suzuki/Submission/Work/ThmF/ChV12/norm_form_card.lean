import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

section
variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- In a finite field of characteristic two, squaring (the Frobenius map) is a bijection. -/
theorem sq_bijective : Function.Bijective (fun x : F => x ^ 2) :=
  ⟨fun _ _ h => CharTwo.sq_inj.mp h,
   Finite.surjective_of_injective (fun _ _ h => CharTwo.sq_inj.mp h)⟩

/-- The square root (inverse Frobenius) in a finite field of characteristic two. -/
noncomputable def sqrtc (a : F) : F :=
  (Equiv.ofBijective (fun x : F => x ^ 2) sq_bijective).symm a

theorem sqrtc_sq (a : F) : (sqrtc a) ^ 2 = a := by
  have h := Equiv.apply_symm_apply (Equiv.ofBijective (fun x : F => x ^ 2) sq_bijective) a
  rwa [Equiv.ofBijective_apply] at h

theorem sqrtc_ne_zero {a : F} (ha : a ≠ 0) : sqrtc a ≠ 0 := by
  intro h
  have : a = 0 := by rw [← sqrtc_sq a, h]; simp
  exact ha this

omit [Fintype F] in
theorem sq_eq_one {x : F} (h : x ^ 2 = 1) : x = 1 := by
  have h' : x ^ 2 = 1 ^ 2 := by rwa [one_pow]
  exact CharTwo.sq_inj.mp h'

/-- The element `s` with `s ^ 2 = (t ^ 2 + t + 1)⁻¹`. -/
noncomputable def sqinv (t : F) : F := sqrtc ((t ^ 2 + t + 1)⁻¹)

theorem sqinv_sq (t : F) : (sqinv t) ^ 2 = (t ^ 2 + t + 1)⁻¹ := sqrtc_sq _

theorem sqinv_ne_zero (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) (t : F) : sqinv t ≠ 0 :=
  sqrtc_ne_zero (inv_ne_zero (hroot t))

/-- The point `(t·s, s)` with `s ^ 2 = (t ^ 2 + t + 1)⁻¹`, lying on the curve. -/
noncomputable def invPt (t : F) : F × F := (t * sqinv t, sqinv t)

theorem invPt_mem (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) (t : F) :
    (invPt t).1 ^ 2 + (invPt t).1 * (invPt t).2 + (invPt t).2 ^ 2 = 1 := by
  unfold invPt
  simp only
  rw [show (t * sqinv t) ^ 2 + (t * sqinv t) * sqinv t + (sqinv t) ^ 2
        = (sqinv t) ^ 2 * (t ^ 2 + t + 1) from by ring,
      sqinv_sq, inv_mul_cancel₀ (hroot t)]

/-- The map from the curve to `Option F`, sending `(x, y)` with `y ≠ 0` to `x / y` and the
point `(1, 0)` to `none`. -/
noncomputable def cTo [DecidableEq F]
    (p : {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1}) : Option F :=
  if p.1.2 = 0 then none else some (p.1.1 / p.1.2)

/-- The inverse map: `none ↦ (1, 0)` and `t ↦ (t·s, s)`. -/
noncomputable def cInv (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) (o : Option F) :
    {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} :=
  match o with
  | none => ⟨(1, 0), by simp⟩
  | some t => ⟨invPt t, invPt_mem hroot t⟩

theorem c_left [DecidableEq F] (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) :
    Function.LeftInverse (cInv hroot) cTo := by
  rintro ⟨⟨x, y⟩, hxy⟩
  unfold cTo
  by_cases hy : y = 0
  · rw [ite_eq_left hy]
    unfold cInv
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    have hx1 : x = 1 := by
      apply sq_eq_one
      have h := hxy
      rw [hy] at h
      simpa using h
    exact ⟨hx1.symm, hy.symm⟩
  · rw [ite_eq_right hy]
    unfold cInv invPt
    apply Subtype.ext
    set t := x / y with ht
    simp only [Prod.mk.injEq]
    have hxy' : y ^ 2 * (t ^ 2 + t + 1) = 1 := by
      have hx : x = t * y := by rw [ht, div_mul_cancel₀ _ hy]
      rw [hx] at hxy
      rw [show (t * y) ^ 2 + (t * y) * y + y ^ 2 = y ^ 2 * (t ^ 2 + t + 1) from by ring] at hxy
      exact hxy
    have hy2eq : y ^ 2 = (t ^ 2 + t + 1)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hy2 : y ^ 2 = (sqinv t) ^ 2 := by rw [hy2eq, sqinv_sq]
    have hsy : sqinv t = y := (CharTwo.sq_inj.mp hy2).symm
    have htx : t * sqinv t = x := by rw [hsy, ht, div_mul_cancel₀ _ hy]
    exact ⟨htx, hsy⟩

theorem c_right [DecidableEq F] (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) :
    Function.RightInverse (cInv hroot) cTo := by
  intro o
  cases o with
  | none =>
    unfold cInv cTo
    simp
  | some t =>
    unfold cInv cTo invPt
    simp only
    have hs : sqinv t ≠ 0 := sqinv_ne_zero hroot t
    rw [ite_eq_right hs]
    congr 1
    exact mul_div_cancel_right₀ t hs

/-- The conic `x ^ 2 + x * y + y ^ 2 = 1` over a finite field of characteristic two in which
`X ^ 2 + X + 1` has no root is in bijection with `Option F`. -/
noncomputable def curveEquiv [DecidableEq F] (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) :
    {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} ≃ Option F :=
  { toFun := cTo
    invFun := cInv hroot
    left_inv := c_left hroot
    right_inv := c_right hroot }

end

theorem norm_form_card {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) :
    Nat.card {p : F × F // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = 1} = Nat.card F + 1 := by
  classical
  rw [Nat.card_congr (curveEquiv hroot)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

end Work.ThmF.ChV12
