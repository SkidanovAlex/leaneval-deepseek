/-
# `GaussFourier`: the finite Fourier analysis on the Gaussian residue ring.

Orthogonality of the additive characters `θ ↦ e^{2πi Re(x θ̄)/(4d)}` of `(ℤ[i]/4d)`, the resulting
Parseval identity, and the substitution that computes `Fhat` at a unit.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.GaussChi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

namespace GaussBasic

variable {d : ℕ} [NeZero (4 * d)]

/-- Conjugation inverts the standard additive character. -/
lemma star_stdAddChar (t : ZMod (4 * d)) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  have h : ZMod.toCircle (-t) = (ZMod.toCircle t)⁻¹ := AddChar.map_neg_eq_inv _ t
  simp only [ZMod.stdAddChar_apply]
  rw [h, Circle.coe_inv_eq_conj]
  rfl

lemma stdAddChar_eq_one_iff {t : ZMod (4 * d)} :
    ZMod.stdAddChar t = 1 ↔ t = 0 :=
  ⟨fun h => ZMod.injective_stdAddChar (by rw [ZMod.stdAddChar.map_zero_eq_one]; exact h),
   fun h => by rw [h]; exact ZMod.stdAddChar.map_zero_eq_one⟩

/-- The sum of a nontrivial additive character of `ZMod (4d)` vanishes. -/
lemma sum_stdAddChar_mul (c : ZMod (4 * d)) :
    (∑ a : ZMod (4 * d), ZMod.stdAddChar (a * c))
      = if c = 0 then (((4 * d : ℕ)) : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    simp [ZMod.card]
  · rw [if_neg hc]
    let ψ : AddChar (ZMod (4 * d)) ℂ :=
      { toFun := fun a => ZMod.stdAddChar (a * c)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := by intro a b; rw [add_mul, AddChar.map_add_eq_mul] }
    have hψ : ψ ≠ 1 := by
      rw [AddChar.ne_one_iff]
      refine ⟨1, ?_⟩
      show ZMod.stdAddChar (1 * c) ≠ 1
      rw [one_mul]
      intro hcon
      exact hc (stdAddChar_eq_one_iff.mp hcon)
    have h := AddChar.sum_eq_zero_of_ne_one hψ
    simpa [ψ] using h

lemma pairG_neg (θ x : ZMod (4 * d) × ZMod (4 * d)) : pairG d θ (-x) = -pairG d θ x := by
  simp only [pairG, Prod.fst_neg, Prod.snd_neg]; ring

lemma pairG_sub (θ x y : ZMod (4 * d) × ZMod (4 * d)) :
    pairG d θ (x - y) = pairG d θ x - pairG d θ y := by
  simp only [pairG, Prod.fst_sub, Prod.snd_sub]; ring

lemma pairG_add (θ x y : ZMod (4 * d) × ZMod (4 * d)) :
    pairG d θ (x + y) = pairG d θ x + pairG d θ y := by
  simp only [pairG, Prod.fst_add, Prod.snd_add]; ring

lemma stdAddChar_mul (a b : ZMod (4 * d)) :
    ZMod.stdAddChar a * ZMod.stdAddChar b = ZMod.stdAddChar (a + b) :=
  (AddChar.map_add_eq_mul (ZMod.stdAddChar (N := 4 * d)) a b).symm

lemma star_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    star (∑ i ∈ s, g i) = ∑ i ∈ s, star (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Orthogonality of the additive characters of `(ℤ[i]/(4d))²`. -/
lemma sum_stdAddChar_pairG (x : ZMod (4 * d) × ZMod (4 * d)) :
    (∑ θ : ZMod (4 * d) × ZMod (4 * d), ZMod.stdAddChar (pairG d θ x))
      = if x = 0 then ((((4 * d : ℕ)) : ℂ) * (((4 * d : ℕ)) : ℂ)) else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [pairG, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum]
  have h1 : (∑ b : ZMod (4*d), ZMod.stdAddChar (x.1 * b))
      = ∑ b : ZMod (4*d), ZMod.stdAddChar (b * x.1) := by
    exact Finset.sum_congr rfl (fun b _ => by rw [mul_comm x.1 b])
  have h2 : (∑ b : ZMod (4*d), ZMod.stdAddChar (x.2 * b))
      = ∑ b : ZMod (4*d), ZMod.stdAddChar (b * x.2) := by
    exact Finset.sum_congr rfl (fun b _ => by rw [mul_comm x.2 b])
  rw [h1, h2, sum_stdAddChar_mul x.1, sum_stdAddChar_mul x.2]
  have hx : x = 0 ↔ x.1 = 0 ∧ x.2 = 0 :=
    ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1,h2⟩ => by ext <;> assumption⟩
  by_cases h : x = 0
  · obtain ⟨h1', h2'⟩ := hx.mp h
    rw [if_pos h1', if_pos h2', if_pos h]
  · have hnn : ¬ (x.1 = 0 ∧ x.2 = 0) := fun hh => h (hx.mpr hh)
    rcases not_and_or.mp hnn with h1' | h2'
    · rw [if_neg h1', if_neg h, zero_mul]
    · rw [if_neg h2', if_neg h, mul_zero]

/-! ## Parseval -/

open Classical in
/-- Parseval's identity for the finite Fourier transform on `(ℤ[i]/(4d))²`. -/
lemma parseval (f : ZMod (4 * d) × ZMod (4 * d) → ℂ) :
    (∑ θ : ZMod (4 * d) × ZMod (4 * d),
        (∑ x, f x * ZMod.stdAddChar (pairG d θ x))
          * star (∑ x, f x * ZMod.stdAddChar (pairG d θ x)))
      = ((((4 * d : ℕ)) : ℂ) * ((((4 * d : ℕ)) : ℂ))) * ∑ x, f x * star (f x) := by
  have hstar : ∀ θ : ZMod (4 * d) × ZMod (4 * d),
      star (∑ x, f x * ZMod.stdAddChar (pairG d θ x))
        = ∑ y, star (f y) * ZMod.stdAddChar (pairG d θ (-y)) := by
    intro θ
    rw [show star (∑ x, f x * ZMod.stdAddChar (pairG d θ x))
        = ∑ x, star (f x * ZMod.stdAddChar (pairG d θ x)) from star_sum Finset.univ _]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [star_mul, star_stdAddChar, ← pairG_neg θ y]
    ring
  have hcomb : ∀ (θ x y : ZMod (4 * d) × ZMod (4 * d)),
      (f x * ZMod.stdAddChar (pairG d θ x)) * (star (f y) * ZMod.stdAddChar (pairG d θ (-y)))
        = (f x * star (f y)) * ZMod.stdAddChar (pairG d θ (x - y)) := by
    intro θ x y
    rw [show (f x * ZMod.stdAddChar (pairG d θ x))
          * (star (f y) * ZMod.stdAddChar (pairG d θ (-y)))
        = (f x * star (f y)) * (ZMod.stdAddChar (pairG d θ x)
            * ZMod.stdAddChar (pairG d θ (-y))) from by ring]
    rw [stdAddChar_mul, pairG_neg, pairG_sub, sub_eq_add_neg]
  calc (∑ θ : ZMod (4 * d) × ZMod (4 * d),
        (∑ x, f x * ZMod.stdAddChar (pairG d θ x))
          * star (∑ x, f x * ZMod.stdAddChar (pairG d θ x)))
      = ∑ θ : ZMod (4 * d) × ZMod (4 * d),
          (∑ x, f x * ZMod.stdAddChar (pairG d θ x))
            * (∑ y, star (f y) * ZMod.stdAddChar (pairG d θ (-y))) := by
        refine Finset.sum_congr rfl (fun θ _ => ?_); rw [hstar θ]
    _ = ∑ θ : ZMod (4 * d) × ZMod (4 * d),
          ∑ x, ∑ y, (f x * ZMod.stdAddChar (pairG d θ x))
            * (star (f y) * ZMod.stdAddChar (pairG d θ (-y))) := by
        refine Finset.sum_congr rfl (fun θ _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ θ : ZMod (4 * d) × ZMod (4 * d),
          ∑ x, ∑ y, (f x * star (f y)) * ZMod.stdAddChar (pairG d θ (x - y)) := by
        refine Finset.sum_congr rfl (fun θ _ => Finset.sum_congr rfl (fun x _ =>
          Finset.sum_congr rfl (fun y _ => hcomb θ x y)))
    _ = ∑ x : ZMod (4 * d) × ZMod (4 * d),
          ∑ y, ∑ θ, (f x * star (f y)) * ZMod.stdAddChar (pairG d θ (x - y)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ x : ZMod (4 * d) × ZMod (4 * d),
          ∑ y, (f x * star (f y)) * (if x = y
            then ((((4 * d : ℕ)) : ℂ) * ((((4 * d : ℕ)) : ℂ))) else 0) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [← Finset.mul_sum, sum_stdAddChar_pairG]
        simp only [sub_eq_zero]
    _ = ∑ x : ZMod (4 * d) × ZMod (4 * d),
          (f x * star (f x)) * ((((4 * d : ℕ)) : ℂ) * ((((4 * d : ℕ)) : ℂ))) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl]
        · intro y _ hyx; rw [if_neg (Ne.symm hyx), mul_zero]
        · intro hx; exact absurd (Finset.mem_univ x) hx
    _ = ((((4 * d : ℕ)) : ℂ) * ((((4 * d : ℕ)) : ℂ))) * ∑ x, f x * star (f x) := by
        rw [← Finset.sum_mul]; ring

/-! ## Reindexing the box `[0, 4d)²` as the residue group -/

lemma sum_zmod_val_eq {n : ℕ} [NeZero n] (g : ℕ → ℂ) :
    (∑ x : ZMod n, g x.val) = ∑ a ∈ Finset.range n, g a := by
  classical
  refine Finset.sum_bij' (fun (x : ZMod n) (_ : x ∈ Finset.univ) => x.val)
    (fun (a : ℕ) (_ : a ∈ Finset.range n) => (a : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro x _; rfl

lemma sum_range_range_eq (g : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.range (4 * d), ∑ b ∈ Finset.range (4 * d), g a b)
      = ∑ x : ZMod (4 * d) × ZMod (4 * d), g x.1.val x.2.val := by
  rw [← sum_zmod_val_eq (n := 4 * d) (g := fun a => ∑ b ∈ Finset.range (4 * d), g a b),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact (sum_zmod_val_eq (n := 4 * d) (g := fun b => g a.val b)).symm

/-- Multiplication by a class against an integer scalar, in terms of the canonical representative. -/
lemma gmul_intCast_val {n : ℕ} [NeZero n] (x : ZMod n) (b : ℤ) :
    x * (b : ZMod n) = (((x.val : ℤ) * b : ℤ) : ZMod n) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Int.cast_natCast (R := ZMod n) x.val, ← Int.cast_mul]

/-- `gaussSum` is the finite Fourier transform `Fhat` of the periodic weight `FR`. -/
lemma gaussSum_eq_sum (chi : GaussianInt → ℂ) (ξ : GaussianInt) :
    gaussSum d chi ξ =
      ∑ x : ZMod (4 * d) × ZMod (4 * d),
        FR d chi x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x) := by
  classical
  have hstep : gaussSum d chi ξ =
      ∑ a ∈ Finset.range (4 * d), ∑ b ∈ Finset.range (4 * d),
        (if isOddG (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) then
          chi (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ) : ℂ) / ((4 * d : ℕ) : ℂ)))
         else 0) := by
    rw [gaussSum]
    exact Finset.sum_product' (Finset.range (4 * d)) (Finset.range (4 * d))
      (fun a b => (if isOddG (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) then
          chi (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℤ) * ξ.re + (b : ℤ) * ξ.im : ℤ) : ℂ) / ((4 * d : ℕ) : ℂ)))
         else 0))
  rw [hstep, sum_range_range_eq]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hFR : FR d chi x = (if isOddG (⟨(x.1.val : ℤ), (x.2.val : ℤ)⟩ : GaussianInt)
      then chi ⟨(x.1.val : ℤ), (x.2.val : ℤ)⟩ else 0) := rfl
  have hpair : pairG d (gOfZI d ξ) x
      = ((((x.1.val : ℤ) * ξ.re + (x.2.val : ℤ) * ξ.im : ℤ)) : ZMod (4 * d)) := by
    simp only [pairG, gOfZI_re, gOfZI_im]
    rw [gmul_intCast_val x.1 ξ.re, gmul_intCast_val x.2 ξ.im]
    push_cast
    ring
  have hω : ZMod.stdAddChar (pairG d (gOfZI d ξ) x)
      = Complex.exp (2 * Real.pi * Complex.I *
          ((((x.1.val : ℤ) * ξ.re + (x.2.val : ℤ) * ξ.im : ℤ) : ℂ) / ((4 * d : ℕ) : ℂ))) := by
    rw [hpair, ZMod.stdAddChar_coe]
    congr 1
    ring
  rw [hFR, hω]
  split_ifs <;> ring

/-- `gaussSum` at `ξ` is `Fhat` at the residue class of `ξ`. -/
lemma gaussSum_eq_Fhat (chi : GaussianInt → ℂ) (ξ : GaussianInt) :
    gaussSum d chi ξ = Fhat d chi (gOfZI d ξ) :=
  gaussSum_eq_sum chi ξ

/-! ## The substitution at a unit -/

/-- Every unit `x` has a "pre-inverse" `v` with `v·x̄ = 1` in the Gaussian residue ring. -/
lemma exists_gmul_gconj_eq_gone {x : ZMod (4 * d) × ZMod (4 * d)} (hx : IsUnitR d x) :
    ∃ v, gmul d v (gconj d x) = gone d := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨gconj d y, by rw [← gconj_gmul, gmul_comm y x, hy, gconj_gone]⟩

/-- **The substitution.**  If `v·x̄ = 1`, the change of variables `t ↦ v·t` computes `Fhat` at
`x` from `Fhat` at `1`, at the cost of the character value `χ(v)`. -/
lemma Fhat_eq_of_gmul_eq_one {chi : GaussianInt → ℂ} (hchi : Work.FITop3.IsCharMod4d d chi)
    {u v : ZMod (4 * d) × ZMod (4 * d)} (huv : gmul d v (gconj d u) = gone d) :
    Fhat d chi u = chiR d chi v * Fhat d chi (gone d) := by
  have hv : IsUnitR d v := ⟨gconj d u, huv⟩
  have hK : ∀ t : ZMod (4 * d) × ZMod (4 * d),
      ZMod.stdAddChar (pairG d u (gmul d v t))
        = ZMod.stdAddChar (pairG d (gone d) t) := by
    intro t
    congr 1
    rw [pairG_eq_fst_gmul, gmul_assoc, gmul_comm t (gconj d u), ← gmul_assoc, huv,
      gmul_gone_left, pairG]
    simp
  let e : ZMod (4 * d) × ZMod (4 * d) ≃ ZMod (4 * d) × ZMod (4 * d) :=
    { toFun := fun t => gmul d v t
      invFun := fun t => gmul d (gconj d u) t
      left_inv := by
        intro t
        change gmul d (gconj d u) (gmul d v t) = t
        rw [← gmul_assoc, gmul_comm (gconj d u) v, huv, gmul_gone_left]
      right_inv := by
        intro t
        change gmul d v (gmul d (gconj d u) t) = t
        rw [← gmul_assoc, huv, gmul_gone_left] }
  calc Fhat d chi u
      = ∑ x : ZMod (4 * d) × ZMod (4 * d),
          FR d chi x * ZMod.stdAddChar (pairG d u x) := rfl
    _ = ∑ t : ZMod (4 * d) × ZMod (4 * d),
          FR d chi (gmul d v t) * ZMod.stdAddChar (pairG d u (gmul d v t)) := by
        exact (Fintype.sum_equiv e
          (fun t => FR d chi (gmul d v t) * ZMod.stdAddChar (pairG d u (gmul d v t)))
          (fun x => FR d chi x * ZMod.stdAddChar (pairG d u x))
          (fun x => rfl)).symm
    _ = ∑ t : ZMod (4 * d) × ZMod (4 * d),
          chiR d chi v * (FR d chi t * ZMod.stdAddChar (pairG d (gone d) t)) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [hK t, gmul_comm v t, FR_mul_unit hchi hv t]
        ring
    _ = chiR d chi v * ∑ t : ZMod (4 * d) × ZMod (4 * d),
          FR d chi t * ZMod.stdAddChar (pairG d (gone d) t) := by
        rw [Finset.mul_sum]
    _ = chiR d chi v * Fhat d chi (gone d) := rfl


end GaussBasic

end

end Work.FIArea5.S16Hecke
