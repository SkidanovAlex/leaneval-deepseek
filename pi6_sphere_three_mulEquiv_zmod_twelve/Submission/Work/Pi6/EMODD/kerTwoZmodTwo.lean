import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

open Multiplicative

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val a, h0]; norm_num
  · right; rw [← ZMod.natCast_zmod_val a, h1]; norm_num

/-- `Multiplicative (ZMod 2)` has exactly the two elements `1` and `ofAdd 1`. -/
lemma mult_zmod_two_eq_one_or (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
  have h : x.toAdd = 0 ∨ x.toAdd = 1 := zmod_two_eq_zero_or_one x.toAdd
  rcases h with h0 | h1
  · left; rw [← ofAdd_toAdd x, h0, ofAdd_zero]
  · right; rw [← ofAdd_toAdd x, h1]

/-- `Multiplicative.ofAdd 1` generates `Multiplicative ℤ`, in powers. -/
lemma ofAdd_one_zpow (z : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ)) ^ z = Multiplicative.ofAdd z := by
  rw [← ofAdd_zsmul]
  simp

/-- A hom out of `Multiplicative ℤ` is determined by its value on the generator. -/
lemma hom_apply_ofAdd (η : Multiplicative ℤ →* Multiplicative (ZMod 2)) (z : ℤ) :
    η (Multiplicative.ofAdd z) = η (Multiplicative.ofAdd (1 : ℤ)) ^ z := by
  rw [← ofAdd_one_zpow z, map_zpow]

/-- A surjective hom `Multiplicative ℤ →* Multiplicative (ZMod 2)` must send the generator
`ofAdd 1` to the generator `ofAdd 1`. -/
lemma hom_ofAdd_one_of_surj (η : Multiplicative ℤ →* Multiplicative (ZMod 2))
    (hη : Function.Surjective η) :
    η (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ZMod 2) := by
  rcases mult_zmod_two_eq_one_or (η (Multiplicative.ofAdd (1 : ℤ))) with h | h
  · exfalso
    obtain ⟨g, hg⟩ := hη (Multiplicative.ofAdd (1 : ZMod 2))
    obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective g
    have h1 : η (Multiplicative.ofAdd w) = 1 := by
      rw [hom_apply_ofAdd η w, h, one_zpow]
    rw [h1] at hg
    have hg' : Multiplicative.ofAdd (1 : ZMod 2) = 1 := hg.symm
    rw [ofAdd_eq_one] at hg'
    exact one_ne_zero hg'
  · exact h

/-- A surjective hom `Multiplicative ℤ →* Multiplicative (ZMod 2)` is reduction of the
`ℤ`-coordinate mod `2`. -/
lemma hom_apply_ofAdd_cast (η : Multiplicative ℤ →* Multiplicative (ZMod 2))
    (hη : Function.Surjective η) (z : ℤ) :
    η (Multiplicative.ofAdd z) = Multiplicative.ofAdd ((z : ZMod 2)) := by
  rw [hom_apply_ofAdd η z, hom_ofAdd_one_of_surj η hη, ← ofAdd_zsmul]
  congr 1
  exact (zsmul_eq_mul (1 : ZMod 2) z).trans (mul_one _)

/-- **The kernel of a surjection onto `ZMod 2`, read off in a `ℤ`-coordinate.** Let `f : G →* B` be a surjective homomorphism of groups, `eG : G ≃* Multiplicative ℤ` and `eB : B ≃* Multiplicative (ZMod 2)` multiplicative equivalences. Then, in the coordinate `m = (eG y).toAdd`, the kernel of `f` is exactly `2ℤ`:
`f y = 1 ↔ (2 : ℤ) ∣ (eG y).toAdd`.

(Route: the composite `η = eB ∘ f ∘ eG.symm : Multiplicative ℤ →* Multiplicative (ZMod 2)` is surjective, so `η (ofAdd 1) ≠ 1`, hence `η (ofAdd 1) = ofAdd 1` (`Multiplicative` of `ZMod 2` has two elements); by multiplicativity `η (ofAdd m) = ofAdd (m : ZMod 2)`, and `ofAdd (m : ZMod 2) = 1 ↔ (m : ZMod 2) = 0 ↔ 2 ∣ m` (`ofAdd_eq_one`, `ZMod.intCast_zmod_eq_zero_iff_dvd`).)

Naming note: the file's namespace is `Work.Pi6.EMODD` (module `Submission.Work.Pi6.EMODD.kerTwoZmodTwo`). Helper lemmas above the statement are welcome. -/
theorem kerTwoZmodTwo {G B : Type*} [Group G] [Group B]
    (f : G →* B) (hf : Function.Surjective f) (eG : G ≃* Multiplicative ℤ)
    (eB : B ≃* Multiplicative (ZMod 2)) (y : G) :
    f y = 1 ↔ (2 : ℤ) ∣ (eG y).toAdd := by
  let η : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
    eB.toMonoidHom.comp (f.comp eG.symm.toMonoidHom)
  have hη : Function.Surjective η := by
    intro x
    obtain ⟨b, hb⟩ := eB.surjective x
    obtain ⟨g, hg⟩ := hf b
    refine ⟨eG g, ?_⟩
    show eB (f (eG.symm (eG g))) = x
    rw [MulEquiv.symm_apply_apply, hg, hb]
  have hcomp : η (eG y) = eB (f y) := by
    show eB (f (eG.symm (eG y))) = eB (f y)
    rw [MulEquiv.symm_apply_apply]
  have key : eB (f y) = Multiplicative.ofAdd (((eG y).toAdd : ℤ) : ZMod 2) := by
    rw [← hcomp]
    conv_lhs => rw [← ofAdd_toAdd (eG y)]
    exact hom_apply_ofAdd_cast η hη (eG y).toAdd
  rw [← MulEquiv.map_eq_one_iff eB, key, ofAdd_eq_one]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd ((eG y).toAdd) 2

end Work.Pi6.EMODD
