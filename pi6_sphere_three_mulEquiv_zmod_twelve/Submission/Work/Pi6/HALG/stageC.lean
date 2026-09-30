import Mathlib
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsZ
import Submission.Work.Pi6.HALG.card_eq_mul_card_of_shortExact
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Pi6.HALG

/-- **HALG step 4: `|H₆(Z;ℤ)| = 12`.**

Write `Submission/Work/Pi6/HALG/stageC.lean` (module `Submission.Work.Pi6.HALG.stageC`), namespace
`Work.Pi6.HALG`.  Imports: `Submission.Work.Pi6.Interfaces`,
`Submission.Work.Pi6.HALG.fibrationSetup`, `Submission.Work.Pi6.HALG.rangeInputsZ`,
`Submission.Work.Pi6.HALG.card_eq_mul_card_of_shortExact`.

Route (`REFS/NOTES_LEAD_PI6.md` §0 step 4).  `EMTableZ` at `hK5` gives `H₆(P₅) = 0` and
`H₇(P₅) ≅ ℤ/2` (so `2 • x = 0` for `x : H₇(P₅)`).  `h7div` makes the middle map
`hmap ℤ g5 7 : H₇(Y) → H₇(P₅)` of `Work.Pi6.HALG.rangeLES_five ℤ hR g3 g4 g5 _ _ _` zero
(`f (2b) = 2 • f b = 0`), and `rangeInputsZ hT ...` supplies the side conditions (`H_j(Z) = 0` for
`0 < j ≤ 5`, `π₀(Z)` trivial, `π_i(P₅) = 0` for `i < 5`).  At `i = 6`:
`H₇(Z) → H₇(Y) → H₇(P₅) → H₆(Z) → H₆(Y) → H₆(P₅) = 0`; the map into `H₆(Z)` has kernel
`im (hmap ℤ g5 7) = 0`, so it is injective, and exactness at `H₆(Y)` makes `H₆(Z) → H₆(Y)`
surjective.  With `h6Y` and `card_eq_mul_card_of_shortExact`, conclude
`Nat.card H₆(Z) = 2 * 6 = 12`. -/
theorem stageC (hR : Work.Pi6.SerreRangeLES) (hZt : Work.Pi6.EMTableZ) (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (hK4 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (Work.Pi6.e0 g3)))
    (P5 : Type) [TopologicalSpace P5] (g5 : C(Work.Pi6.Ycov g3 g4, P5))
    (h5 : Work.Pi6.PostnikovData 5 12 g5 (Work.Pi6.y0 g3 g4))
    (hK5 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) 12 P5 (g5 (Work.Pi6.y0 g3 g4)))
    (h5Y : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2))
    (h6Y : Nat.card ↥(Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 6) = 6)
    (h7div : ∀ a : Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 7, ∃ b, (2 : ℤ) • b = a) :
    Nat.card ↥(Work.Pi6.HR ℤ (Work.Pi6.Zcov g3 g4 g5) 6) = 12 := by
  -- the three inputs of the Serre range sequence of `mpathQ g₅`
  obtain ⟨hZvan, hZpi0, hP5pi⟩ := rangeInputsZ hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  obtain ⟨incl, bd, hex⟩ := rangeLES_five ℤ hR g3 g4 g5 hP5pi hZpi0
    (fun j hj hj6 => hZvan j hj (by omega))
  -- the integral tables of `P₅`
  obtain ⟨hP56zero, hP57iso⟩ := hZt.2 P5 (g5 (y0 g3 g4)) 12 (le_refl 12) hK5
  -- `H₇(P₅) ≅ ℤ/2`, so it is killed by `2`
  have hP57two : ∀ x : ↥(HR ℤ P5 7), (2 : ℤ) • x = 0 := by
    intro x
    obtain ⟨e⟩ := hP57iso
    apply e.injective
    rw [map_zsmul, CharTwo.two_zsmul, map_zero]
  -- hence the middle map `hmap ℤ g5 7 : H₇(Y) → H₇(P₅)` vanishes (`h7div`)
  have hzero7 : (hmap ℤ g5 7).hom = 0 := by
    apply LinearMap.ext
    intro a
    obtain ⟨b, hb⟩ := h7div a
    rw [← hb, LinearMap.zero_apply, map_zsmul, hP57two]
  have hzero7app : ∀ z : ↥(HR ℤ (Ycov g3 g4) 7), (hmap ℤ g5 7).hom z = 0 :=
    fun z => by rw [hzero7, LinearMap.zero_apply]
  obtain ⟨h5a, h5b, h5c⟩ := hex 5 (by norm_num)
  obtain ⟨h6a, h6b, h6c⟩ := hex 6 (by norm_num)
  -- `H₇(P₅) → H₆(Z)` is injective: its kernel is `im (hmap ℤ g5 7) = 0`
  have hbd6inj : Function.Injective (bd 6).hom := by
    intro x y hxy
    have h1 : (bd 6).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((h6b (x - y)).mp h1)
    rw [hzero7app z] at hz
    exact sub_eq_zero.mp hz.symm
  -- `H₆(Z) → H₆(Y)` is surjective because `H₆(P₅) = 0` is the next term
  have hincl6surj : Function.Surjective (incl 6).hom := by
    intro y
    have hy : (hmap ℤ g5 6).hom y = 0 := hP56zero.elim _ _
    exact Set.mem_range.mp ((h5a y).mp hy)
  -- `0 → ℤ/2 → H₆(Z) → H₆(Y) → 0`, so `|H₆(Z)| = 2 · 6 = 12`
  obtain ⟨e7⟩ := hP57iso
  have hA : Finite ↥(HR ℤ P5 7) := Finite.of_equiv (ZMod 2) e7.symm.toEquiv
  have hC : Finite ↥(HR ℤ (Ycov g3 g4) 6) :=
    (Nat.card_ne_zero.mp (by rw [h6Y]; norm_num)).2
  have hcard := card_eq_mul_card_of_shortExact (f := (bd 6).hom.toAddMonoidHom)
    (g := (incl 6).hom.toAddMonoidHom) hbd6inj hincl6surj h6c hA hC
  rw [hcard]
  have hcA : Nat.card ↥(HR ℤ P5 7) = 2 := by
    rw [Nat.card_congr e7.toEquiv, Nat.card_zmod]
  rw [hcA, h6Y]

end Work.Pi6.HALG
