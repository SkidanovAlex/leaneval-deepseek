import Mathlib
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsZ
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# HALG, step 2: `H₅(P₅;ℤ) ≅ ℤ/2`

The Serre range sequence (`Work.Pi6.HALG.rangeLES_five`) of the fibration `mpathQ g₅` reads

`H_{i+1}(Z) → H_{i+1}(Y) → H_{i+1}(P₅) → H_i(Z) → H_i(Y)`   (`i + 1 < 11`),

where `Y = S³⟨4⟩`, `Z = S³⟨5⟩` and `P₅` is the `K(ℤ/2,5)` range model.  At `i = 4` this reads

`H₅(Z) → H₅(Y) → H₅(P₅) → H₄(Z) → H₄(Y)`,

and `H₅(Z) = H₄(Z) = 0` because `Z` is `5`-connected (`rangeInputsZ`).  Hence the middle map
`(g₅)_* : H₅(Y) → H₅(P₅)` is bijective: it is injective because its kernel is the image of the
zero map `H₅(Z) → H₅(Y)`, and surjective because the next map lands in `H₄(Z) = 0`.  Composing
with the hypothesis `H₅(Y) ≅ ℤ/2` gives `H₅(P₅) ≅ ℤ/2`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

open Work.Pi6

/-- **HALG: `H₅(P₅;ℤ) ≅ ℤ/2`.**

Write `Submission/Work/Pi6/HALG/stagePH5.lean`, module `Submission.Work.Pi6.HALG.stagePH5`, namespace
`Work.Pi6.HALG`.  Imports: `Submission.Work.Pi6.Interfaces`,
`Submission.Work.Pi6.HALG.fibrationSetup`, `Submission.Work.Pi6.HALG.rangeInputsZ`.

Route.  Feed `rangeInputsZ hT ...` into `Work.Pi6.HALG.rangeLES_five ℤ hR g3 g4 g5 hB hF0 hF`
(`i + 1 < 11`), whose middle maps are `hmap ℤ g5 _`.  At `i = 4` the sequence reads
`H₅(Z) → H₅(Y) → H₅(P₅) → H₄(Z) → H₄(Y)`, and `H₅(Z) = H₄(Z) = H₄(Y) = 0` (5-connectedness of `Z`,
4-connectedness of `Y`), so `H₅(Y) ≅ H₅(P₅)`.  Compose with `h5Y`. -/
theorem stagePH5 (hR : Work.Pi6.SerreRangeLES) (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (P5 : Type) [TopologicalSpace P5] (g5 : C(Work.Pi6.Ycov g3 g4, P5))
    (h5 : Work.Pi6.PostnikovData 5 12 g5 (Work.Pi6.y0 g3 g4))
    (h5Y : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2)) :
    Nonempty (Work.Pi6.HR ℤ P5 5 ≃ₗ[ℤ] ZMod 2) := by
  -- the three inputs of the Serre range sequence of `mpathQ g₅`
  obtain ⟨hZvan, hZpi0, hP5pi⟩ := rangeInputsZ hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  obtain ⟨incl, bd, hex⟩ := rangeLES_five ℤ hR g3 g4 g5 hP5pi hZpi0
    (fun j hj hj6 => hZvan j hj (by omega))
  -- the four-term exact sequence `H₅(Z) → H₅(Y) → H₅(P₅) → H₄(Z)`
  obtain ⟨hE1, hE2, _⟩ := hex 4 (by norm_num)
  -- `H₅(Z) = 0` and `H₄(Z) = 0`
  haveI hZ5 : Subsingleton ↥(HR ℤ (Zcov g3 g4 g5) 5) :=
    ModuleCat.subsingleton_of_isZero (hZvan 5 (by norm_num) (le_refl 5))
  haveI hZ4 : Subsingleton ↥(HR ℤ (Zcov g3 g4 g5) 4) :=
    ModuleCat.subsingleton_of_isZero (hZvan 4 (by norm_num) (by norm_num))
  -- `(g₅)_* : H₅(Y) → H₅(P₅)` is injective: its kernel is the range of `H₅(Z) → H₅(Y)`.
  have hinj : Function.Injective (hmap ℤ g5 5).hom := by
    intro x y hxy
    have h1 : (hmap ℤ g5 5).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((hE1 (x - y)).mp h1)
    have hz0 : z = 0 := Subsingleton.elim z 0
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  -- ... and surjective: its cokernel maps into the zero group `H₄(Z)`.
  have hsurj : Function.Surjective (hmap ℤ g5 5).hom := fun y =>
    Set.mem_range.mp ((hE2 y).mp (Subsingleton.elim ((bd 4).hom y) 0))
  obtain ⟨e⟩ := h5Y
  exact ⟨(LinearEquiv.ofBijective (hmap ℤ g5 5).hom ⟨hinj, hsurj⟩).symm.trans e⟩

end

end Work.Pi6.HALG
