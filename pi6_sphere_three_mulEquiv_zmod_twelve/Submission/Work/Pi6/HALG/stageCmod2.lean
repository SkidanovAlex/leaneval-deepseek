import Mathlib
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsZ
import Submission.Work.Pi6.HALG.card_le_of_rank_le
import Submission.Work.Pi6.HALG.stageCmod2Aux
import Submission.Work.Pi6.HALG.twoCok_twoKer_card_two
import Submission.Work.Pi6.HALG.twoCok_twoKer_card_one
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 800000

namespace Work.Pi6.HALG

open CategoryTheory CategoryTheory.Limits

noncomputable section

open Work.Pi6

/-- **HALG step 5: `|H₆(Z;𝔽₂)| = 2`.**

Write `Submission/Work/Pi6/HALG/stageCmod2.lean` (module `Submission.Work.Pi6.HALG.stageCmod2`),
namespace `Work.Pi6.HALG`.  Imports: `Submission.Work.Pi6.Interfaces`,
`Submission.Work.Pi6.HALG.defs`, `Submission.Work.Pi6.HALG.fibrationSetup`,
`Submission.Work.Pi6.HALG.rangeInputsZ`, `Submission.Work.Pi6.HALG.card_le_of_rank_le`.

Route (`REFS/NOTES_LEAD_PI6.md` §0 step 5).  `rangeInputsZ hT ...` + `rangeLES_five (ZMod 2) hR` at
`i = 6` gives
`H₇(Z;𝔽₂) → H₇(Y;𝔽₂) →^{hmap (ZMod 2) g5 7} H₇(P₅;𝔽₂) → H₆(Z;𝔽₂) → H₆(Y;𝔽₂) → H₆(P₅;𝔽₂) → H₅(Z;𝔽₂) = 0`.
`h7mod2` and `h5P5` + `hZt` + `hB2` give `Nat.card H₇(P₅;𝔽₂) = 2`; `hf` is then injective, so
`H₆(Z;𝔽₂) ↪ H₆(Y;𝔽₂)`.  `hB2` + `h6Y` + `h5Y` give `Nat.card H₆(Y;𝔽₂) = 2 * 2 = 4`;
`h5P5` + `hZt` + `hB2` give `Nat.card H₆(P₅;𝔽₂) = 2`, and exactness at `H₆(P₅;𝔽₂)` (whose successor
`H₅(Z;𝔽₂)` is zero, from `rangeInputsZ`) makes `H₆(Y;𝔽₂) → H₆(P₅;𝔽₂)` surjective.  Rank–nullity
(count the kernel of `H₆(Z;𝔽₂) → H₆(Y;𝔽₂)` as `im` of the injection into it, using
`Finite.of_injective`/`Finite.of_surjective` and `Nat.card` multiplicativity) gives
`Nat.card H₆(Z;𝔽₂) = 1`.  Note `H₅(Z;𝔽₂) = 0` follows from `H₅(Z) = H₄(Z) = 0` and `hB2`. -/
theorem stageCmod2 (hB2 : Work.Pi6.HALG.BocksteinTwo) (hR : Work.Pi6.SerreRangeLES)
    (hZt : Work.Pi6.EMTableZ) (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (hK4 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (Work.Pi6.e0 g3)))
    (P5 : Type) [TopologicalSpace P5] (g5 : C(Work.Pi6.Ycov g3 g4, P5))
    (h5 : Work.Pi6.PostnikovData 5 12 g5 (Work.Pi6.y0 g3 g4))
    (hK5 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) 12 P5 (g5 (Work.Pi6.y0 g3 g4)))
    (hf : Work.Pi6.hmap (ZMod 2) g5 7 ≠ 0)
    (h5Y : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2))
    (h6Y : Nat.card ↥(Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 6) = 6)
    (h7mod2 : Nat.card ↥(Work.Pi6.HR (ZMod 2) (Work.Pi6.Ycov g3 g4) 7) = 2)
    (h5P5 : Nonempty (Work.Pi6.HR ℤ P5 5 ≃ₗ[ℤ] ZMod 2)) :
    Nat.card ↥(Work.Pi6.HR (ZMod 2) (Work.Pi6.Zcov g3 g4 g5) 6) = 2 := by
  -- the three inputs and the Serre range exact sequence of `mpathQ g₅`
  obtain ⟨hZvan, hZpi0, hP5pi⟩ := rangeInputsZ hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  obtain ⟨incl, bd, hex⟩ := rangeLES_five (ZMod 2) hR g3 g4 g5 hP5pi hZpi0
    (fun j hj hj6 => hZvan j hj (by omega))
  -- exactness at `H₆(Z)`, `H₆(Y)`, `H₆(P₅)` (index `5`) and at `H₇(Y)`, `H₇(P₅)`, `H₆(Z)` (index `6`)
  have hex5 := hex 5 (by norm_num)
  have hex6 := hex 6 (by norm_num)
  -- the integral tables of `P₅` (`K(ℤ/2,5)`): `H₆(P₅;ℤ) = 0`, `H₇(P₅;ℤ) ≅ ℤ/2`
  obtain ⟨hP56ss, hP57iso⟩ := hZt.2 P5 (g5 (y0 g3 g4)) 12 (le_refl 12) hK5
  -- cardinalities of the integral homology groups entering the Bockstein sequences
  obtain ⟨e5P⟩ := h5P5
  obtain ⟨e5Y⟩ := h5Y
  obtain ⟨e7⟩ := hP57iso
  have hcardP55 : Nat.card ↥(HR ℤ P5 5) = 2 := natCard_eq_two_of_linearEquiv_zmodTwo e5P
  have hcardP57 : Nat.card ↥(HR ℤ P5 7) = 2 := natCard_eq_two_of_linearEquiv_zmodTwo e7
  have hcardY5 : Nat.card ↥(HR ℤ (Ycov g3 g4) 5) = 2 := natCard_eq_two_of_linearEquiv_zmodTwo e5Y
  -- **(a)** `|H₇(P₅;𝔽₂)| = 2`: Bockstein `|H₇(P₅;𝔽₂)| = |H₇(P₅;ℤ)/2| · |H₆(P₅;ℤ)[2]| = 2 · 1`
  have hcardH7P5 : Nat.card ↥(HR (ZMod 2) P5 7) = 2 := by
    have hA : Nat.card ↥(twoCok (HR ℤ P5 7)) = 2 := (twoCok_twoKer_card_two hcardP57).1
    have hB : Nat.card ↥(twoKer (HR ℤ P5 6)) = 1 := (twoCok_twoKer_card_one hP56ss).2
    have h := bocksteinCard_of_cards hB2 (X := P5) 6 hA hB
    simpa using h
  -- **(b)** `|H₆(P₅;𝔽₂)| = 2`: Bockstein `= |H₆(P₅;ℤ)/2| · |H₅(P₅;ℤ)[2]| = 1 · 2`
  have hcardH6P5 : Nat.card ↥(HR (ZMod 2) P5 6) = 2 := by
    have hA : Nat.card ↥(twoCok (HR ℤ P5 6)) = 1 := (twoCok_twoKer_card_one hP56ss).1
    have hB : Nat.card ↥(twoKer (HR ℤ P5 5)) = 2 := (twoCok_twoKer_card_two hcardP55).2
    have h := bocksteinCard_of_cards hB2 (X := P5) 5 hA hB
    simpa using h
  -- **(c)** `|H₆(Y;𝔽₂)| = 4`: Bockstein `= |H₆(Y;ℤ)/2| · |H₅(Y;ℤ)[2]| = 2 · 2`
  have hcardH6Y : Nat.card ↥(HR (ZMod 2) (Ycov g3 g4) 6) = 4 := by
    have hA : Nat.card ↥(twoCok (HR ℤ (Ycov g3 g4) 6)) = 2 := card_twoCok_of_card_six h6Y
    have hB : Nat.card ↥(twoKer (HR ℤ (Ycov g3 g4) 5)) = 2 :=
      (twoCok_twoKer_card_two hcardY5).2
    have h := bocksteinCard_of_cards hB2 (X := Ycov g3 g4) 5 hA hB
    simpa using h
  -- **(d)** `H₅(Z;𝔽₂) = 0`: Bockstein `= |H₅(Z;ℤ)/2| · |H₄(Z;ℤ)[2]| = 1 · 1`
  have hH5Zss : Subsingleton ↥(HR (ZMod 2) (Zcov g3 g4 g5) 5) := by
    have hss5 : Subsingleton ↥(HR ℤ (Zcov g3 g4 g5) 5) :=
      ModuleCat.subsingleton_of_isZero (hZvan 5 (by norm_num) (le_refl 5))
    have hss4 : Subsingleton ↥(HR ℤ (Zcov g3 g4 g5) 4) :=
      ModuleCat.subsingleton_of_isZero (hZvan 4 (by norm_num) (by norm_num))
    have hA : Nat.card ↥(twoCok (HR ℤ (Zcov g3 g4 g5) 5)) = 1 :=
      (twoCok_twoKer_card_one hss5).1
    have hB : Nat.card ↥(twoKer (HR ℤ (Zcov g3 g4 g5) 4)) = 1 :=
      (twoCok_twoKer_card_one hss4).2
    have h := bocksteinCard_of_cards hB2 (X := Zcov g3 g4 g5) 4 hA hB
    have h1 : Nat.card ↥(HR (ZMod 2) (Zcov g3 g4 g5) 5) = 1 := by simpa using h
    exact subsingleton_of_natCard_eq_one h1
  -- `(g₅)_* : H₇(Y;𝔽₂) → H₇(P₅;𝔽₂)` is nonzero between two groups of order `2`, hence surjective
  obtain ⟨x7, hx7⟩ := exists_hom_apply_ne_zero (hmap (ZMod 2) g5 7) hf
  have hmap7surj : Function.Surjective (hmap (ZMod 2) g5 7).hom :=
    card_two_surjective_of_ne_zero (hmap (ZMod 2) g5 7).hom.toAddMonoidHom
      h7mod2 hcardH7P5 ⟨x7, hx7⟩
  -- hence the transgression `H₇(P₅;𝔽₂) → H₆(Z;𝔽₂)` is zero ...
  have hbd6zero : ∀ y : ↥(HR (ZMod 2) P5 7), (bd 6).hom y = 0 :=
    fun y => (hex6.2.1 y).mpr (hmap7surj y)
  -- ... so `H₆(Z;𝔽₂) → H₆(Y;𝔽₂)` is injective (exactness at `H₆(Z;𝔽₂)`)
  have hincl6inj : Function.Injective (incl 6).hom := by
    intro x y hxy
    have h1 : (incl 6).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((hex6.2.2 (x - y)).mp h1)
    rw [hbd6zero z] at hz
    exact sub_eq_zero.mp hz.symm
  -- `H₆(Y;𝔽₂) → H₆(P₅;𝔽₂)` is surjective, since `H₅(Z;𝔽₂) = 0` is the successor term
  have hmap6surj : Function.Surjective (hmap (ZMod 2) g5 6).hom := by
    intro y
    exact Set.mem_range.mp ((hex5.2.1 y).mp (Subsingleton.elim ((bd 5).hom y) 0))
  -- rank–nullity for `H₆(Z;𝔽₂) ↪ H₆(Y;𝔽₂) ↠ H₆(P₅;𝔽₂)`: `4 = |H₆(Z;𝔽₂)| · 2`
  have hfinal : Nat.card ↥(HR (ZMod 2) (Zcov g3 g4 g5) 6) = 2 := by
    have h := card_eq_mul_card_of_exact (f := (incl 6).hom.toAddMonoidHom)
      (g := (hmap (ZMod 2) g5 6).hom.toAddMonoidHom) hincl6inj hmap6surj hex5.1
    rw [hcardH6Y, hcardH6P5] at h
    omega
  exact hfinal

end

end Work.Pi6.HALG
