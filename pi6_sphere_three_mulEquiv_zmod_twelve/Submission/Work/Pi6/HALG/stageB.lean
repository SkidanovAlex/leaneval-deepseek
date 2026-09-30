import Mathlib
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsY
import Submission.Work.Pi6.HALG.card_eq_mul_card_of_shortExact
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# HALG, step 1: `H₅(Y;ℤ) ≅ ℤ/2` and `|H₆(Y;ℤ)| = 6`

The Serre range sequence (`Work.Pi6.HALG.rangeLES_four`) of the fibration `mpathQ g₄` reads

`H_{i+1}(Y) → H_{i+1}(E) → H_{i+1}(P₄) → H_i(Y) → H_i(E)`   (`i + 1 < 9`),

where `E = S³⟨3⟩`, `Y = S³⟨4⟩`, and `P₄` is the `K(ℤ/2,4)` range model.  With the integral tables
`H₅(E) = 0`, `H₆(E) ≅ ℤ/3`, `H₇(E) = 0` (`EFacts`) and `H₆(P₄) ≅ ℤ/2`, `H₇(P₄) ≅ ℤ/2` (`EMTableZ`):

* at `i = 5`: `H₆(Y) → H₆(E) → H₆(P₄) → H₅(Y) → H₅(E) = 0`.  Since every homomorphism
  `ℤ/3 → ℤ/2` is zero, `H₆(P₄) → H₅(Y)` is an isomorphism, and `H₅(Y) ≅ ℤ/2`;
* at `i = 6`: `H₇(Y) → H₇(E) = 0 → H₇(P₄) → H₆(Y) → H₆(E) → H₆(P₄)` exhibits
  `0 → ℤ/2 → H₆(Y) → ℤ/3 → 0`, so `|H₆(Y)| = 2·3 = 6`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

open Work.Pi6

/-! ## Elementary inputs -/

/-- Every `ℤ`-linear map `ℤ/3 → ℤ/2` vanishes: `3 • x = 0` in the source while `3 ≡ 1` in the
target, so `f x = 3 • f x = f (3 • x) = 0`. -/
lemma stageB_zmod_three_to_zmod_two_eq_zero (f : ZMod 3 →ₗ[ℤ] ZMod 2) : f = 0 := by
  ext x
  have h3 : (3 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul, show ((3 : ℤ) : ZMod 3) = 0 from by decide, zero_mul]
  have h : (3 : ℤ) • f x = 0 := by rw [← map_zsmul, h3, map_zero]
  rwa [zsmul_eq_mul, show ((3 : ℤ) : ZMod 2) = 1 from by decide, one_mul] at h

/-- A `ℤ`-linear map `M → N` with `M ≃ₗ ℤ/3` and `N ≃ₗ ℤ/2` is zero. -/
lemma stageB_eq_zero_of_equiv_zmod_three_zmod_two {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e1 : M ≃ₗ[ℤ] ZMod 3) (e2 : N ≃ₗ[ℤ] ZMod 2)
    (f : M →ₗ[ℤ] N) : f = 0 := by
  have hF : e2.toLinearMap.comp (f.comp e1.symm.toLinearMap) = 0 :=
    stageB_zmod_three_to_zmod_two_eq_zero _
  ext x
  have h1 : e2 (f x) = 0 := by
    have := congrArg (fun g : ZMod 3 →ₗ[ℤ] ZMod 2 => g (e1 x)) hF
    simpa using this
  exact e2.injective (h1.trans (map_zero e2).symm)

/-- In an exact pair `f → g` whose target is a point, `f` is onto. -/
lemma stageB_exact_surjective_of_subsingleton {A B C : Type*} [Zero C] {f : A → B} {g : B → C}
    (h : Function.Exact f g) (hC : Subsingleton C) : Function.Surjective f :=
  fun b => Set.mem_range.mp ((h b).mp (hC.elim (g b) 0))

/-- In an exact pair `f → g` with `g = 0`, the map `f` is onto. -/
lemma stageB_exact_surjective_of_forall_eq_zero {A B C : Type*} [Zero C] {f : A → B}
    {g : B → C} (h : Function.Exact f g) (hg : ∀ b, g b = 0) : Function.Surjective f :=
  fun b => Set.mem_range.mp ((h b).mp (hg b))

/-! ## The main statement -/

/-- **HALG step 1 (task 1): `H₅(Y;ℤ) ≅ ℤ/2` and `|H₆(Y;ℤ)| = 6`.**

Write `Submission/Work/Pi6/HALG/stageB.lean`, module `Submission.Work.Pi6.HALG.stageB`, namespace
`Work.Pi6.HALG`.  Imports: `Submission.Work.Pi6.Interfaces`, `Submission.Work.Pi6.HALG.fibrationSetup`,
`Submission.Work.Pi6.HALG.rangeInputsY`, `Submission.Work.Pi6.HALG.card_eq_mul_card_of_shortExact`.

Route (`REFS/NOTES_LEAD_PI6.md` §0 steps 1–2).  Get the three inputs of
`rangeInputsY hT P3 g3 h3 P4 g4 h4` (integral vanishing of `H_j(Y)` for `0 < j ≤ 4`, `π₀(Y)`
trivial, `π_i(P4) = 0` for `i < 4`).  Get `Work.Pi6.HALG.rangeLES_four ℤ hR g3 g4 hB hF0 hF`
(`i + 1 < 9`), with middle maps `hmap ℤ g4 _`.  `EFacts` gives `H₅(E) = 0`, `H₆(E) ≅ ℤ/3`,
`H₇(E) = 0`; `EMTableZ` at `hK4` gives `H₆(P4) ≅ ℤ/2` and `H₇(P4) ≅ ℤ/2`.
* At `i = 5`: `H₆(Y) → H₆(E) → H₆(P4) → H₅(Y) → H₅(E) = 0`.  Every homomorphism `ℤ/3 → ℤ/2` is
  zero, so `H₆(P4) → H₅(Y)` is an isomorphism; conclude `H₅(Y) ≅ ℤ/2`.
* At `i = 6`: `H₇(Y) → H₇(E) = 0 → H₇(P4) → H₆(Y) → H₆(E) → H₆(P4)`, so `H₇(P4) ↪ H₆(Y)` and
  `H₆(Y) ↠ H₆(E)`; with `|H₇(P4)| = 2` and `|H₆(E)| = 3` use
  `card_eq_mul_card_of_shortExact` to get `Nat.card H₆(Y) = 6`.
To turn `Nat.card (HR ℤ Ycov 5) = 2` into a `ℤ`-linear equivalence with `ZMod 2`, use
`AddEquiv.toLinearEquiv`/`ModuleCat.of` or `LinearEquiv.ofBijective` with `Nat.card`-to-`Fintype`
(`Fintype.ofFinite`). -/
theorem stageB (hR : Work.Pi6.SerreRangeLES) (hE : Work.Pi6.EFacts) (hZt : Work.Pi6.EMTableZ)
    (hT : Work.Pi6.TowerPi)
    (P3 : Type) [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (h3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3)
    (P4 : Type) [TopologicalSpace P4] (g4 : C(Work.Pi6.Ecov g3, P4))
    (h4 : Work.Pi6.PostnikovData 4 12 g4 (Work.Pi6.e0 g3))
    (hK4 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (Work.Pi6.e0 g3))) :
    Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2) ∧
      Nat.card ↥(Work.Pi6.HR ℤ (Work.Pi6.Ycov g3 g4) 6) = 6 := by
  -- the three inputs of the Serre range sequence of `mpathQ g₄`
  obtain ⟨hYvan, hYpi0, hP4pi⟩ := rangeInputsY hT P3 g3 h3 P4 g4 h4
  obtain ⟨incl, bd, hex⟩ := rangeLES_four ℤ hR g3 g4 hP4pi hYpi0
    (fun j hj hj5 => hYvan j hj (by omega))
  -- the integral tables of `E` and of `P₄`
  obtain ⟨-, hE5, hE6, hE7, -⟩ := hE P3 g3 h3
  obtain ⟨hP46, hP47, -⟩ := hZt.1 P4 (g4 (e0 g3)) 12 (le_refl 12) hK4
  -- every homomorphism `H₆(E) ≅ ℤ/3 → H₆(P₄) ≅ ℤ/2` is zero, in particular `g₄*` in degree 6
  have hzero6 : (hmap ℤ g4 6).hom = 0 := by
    obtain ⟨e1⟩ := hE6
    obtain ⟨e2⟩ := hP46
    exact stageB_eq_zero_of_equiv_zmod_three_zmod_two e1 e2 _
  obtain ⟨h5a, h5b, h5c⟩ := hex 5 (by norm_num)
  obtain ⟨h6a, h6b, h6c⟩ := hex 6 (by norm_num)
  -- `H₆(P₄) → H₅(Y)` is injective (its kernel is the range of the zero map `H₆(E) → H₆(P₄)`) ...
  have hbd5inj : Function.Injective (bd 5).hom := by
    intro x y hxy
    have h1 : (bd 5).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((h5b (x - y)).mp h1)
    have hz0 : (hmap ℤ g4 6).hom z = 0 := by rw [hzero6, LinearMap.zero_apply]
    rw [hz0] at hz
    exact sub_eq_zero.mp hz.symm
  -- ... and surjective because `H₅(E) = 0` is the next term of the sequence.
  have hbd5surj : Function.Surjective (bd 5).hom :=
    stageB_exact_surjective_of_subsingleton h5c hE5
  -- `H₇(P₄) → H₆(Y)` is injective: `H₇(E) = 0` is the previous term.
  have hbd6inj : Function.Injective (bd 6).hom := by
    intro x y hxy
    have h1 : (bd 6).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((h6b (x - y)).mp h1)
    have hz0 : z = 0 := hE7.elim z 0
    rw [hz0, map_zero] at hz
    exact sub_eq_zero.mp hz.symm
  -- `H₆(Y) → H₆(E)` is surjective, since the next map `H₆(E) → H₆(P₄)` is zero.
  have hincl6surj : Function.Surjective (incl 6).hom :=
    stageB_exact_surjective_of_forall_eq_zero h5a
      (fun b => by rw [hzero6, LinearMap.zero_apply])
  constructor
  · -- `H₅(Y) ≅ H₆(P₄) ≅ ℤ/2`
    obtain ⟨e2⟩ := hP46
    exact ⟨(LinearEquiv.ofBijective (bd 5).hom ⟨hbd5inj, hbd5surj⟩).symm.trans e2⟩
  · -- `0 → ℤ/2 → H₆(Y) → ℤ/3 → 0`, so `|H₆(Y)| = 2 · 3 = 6`
    obtain ⟨e3⟩ := hP47
    obtain ⟨e4⟩ := hE6
    have hA : Finite ↥(HR ℤ P4 7) := Finite.of_equiv (ZMod 2) e3.symm.toEquiv
    have hC : Finite ↥(HR ℤ (Ecov g3) 6) := Finite.of_equiv (ZMod 3) e4.symm.toEquiv
    have hcard := card_eq_mul_card_of_shortExact (f := (bd 6).hom.toAddMonoidHom)
      (g := (incl 6).hom.toAddMonoidHom) hbd6inj hincl6surj h6c hA hC
    rw [hcard]
    have hcA : Nat.card ↥(HR ℤ P4 7) = 2 := by
      rw [Nat.card_congr e3.toEquiv, Nat.card_zmod]
    have hcC : Nat.card ↥(HR ℤ (Ecov g3) 6) = 3 := by
      rw [Nat.card_congr e4.toEquiv, Nat.card_zmod]
    rw [hcA, hcC]

end

end Work.Pi6.HALG
