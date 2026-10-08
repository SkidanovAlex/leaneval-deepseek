/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / Aut : `[PGL(2,q) : PSL(2,q)] = 2`

Inside the permutation model `pslImage F ≤ pglImage F ≤ Perm ℙ¹(F)` of Mathlib's
`PSL(2,F)`, `PGL(2,F)`, we prove

`(pslImage F).relIndex (pglImage F) = 2`  for `F = GF(p^k)`, `p` odd.

The mathematical content is that the determinant induces
`PGL(2,F) / PSL(2,F) ≅ Fˣ/(Fˣ)²`, of order `2` because `F` is a finite field of odd
characteristic.  Formally the argument is:

* `pglHomInjective` (faithfulness of the Möbius action, `Submission/Work/AUTL2/Aut/`), so that
  membership in `pglImage` can be tested on matrices;
* `mem_pslImage_iff_isSquare_det` : `pglHom F (mk B) ∈ pslImage F ↔ IsSquare B.det`
  (the kernel of the determinant modulo squares is exactly the image of `PSL`);
* `squareDichotomy` + `isSquare_units_or` : for a non-square `d` and every `δ`,
  `δ` or `δ * d` is a square;
* `relIndex_eq_two_iff_exists_notMem_and` applied to `a = x ↦ d·x ∈ pglImage ∖ pslImage`:
  for `b = pglHom (mk B)`, one of `b`, `b * a` lies in `pslImage` because
  `det (B · diag(d,1)) = det B · d`.

The main statement `pglIndex` is the interface lemma needed for step A6 of the
Gorenstein–Walter / Bender–Glauberman route (`M' = Q ⊓ pglImage` has index `≤ 2` over
`pslImage`).
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Normalizer.Defs
import Submission.Work.AUTL2.Aut.pglHomInjective
import Submission.Work.AUTL2.Aut.squareDichotomy

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Aut

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-- The determinant of the diagonal matrix `diag(c,1) ∈ GL(2,F)` (`Normalizer.diagGL`) is `c`. -/
theorem diagGL_det (c : F) (hc : c ≠ 0) :
    (Normalizer.diagGL F c hc).det = Units.mk0 c hc := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Normalizer.diagGL,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_mk0, Matrix.det_fin_two]
  simp

/-- `IsSquare` for a unit is the same as `IsSquare` for its underlying field element. -/
theorem isSquare_coe_units_iff (δ : Fˣ) : IsSquare (δ : F) ↔ IsSquare δ := by
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp only [mul_zero] at hc
      exact Units.ne_zero δ hc
    exact ⟨Units.mk0 c hc0, by
      apply Units.ext
      rw [Units.val_mul, Units.val_mk0]
      exact hc⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v : F), by rw [hv, Units.val_mul]⟩

/-- The square/nonsquare dichotomy, transported to the group of units:
if `d` is a non-square then for every unit `δ`, one of `δ`, `δ * d` is a square. -/
theorem isSquare_units_or [Fintype F] (hF : ringChar F ≠ 2) (d : F) (hd : ¬ IsSquare d)
    (hd0 : d ≠ 0) (δ : Fˣ) : IsSquare δ ∨ IsSquare (δ * Units.mk0 d hd0) := by
  rcases squareDichotomy F hF d hd (δ : F) with h | h
  · exact Or.inl ((isSquare_coe_units_iff F δ).mp h)
  · exact Or.inr ((isSquare_coe_units_iff F (δ * Units.mk0 d hd0)).mp (by simpa using h))

/-- The element of `pglImage F` represented by a matrix `B ∈ GL(2,F)` lies in `pslImage F`
exactly when `det B` is a square: the determinant induces `PGL(2,F)/PSL(2,F) ≅ Fˣ/(Fˣ)²`. -/
theorem mem_pslImage_iff_isSquare_det (B : GL (Fin 2) F) :
    pglHom F (Matrix.ProjGenLinGroup.mk B) ∈ pslImage F ↔ IsSquare B.det := by
  constructor
  · intro hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 : Matrix.ProjectiveSpecialLinearGroup.toPGL c = Matrix.ProjGenLinGroup.mk B :=
      pglHomInjective F (by simpa [pslHom] using hc)
    obtain ⟨C, hC⟩ := QuotientGroup.mk_surjective
      (s := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) c
    have h1' : Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL C) =
        Matrix.ProjGenLinGroup.mk B := by
      rw [← hC] at h1
      rwa [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk] at h1
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h1'
    refine ⟨u, ?_⟩
    rw [← hu, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
      Matrix.SpecialLinearGroup.coeToGL_det, one_mul, pow_two]
  · rintro ⟨u, hu⟩
    set C : GL (Fin 2) F := B * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ with hCdef
    have hCdet : Matrix.GeneralLinearGroup.det C = 1 := by
      rw [hCdef, map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, hu]
      group
    have hC_range : C ∈ (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact hCdet
    obtain ⟨C', hC'⟩ := hC_range
    refine ⟨QuotientGroup.mk C', ?_⟩
    have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk B := by
      rw [hCdef, map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]
    rw [pslHom, MonoidHom.comp_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, hC', hmk]

/-- **The index of `PSL(2,q)` in `PGL(2,q)` inside `Sym(ℙ¹(q))` is `2`.**

`PGL(2,q)/PSL(2,q) ≅ Fˣ/(Fˣ)²` has order `2` for `q = p^k` of odd characteristic: a
non-square `d` gives the element `x ↦ d·x` of `pglImage` outside `pslImage`, and multiplying
the determinant by `d` swaps the square and non-square classes. -/
theorem pglIndex (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    (Work.AUTL2.pslImage (GaloisField p k)).relIndex
      (Work.AUTL2.pglImage (GaloisField p k)) = 2 := by
  haveI : CharP (GaloisField p k) p := inferInstance
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    intro h
    obtain ⟨m, hm⟩ := hp
    omega
  haveI : Finite (GaloisField p k) := Finite.of_fintype _
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare (F := GaloisField p k) hchar
  have hd0 : d ≠ 0 := by rintro rfl; exact hd ⟨0, by ring⟩
  let D : GL (Fin 2) (GaloisField p k) := Normalizer.diagGL _ d hd0
  let a : Equiv.Perm (P1 (GaloisField p k)) := pglHom _ (Matrix.ProjGenLinGroup.mk D)
  have ha_mem : a ∈ pglImage (GaloisField p k) := ⟨_, rfl⟩
  have ha_not : a ∉ pslImage (GaloisField p k) := by
    intro h
    have h2 : IsSquare D.det :=
      (mem_pslImage_iff_isSquare_det _ D).mp (by simpa [a] using h)
    rw [show D.det = Units.mk0 d hd0 from diagGL_det _ d hd0] at h2
    exact hd (by
      simpa [Units.val_mk0] using (isSquare_coe_units_iff _ (Units.mk0 d hd0)).mpr h2)
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨a, ha_mem, ha_not, ?_⟩
  intro b hb
  obtain ⟨g, rfl⟩ := hb
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hmul : pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B) * a =
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (B * D)) := by
    simp only [a, map_mul]
  rw [hmul, mem_pslImage_iff_isSquare_det, mem_pslImage_iff_isSquare_det]
  have hdet : (B * D).det = B.det * Units.mk0 d hd0 := by
    rw [map_mul, show D.det = Units.mk0 d hd0 from diagGL_det _ d hd0]
  rw [hdet]
  exact (isSquare_units_or (GaloisField p k) hchar d hd hd0 B.det).symm

end Work.AUTL2.Aut
