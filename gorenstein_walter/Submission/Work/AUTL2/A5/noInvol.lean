/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / A5 : no involution in the coset `x · σ · PSL`

If `x ∈ pglImage \ pslImage` and `σ` is the field involution, then no element of the coset
`(x · galHom σ) · pslImage` is an involution.  This is the case-B input of the A5 analysis.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.A5.tools
import Submission.Work.AUTL2.A5.mat

open scoped MatrixGroups

set_option linter.style.haveILetI false

namespace Work.AUTL2.A5
open Work.AUTL2

/-- No element of the coset `(x * galHom σ) * pslImage` is an involution, when `x ∈ pglImage`
but `x ∉ pslImage` and `σ * σ = 1`, `σ ≠ 1`. -/
theorem coset_sq_ne_one (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)]
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1)
    (x : Equiv.Perm (P1 (GaloisField p k)))
    (hxP : x ∈ pglImage (GaloisField p k))
    (hxS : x ∉ pslImage (GaloisField p k))
    (s : Equiv.Perm (P1 (GaloisField p k))) (hsS : s ∈ pslImage (GaloisField p k)) :
    (x * galHom (GaloisField p k) σ * s) ^ 2 ≠ 1 := by
  intro hcon
  have hconjS : galHom (GaloisField p k) σ * s * (galHom (GaloisField p k) σ)⁻¹ ∈ pslImage (GaloisField p k) :=
    (Subgroup.le_normalizer_iff.mp (Galois.galSub_le_normalizer_pslImage (GaloisField p k)))
      (galHom (GaloisField p k) σ) ⟨σ, rfl⟩ s hsS
  set a : Equiv.Perm (P1 (GaloisField p k)) := x * (galHom (GaloisField p k) σ * s * (galHom (GaloisField p k) σ)⁻¹) with hadef
  have haP : a ∈ pglImage (GaloisField p k) :=
    mul_mem hxP (pslImage_le_pglImage (GaloisField p k) hconjS)
  have hgs : x * galHom (GaloisField p k) σ * s = a * galHom (GaloisField p k) σ := by
    rw [hadef]; group
  rw [hgs] at hcon
  obtain ⟨A, hA⟩ : ∃ A : Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k),
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) = a := by
    obtain ⟨y, hy⟩ := haP
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
    exact ⟨A, hy⟩
  have hconj : galHom (GaloisField p k) σ * pglHom (GaloisField p k)
        (Matrix.ProjGenLinGroup.mk A) =
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)) *
        galHom (GaloisField p k) σ := by
    rw [← Galois.fieldAut_conj_pgl (GaloisField p k) σ A]; group
  have hσσ : galHom (GaloisField p k) σ * galHom (GaloisField p k) σ = 1 := by
    rw [← map_mul, hσ, map_one]
  have hsq : (a * galHom (GaloisField p k) σ) ^ 2 =
      pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
        (A * Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)) := by
    calc (a * galHom (GaloisField p k) σ) ^ 2
        = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) *
          (galHom (GaloisField p k) σ * pglHom (GaloisField p k)
            (Matrix.ProjGenLinGroup.mk A)) * galHom (GaloisField p k) σ := by
          rw [pow_two, ← hA]; group
      _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) *
          (pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)) *
            galHom (GaloisField p k) σ) * galHom (GaloisField p k) σ := by rw [hconj]
      _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) *
          pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)) *
          (galHom (GaloisField p k) σ * galHom (GaloisField p k) σ) := by group
      _ = pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (A *
            Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)) := by
          rw [hσσ, mul_one, ← map_mul, ← map_mul]
  rw [hsq] at hcon
  have hcenter : A * Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (GaloisField p k)) :=
    (pglHom_mk_eq_one_iff (A * Matrix.GeneralLinearGroup.map (σ : GaloisField p k →+* GaloisField p k) A)).mp hcon
  have hsqdet := isSquare_det_of_mul_map_eq_scalar p k hp hq σ hσ hne A hcenter
  have haS : a ∈ pslImage (GaloisField p k) := by
    rw [← hA]
    exact isSquare_det_mem_pslImage A hsqdet
  apply hxS
  have h2 : x = a * (galHom (GaloisField p k) σ * s * (galHom (GaloisField p k) σ)⁻¹)⁻¹ := by
    rw [hadef]; group
  rw [h2]
  exact mul_mem haS (inv_mem hconjS)

end Work.AUTL2.A5
