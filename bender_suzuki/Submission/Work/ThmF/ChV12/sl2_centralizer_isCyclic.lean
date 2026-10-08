import Mathlib
import Submission.Work.ThmF.ChV12.torus_aux
import Submission.Work.Hering.AppVIII.QuadExt
import Submission.Work.Hering.AppVIII.QuadExtNorm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

open Polynomial Matrix
open Work.Hering.AppVIII

set_option maxHeartbeats 1600000

/-- In a finite field `F` of characteristic two with `3 ∣ Nat.card F + 1`, the quadratic form
`(a, b) ↦ a² + ab + b²` is anisotropic, equivalently `X² + X + 1` is irreducible over `F`. -/
theorem anisotropic_one {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (h3 : 3 ∣ Nat.card F + 1) : Anisotropic F 1 := by
  intro a b h
  rw [one_mul] at h
  have hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0 := fun t ht => torus_no_root h3 t ht
  by_cases hb : b = 0
  · subst hb
    simp only [mul_zero, add_zero] at h
    exact ⟨mul_self_eq_zero.mp h, rfl⟩
  · exfalso
    have hb2 : b * b ≠ 0 := mul_ne_zero hb hb
    have key : (b * b) * ((a / b) ^ 2 + (a / b) + 1) = a * a + a * b + b * b := by
      field_simp
    rw [h] at key
    have hz : (a / b) ^ 2 + (a / b) + 1 = 0 := (mul_eq_zero.mp key).resolve_left hb2
    exact hroot (a / b) hz

/-- The centralizer in `SL(2, F)` of an element of order `3` is cyclic, for `F` a finite field
of characteristic `2` with `3 ∣ |F| + 1`.  The element is regular, so its centralizer is the
multiplicative group of the field `F_{|F|²}` cut down by the norm-one condition. -/
theorem sl2_centralizer_isCyclic {F : Type*} [Field F] [Fintype F] [CharP F 2] (n : ℕ)
    (hF : Nat.card F = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (c : Matrix.SpecialLinearGroup (Fin 2) F) (hc : orderOf c = 3) :
    IsCyclic ↥(Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  have hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0 := by
    intro t ht
    exact torus_no_root (by rw [hF]; exact h3) t ht
  have haniso : Anisotropic F 1 := anisotropic_one (F := F) (by rw [hF]; exact h3)
  haveI : Fact (Irreducible (quadPoly F 1)) := ⟨quadPoly_irreducible F haniso⟩
  set cm : Matrix (Fin 2) (Fin 2) F := (c : Matrix (Fin 2) (Fin 2) F) with hcm
  have hc0 : cm * cm + cm + 1 = 0 := by
    rw [hcm]; exact sl2_order_three_sq c hc
  -- the algebra hom `F[α] → M₂(F)` sending `α` to `c`
  have haeval : (Polynomial.aeval cm) (quadPoly F 1) = 0 := by
    have hquad : (quadPoly F 1 : F[X]) = X ^ 2 + X + 1 := by rw [quadPoly]; simp
    rw [hquad]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, map_one, pow_two]
    exact hc0
  have hφ : ∀ a ∈ Ideal.span ({quadPoly F 1} : Set F[X]), (Polynomial.aeval cm) a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, haeval, zero_mul]
  let ψ : QuadExt F 1 →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
    Ideal.Quotient.liftₐ (Ideal.span ({quadPoly F 1} : Set F[X])) (Polynomial.aeval cm) hφ
  have hψroot : ψ (qalpha F 1) = cm := by
    have hcomp : ψ.comp (AdjoinRoot.mkₐ (quadPoly F 1)) = Polynomial.aeval cm :=
      Ideal.Quotient.liftₐ_comp (Ideal.span ({quadPoly F 1} : Set F[X])) (Polynomial.aeval cm) hφ
    have h2 : ψ ((AdjoinRoot.mkₐ (quadPoly F 1)) (X : F[X])) = (Polynomial.aeval cm) (X : F[X]) :=
      DFunLike.congr_fun hcomp (X : F[X])
    rw [Polynomial.aeval_X] at h2
    exact h2
  have hψinj : Function.Injective ψ :=
    RingHom.injective (ψ : QuadExt F 1 →+* Matrix (Fin 2) (Fin 2) F)
  set C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hC
  let toMat : C → Matrix (Fin 2) (Fin 2) F := fun x => (x : Matrix (Fin 2) (Fin 2) F)
  have toMat_mul : ∀ x y : C, toMat (x * y) = toMat x * toMat y := by
    intro x y
    simp only [toMat, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have toMat_one : toMat 1 = 1 := by
    simp only [toMat, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
  -- every element of the centralizer lies in the range of `ψ`
  have hmem : ∀ x : C, toMat x ∈ ψ.range := by
    intro x
    have hxmem : (x : Matrix.SpecialLinearGroup (Fin 2) F)
        ∈ Subgroup.centralizer ({c} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := x.2
    have hxcomm : (x : Matrix.SpecialLinearGroup (Fin 2) F) * c
        = c * (x : Matrix.SpecialLinearGroup (Fin 2) F) :=
      ((Subgroup.mem_centralizer_iff.mp hxmem) c (Set.mem_singleton c)).symm
    have hxcm : toMat x * cm = cm * toMat x := by
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
        (z : Matrix (Fin 2) (Fin 2) F)) hxcomm
      simpa [toMat, hcm, Matrix.SpecialLinearGroup.coe_mul] using h
    obtain ⟨p, q, hpq⟩ := (matrix_centralizer_eq_span (c := cm) hc0 hroot (toMat x)).mp hxcm
    rw [AlgHom.mem_range]
    refine ⟨algebraMap F (QuadExt F 1) p + algebraMap F (QuadExt F 1) q * qalpha F 1, ?_⟩
    rw [map_add, map_mul, hψroot, AlgHom.commutes, AlgHom.commutes]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact hpq.symm
  let e : (ψ.range) ≃+* QuadExt F 1 := (AlgEquiv.ofInjective ψ hψinj).symm.toRingEquiv
  let g : C →* QuadExt F 1 :=
    { toFun := fun x => e ⟨toMat x, hmem x⟩
      map_one' := by
        have h1 : (⟨toMat 1, hmem 1⟩ : ψ.range) = 1 := Subtype.ext (by simp [toMat_one])
        rw [h1]; exact map_one e
      map_mul' := by
        intro x y
        have hQR : (⟨toMat (x * y), hmem (x * y)⟩ : ψ.range)
            = ⟨toMat x, hmem x⟩ * ⟨toMat y, hmem y⟩ :=
          Subtype.ext (toMat_mul x y)
        rw [hQR, map_mul] }
  have hginj : Function.Injective g := by
    intro x y hxy
    change e ⟨toMat x, hmem x⟩ = e ⟨toMat y, hmem y⟩ at hxy
    have h2 := e.injective hxy
    have h4 : toMat x = toMat y :=
      congrArg (fun z : ψ.range => (z : Matrix (Fin 2) (Fin 2) F)) h2
    exact Subtype.ext (Subtype.ext (by simpa [toMat] using h4))
  exact isCyclic_of_injective_ringHom g hginj

end Work.ThmF.ChV12
