import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.quadAlgebra
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.PSL.pslMap_eq_iff
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Involution.orderOf_pslZ
import Submission.Work.L2F.Involution.mem_normalizer_zpowers

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

variable {F : Type*} [Field F]

/-- `(↑(G⁻¹) : Matrix) = (↑G)⁻¹`. -/
theorem ti_coe_inv_eq (G : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
      (((G : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem ti_mul_inv_coe (G : Matrix.SpecialLinearGroup (Fin 2) F) :
    (G : Matrix (Fin 2) (Fin 2) F) *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem ti_inv_mul_coe (G : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

/-- Conjugating `quadMat d p q` by `G ∈ SL(2,F)`. -/
theorem ti_conj_quadMat (d : F) (G : Matrix.SpecialLinearGroup (Fin 2) F) (p q : F) :
    (G : Matrix (Fin 2) (Fin 2) F) * quadMat d p q *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
      p • (1 : Matrix (Fin 2) (Fin 2) F) + q •
        ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) := by
  rw [quadMat_smul_one_add]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, ti_mul_inv_coe, Matrix.mul_assoc]

/-- `G⁻¹ (G N G⁻¹) G = N` as matrices. -/
theorem ti_conj_cancel (G : Matrix.SpecialLinearGroup (Fin 2) F) (N : Matrix (Fin 2) (Fin 2) F) :
    (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        ((G : Matrix (Fin 2) (Fin 2) F) * N *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
        (G : Matrix (Fin 2) (Fin 2) F) = N := by
  rw [← Matrix.mul_assoc (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        ((G : Matrix (Fin 2) (Fin 2) F) * N)
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)]
  rw [← Matrix.mul_assoc (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        (G : Matrix (Fin 2) (Fin 2) F) N]
  rw [ti_inv_mul_coe, Matrix.one_mul]
  rw [Matrix.mul_assoc N (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        (G : Matrix (Fin 2) (Fin 2) F)]
  rw [ti_inv_mul_coe, Matrix.mul_one]

/-- If `Mβ` lies in the quadratic algebra `A = {M | inQuad d M}` and has non-zero `(1,0)` entry,
and `G Mβ G⁻¹` also lies in `A`, then `G T G⁻¹ ∈ A` for `T = quadT d`. -/
theorem ti_inQuad_conj_quadT {d : F}
    {G : Matrix.SpecialLinearGroup (Fin 2) F} {Mβ : Matrix (Fin 2) (Fin 2) F}
    (hβ : inQuad d Mβ) (hns : Mβ 1 0 ≠ 0)
    (hconj : inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * Mβ *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))) :
    inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) := by
  obtain ⟨c, e, he⟩ := (inQuad_iff d Mβ).mp hβ
  have he0 : e ≠ 0 := by
    intro h
    apply hns
    rw [he, h]
    simp
  rw [he, ti_conj_quadMat d G c e] at hconj
  have h1 : inQuad d (c • (1 : Matrix (Fin 2) (Fin 2) F)) := inQuad_smul c (inQuad_one d)
  have h2 : inQuad d ((c • (1 : Matrix (Fin 2) (Fin 2) F) +
      e • ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))) -
      c • (1 : Matrix (Fin 2) (Fin 2) F)) := inQuad_sub hconj h1
  have h3 : inQuad d (e • ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))) := by
    convert h2 using 1
    abel
  have h4 := inQuad_smul (e⁻¹) h3
  simpa [smul_smul, inv_mul_cancel₀ he0, one_smul] using h4

end Work.L2F.Mat2

namespace Work.L2F.Mat2

variable {F : Type*} [Field F]

/-- Conjugation by `G ∈ SL(2,F)` preserves the quadratic algebra `A = {M | inQuad d M}`,
provided `G T G⁻¹ ∈ A` for `T = quadT d`. -/
theorem ti_conj_mem_inQuad_iff (d : F) (G : Matrix.SpecialLinearGroup (Fin 2) F)
    (hT : inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)))
    (M : Matrix (Fin 2) (Fin 2) F) :
    inQuad d M ↔ inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * M *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) := by
  constructor
  · intro hM
    obtain ⟨p, q, hpq⟩ := (inQuad_iff d M).mp hM
    rw [hpq, ti_conj_quadMat d G p q]
    exact inQuad_add (inQuad_smul p (inQuad_one d)) (inQuad_smul q hT)
  · intro hMc
    obtain ⟨a, b, hab⟩ := (inQuad_iff d ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))).mp hT
    have hb : b ≠ 0 := by
      intro hb0
      have hscalar : (G : Matrix (Fin 2) (Fin 2) F) * quadT d *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
            a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hab, hb0, quadMat_smul_one_add, zero_smul, add_zero]
      have hTscalar : quadT d = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        calc quadT d = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
              ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
                (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
              (G : Matrix (Fin 2) (Fin 2) F) := (ti_conj_cancel G (quadT d)).symm
          _ = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
                (a • (1 : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) := by
                rw [hscalar]
          _ = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
                rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ti_inv_mul_coe]
      have hentry := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 1 0) hTscalar
      rw [quadT_apply_10] at hentry
      have hz : (a • (1 : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
        simp [Matrix.smul_apply]
      rw [hz] at hentry
      exact one_ne_zero hentry
    have hN0 : (G : Matrix (Fin 2) (Fin 2) F) * quadMat d (-(a/b)) b⁻¹ *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = quadT d := by
      rw [ti_conj_quadMat d G (-(a/b)) b⁻¹, hab, quadMat_smul_one_add]
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul, ← add_assoc, ← add_smul]
      have hc : -(a / b) + b⁻¹ * a = 0 := by
        rw [div_eq_mul_inv, mul_comm b⁻¹ a, neg_add_cancel]
      rw [hc, zero_smul, zero_add]
    have hGiTG : (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        quadT d * (G : Matrix (Fin 2) (Fin 2) F) = quadMat d (-(a/b)) b⁻¹ := by
      rw [← hN0]
      exact ti_conj_cancel G (quadMat d (-(a/b)) b⁻¹)
    obtain ⟨c, e, hce⟩ := (inQuad_iff d ((G : Matrix (Fin 2) (Fin 2) F) * M *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))).mp hMc
    have hM : M = c • (1 : Matrix (Fin 2) (Fin 2) F) + e • quadMat d (-(a/b)) b⁻¹ := by
      calc M = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
            ((G : Matrix (Fin 2) (Fin 2) F) * M *
              (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
            (G : Matrix (Fin 2) (Fin 2) F) := (ti_conj_cancel G M).symm
        _ = (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
              quadMat d c e * (G : Matrix (Fin 2) (Fin 2) F) := by rw [hce]
        _ = c • (1 : Matrix (Fin 2) (Fin 2) F) + e •
              ((((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
                quadT d * (G : Matrix (Fin 2) (Fin 2) F)) := by
              have hcq := ti_conj_quadMat d (G⁻¹) c e
              simp only [inv_inv] at hcq
              rw [hcq]
        _ = c • (1 : Matrix (Fin 2) (Fin 2) F) + e • quadMat d (-(a/b)) b⁻¹ := by
              rw [hGiTG]
    rw [hM]
    exact inQuad_add (inQuad_smul c (inQuad_one d)) (inQuad_smul e (inQuad_quadMat d _ _))

end Work.L2F.Mat2

namespace Work.L2F.Mat2

variable {F : Type*} [Field F]

/-- If `G T G⁻¹ ∈ A`, then `G` normalizes `hypTorus F d` inside `SL(2,F)`. -/
theorem ti_mem_normalizer_hypTorus {d : F}
    {G : Matrix.SpecialLinearGroup (Fin 2) F}
    (hT : inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * quadT d *
      (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))) :
    G ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hMq : inQuad d ((h : Matrix (Fin 2) (Fin 2) F)) := inQuad_of_mem_hypTorus hh
    have hcj : inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) :=
      (ti_conj_mem_inQuad_iff d G hT (h : Matrix (Fin 2) (Fin 2) F)).mp hMq
    have hdet : ((G : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
        Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe]
      ring
    have hres := mem_hypTorus_of_inQuad hcj hdet
    have heq : (⟨(G : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F), hdet⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) = G * h * G⁻¹ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rwa [heq] at hres
  · intro hh
    have hMq : inQuad d (((G * h * G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) := inQuad_of_mem_hypTorus hh
    have hcoe : (((G * h * G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F) *
          (h : Matrix (Fin 2) (Fin 2) F) *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [hcoe] at hMq
    have hMq' : inQuad d ((h : Matrix (Fin 2) (Fin 2) F)) :=
      (ti_conj_mem_inQuad_iff d G hT (h : Matrix (Fin 2) (Fin 2) F)).mpr hMq
    have hdet : (h : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe h
    have hres := mem_hypTorus_of_inQuad hMq' hdet
    have heq : (⟨(h : Matrix (Fin 2) (Fin 2) F), hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F) = h :=
      Subtype.ext rfl
    rwa [heq] at hres

end Work.L2F.Mat2

namespace Work.L2F.PSL

variable {F : Type*} [Field F]

/-- The image in `PSL(2,F)` of an element of `SL(2,F)` normalizing `hypTorus F d` normalizes
`pslHypTorus F d`. -/
theorem ti_pslMap_mem_normalizer_pslHypTorus {d : F}
    {G : Matrix.SpecialLinearGroup (Fin 2) F}
    (hG : G ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    Work.PSL2.pslMap F G ∈ Subgroup.normalizer (Work.L2F.pslHypTorus F d :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
  have hfwd : ∀ (K : Matrix.SpecialLinearGroup (Fin 2) F),
      K ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∀ z ∈ Work.L2F.pslHypTorus F d,
        Work.PSL2.pslMap F K * z * (Work.PSL2.pslMap F K)⁻¹ ∈ Work.L2F.pslHypTorus F d := by
    intro K hK z hz
    obtain ⟨hh, hhh, rfl⟩ := Subgroup.mem_map.mp hz
    have hKh : K * hh * K⁻¹ ∈ Work.L2F.hypTorus F d :=
      (Subgroup.mem_normalizer_iff.mp hK hh).mp hhh
    rw [show Work.PSL2.pslMap F K * Work.PSL2.pslMap F hh * (Work.PSL2.pslMap F K)⁻¹ =
        Work.PSL2.pslMap F (K * hh * K⁻¹) from by rw [map_mul, map_mul, map_inv]]
    exact Subgroup.mem_map.mpr ⟨K * hh * K⁻¹, hKh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hfwd G hG z
  · intro hz
    have hGinv : G⁻¹ ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      (Subgroup.normalizer (Work.L2F.hypTorus F d : Set (Matrix.SpecialLinearGroup (Fin 2) F))).inv_mem hG
    have hx : z = Work.PSL2.pslMap F G⁻¹ *
        (Work.PSL2.pslMap F G * z * (Work.PSL2.pslMap F G)⁻¹) *
        (Work.PSL2.pslMap F G⁻¹)⁻¹ := by
      rw [map_inv]
      group
    rw [hx]
    exact hfwd G⁻¹ hGinv _ hz

end Work.L2F.PSL

namespace Work.L2F.PSL

open scoped MatrixGroups
open Matrix

/-- `pslHypTorus F d` (`d ≠ 0`, odd characteristic) is a TI subgroup of `PSL(2,F)`: its conjugates
by elements outside its normalizer meet it trivially.  Proof: suppose `1 ≠ t ∈ Tp ⊓ Tp^g`; lift to
`α ∈ H = hypTorus F d` with `π(α) = t` and to `β ∈ H` with `π(g β g⁻¹) = t`, so `α = ± g β g⁻¹`
(replacing `β` by `-β ∈ H` handles the `-` sign).  Since `t ≠ 1`, `α` is not scalar, so
`C_{M₂(F)}(α) = F[α]`; hence `g F[β] g⁻¹ = F[α]`, so `g` normalizes the 2-dimensional `F`-algebra
`A = F[H]` (every element of `H` has the form `a • 1 + b • T`, `T = !![0,d;1,0]`, so `A = F[T]`), and
conjugation induces an `F`-algebra automorphism of `A` sending `T` to `±T`; both kinds normalize
`H` (elements of `A^•` centralize it and the `T ↦ -T` automorphism inverts it, as
`(a•1 + b•T)⁻¹ = a•1 - b•T`).  Hence `π(g) ∈ N(Tp)`. -/
theorem ti_pslHypTorus (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hg : g ∉ Subgroup.normalizer (Work.L2F.pslHypTorus F d :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) :
    Work.L2F.pslHypTorus F d ⊓
        (Work.L2F.pslHypTorus F d).map (MulAut.conj g).toMonoidHom = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxT, hxTg⟩ := hx
  by_contra hx1
  obtain ⟨G, hG⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
  have hpg : Work.PSL2.pslMap F G = g := hG
  obtain ⟨α, hαH, hαx⟩ := Subgroup.mem_map.mp hxT
  obtain ⟨y, hyT, hyx⟩ := Subgroup.mem_map.mp hxTg
  have hyx' : x = g * y * g⁻¹ := by
    rw [← hyx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨β, hβH, hβy⟩ := Subgroup.mem_map.mp hyT
  have hR : Work.PSL2.pslMap F (G * β * G⁻¹) = g * y * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hpg, hβy]
  have hL : Work.PSL2.pslMap F α = g * y * g⁻¹ := by rw [hαx]; exact hyx'
  have hconj : Work.PSL2.pslMap F α = Work.PSL2.pslMap F (G * β * G⁻¹) := hL.trans hR.symm
  have hneg_mem : Work.L2F.negOne F ∈ Work.L2F.hypTorus F d := by
    rw [Work.L2F.Conic.mem_hypTorus]
    refine ⟨-1, 0, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]
  have hkey : ∀ (β' : Matrix.SpecialLinearGroup (Fin 2) F),
      β' ∈ Work.L2F.hypTorus F d → α = G * β' * G⁻¹ →
      Work.PSL2.pslMap F G ∈ Subgroup.normalizer (Work.L2F.pslHypTorus F d :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    intro β' hβ'H hβ'eq
    have hns : ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      intro h0
      obtain ⟨a, b, hab⟩ := (Work.L2F.Mat2.inQuad_iff d
        ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).mp
        (Work.L2F.Mat2.inQuad_of_mem_hypTorus hβ'H)
      have hb0 : b = 0 := by rw [hab] at h0; simpa using h0
      have hβ'scalar : ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hab, hb0, Work.L2F.Mat2.quadMat_smul_one_add, zero_smul, add_zero]
      have hαscalar : ((α : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hβ'eq]
        simp only [Matrix.SpecialLinearGroup.coe_mul, hβ'scalar, Work.L2F.Mat2.ti_mul_inv_coe,
          Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      have hαcenter : α ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hαscalar]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
      have hpsl1 : Work.PSL2.pslMap F α = 1 := by
        show QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) α = 1
        exact (QuotientGroup.eq_one_iff α).mpr hαcenter
      exact hx1 (by rw [← hαx, hpsl1])
    have hαq : Work.L2F.Mat2.inQuad d
        ((α : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
      Work.L2F.Mat2.inQuad_of_mem_hypTorus hαH
    have hβ'q : Work.L2F.Mat2.inQuad d
        ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
      Work.L2F.Mat2.inQuad_of_mem_hypTorus hβ'H
    have hmat : ((α : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) *
          ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [hβ'eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have hconjq : Work.L2F.Mat2.inQuad d
        ((G : Matrix (Fin 2) (Fin 2) F) *
          ((β' : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) := by
      rw [← hmat]; exact hαq
    have hT : Work.L2F.Mat2.inQuad d ((G : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Mat2.quadT d *
        (((G⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) :=
      Work.L2F.Mat2.ti_inQuad_conj_quadT hβ'q hns hconjq
    have hGnorm : G ∈ Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := Work.L2F.Mat2.ti_mem_normalizer_hypTorus hT
    exact Work.L2F.PSL.ti_pslMap_mem_normalizer_pslHypTorus hGnorm
  rcases (Work.L2F.PSL.pslMap_eq_iff F h2 α (G * β * G⁻¹)).mp hconj with hcase | hcase
  · exact hg (by rw [← hpg]; exact hkey β hβH hcase)
  · have hβ'mem : Work.L2F.negOne F * β ∈ Work.L2F.hypTorus F d :=
      (Work.L2F.hypTorus F d).mul_mem hneg_mem hβH
    have heq : α = G * (Work.L2F.negOne F * β) * G⁻¹ := by
      rw [hcase]
      calc Work.L2F.negOne F * (G * β * G⁻¹)
          = (Work.L2F.negOne F * G) * β * G⁻¹ := by group
        _ = (G * Work.L2F.negOne F) * β * G⁻¹ := by rw [Work.L2F.Involution.negOne_mul_comm F G]
        _ = G * (Work.L2F.negOne F * β) * G⁻¹ := by group
    exact hg (by rw [← hpg]; exact hkey (Work.L2F.negOne F * β) hβ'mem heq)

end Work.L2F.PSL
