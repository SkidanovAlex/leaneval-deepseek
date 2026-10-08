/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The centralizer of a semisimple element of `SL(2,F)` is a torus

For `x ∈ SL(2,F)` with `(tr x) ^ 2 ≠ 4` and `F` a field with `(2 : F) ≠ 0`, the centralizer
`C_{SL(2,F)}(x)` is isomorphic to the "torus"
`hypTorus F d = {!![a, d*b; b, a] | a² - d·b² = 1}`, `d = disc F x = (tr x)² - 4`.

The isomorphism is `u ↦ (u 0 0) • 1 + (u 1 0) • W` where `W = conjMat F x = 2 • x - tr(x) • 1`
(the traceless part of `x`): both groups are the norm-one elements of the quadratic algebra
`F[X]/(X² - d)` realized as the commutative algebra `F·1 + F·W ⊆ M₂(F)` (with `W² = d • 1`).
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.centralizer_aux
import Submission.Work.L2F.Mat2.quadAlgebra
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Torus.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

variable {F : Type*} [Field F]

/-- An element of `hypTorus F d` is the matrix `quadMat d a b` formed from its own `(0,0)`- and
`(1,0)`-entries. -/
theorem hypTorus_eq_quadMat (d : F) (u : Work.L2F.hypTorus F d) :
    ((u : Matrix (Fin 2) (Fin 2) F))
      = quadMat d ((u : Matrix (Fin 2) (Fin 2) F) 0 0) ((u : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  obtain ⟨a, b, _, hu⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (u : Matrix.SpecialLinearGroup (Fin 2) F)).mp u.2
  have h00 : ((u : Matrix (Fin 2) (Fin 2) F)) 0 0 = a := by
    rw [hu]
    simp
  have h10 : ((u : Matrix (Fin 2) (Fin 2) F)) 1 0 = b := by
    rw [hu]
    simp
  rw [h00, h10, hu]
  rfl

/-- The norm relation for elements of `hypTorus F d`, in terms of the entries. -/
theorem hypTorus_entry_norm (d : F) (u : Work.L2F.hypTorus F d) :
    ((u : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2
        - d * ((u : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 = 1 := by
  obtain ⟨a, b, hab, hu⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (u : Matrix.SpecialLinearGroup (Fin 2) F)).mp u.2
  have h00 : ((u : Matrix (Fin 2) (Fin 2) F)) 0 0 = a := by
    rw [hu]
    simp
  have h10 : ((u : Matrix (Fin 2) (Fin 2) F)) 1 0 = b := by
    rw [hu]
    simp
  rw [h00, h10]
  exact hab

/-- The `(0,0)`-entry of a product in `hypTorus F d`: the coordinate law
`(a, b) * (c, e) = (a * c + d * b * e, a * e + b * c)`. -/
theorem hypTorus_entry_mul_fst (d : F) (u v : Work.L2F.hypTorus F d) :
    ((u * v : Work.L2F.hypTorus F d) : Matrix (Fin 2) (Fin 2) F) 0 0
      = ((u : Matrix (Fin 2) (Fin 2) F) 0 0) * ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
        + d * (((u : Matrix (Fin 2) (Fin 2) F) 1 0) * ((v : Matrix (Fin 2) (Fin 2) F) 1 0)) := by
  obtain ⟨a, b, _, hu⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (u : Matrix.SpecialLinearGroup (Fin 2) F)).mp u.2
  obtain ⟨c, e, _, hv⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (v : Matrix.SpecialLinearGroup (Fin 2) F)).mp v.2
  have hu' : ((u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = quadMat d a b := by rw [hu]; rfl
  have hv' : ((v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = quadMat d c e := by rw [hv]; rfl
  have h00u : ((u : Matrix (Fin 2) (Fin 2) F)) 0 0 = a := by rw [hu']; simp
  have h10u : ((u : Matrix (Fin 2) (Fin 2) F)) 1 0 = b := by rw [hu']; simp
  have h00v : ((v : Matrix (Fin 2) (Fin 2) F)) 0 0 = c := by rw [hv']; simp
  have h10v : ((v : Matrix (Fin 2) (Fin 2) F)) 1 0 = e := by rw [hv']; simp
  calc ((u * v : Work.L2F.hypTorus F d) : Matrix (Fin 2) (Fin 2) F) 0 0
      = (quadMat d a b * quadMat d c e) 0 0 := by
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu', hv']
    _ = (quadMat d (a * c + d * (b * e)) (a * e + b * c)) 0 0 := by rw [quadMat_mul]
    _ = a * c + d * (b * e) := by simp
    _ = ((u : Matrix (Fin 2) (Fin 2) F) 0 0) * ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
        + d * (((u : Matrix (Fin 2) (Fin 2) F) 1 0) * ((v : Matrix (Fin 2) (Fin 2) F) 1 0)) := by
        rw [h00u, h10u, h00v, h10v]

/-- The `(1,0)`-entry of a product in `hypTorus F d`. -/
theorem hypTorus_entry_mul_snd (d : F) (u v : Work.L2F.hypTorus F d) :
    ((u * v : Work.L2F.hypTorus F d) : Matrix (Fin 2) (Fin 2) F) 1 0
      = ((u : Matrix (Fin 2) (Fin 2) F) 0 0) * ((v : Matrix (Fin 2) (Fin 2) F) 1 0)
        + ((u : Matrix (Fin 2) (Fin 2) F) 1 0) * ((v : Matrix (Fin 2) (Fin 2) F) 0 0) := by
  obtain ⟨a, b, _, hu⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (u : Matrix.SpecialLinearGroup (Fin 2) F)).mp u.2
  obtain ⟨c, e, _, hv⟩ :=
    (Work.L2F.Conic.mem_hypTorus F d (v : Matrix.SpecialLinearGroup (Fin 2) F)).mp v.2
  have hu' : ((u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = quadMat d a b := by rw [hu]; rfl
  have hv' : ((v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = quadMat d c e := by rw [hv]; rfl
  have h00u : ((u : Matrix (Fin 2) (Fin 2) F)) 0 0 = a := by rw [hu']; simp
  have h10u : ((u : Matrix (Fin 2) (Fin 2) F)) 1 0 = b := by rw [hu']; simp
  have h00v : ((v : Matrix (Fin 2) (Fin 2) F)) 0 0 = c := by rw [hv']; simp
  have h10v : ((v : Matrix (Fin 2) (Fin 2) F)) 1 0 = e := by rw [hv']; simp
  calc ((u * v : Work.L2F.hypTorus F d) : Matrix (Fin 2) (Fin 2) F) 1 0
      = (quadMat d a b * quadMat d c e) 1 0 := by
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu', hv']
    _ = (quadMat d (a * c + d * (b * e)) (a * e + b * c)) 1 0 := by rw [quadMat_mul]
    _ = a * e + b * c := by simp
    _ = ((u : Matrix (Fin 2) (Fin 2) F) 0 0) * ((v : Matrix (Fin 2) (Fin 2) F) 1 0)
        + ((u : Matrix (Fin 2) (Fin 2) F) 1 0) * ((v : Matrix (Fin 2) (Fin 2) F) 0 0) := by
        rw [h00u, h10u, h00v, h10v]

/-- **The centralizer of a semisimple element of `SL(2,F)` is a torus.**  For `x ∈ SL(2,F)` with
`(tr x) ^ 2 ≠ 4` in a field with `(2 : F) ≠ 0`, the centralizer of `x` in `SL(2,F)` is isomorphic
to `hypTorus F (disc F x)`: the map `u ↦ (u 0 0) • 1 + (u 1 0) • W` (with
`W = conjMat F x = 2 • x - tr(x) • 1`) is an isomorphism onto `C_{SL(2,F)}(x)`, both sides being
the norm-one elements of the algebra `F·1 + F·W`, where `W² = disc F x • 1`. -/
theorem nonempty_hypTorus_mulEquiv_centralizer (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4) :
    Nonempty (Work.L2F.hypTorus F (Work.L2F.Torus.disc F x) ≃*
      Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  classical
  have hdisc : Work.L2F.Torus.disc F x ≠ 0 := by
    rw [Work.L2F.Torus.disc_apply]
    exact sub_ne_zero.mpr hx
  -- the map on `SL(2,F)`
  let φSL : Work.L2F.hypTorus F (Work.L2F.Torus.disc F x) →
      Matrix.SpecialLinearGroup (Fin 2) F :=
    fun u => ⟨((u : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
        + ((u : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x, by
      rw [det_smul_one_add_smul, Work.L2F.Torus.conjMat_trace, conjMat_det h2 x]
      have h := hypTorus_entry_norm (Work.L2F.Torus.disc F x) u
      linear_combination h⟩
  have hφSL_apply : ∀ u : Work.L2F.hypTorus F (Work.L2F.Torus.disc F x),
      ((φSL u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((u : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
          + ((u : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x := fun u => rfl
  -- membership of the image in the centralizer
  have hφSL_mem : ∀ u : Work.L2F.hypTorus F (Work.L2F.Torus.disc F x),
      φSL u ∈ Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    intro u
    rw [mem_centralizer_iff_smul_one_add F h2 x hx]
    exact ⟨(u : Matrix (Fin 2) (Fin 2) F) 0 0, (u : Matrix (Fin 2) (Fin 2) F) 1 0,
      hypTorus_entry_norm (Work.L2F.Torus.disc F x) u, by rw [hφSL_apply]⟩
  -- the monoid homomorphism
  let φ : Work.L2F.hypTorus F (Work.L2F.Torus.disc F x) →*
      Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    { toFun := fun u => ⟨φSL u, hφSL_mem u⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp [φSL]
      map_mul' := by
        intro u v
        apply Subtype.ext
        apply Subtype.ext
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        change ((φSL (u * v) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)
            = ((φSL u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              * ((φSL v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        rw [hφSL_apply (u * v), hφSL_apply u, hφSL_apply v,
          hypTorus_entry_mul_fst (Work.L2F.Torus.disc F x) u v,
          hypTorus_entry_mul_snd (Work.L2F.Torus.disc F x) u v]
        rw [smul_one_add_smul_mul (Work.L2F.Torus.conjMat_mul_self F x)] }
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · -- injectivity
    intro u v huv
    have hmat : ((φSL u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((φSL v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun t : Subgroup.centralizer
          ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =>
        ((t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) huv
      change ((φSL u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((φSL v : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      exact h
    rw [hφSL_apply u, hφSL_apply v] at hmat
    -- `1` and `W` are linearly independent, so the coefficients agree
    have hV : ∀ c : F, Work.L2F.Torus.conjMat F x ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      intro c hc
      have htr : (Work.L2F.Torus.conjMat F x).trace
          = (c • (1 : Matrix (Fin 2) (Fin 2) F)).trace := by rw [hc]
      rw [Work.L2F.Torus.conjMat_trace, Matrix.trace_smul, Matrix.trace_one,
        Fintype.card_fin] at htr
      have hc0 : c = 0 := by
        have h : c * (2 : F) = 0 := by simpa [smul_eq_mul] using htr.symm
        exact (mul_eq_zero.mp h).resolve_right h2
      rw [hc0, zero_smul] at hc
      exact Work.L2F.Torus.conjMat_ne_zero F x hdisc hc
    have hrearr : (((u : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
              - ((v : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
            + (((u : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x
              - ((v : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x))
        = ((((u : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
              + ((u : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x)
            - ((((v : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F)
              + ((v : Matrix (Fin 2) (Fin 2) F) 1 0) • Work.L2F.Torus.conjMat F x))) := by
      abel
    have hzero : (((u : Matrix (Fin 2) (Fin 2) F) 0 0) - ((v : Matrix (Fin 2) (Fin 2) F) 0 0)) •
          (1 : Matrix (Fin 2) (Fin 2) F)
        + (((u : Matrix (Fin 2) (Fin 2) F) 1 0) - ((v : Matrix (Fin 2) (Fin 2) F) 1 0)) •
          Work.L2F.Torus.conjMat F x = 0 := by
      rw [sub_smul, sub_smul, hrearr]
      exact sub_eq_zero.mpr hmat
    obtain ⟨h1, h2'⟩ := Work.L2F.Torus.algSpan_eq_zero F hV _ _ hzero
    have h00 : (u : Matrix (Fin 2) (Fin 2) F) 0 0 = (v : Matrix (Fin 2) (Fin 2) F) 0 0 :=
      sub_eq_zero.mp h1
    have h10 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = (v : Matrix (Fin 2) (Fin 2) F) 1 0 :=
      sub_eq_zero.mp h2'
    apply Subtype.ext
    apply Subtype.ext
    rw [hypTorus_eq_quadMat (Work.L2F.Torus.disc F x) u,
      hypTorus_eq_quadMat (Work.L2F.Torus.disc F x) v, h00, h10]
  · -- surjectivity
    intro y
    obtain ⟨a, b, hab, hy⟩ :=
      (mem_centralizer_iff_smul_one_add F h2 x hx
        (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
    have hdet : (quadMat (Work.L2F.Torus.disc F x) a b).det = 1 := by
      rw [quadMat_det]
      exact hab
    let u : Work.L2F.hypTorus F (Work.L2F.Torus.disc F x) :=
      ⟨⟨quadMat (Work.L2F.Torus.disc F x) a b, hdet⟩,
        (Work.L2F.Conic.mem_hypTorus F (Work.L2F.Torus.disc F x)
          ⟨quadMat (Work.L2F.Torus.disc F x) a b, hdet⟩).mpr ⟨a, b, hab, rfl⟩⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((φSL u : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (y : Matrix (Fin 2) (Fin 2) F)
    rw [hφSL_apply u]
    have h00 : (u : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by simp [u]
    have h10 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by simp [u]
    rw [h00, h10]
    exact hy.symm

end Work.L2F.Mat2
