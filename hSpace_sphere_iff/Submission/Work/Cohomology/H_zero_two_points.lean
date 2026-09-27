import Mathlib
import Submission.Work.Cohomology.Hzero

/-!
# Degree `0` cohomology is determined by two points meeting every path component

This file proves `Work.Cohomology.H_zero_two_points`: if every point of a space `X` is
path-connected to one of two fixed points `p`, `q`, then a degree `0` cohomology class of the
singular complex of `X` is determined by its values at `p` and `q`.

The key input is that a degree `0` cocycle is *constant along paths*: a path from `x` to `y`
yields a singular `1`-simplex with faces the `0`-simplices at `x` and `y`, and the cocycle
condition makes its two face values equal.
-/

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

noncomputable section

/-- Naturality of `TopCat.toSSetObj₀Equiv` under a morphism of `TopCat`. -/
private lemma toSSetObj₀Equiv_map {Y X : TopCat.{0}} (f : Y ⟶ X)
    (σ : (TopCat.toSSet.obj Y).obj (op ⦋0⦌)) :
    TopCat.toSSetObj₀Equiv (X := X) ((TopCat.toSSet.map f).app (op ⦋0⦌) σ)
      = f (TopCat.toSSetObj₀Equiv (X := Y) σ) := by
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObj₀Equiv_apply]
  have hnat : ∀ t : Convexity.StdSimplex ℝ (Fin 1),
      (TopCat.toSSetObjEquiv X (op ⦋0⦌) ((TopCat.toSSet.map f).app (op ⦋0⦌) σ)) t
        = f ((TopCat.toSSetObjEquiv Y (op ⦋0⦌) σ) t) := fun t => rfl
  exact hnat default

/-- The singular `1`-simplex of `X` determined by a path `γ : Path x y`: it is the image of the
standard `1`-simplex `Δ[1] ⟶ Sim(I)` under `γ`. -/
private def pathSimplex {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    (TopCat.toSSet.obj X).obj (op ⦋1⦌) :=
  SSet.yonedaEquiv (SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map (TopCat.pathEquiv.symm γ).hom)

/-- The `0`-th face of `pathSimplex γ` is the point at the end of the path. -/
private lemma pathSimplex_face_zero {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    (TopCat.toSSet.obj X).δ 0 (pathSimplex γ) = TopCat.toSSetObj₀Equiv.symm y := by
  have h1 : (TopCat.pathEquiv.symm γ).hom 1 = y := (TopCat.pathEquiv.symm γ).hom₁
  rw [pathSimplex, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  rw [show SSet.stdSimplex.δ 0 ≫
        (SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map (TopCat.pathEquiv.symm γ).hom)
      = SSet.const (TopCat.toSSetObj₀Equiv.symm y) from ?_]
  rw [SSet.yonedaEquiv_const]
  · rw [← Category.assoc, SSet.stdSimplex.δ_zero_toSSetObjI, SSet.const_comp]
    congr 1
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_map, Equiv.apply_symm_apply, h1, Equiv.apply_symm_apply]

/-- The `1`-st face of `pathSimplex γ` is the point at the start of the path. -/
private lemma pathSimplex_face_one {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    (TopCat.toSSet.obj X).δ 1 (pathSimplex γ) = TopCat.toSSetObj₀Equiv.symm x := by
  have h0 : (TopCat.pathEquiv.symm γ).hom 0 = x := (TopCat.pathEquiv.symm γ).hom₀
  rw [pathSimplex, ← SSet.stdSimplex.yonedaEquiv_δ_comp]
  rw [show SSet.stdSimplex.δ 1 ≫
        (SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map (TopCat.pathEquiv.symm γ).hom)
      = SSet.const (TopCat.toSSetObj₀Equiv.symm x) from ?_]
  rw [SSet.yonedaEquiv_const]
  · rw [← Category.assoc, SSet.stdSimplex.δ_one_toSSetObjI, SSet.const_comp]
    congr 1
    apply TopCat.toSSetObj₀Equiv.injective
    rw [toSSetObj₀Equiv_map, Equiv.apply_symm_apply, h0, Equiv.apply_symm_apply]

/-- A degree `0` cocycle takes the same value on the two faces of any `1`-simplex. -/
private lemma cocycle_face_eq {S : SSet.{0}} {u : Cochain S ℚ 0} (hu : u ∈ cycles S ℚ 0)
    (σ : S.obj (op ⦋1⦌)) : u (S.δ 0 σ) = u (S.δ 1 σ) := by
  have h : coboundary S ℚ 0 u = 0 := (mem_cycles_iff u).mp hu
  have h2 := congrFun h σ
  rw [coboundary_apply, Fin.sum_univ_two, Pi.zero_apply] at h2
  norm_num at h2
  linarith

/-- A degree `0` cohomology class is constant along paths. -/
private lemma HzeroEval_eq_of_path {X : TopCat.{0}} {x y : X} (γ : Path x y)
    (z : H (TopCat.toSSet.obj X) ℚ 0) :
    HzeroEval X z y = HzeroEval X z x := by
  rw [show z = H.mk (Quot.out z).1 (Quot.out z).2 from (Quot.out_eq z).symm]
  rw [HzeroEval_mk]
  have hσ := cocycle_face_eq (Quot.out z).2 (pathSimplex γ)
  rw [pathSimplex_face_zero γ, pathSimplex_face_one γ] at hσ
  exact hσ

theorem H_zero_two_points {X : TopCat.{0}} (p q : X)
    (h : ∀ x : X, Nonempty (Path p x) ∨ Nonempty (Path q x)) :
    Function.Injective (fun z : Submission.Cohomology.H (TopCat.toSSet.obj X) ℚ 0 =>
      (Submission.Cohomology.HzeroEval X z p, Submission.Cohomology.HzeroEval X z q)) := by
  intro z1 z2 hz
  rw [Prod.mk.injEq] at hz
  obtain ⟨hp, hq⟩ := hz
  apply HzeroEval_injective X
  funext x
  rcases h x with hpx | hqx
  · obtain ⟨γ⟩ := hpx
    rw [HzeroEval_eq_of_path γ z1, HzeroEval_eq_of_path γ z2, hp]
  · obtain ⟨γ⟩ := hqx
    rw [HzeroEval_eq_of_path γ z1, HzeroEval_eq_of_path γ z2, hq]

end

end Work.Cohomology
