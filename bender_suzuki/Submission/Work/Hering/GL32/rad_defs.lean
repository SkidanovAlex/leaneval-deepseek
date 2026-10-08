import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Setup for the simplicity of `M₄` (the trace-zero matrices as a `GL(3,2)`-module)

This file collects the vocabulary used to prove `Work.Hering.GL32.rad_irreducible`:

* `mkGL P Q _ _` is the element of `GL(3,2)` given by the invertible matrix `P` with explicit
  inverse `Q`; `toMatrix'_mkGL` and `toMatrix'_mkGL_symm` compute its matrix.
* `cEnd P Q` is the linear map `A ↦ P * A * Q` on `Mat`, i.e. the conjugation action on matrices.
* `exists_fixed_of_sq` is the elementary fact that an involution acting linearly on a nonzero
  space over `F₂` has a nonzero fixed vector; `fixSub` packages its fixed-point submodule, and
  `fixSub_ne_bot` / `map_fixSub_of` are the two bookkeeping lemmas used for the descent.
* `T1`, `T2`, `T3` are the three elementary (lower) unitriangular involutions whose matrices
  `t1`, `t2`, `t3` generate a Sylow `2`-subgroup of `GL(3,2)`; the centralizer of this subgroup
  inside the trace-zero matrices is spanned by `M20` (proved in `rad_alg`).
* `M01, M10, M12, M21, M02, M20, EE01, EE02` are eight elements of the `GL(3,2)`-orbit of `M20`
  which together span the trace-zero space.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Work.Hering.GL32

/-- The ambient space: `3 × 3` matrices over `F₂`. -/
abbrev Mat : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

/-! ## Elements of `GL(3,2)` from invertible matrices -/

/-- The linear equivalence `F₂³ → F₂³` given by the matrix `P`, whose inverse matrix is `Q`. -/
noncomputable def mkGL (P Q : Mat) (h1 : Q * P = 1) (h2 : P * Q = 1) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun v := Matrix.mulVec P v
  invFun v := Matrix.mulVec Q v
  left_inv v := by
    change Matrix.mulVec Q (Matrix.mulVec P v) = v
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  right_inv v := by
    change Matrix.mulVec P (Matrix.mulVec Q v) = v
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  map_add' u v := Matrix.mulVec_add P u v
  map_smul' c v := Matrix.mulVec_smul P c v

lemma toMatrix'_mkGL (P Q : Mat) (h1 : Q * P = 1) (h2 : P * Q = 1) :
    LinearMap.toMatrix' (mkGL P Q h1 h2 :
      (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = P := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  show (mkGL P Q h1 h2) (Pi.single j 1) i = P i j
  rw [show (mkGL P Q h1 h2) (Pi.single j 1) = Matrix.mulVec P (Pi.single j 1) from rfl,
      Matrix.mulVec_single_one, Matrix.col_apply]

lemma toMatrix'_mkGL_symm (P Q : Mat) (h1 : Q * P = 1) (h2 : P * Q = 1) :
    LinearMap.toMatrix' ((mkGL P Q h1 h2).symm :
      (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = Q := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  show (mkGL P Q h1 h2).symm (Pi.single j 1) i = Q i j
  rw [show (mkGL P Q h1 h2).symm (Pi.single j 1) = Matrix.mulVec Q (Pi.single j 1) from rfl,
      Matrix.mulVec_single_one, Matrix.col_apply]

/-! ## Conjugation on matrices -/

/-- Conjugation of matrices by `P`, with inverse matrix `Q`: `A ↦ P * A * Q`. -/
noncomputable def cEnd (P Q : Mat) : Mat →ₗ[ZMod 2] Mat where
  toFun A := P * A * Q
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]; rfl

/-! ## Fixed points of an involution over `F₂` -/

/-- An involution `f` (`f ∘ f = id`) acting `F₂`-linearly on a nonzero subspace `U` which it
preserves has a nonzero fixed vector.  (In characteristic `2`, `f - id` is a square-zero
endomorphism of `U`.) -/
lemma exists_fixed_of_sq (f : Mat →ₗ[ZMod 2] Mat) (hf : ∀ A, f (f A) = A)
    (U : Submodule (ZMod 2) Mat) (hU : U ≠ ⊥) (hmap : ∀ A ∈ U, f A ∈ U) :
    ∃ A ∈ U, A ≠ 0 ∧ f A = A := by
  have h2 : ∀ x : Mat, x + x = 0 := by
    intro x; ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hneg : ∀ x : Mat, -x = x := fun x => by
    rw [neg_eq_iff_add_eq_zero]; exact h2 x
  have hsub : ∀ x y : Mat, x - y = x + y := fun x y => by
    rw [sub_eq_add_neg, hneg y]
  have key : ∀ x y : Mat, (x - y) - (y - x) = 0 := by
    intro x y
    rw [hsub (x - y) (y - x), hsub x y, hsub y x, add_comm y x]
    exact h2 (x + y)
  have hgg : ∀ A : Mat,
      (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat))
        ((f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) A) = 0 := by
    intro A
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [hf A]
    exact key A (f A)
  have hne : U ⊓ LinearMap.ker (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) ≠ ⊥ := by
    intro hbot
    have hUle : U ≤ LinearMap.ker (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) := by
      intro A hA
      rw [LinearMap.mem_ker]
      have hgA : (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) A ∈ U := by
        rw [LinearMap.sub_apply, LinearMap.id_apply]
        exact U.sub_mem (hmap A hA) hA
      have hker : (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) A ∈
          LinearMap.ker (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) := by
        rw [LinearMap.mem_ker]; exact hgg A
      have hmem : (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) A ∈
          (⊥ : Submodule (ZMod 2) Mat) := by
        rw [← hbot]; exact Submodule.mem_inf.mpr ⟨hgA, hker⟩
      rwa [Submodule.mem_bot (ZMod 2)] at hmem
    exact hU (by rw [← inf_eq_left.mpr hUle, hbot])
  obtain ⟨A, hA, hA0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨A, (Submodule.mem_inf.mp hA).1, hA0, ?_⟩
  have h : (f - (LinearMap.id : Mat →ₗ[ZMod 2] Mat)) A = 0 := (Submodule.mem_inf.mp hA).2
  rwa [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h

/-- The fixed points of the conjugation action `cEnd P Q` inside a subspace `W`. -/
noncomputable def fixSub (P Q : Mat) (W : Submodule (ZMod 2) Mat) : Submodule (ZMod 2) Mat :=
  W ⊓ LinearMap.ker (cEnd P Q - (LinearMap.id : Mat →ₗ[ZMod 2] Mat))

lemma mem_fixSub {P Q : Mat} {W : Submodule (ZMod 2) Mat} {A : Mat} :
    A ∈ fixSub P Q W ↔ A ∈ W ∧ cEnd P Q A = A := by
  rw [fixSub, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

/-- If `cEnd P Q` is an involution preserving `W ≠ ⊥`, then its fixed-point subspace is nonzero. -/
lemma fixSub_ne_bot {P Q : Mat} (hPQ : ∀ A, cEnd P Q (cEnd P Q A) = A)
    {W : Submodule (ZMod 2) Mat} (hW : W ≠ ⊥) (hmap : ∀ A ∈ W, cEnd P Q A ∈ W) :
    fixSub P Q W ≠ ⊥ := by
  obtain ⟨A, hA, hA0, hfix⟩ := exists_fixed_of_sq (cEnd P Q) hPQ W hW hmap
  intro h
  refine hA0 ?_
  have hmem : A ∈ fixSub P Q W := by rw [mem_fixSub]; exact ⟨hA, hfix⟩
  rw [h] at hmem
  simpa using hmem

/-- If `cEnd P' Q'` maps `W` into itself and commutes with `cEnd P Q` on the fixed points of the
latter, then it maps `fixSub P Q W` into itself. -/
lemma map_fixSub_of {P Q P' Q' : Mat} {W : Submodule (ZMod 2) Mat}
    (hmapW : ∀ A ∈ W, cEnd P' Q' A ∈ W)
    (hfix : ∀ A ∈ W, cEnd P Q A = A → cEnd P Q (cEnd P' Q' A) = cEnd P' Q' A) :
    ∀ A ∈ fixSub P Q W, cEnd P' Q' A ∈ fixSub P Q W := by
  intro A hA
  rw [mem_fixSub] at hA ⊢
  exact ⟨hmapW A hA.1, hfix A hA.1 hA.2⟩

/-! ## The elementary unitriangular involutions -/

/-- `I + E_{10}` (add coordinate `0` to coordinate `1`). -/
def T1 : Mat := ![![1,0,0],![1,1,0],![0,0,1]]
/-- `I + E_{21}` (add coordinate `1` to coordinate `2`). -/
def T2 : Mat := ![![1,0,0],![0,1,0],![0,1,1]]
/-- `I + E_{20}` (add coordinate `0` to coordinate `2`). -/
def T3 : Mat := ![![1,0,0],![0,1,0],![1,0,1]]

lemma T1_sq : T1 * T1 = 1 := by decide
lemma T2_sq : T2 * T2 = 1 := by decide
lemma T3_sq : T3 * T3 = 1 := by decide

/-- The element of `GL(3,2)` with matrix `T1`. -/
noncomputable def t1 : GL32 := mkGL T1 T1 T1_sq T1_sq
/-- The element of `GL(3,2)` with matrix `T2`. -/
noncomputable def t2 : GL32 := mkGL T2 T2 T2_sq T2_sq
/-- The element of `GL(3,2)` with matrix `T3`. -/
noncomputable def t3 : GL32 := mkGL T3 T3 T3_sq T3_sq

lemma toMatrix'_t1 :
    LinearMap.toMatrix' (t1 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T1 :=
  toMatrix'_mkGL T1 T1 T1_sq T1_sq

lemma toMatrix'_t1_symm :
    LinearMap.toMatrix' (t1.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T1 :=
  toMatrix'_mkGL_symm T1 T1 T1_sq T1_sq

lemma toMatrix'_t2 :
    LinearMap.toMatrix' (t2 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T2 :=
  toMatrix'_mkGL T2 T2 T2_sq T2_sq

lemma toMatrix'_t2_symm :
    LinearMap.toMatrix' (t2.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T2 :=
  toMatrix'_mkGL_symm T2 T2 T2_sq T2_sq

lemma toMatrix'_t3 :
    LinearMap.toMatrix' (t3 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T3 :=
  toMatrix'_mkGL T3 T3 T3_sq T3_sq

lemma toMatrix'_t3_symm :
    LinearMap.toMatrix' (t3.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) = T3 :=
  toMatrix'_mkGL_symm T3 T3 T3_sq T3_sq

/-! ## The eight matrices spanning the trace-zero space -/

/-- The matrix unit `E_{01}`. -/
def M01 : Mat := ![![0,1,0],![0,0,0],![0,0,0]]
/-- The matrix unit `E_{10}`. -/
def M10 : Mat := ![![0,0,0],![1,0,0],![0,0,0]]
/-- The matrix unit `E_{12}`. -/
def M12 : Mat := ![![0,0,0],![0,0,1],![0,0,0]]
/-- The matrix unit `E_{21}`. -/
def M21 : Mat := ![![0,0,0],![0,0,0],![0,1,0]]
/-- The matrix unit `E_{02}`. -/
def M02 : Mat := ![![0,0,1],![0,0,0],![0,0,0]]
/-- The matrix unit `E_{20}`. -/
def M20 : Mat := ![![0,0,0],![0,0,0],![1,0,0]]
/-- `(e₀+e₁)(e₀+e₁)ᵀ = E_{00} + E_{01} + E_{10} + E_{11}`. -/
def EE01 : Mat := ![![1,1,0],![1,1,0],![0,0,0]]
/-- `(e₀+e₂)(e₀+e₂)ᵀ = E_{00} + E_{02} + E_{20} + E_{22}`. -/
def EE02 : Mat := ![![1,0,1],![0,0,0],![1,0,1]]

/-- The eight explicit trace-zero matrices spanning the space of trace-zero matrices. -/
def S : Set Mat := {M01, M10, M12, M21, M02, M20, EE01, EE02}

/-- Every trace-zero matrix is the following explicit `F₂`-linear combination of the eight
elements of `S`.  This is a finite verification, carried out by `decide`. -/
lemma tracezero_eq_combo : ∀ A : Mat, A.trace = 0 →
    A = (A 0 1 - A 1 1) • M01 + (A 1 0 - A 1 1) • M10 + A 1 2 • M12 + A 2 1 • M21 +
        (A 0 2 - A 0 0 + A 1 1) • M02 + (A 2 0 - A 0 0 + A 1 1) • M20 + A 1 1 • EE01 +
        (A 0 0 - A 1 1) • EE02 := by
  decide

end Work.Hering.GL32
