import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.AffCoord
import Submission.Work.SG.intMat_lattice
import Submission.Work.SG.sgSet_basic
import Submission.Work.SG.matOf_affCoord

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# conj_sgSet_integral — affine conjugacies of normal forms are integral (medium, ~400–800 lines)

**Claim.** If `φ (sgSet P τ) φ⁻¹ = sgSet P' τ'` then `φ x = U x + s` with `U ∈ GL₃(ℤ)`,
`det φ.linear = det U`, and `IntEquiv P τ P' τ' U s`.

**Sketch.** The translations in `sgSet P τ` are exactly `x ↦ x + n`, `n ∈ ℤ³`. (`A = 1` forces
linear part `1`, and `τ 1 ∈ ℤ³` by the cocycle identity at `(1,1)`. Conversely an element with
linear part `1` has `A = 1` because `A ↦ toLin' A` is injective.) Conjugation maps the
translation by `n` to the translation by `L n`, where `L = φ.linear`. So `L ℤ³ ⊆ ℤ³`, and by
symmetry (apply the same to `φ⁻¹`) `L⁻¹ ℤ³ ⊆ ℤ³`. Let `U` = the integer matrix of `L` in the
standard basis (`LinearMap.toMatrix'`). Then `U` is unimodular and `det L = det U`. Set
`s := φ 0`. Unfold `φ (A, τ A + n) φ⁻¹ = (U A U⁻¹, U(τ A + n) + s − U A U⁻¹ s)`. Matching the
two sets gives both clauses of `IntEquiv` (the `n` absorbs `U n ∈ ℤ³`).

**Pitfalls.** `U⁻¹` is `Matrix.inv` over `ℤ` (`Ring.inverse det • adjugate`). Use
`Matrix.mul_nonsing_inv` with `IsUnit U.det`. Casting `(U⁻¹).map Int.cast = (U.map Int.cast)⁻¹`
needs `Matrix.map_inv`/`RingHom.map_inv`-style lemmas, or prove it by uniqueness of inverses.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix

noncomputable section

/-! ### Elementary consequences of the coordinate model -/

/-- Conjunct 8 of `matOf_affCoord`: the coordinate representation `x ↦ M *ᵥ x.ofLp + v` of an
affine map determines `M` and `v`. -/
private theorem eq_of_apply_formula {g : AffineGroup 3} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {v : Fin 3 → ℝ} (h : ∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec M x.ofLp + v)) :
    matOf g = M ∧ (g 0).ofLp = v :=
  (matOf_affCoord).2.2.2.2.2.2.2 g M v h

/-- `matOf φ` applied to `(φ⁻¹ z).ofLp` recovers `z.ofLp`. -/
theorem matOf_symm_mulVec (φ : AffineGroup 3) (z : E 3) :
    Matrix.mulVec (matOf φ) ((φ⁻¹) z).ofLp + (φ 0).ofLp = z.ofLp := by
  have h1 : φ (φ⁻¹ z) = z := AffineEquiv.apply_symm_apply φ z
  rw [(matOf_affCoord).1 φ] at h1
  exact congrArg WithLp.ofLp h1

/-- `(φ⁻¹ z).ofLp` in terms of the matrix of `φ⁻¹`. -/
theorem ofLp_symm_apply (φ : AffineGroup 3) (z : E 3) :
    ((φ⁻¹) z).ofLp = Matrix.mulVec (matOf φ⁻¹) (z.ofLp - (φ 0).ofLp) := by
  have hkey : Matrix.mulVec (matOf φ) ((φ⁻¹) z).ofLp = z.ofLp - (φ 0).ofLp := by
    rw [← matOf_symm_mulVec φ z]; abel
  have hcomp : matOf φ⁻¹ * matOf φ = 1 := by
    rw [← (matOf_affCoord).2.2.1, inv_mul_cancel, (matOf_affCoord).2.2.2.1]
  calc ((φ⁻¹) z).ofLp
      = Matrix.mulVec (matOf φ⁻¹ * matOf φ) ((φ⁻¹) z).ofLp := by
        rw [hcomp, Matrix.one_mulVec]
    _ = Matrix.mulVec (matOf φ⁻¹) (Matrix.mulVec (matOf φ) ((φ⁻¹) z).ofLp) :=
        (Matrix.mulVec_mulVec ((φ⁻¹) z).ofLp (matOf φ⁻¹) (matOf φ)).symm
    _ = Matrix.mulVec (matOf φ⁻¹) (z.ofLp - (φ 0).ofLp) := by rw [hkey]

/-- Conjugation of a matrix-affine map: if `g x = B x + v` then
`(φ g φ⁻¹) x = (Mφ B Mφ⁻¹) x + (Mφ v + φ 0 - (Mφ B Mφ⁻¹) φ 0)`. -/
theorem conj_apply {φ g : AffineGroup 3} {B : IMat} {v : Fin 3 → ℝ}
    (hg : ∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp + v)) (z : E 3) :
    (φ * g * φ⁻¹) z = WithLp.toLp 2
      (Matrix.mulVec (matOf φ * matR B * matOf φ⁻¹) z.ofLp +
        (Matrix.mulVec (matOf φ) v + (φ 0).ofLp -
          Matrix.mulVec (matOf φ * matR B * matOf φ⁻¹) (φ 0).ofLp)) := by
  have hgz : g (φ⁻¹ z) =
      WithLp.toLp 2 (Matrix.mulVec (matR B) (Matrix.mulVec (matOf φ⁻¹) (z.ofLp - (φ 0).ofLp)) + v) := by
    rw [hg, ofLp_symm_apply]
  have h1 : (φ * g * φ⁻¹) z = φ (g (φ⁻¹ z)) := rfl
  rw [h1, hgz, (matOf_affCoord).1 φ]
  have hkey : Matrix.mulVec (matOf φ)
        (Matrix.mulVec (matR B) (Matrix.mulVec (matOf φ⁻¹) (z.ofLp - (φ 0).ofLp)) + v) + (φ 0).ofLp
      = Matrix.mulVec (matOf φ * matR B * matOf φ⁻¹) z.ofLp +
        (Matrix.mulVec (matOf φ) v + (φ 0).ofLp -
          Matrix.mulVec (matOf φ * matR B * matOf φ⁻¹) (φ 0).ofLp) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel
  rw [hkey]

/-! ### The structural description of `sgSet` -/

/-- An element of `sgSet P τ` is `x ↦ A x + τ A + n` with `A ∈ P`, `n ∈ ℤ³`. -/
theorem sgSet_elim {P : Set IMat} {τ : IMat → Fin 3 → ℝ} {g : AffineGroup 3}
    (hg : g ∈ sgSet P τ) :
    ∃ A ∈ P, ∃ n : Fin 3 → ℤ, matOf g = matR A ∧ (g 0).ofLp = τ A + intVec n := by
  obtain ⟨A, hA, n, hform⟩ := hg
  have hform' : ∀ x : E 3, g x =
      WithLp.toLp 2 (Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) x.ofLp + (τ A + intVec n)) := by
    intro x
    rw [hform x, add_assoc]
  have h := eq_of_apply_formula hform'
  refine ⟨A, hA, n, ?_⟩
  exact ⟨h.1.trans (matR_eq_mapCast A).symm, h.2⟩

/-- Conversely, `x ↦ A x + τ A + n` belongs to `sgSet P τ`. -/
theorem sgSet_intro {P : Set IMat} {τ : IMat → Fin 3 → ℝ} {g : AffineGroup 3} {A : IMat}
    (hA : A ∈ P) (n : Fin 3 → ℤ) (hM : matOf g = matR A) (hv : (g 0).ofLp = τ A + intVec n) :
    g ∈ sgSet P τ := by
  refine ⟨A, hA, n, fun x => ?_⟩
  rw [(matOf_affCoord).1 g x, hM, matR_eq_mapCast, hv, add_assoc]

/-! ### An affine conjugacy of normal forms preserves the standard lattice -/

/-- If `φ` conjugates `sgSet P τ` to `sgSet P' τ'`, then `matOf φ` maps every integer vector to
an integer vector. -/
theorem conj_maps_int {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ}
    (hP : IsIntPointGroup P) (hτ : IsIntCocycle P τ)
    (hP' : IsIntPointGroup P') (hτ' : IsIntCocycle P' τ')
    {φ : AffineGroup 3} (h : conjSet φ (sgSet P τ) = sgSet P' τ') :
    ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ, Matrix.mulVec (matOf φ) (intVec n) = intVec k := by
  intro n
  obtain ⟨g, hg, hgform⟩ := (sgSet_basic).2.1 P τ hP hτ n
  have hψmem : φ * g * φ⁻¹ ∈ sgSet P' τ' := by
    rw [← h]; exact ⟨g, hg, rfl⟩
  have hform : ∀ z : E 3,
      (φ * g * φ⁻¹) z = WithLp.toLp 2 (z.ofLp + Matrix.mulVec (matOf φ) (intVec n)) := by
    intro z
    have h1 : (φ * g * φ⁻¹) z = φ (g (φ⁻¹ z)) := rfl
    rw [h1, hgform, (matOf_affCoord).1 φ, WithLp.ofLp_add, Matrix.mulVec_add]
    have hkey : Matrix.mulVec (matOf φ) ((φ⁻¹) z).ofLp +
          Matrix.mulVec (matOf φ) (intVec n) + (φ 0).ofLp
        = z.ofLp + Matrix.mulVec (matOf φ) (intVec n) := by
      rw [← matOf_symm_mulVec φ z]; abel
    rw [hkey]
  have hform' : ∀ z : E 3, (φ * g * φ⁻¹) z =
      WithLp.toLp 2 (Matrix.mulVec (1 : Matrix (Fin 3) (Fin 3) ℝ) z.ofLp +
        Matrix.mulVec (matOf φ) (intVec n)) := by
    intro z; rw [hform z, Matrix.one_mulVec]
  have hmatψ : matOf (φ * g * φ⁻¹) = 1 := (eq_of_apply_formula hform').1
  have hψ0 : ((φ * g * φ⁻¹) 0).ofLp = Matrix.mulVec (matOf φ) (intVec n) :=
    (eq_of_apply_formula hform').2
  obtain ⟨A', hA', n'', hmatA', hvA'⟩ := sgSet_elim hψmem
  have hA'1 : A' = 1 := by
    apply matR_injective
    rw [← hmatA', hmatψ, matR_one]
  obtain ⟨m', hm'⟩ := (sgSet_basic).1 P' τ' hτ' hP'.2.1
  refine ⟨m' + n'', ?_⟩
  have hthis : Matrix.mulVec (matOf φ) (intVec n) = τ' 1 + intVec n'' := by
    rw [← hψ0, hvA', hA'1]
  rw [hthis, hm', ← intVec_add]

/-! ### The main theorem -/

/-- An affine conjugacy between two lattice-normalised space groups is integral:
`φ x = U x + s` with `U ∈ GL₃(ℤ)`, and it induces `IntEquiv`. -/
theorem conj_sgSet_integral {P P' : Set IMat} {τ τ' : IMat → Fin 3 → ℝ}
    (hP : IsIntPointGroup P) (hτ : IsIntCocycle P τ)
    (hP' : IsIntPointGroup P') (hτ' : IsIntCocycle P' τ')
    {φ : AffineGroup 3} (h : conjSet φ (sgSet P τ) = sgSet P' τ') :
    ∃ U : IMat, IsUnit U.det ∧ (φ.linear.det : ℝ) = (U.det : ℝ) ∧ ∃ s : Fin 3 → ℝ,
      (∀ x : E 3, φ x = WithLp.toLp 2 ((U.map (Int.cast : ℤ → ℝ)).mulVec x.ofLp + s)) ∧
        IntEquiv P τ P' τ' U s := by
  have hMφψ : matOf φ * matOf φ⁻¹ = 1 := by
    rw [← (matOf_affCoord).2.2.1, mul_inv_cancel, (matOf_affCoord).2.2.2.1]
  have hMψφ : matOf φ⁻¹ * matOf φ = 1 := by
    rw [← (matOf_affCoord).2.2.1, inv_mul_cancel, (matOf_affCoord).2.2.2.1]
  have hintφ : ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ,
      Matrix.mulVec (matOf φ) (intVec n) = intVec k := conj_maps_int hP hτ hP' hτ' h
  have hintψ : ∀ n : Fin 3 → ℤ, ∃ k : Fin 3 → ℤ,
      Matrix.mulVec (matOf φ⁻¹) (intVec n) = intVec k := by
    have h' : conjSet φ⁻¹ (sgSet P' τ') = sgSet P τ := by rw [← h, (sgSet_basic).2.2.1]
    exact conj_maps_int hP' hτ' hP hτ h'
  obtain ⟨U, V, hMU, hMV, hUV, hVU⟩ := intMat_lattice hMφψ hMψφ hintφ hintψ
  have hUdet : IsUnit U.det := Matrix.isUnit_det_of_right_inverse hUV
  have hUinv : U⁻¹ = V := Matrix.inv_eq_right_inv hUV
  -- the matrix of the conjugate of any `B ∈ P` element
  have hmatB : ∀ {B : IMat} {v : Fin 3 → ℝ} {g : AffineGroup 3},
      (∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp + v)) →
      matOf φ * matR B * matOf φ⁻¹ = matR (U * B * U⁻¹) := by
    intro B v g hg
    rw [hMU, hMV, ← matR_mul, ← matR_mul, hUinv]
  have hmat_of_conj : ∀ {B : IMat} {v : Fin 3 → ℝ} {g : AffineGroup 3},
      (∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp + v)) →
      matOf (φ * g * φ⁻¹) = matR (U * B * U⁻¹) := by
    intro B v g hg
    rw [(eq_of_apply_formula (fun z => conj_apply (φ := φ) hg z)).1, hmatB hg]
  have hconj_trans : ∀ {B : IMat} {v : Fin 3 → ℝ} {g : AffineGroup 3},
      (∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp + v)) →
      ((φ * g * φ⁻¹) 0).ofLp =
        Matrix.mulVec (matOf φ) v + (φ 0).ofLp -
          Matrix.mulVec (matOf φ * matR B * matOf φ⁻¹) (φ 0).ofLp := by
    intro B v g hg
    exact (eq_of_apply_formula (fun z => conj_apply hg z)).2
  refine ⟨U, hUdet, ?_, (φ 0).ofLp, ?_, ?_⟩
  · rw [← (matOf_affCoord).2.2.2.2.1 φ, hMU, matR_eq_mapCast U]
    exact (Int.cast_det U).symm
  · intro x
    rw [(matOf_affCoord).1 φ, hMU, matR_eq_mapCast]
  · constructor
    · intro A
      constructor
      · -- `A ∈ P'` is a conjugate of an element of `P`
        intro hA
        have hAunit : IsUnit A.det := hP'.2.2.2 A hA
        have hψmem : affOfInt A hAunit (τ' A + intVec 0) ∈ sgSet P' τ' := by
          refine sgSet_intro hA 0 ?_ ?_
          · exact (matOf_affCoord).2.2.2.2.2.2.1 (matR A) (isUnit_matR_det hAunit) (τ' A + intVec 0)
          · rw [affOfInt_apply_zero]
        have hgmem : φ⁻¹ * affOfInt A hAunit (τ' A + intVec 0) * φ ∈ sgSet P τ := by
          have h' : conjSet φ⁻¹ (sgSet P' τ') = sgSet P τ := by rw [← h, (sgSet_basic).2.2.1]
          rw [← h']
          exact ⟨_, hψmem, rfl⟩
        obtain ⟨B, hB, n₀, hmatB, hvB⟩ := sgSet_elim hgmem
        have hform : ∀ z : E 3,
            (φ⁻¹ * affOfInt A hAunit (τ' A + intVec 0) * φ) z =
              WithLp.toLp 2 (Matrix.mulVec (matOf φ⁻¹ * matR A * matOf φ) z.ofLp +
                (Matrix.mulVec (matOf φ⁻¹) (τ' A + intVec 0) + (φ⁻¹ 0).ofLp -
                  Matrix.mulVec (matOf φ⁻¹ * matR A * matOf φ) (φ⁻¹ 0).ofLp)) := by
          intro z
          have := conj_apply (φ := φ⁻¹) (g := affOfInt A hAunit (τ' A + intVec 0))
            (B := A) (v := τ' A + intVec 0)
            (fun x => affOfInt_apply A hAunit (τ' A + intVec 0) x) z
          rwa [inv_inv] at this
        have hmat_conj2 : matOf (φ⁻¹ * affOfInt A hAunit (τ' A + intVec 0) * φ) =
            matR (V * A * U) := by
          have h1 := (eq_of_apply_formula hform).1
          rw [h1, hMV, hMU, matR_mul, matR_mul]
        have hBA : B = V * A * U := by
          apply matR_injective
          rw [← hmatB, hmat_conj2]
        refine ⟨B, hB, ?_⟩
        rw [hBA]
        have : U * (V * A * U) * U⁻¹ = A := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one, ← Matrix.mul_assoc, hUV,
            Matrix.one_mul]
        exact this.symm
      · -- `U B U⁻¹ ∈ P'` for `B ∈ P`
        rintro ⟨B, hB, rfl⟩
        have hBunit : IsUnit B.det := hP.2.2.2 B hB
        have hgform : ∀ x : E 3, affOfInt B hBunit (τ B + intVec 0) x =
            WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp + (τ B + intVec 0)) :=
          fun x => affOfInt_apply B hBunit (τ B + intVec 0) x
        have hgmem : affOfInt B hBunit (τ B + intVec 0) ∈ sgSet P τ := by
          refine sgSet_intro hB 0 ?_ ?_
          · exact (matOf_affCoord).2.2.2.2.2.2.1 (matR B) (isUnit_matR_det hBunit) (τ B + intVec 0)
          · rw [affOfInt_apply_zero]
        have hψmem : φ * affOfInt B hBunit (τ B + intVec 0) * φ⁻¹ ∈ sgSet P' τ' := by
          rw [← h]
          exact ⟨_, hgmem, rfl⟩
        obtain ⟨A', hA', n', hmatA', hvA'⟩ := sgSet_elim hψmem
        have hsub : matR A' = matR (U * B * U⁻¹) := by
          rw [← hmatA', hmat_of_conj hgform]
        have hA'eq : A' = U * B * U⁻¹ := matR_injective hsub
        rwa [← hA'eq]
    · -- cocycle compatibility
      intro B hB
      have hBunit : IsUnit B.det := hP.2.2.2 B hB
      set g := affOfInt B hBunit (τ B + intVec 0) with hgdef
      have hgform : ∀ x : E 3, g x = WithLp.toLp 2 (Matrix.mulVec (matR B) x.ofLp +
          (τ B + intVec 0)) := fun x => affOfInt_apply B hBunit (τ B + intVec 0) x
      have hgmem : g ∈ sgSet P τ := by
        refine sgSet_intro hB 0 ?_ ?_
        · exact (matOf_affCoord).2.2.2.2.2.2.1 (matR B) (isUnit_matR_det hBunit) (τ B + intVec 0)
        · rw [hgdef, affOfInt_apply_zero]
      have hψmem : φ * g * φ⁻¹ ∈ sgSet P' τ' := by
        rw [← h]; exact ⟨g, hgmem, rfl⟩
      obtain ⟨A', hA', n', hmatA', hvA'⟩ := sgSet_elim hψmem
      have hsub : matR A' = matR (U * B * U⁻¹) := by
        rw [← hmatA', hmat_of_conj hgform]
      have hA'eq : A' = U * B * U⁻¹ := matR_injective hsub
      have hψ0 := hconj_trans hgform
      refine ⟨-n', ?_⟩
      have hkey : τ' A' = Matrix.mulVec (matR U) (τ B) + (φ 0).ofLp -
          Matrix.mulVec (matR A') (φ 0).ofLp - intVec n' := by
        have hv : τ' A' = ((φ * g * φ⁻¹) 0).ofLp - intVec n' := by
          rw [hvA']; abel
        rw [hv, hψ0]
        have hv' : Matrix.mulVec (matOf φ) (τ B + intVec 0) = Matrix.mulVec (matR U) (τ B) := by
          rw [hMU, Matrix.mulVec_add, intVec_zero, Matrix.mulVec_zero, add_zero]
        rw [hv', hmatB hgform, hA'eq]
      rw [intVec_neg, ← matR_eq_mapCast U, ← matR_eq_mapCast (U * B * U⁻¹), ← hA'eq, hkey]
      abel

end

end Work.SG
