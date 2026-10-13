import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Jac

set_option autoImplicit false
noncomputable section

namespace Work.WilE9G.Lagrange

open Classical WilkiesDesign WilkiesDesign.E Work.WilE9G

/-! ## Elementary preliminary lemmas

The two lemmas below are the linear-algebra input of the argument: (i) a real matrix with as many
rows as its rank has linearly independent rows, so left multiplication by it is injective;
(ii) evaluating `∑ i, c i • proj i` on a vector. -/

/-- A real matrix with `j` rows and rank `j` has linearly independent rows. -/
private lemma linearIndependent_rows_of_rank_eq_card {j N : ℕ} (A : Matrix (Fin j) (Fin N) ℝ)
    (h : A.rank = j) : LinearIndependent ℝ A.row := by
  refine linearIndependent_iff_card_eq_finrank_span.mpr ?_
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.row)) = j :=
    (Matrix.rank_eq_finrank_span_row A).symm.trans h
  rw [Fintype.card_fin]
  exact h1.symm

/-- Evaluating the continuous linear map `∑ i, f i • proj i` on a vector. -/
private lemma sum_smul_proj_apply {k : ℕ} (f v : Fin k → ℝ) :
    (∑ i, f i • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) v = ∑ i, f i * v i := by
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The base projection of a vector, read off at a `castAdd` index. -/
private lemma projBase_castAdd {n k : ℕ} (v : Fin (n + k) → ℝ) (i : Fin n) :
    projBase (Nat.le_add_right n k) v i = v (Fin.castAdd k i) := rfl

/-! ## The main theorem -/

/-- **A non-zero left kernel of the fibre block kills base-submersivity.**

If `ν ≠ 0` is a non-zero vector of coefficients such that
`∑ a, ν a * ∂_{n+l} h_a (z) = 0` for every fibre coordinate `l` (i.e. `ν` annihilates the fibre
block of the Jacobian of the equations at `z`), then the projection `π_n` cannot map the tangent
space `ker dh(z)` of the `Good` stratum `S` onto `ℝ^n` at `z`: base-submersivity would force
`ν ᵥ* J = 0`, contradicting the fact that the `j × N` Jacobian has rank `j` (`S.Good`), i.e. that
its `j` rows are linearly independent. -/
theorem not_isBaseSubmersiveAt_of_fibre_kernel {n m : ℕ}
    (S : Work.WilE9G.AmbStratum (n + (1 + m))) (hS : S.Good)
    (z : Fin (n + (1 + m)) → ℝ) (hz : z ∈ S.X.set) (ν : Fin S.j → ℝ)
    (hν : (∑ a, (ν a) ^ 2) ≠ 0)
    (hker : ∀ l : Fin (1 + m),
      ∑ a, ν a * WilkiesDesign.E.eaEval S.X.c
        (WilkiesDesign.E.eaD S.X.c (Fin.natAdd n l) (S.h a)) z = 0) :
    ¬ Work.WilE9G.AmbStratum.IsBaseSubmersiveAt S (Nat.le_add_right n (1 + m)) z := by
  classical
  -- The Jacobian of the equations of `S` at `z`.
  let A : Matrix (Fin S.j) (Fin (n + (1 + m))) ℝ :=
    Matrix.of fun a l => eaEval S.X.c (eaD S.X.c l (S.h a)) z
  -- `ν` is non-zero.
  have hν' : ν ≠ 0 := fun h => hν (by simp [h])
  -- `Good` gives that the Jacobian has rank `S.j`, hence independent rows.
  have hrank : A.rank = S.j := AmbStratum_rank S hS hz
  have hinj : Function.Injective (fun v : Fin S.j → ℝ => Matrix.vecMul v A) :=
    Matrix.vecMul_injective_iff.mpr (linearIndependent_rows_of_rank_eq_card A hrank)
  intro hsub
  -- `ν` annihilates the fibre block of the Jacobian, by hypothesis.
  have hright : ∀ l : Fin (1 + m), Matrix.vecMul ν A (Fin.natAdd n l) = 0 := by
    intro l
    rw [Matrix.vecMul_apply_eq_sum]
    exact hker l
  -- Base-submersivity forces `ν` to annihilate the base block as well.
  have hleft : ∀ i : Fin n, Matrix.vecMul ν A (Fin.castAdd (1 + m) i) = 0 := by
    intro i
    -- A tangent vector whose first `n` coordinates are the `i`-th standard basis vector.
    obtain ⟨v, hvbase, hvker⟩ := hsub (fun b : Fin n => if b = i then (1 : ℝ) else 0)
    -- Its base coordinates.
    have hvb : ∀ b : Fin n, v (Fin.castAdd (1 + m) b) = (if b = i then (1 : ℝ) else 0) := by
      intro b
      have h := congrFun hvbase b
      simpa [projBase, Fin.castAdd] using h
    -- The Fréchet derivative of each equation is its symbolic derivative.
    have hfac : ∀ a : Fin S.j, (A.mulVec v) a =
        (fderiv ℝ (fun z' : Fin (n + (1 + m)) → ℝ => eaEval S.X.c (S.h a) z') z) v := by
      intro a
      rw [(Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z).fderiv, sum_smul_proj_apply]
      exact Matrix.mulVec_apply_eq_sum A v a
    -- So `ν ⬝ (J v) = 0`.
    have h1 : ∑ a : Fin S.j, ν a * (A.mulVec v) a = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hfac a, hvker a, mul_zero]
    -- Reassociate it as a dot product with `ν ᵥ* A`.
    have h2 : (∑ a : Fin S.j, ν a * (A.mulVec v) a)
        = ∑ l : Fin (n + (1 + m)), Matrix.vecMul ν A l * v l := by
      have h := Matrix.dotProduct_mulVec ν A v
      simp only [dotProduct] at h ⊢
      exact h
    -- Split the coordinates into base and fibre ones.
    have h3 : ∑ l : Fin (n + (1 + m)), Matrix.vecMul ν A l * v l
        = Matrix.vecMul ν A (Fin.castAdd (1 + m) i) := by
      rw [Fin.sum_univ_add]
      have hz2 : (∑ l : Fin (1 + m),
          Matrix.vecMul ν A (Fin.natAdd n l) * v (Fin.natAdd n l)) = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [hright l, zero_mul]
      rw [hz2, add_zero]
      have hstep : (∑ b : Fin n,
            Matrix.vecMul ν A (Fin.castAdd (1 + m) b) * v (Fin.castAdd (1 + m) b))
          = ∑ b : Fin n,
            (if b = i then Matrix.vecMul ν A (Fin.castAdd (1 + m) b) else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hvb b]
        by_cases h : b = i
        · rw [if_pos h, mul_one, if_pos h]
        · rw [if_neg h, mul_zero, if_neg h]
      rw [hstep, Finset.sum_ite_eq', if_pos (Finset.mem_univ i)]
    rw [← h3, ← h2]
    exact h1
  -- Hence `ν ᵥ* A = 0`.
  have hνA : Matrix.vecMul ν A = 0 := by
    funext l
    exact Fin.addCases hleft hright l
  -- But `A.vecMul` is injective and `ν ≠ 0`: contradiction.
  refine hν' (hinj ?_)
  show Matrix.vecMul ν A = Matrix.vecMul 0 A
  rw [hνA]
  simp

end Work.WilE9G.Lagrange
