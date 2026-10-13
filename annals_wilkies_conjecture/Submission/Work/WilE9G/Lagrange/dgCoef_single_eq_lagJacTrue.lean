/-
  WilE9G / Lagrange — **`dgCoef_single_eq_lagJacTrue`**.

  The matrix `(dgCoef S Phi p (degenRowInv m r) (single (degenColK n m col) 1))_{r,col}` — the
  derivative of the system `degenH` of the genericity step, tested against the basis vectors
  supported on the reduced coordinates `(yt, ν)` — is exactly the fibre Jacobian `lagJacTrue` of
  the Lagrange system (rows `(L, h, N)`, columns `((y,t), μ, μ₀)`), evaluated at
  `(degenZ p, degenNu p, degenC p)`.

  Concretely, on the three row/column blocks the two sides are

  * `(L_{l'}, yt_{l0})`: `ν₀(∂_{l₀}∂_{l'}Φ + c_{l'} ∂_{l₀}Φ) - ∑_a ν_a ∂_{l₀}∂_{l'}h_a`,
  * `(L_{l'}, μ_a)`: `- ∂_{l'}h_a`, `(L_{l'}, μ₀)`: `∂_{l'}Φ + Φ c_{l'}`,
  * `(h_a, yt_{l0})`: `∂_{l₀}h_a`, the remaining `h`-rows are `0`,
  * the `N`-row: `0` on the `yt`-columns, `2ν_a` on the `μ_a`-columns and `2ν₀` on `μ₀`.

  The proof is a case analysis on the (already split) row and column indices; each case reduces to
  the derivative of `degenPsi`, `dgLam` or `gradZ` at a basis vector, which are the evaluation
  lemmas above.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.degen_kernel_defs

namespace Work.WilE9G.Lagrange

open WilkiesDesign WilkiesDesign.E Work.WilE9G

set_option autoImplicit false

/-! ## The coordinate embeddings are distinct -/

private theorem dZK_ne_dNuK {n m j : ℕ} (i : Fin (n + (1 + m))) (a : Fin (j + 1)) :
    degenZK n m (j := j) i ≠ degenNuK n m (j := j) a := degenZK_ne_degenNuK i a

private theorem dNuK_ne_dZK {n m j : ℕ} (a : Fin (j + 1)) (i : Fin (n + (1 + m))) :
    degenNuK n m (j := j) a ≠ degenZK n m (j := j) i :=
  fun h => degenZK_ne_degenNuK i a h.symm

private theorem dZK_ne_dCK {n m j : ℕ} (i : Fin (n + (1 + m))) (l : Fin (1 + m)) :
    degenZK n m (j := j) i ≠ degenCK n m (j := j) l := degenZK_ne_degenCK i l

private theorem dCK_ne_dZK {n m j : ℕ} (l : Fin (1 + m)) (i : Fin (n + (1 + m))) :
    degenCK n m (j := j) l ≠ degenZK n m (j := j) i :=
  fun h => degenZK_ne_degenCK i l h.symm

private theorem dNuK_ne_dCK {n m j : ℕ} (a : Fin (j + 1)) (l : Fin (1 + m)) :
    degenNuK n m (j := j) a ≠ degenCK n m (j := j) l := degenNuK_ne_degenCK a l

private theorem dCK_ne_dNuK {n m j : ℕ} (l : Fin (1 + m)) (a : Fin (j + 1)) :
    degenCK n m (j := j) l ≠ degenNuK n m (j := j) a :=
  fun h => degenNuK_ne_degenCK a l h.symm

private theorem castAdd1_ne_last {j : ℕ} (a : Fin j) :
    (Fin.castAdd 1 a : Fin (j + 1)) ≠ Fin.last j := by
  intro h; have := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_castAdd] at this; omega

private theorem last_ne_castAdd1 {j : ℕ} (a : Fin j) :
    (Fin.last j : Fin (j + 1)) ≠ Fin.castAdd 1 a := fun h => castAdd1_ne_last a h.symm

/-- The last multiplier index is the only element of `Fin (j+1)` that is not a `Fin.castAdd`. -/
theorem degenNatAdd_one_eq_last {j : ℕ} (u : Fin 1) : (Fin.natAdd j u : Fin (j + 1)) = Fin.last j := by
  have h : u.val = 0 := by omega
  exact Fin.ext (by simp only [Fin.val_natAdd, Fin.val_last]; omega)

/-! ## The derivatives of `degenPsi` at the basis vectors of the reduced coordinates -/

/-- `dgPsi` at the basis vector of the fibre coordinate `(y,t)_{l₀}`, i.e. the column `yt_{l₀}` of
the Lagrange Jacobian in the `L_{l'}`-row. -/
theorem dgCoef_dgPsi_yt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l' l0 : Fin (1 + m)) :
    dgPsi S Phi p l' (Pi.single (degenColK n m (j := S.j) (Fin.castAdd (S.j + 1) l0)) 1)
      = degenNu p (Fin.last S.j) *
          (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l0) (eaD S.X.c (Fin.natAdd n l') Phi)) (degenZ p)
            + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l0) Phi) (degenZ p) * degenC p l')
        - ∑ a : Fin S.j, degenNu p (Fin.castAdd 1 a) * eaEval S.X.c
            (eaD S.X.c (Fin.natAdd n l0) (eaD S.X.c (Fin.natAdd n l') (S.h a))) (degenZ p) := by
  rw [dgPsi]
  simp only [add_apply, sub_apply, smul_apply, sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [degenColK_castAdd]
  simp only [dgA, AVal, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    gradZ_apply_single_zk, Pi.single_apply, dCK_ne_dZK, dNuK_ne_dZK,
    ite_false, mul_zero, add_zero, zero_add]
  ring

/-- `dgPsi` at the basis vector of the multiplier `ν_a`, i.e. the column `μ_a` of the Lagrange
Jacobian in the `L_{l'}`-row. -/
theorem dgCoef_dgPsi_mu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l' : Fin (1 + m)) (a : Fin S.j) :
    dgPsi S Phi p l' (Pi.single (degenColK n m (j := S.j) (Fin.natAdd (1 + m) (Fin.castAdd 1 a))) 1)
      = - eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') (S.h a)) (degenZ p) := by
  rw [dgPsi]
  simp only [add_apply, sub_apply, smul_apply, sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [degenColK_natAdd]
  simp only [dgA, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    gradZ_apply_single_nuk, Pi.single_apply, dCK_ne_dNuK, last_ne_castAdd1,
    degenNuK_injective.eq_iff, Fin.castAdd_inj, ite_false, mul_ite, mul_one, mul_zero,
    add_zero, zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- `dgPsi` at the basis vector of the normalising multiplier `ν₀`, i.e. the column `μ₀` of the
Lagrange Jacobian in the `L_{l'}`-row. -/
theorem dgCoef_dgPsi_mu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (degenDim n m S.j) → ℝ) (l' : Fin (1 + m)) :
    dgPsi S Phi p l' (Pi.single (degenColK n m (j := S.j) (Fin.natAdd (1 + m) (Fin.last S.j))) 1)
      = eaEval S.X.c (eaD S.X.c (Fin.natAdd n l') Phi) (degenZ p)
        + eaEval S.X.c Phi (degenZ p) * degenC p l' := by
  rw [dgPsi]
  simp only [add_apply, sub_apply, smul_apply, sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [degenColK_natAdd]
  simp only [dgA, AVal, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    gradZ_apply_single_nuk, Pi.single_apply, degenNuK_injective.eq_iff, dCK_ne_dNuK,
    castAdd1_ne_last, ite_false, ite_true, mul_one, mul_zero, add_zero, zero_add,
    Finset.sum_const_zero]
  ring

/-! ## The derivatives of the normalisation at the basis vectors of the reduced coordinates -/

/-- `dgLam` vanishes on the fibre-coordinate directions. -/
theorem dgCoef_dgLam_yt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) (l0 : Fin (1 + m)) :
    dgLam p (Pi.single (degenColK n m (j := S.j) (Fin.castAdd (S.j + 1) l0)) 1) = 0 := by
  rw [dgLam]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [degenColK_castAdd]
  simp only [Pi.single_apply, dNuK_ne_dZK, ite_false, mul_zero, Finset.sum_const_zero]

/-- `dgLam` on the multiplier direction `ν_b` is `2 ν_b`. -/
theorem dgCoef_dgLam_mu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) (b : Fin S.j) :
    dgLam p (Pi.single (degenColK n m (j := S.j) (Fin.natAdd (1 + m) (Fin.castAdd 1 b))) 1)
      = 2 * degenNu p (Fin.castAdd 1 b) := by
  rw [dgLam]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [degenColK_natAdd]
  simp only [Pi.single_apply, degenNuK_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `dgLam` on the direction `ν₀` is `2 ν₀`. -/
theorem dgCoef_dgLam_mu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (p : Fin (degenDim n m S.j) → ℝ) :
    dgLam p (Pi.single (degenColK n m (j := S.j) (Fin.natAdd (1 + m) (Fin.last S.j))) 1)
      = 2 * degenNu p (Fin.last S.j) := by
  rw [dgLam]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [degenColK_natAdd]
  simp only [Pi.single_apply, degenNuK_injective.eq_iff, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ## The matrix identity -/

theorem dgCoef_single_eq_lagJacTrue {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ) :
    (Matrix.of fun (r col : Fin ((1 + m) + (S.j + 1))) =>
        Work.WilE9G.Lagrange.dgCoef S Phi p (Work.WilE9G.Lagrange.degenRowInv m (j := S.j) r)
          (Pi.single (Work.WilE9G.Lagrange.degenColK n m (j := S.j) col) 1))
      = Work.WilE9G.Lagrange.lagJacTrue S Phi (Work.WilE9G.Lagrange.degenC p)
          (Work.WilE9G.Lagrange.degenZ p)
          (fun a => Work.WilE9G.Lagrange.degenNu p (Fin.castAdd 1 a))
          (Work.WilE9G.Lagrange.degenNu p (Fin.last S.j)) := by
  -- Work entrywise and split both indices into their block form.
  ext r col
  simp only [Matrix.of_apply]
  revert r
  refine Fin.addCases ?_ ?_
  · -- the `L`-rows
    intro l'
    rw [degenRowInv, Fin.addCases_left]
    rw [dgCoef, Fin.addCases_right, Fin.addCases_right]
    rw [lagJacTrue]
    simp only [Matrix.of_apply]
    revert col
    refine Fin.addCases ?_ ?_
    · -- column `yt_{l₀}`
      intro l0
      rw [dgCoef_dgPsi_yt]
      simp only [Fin.addCases_left]
    · intro s
      revert s
      refine Fin.addCases ?_ ?_
      · -- column `μ_a`
        intro a
        rw [dgCoef_dgPsi_mu]
        simp only [Fin.addCases_left, Fin.addCases_right]
      · -- column `μ₀`
        intro u
        simp only [Fin.addCases_left, Fin.addCases_right]
        rw [degenNatAdd_one_eq_last u, dgCoef_dgPsi_mu0]
  · intro s
    revert s
    refine Fin.addCases ?_ ?_
    · -- the `h_a`-rows
      intro a
      rw [degenRowInv, Fin.addCases_right, Fin.addCases_left]
      rw [dgCoef, Fin.addCases_left]
      rw [lagJacTrue]
      simp only [Matrix.of_apply]
      revert col
      refine Fin.addCases ?_ ?_
      · -- column `yt_{l₀}`
        intro l0
        rw [degenColK_castAdd, gradZ_apply_single_zk]
        simp only [Fin.addCases_left, Fin.addCases_right]
      · intro s'
        revert s'
        refine Fin.addCases ?_ ?_
        · -- column `μ_b`
          intro b
          rw [degenColK_natAdd, gradZ_apply_single_nuk]
          simp only [Fin.addCases_left, Fin.addCases_right]
        · -- column `μ₀`
          intro u
          simp only [Fin.addCases_left, Fin.addCases_right]
          rw [degenNatAdd_one_eq_last u, degenColK_natAdd, gradZ_apply_single_nuk]
    · -- the `N`-row
      intro u
      rw [degenRowInv, Fin.addCases_right, Fin.addCases_right]
      rw [dgCoef, Fin.addCases_right, Fin.addCases_left]
      rw [lagJacTrue]
      simp only [Matrix.of_apply]
      revert col
      refine Fin.addCases ?_ ?_
      · -- column `yt_{l₀}`
        intro l0
        rw [dgCoef_dgLam_yt]
        simp only [Fin.addCases_left, Fin.addCases_right]
      · intro s'
        revert s'
        refine Fin.addCases ?_ ?_
        · -- column `μ_b`
          intro b
          rw [dgCoef_dgLam_mu]
          simp only [Fin.addCases_left, Fin.addCases_right]
        · -- column `μ₀`
          intro u'
          simp only [Fin.addCases_right]
          rw [degenNatAdd_one_eq_last u', dgCoef_dgLam_mu0]

end Work.WilE9G.Lagrange
