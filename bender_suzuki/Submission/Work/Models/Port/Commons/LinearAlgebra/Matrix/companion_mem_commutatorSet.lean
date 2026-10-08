import Mathlib
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.exists_isSimilar_companion

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option backward.isDefEq.respectTransparency false

namespace Commons.LinearAlgebra.Matrix

open _root_.Matrix
open scoped Matrix MatrixGroups commutatorElement

/-- In a finite field with at least `4` elements there is a nonzero element `μ` with `μ ^ 2 ≠ 1`. -/
lemma exists_ne_zero_sq_ne_one {F : Type*} [Field F] [Fintype F] (hF : 4 ≤ Fintype.card F) :
    ∃ μ : F, μ ≠ 0 ∧ μ ^ 2 ≠ 1 := by
  classical
  have hcard : ({0, 1, -1} : Finset F).card ≤ 3 := by
    rw [show ({0, 1, -1} : Finset F) = insert 0 (insert 1 ({-1} : Finset F)) from rfl]
    calc (insert 0 (insert 1 ({-1} : Finset F)) : Finset F).card
        ≤ (insert 1 ({-1} : Finset F)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({-1} : Finset F).card + 1) + 1 := by
            gcongr
            exact Finset.card_insert_le _ _
      _ = 3 := by simp
  have hlt : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨μ, -, hμ⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hμ
  refine ⟨μ, hμ.1, ?_⟩
  intro h
  rcases sq_eq_one_iff.mp h with h1 | h1
  · exact hμ.2.1 h1
  · exact hμ.2.2 h1

/-- **Every companion matrix `![![0, -1], ![1, t]]` in `SL(2, F)` is a commutator**, for `F` a finite
field with at least `4` elements.

Explicitly, choosing `μ ≠ 0` with `μ ^ 2 ≠ 1` and setting `κ = (2 - t) / (μ - μ⁻¹) ^ 2`, the matrices
`X = diag(μ, μ⁻¹)` and `Y = !![1 + κ, 1; κ, 1]` lie in `SL(2, F)` and
`⁅X, Y⁆ = !![1 + κ - μ ^ 2 κ, (1 + κ)(μ ^ 2 - 1); κ((μ⁻¹) ^ 2 - 1), 1 + κ - (μ⁻¹) ^ 2 κ]`
is a non-scalar element of trace `t`; by the rational canonical form it is `GL₂`-conjugate to the
companion matrix, and conjugation by `GL₂` preserves the commutator set of `SL(2, F)`. -/
theorem companion_mem_commutatorSet {F : Type*} [Field F] [Fintype F] (hF : 4 ≤ Fintype.card F) (t : F) :
    (⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩ : Matrix.SpecialLinearGroup (Fin 2) F)
      ∈ commutatorSet (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨μ, hμ0, hμ2⟩ := exists_ne_zero_sq_ne_one hF
  have hΛ : μ - μ⁻¹ ≠ 0 := by
    intro hh
    apply hμ2
    have h1 : μ = μ⁻¹ := sub_eq_zero.mp hh
    have h2 : μ * μ = μ * μ⁻¹ := congrArg (fun x => μ * x) h1
    rw [mul_inv_cancel₀ hμ0] at h2
    simpa [pow_two] using h2
  have hΛ2 : (μ - μ⁻¹)^2 ≠ 0 := pow_ne_zero 2 hΛ
  set κ : F := (2 - t) / (μ - μ⁻¹)^2 with hκ
  have hκΛ : κ * (μ - μ⁻¹)^2 = 2 - t := by
    rw [hκ]; field_simp
  have hμinv2 : (μ⁻¹)^2 ≠ 1 := by
    intro hh
    apply hμ2
    calc μ^2 = μ^2 * (μ⁻¹)^2 := by rw [hh, mul_one]
      _ = (μ * μ⁻¹)^2 := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hμ0, one_pow]
  set X : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![μ, 0; 0, μ⁻¹], by rw [Matrix.det_fin_two]; simp [mul_inv_cancel₀ hμ0]⟩ with hXdef
  set Y : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1 + κ, 1; κ, 1], by rw [Matrix.det_fin_two]; simp⟩ with hYdef
  have hAmat : (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).val
      = !![1 + κ - μ^2 * κ, (1 + κ) * (μ^2 - 1);
          κ * ((μ⁻¹)^2 - 1), 1 + κ - (μ⁻¹)^2 * κ] := by
    have hX : (X : Matrix (Fin 2) (Fin 2) F) = !![μ, 0; 0, μ⁻¹] := rfl
    have hY : (Y : Matrix (Fin 2) (Fin 2) F) = !![1 + κ, 1; κ, 1] := rfl
    rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, hX, hY,
      Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals (field_simp; ring)
  have htrace : (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).val.trace = t := by
    rw [hAmat, Matrix.trace_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    have hshift : μ ^ 2 + (μ⁻¹)^2 - 2 = (μ - μ⁻¹)^2 := by
      rw [sub_sq, show (2 : F) * μ * μ⁻¹ = 2 by rw [mul_assoc, mul_inv_cancel₀ hμ0, mul_one]]
      ring
    have hL : (1 + κ - μ^2 * κ) + (1 + κ - (μ⁻¹)^2 * κ) = 2 - κ * (μ - μ⁻¹)^2 := by
      rw [← hshift]; ring
    rw [hL, hκΛ]; ring
  have hnc : ∀ c : F,
      (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).val ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro c hc
    have h01 : (1 + κ) * (μ^2 - 1) = 0 := by
      have h := congrFun (congrFun hc 0) 1
      rw [hAmat] at h
      simpa [Matrix.smul_apply, Matrix.one_apply] using h
    have h10 : κ * ((μ⁻¹)^2 - 1) = 0 := by
      have h := congrFun (congrFun hc 1) 0
      rw [hAmat] at h
      simpa [Matrix.smul_apply, Matrix.one_apply] using h
    have h1k : 1 + κ = 0 := (mul_eq_zero.mp h01).resolve_right (sub_ne_zero.mpr hμ2)
    have hk0 : κ = 0 := (mul_eq_zero.mp h10).resolve_right (sub_ne_zero.mpr hμinv2)
    rw [hk0, add_zero] at h1k
    exact one_ne_zero h1k
  obtain ⟨P, hP⟩ :=
    exists_isSimilar_companion (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).val
      (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).2 hnc
  have hPm : (P : Matrix (Fin 2) (Fin 2) F)
      * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hPmin : ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * (P : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  let φ : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
  { toFun := fun Z => ⟨(P : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F)
        * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
      by
        rw [Matrix.det_mul, Matrix.det_mul, Z.2, mul_one]
        calc (P : Matrix (Fin 2) (Fin 2) F).det
              * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det
            = ((P : Matrix (Fin 2) (Fin 2) F)
                * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det :=
              (Matrix.det_mul _ _).symm
          _ = 1 := by rw [hPm, Matrix.det_one]⟩
    map_one' := by
      apply Subtype.ext
      show (P : Matrix (Fin 2) (Fin 2) F)
          * ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, hPm]
    map_mul' := by
      intro Z W
      apply Subtype.ext
      show (P : Matrix (Fin 2) (Fin 2) F)
          * ((Z * W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((P : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F)
            * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          * ((P : Matrix (Fin 2) (Fin 2) F) * (W : Matrix (Fin 2) (Fin 2) F)
            * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) (P : Matrix (Fin 2) (Fin 2) F)
            ((W : Matrix (Fin 2) (Fin 2) F)
              * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)),
          hPmin, one_mul] }
  have hmem : φ (⁅X, Y⁆) ∈ commutatorSet (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [map_commutatorElement φ]
    exact commutator_mem_commutatorSet (φ X) (φ Y)
  have heq : φ (⁅X, Y⁆)
      = (⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) F)
        * (⁅X, Y⁆ : Matrix.SpecialLinearGroup (Fin 2) F).val
        * ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = !![0, -1; 1, t]
    rw [hP, htrace]
  rw [← heq]
  exact hmem

end Commons.LinearAlgebra.Matrix
