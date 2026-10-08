import Mathlib
import Submission.Work.L2F.Props.CentralizerTorusDefs
import Submission.Work.L2F.Props.traceless_mul_add_mul_trace
import Submission.Work.L2F.Props.exists_rhoSL_eq
import Submission.Work.L2F.Semisimple.primeOrderCentralizer

-- `hns` occurs in the hypothesis list of the statement (fixed by the requester) but is not needed
-- for the argument below, which only uses `h2` and `hd`.
set_option linter.unusedVariables false

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-- The centralizer in `M₂(F)` of a traceless `2 × 2` matrix `W` with `W * W = D • 1`, `D ≠ 0`,
is the `F`-span of `1` and `W`: every `Y` commuting with `W` is `a • 1 + b • W`.

(Writing `Z = Y - (tr Y / 2) • 1` for the traceless part of `Y`, the identity
`Z * W + W * Z = (Z * W).trace • 1` of `traceless_mul_add_mul_trace`, together with
`Z * W = W * Z`, gives `2 • (Z * W) = (Z * W).trace • 1`; multiplying by `W` on the right and
using `W * W = D • 1` yields `2 * D • Z = (Z * W).trace • W`, whence `Z ∈ span {W}`.) -/
theorem w_centralizer_span (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (D : F)
    (W Y : Matrix (Fin 2) (Fin 2) F)
    (hW : W * W = D • 1) (hD : D ≠ 0) (hWtr : W.trace = 0) (hc : Y * W = W * Y) :
    ∃ a b : F, Y = a • 1 + b • W := by
  set Z : Matrix (Fin 2) (Fin 2) F := Y - (Y.trace / 2) • 1 with hZdef
  have hZtr : Z.trace = 0 := by
    rw [hZdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp only [smul_eq_mul, Nat.cast_ofNat]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ h2).symm
  have hcZ : Z * W = W * Z := by
    rw [hZdef, sub_mul, Matrix.smul_mul, one_mul, mul_sub, Matrix.mul_smul, mul_one, hc]
  have hYdecomp : Y = (Y.trace / 2) • 1 + Z := by rw [hZdef]; abel
  have h1 : (2 : F) • (Z * W) = (Z * W).trace • 1 := by
    have h := traceless_mul_add_mul_trace F Z W hZtr hWtr
    rw [← hcZ, ← two_smul F (Z * W)] at h
    exact h
  have h2' : Z * W = ((Z * W).trace / 2) • 1 := by
    have h := congrArg (fun x : Matrix (Fin 2) (Fin 2) F => (2 : F)⁻¹ • x) h1
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul, smul_smul] at h
    simpa [div_eq_inv_mul] using h
  have h3 : Z * W * W = ((Z * W).trace / 2) • W := by
    conv_lhs => rw [h2']
    rw [Matrix.smul_mul, one_mul]
  have h4 : D • Z = ((Z * W).trace / 2) • W := by
    rw [← h3, mul_assoc, hW, Matrix.mul_smul, mul_one]
  have h5 : Z = (D⁻¹ * ((Z * W).trace / 2)) • W := by
    have h := congrArg (fun x : Matrix (Fin 2) (Fin 2) F => D⁻¹ • x) h4
    rw [smul_smul, inv_mul_cancel₀ hD, one_smul, smul_smul] at h
    exact h
  refine ⟨Y.trace / 2, D⁻¹ * ((Z * W).trace / 2), ?_⟩
  conv_lhs => rw [hYdecomp, h5]

theorem glCent_algSpan (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (g : GL (Fin 2) F)
    (hd : glD F g ≠ 0) (hns : ∀ c : F, glW F g ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (h : GL (Fin 2) F) :
    h ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)) ↔
      ∃ a b : F, (h : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • glW F g := by
  constructor
  · -- a matrix commuting with `g` commutes with the traceless part `glW F g`
    intro hmem
    have hgh : h * g = g * h := Subgroup.mem_centralizer_singleton_iff.mp hmem
    have hmat : (h : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
        = (g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) := by
      have hh := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hgh
      simpa [Matrix.GeneralLinearGroup.coe_mul] using hh
    have hcW : (h : Matrix (Fin 2) (Fin 2) F) * glW F g
        = glW F g * (h : Matrix (Fin 2) (Fin 2) F) := by
      have hcomm : Commute (h : Matrix (Fin 2) (Fin 2) F) (g : Matrix (Fin 2) (Fin 2) F) := hmat
      have hW : glW F g = (g : Matrix (Fin 2) (Fin 2) F)
          - (((g : Matrix (Fin 2) (Fin 2) F).trace / 2) • 1) := by
        rw [glW_apply]
      rw [hW]
      exact hcomm.sub_right ((Commute.one_right (h : Matrix (Fin 2) (Fin 2) F)).smul_right _)
    exact w_centralizer_span F h2 (glD F g) (glW F g) (h : Matrix (Fin 2) (Fin 2) F)
      (glW_mul_self F h2 g) hd (glW_trace F h2 g) hcW
  · -- conversely `a • 1 + b • glW F g` commutes with `(tr g / 2) • 1 + glW F g = g`
    rintro ⟨a, b, hab⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hab]
    exact smul_one_add_smul_glW_comm_g F g a b

end Work.L2F.Props
