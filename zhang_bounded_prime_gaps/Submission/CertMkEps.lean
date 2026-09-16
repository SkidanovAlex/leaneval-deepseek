import Submission.CertJArith
import Submission.CertIArith
import Submission.CertSmooth
import Submission.M4Cert

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000000

open scoped BigOperators Topology
open Filter Finset MeasureTheory

/-!
# The `k = 50` certificate in the `MkEps` form: `M_{50,1/25} > 4`

`Submission/CertJArith.lean` evaluates the two quadratic forms of the certificate,

  `IFuncOrth 50 certFun = certK²·(certqI/certDI)`,
  `Σ_i JFunc 50 i (24/25) certFun = 50·certK²·(certqJ/certDJ)`,

so the certificate's variational quotient is `50·certqJ·certDI/(certqI·certDJ)`, which exceeds
`4` by the exact integer inequality `50·certqJ·certDI > 4·certqI·certDJ` (a single `decide`).
Since `certFun` is supported on `simplexSet 50 (26/25) = simplexSet 50 (1 + 1/25)`, this gives
the certificate value `M_{50,1/25} > 4` (Polymath8a, Theorem 3.13(i)).
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

theorem certFun_support' (t : Fin 50 → ℝ) (ht : t ∉ simplexSet 50 ((26 : ℝ) / 25)) :
    certFun t = 0 := by
  unfold certFun
  rw [simplexC_eq_simplexSet]
  exact Set.indicator_of_notMem (f := certPoly) ht

theorem certK_pos : (0 : ℝ) < (certK : ℝ) := by norm_num [certK]

theorem certDI_pos : (0 : ℝ) < (certDI : ℝ) := by exact_mod_cast (by decide : (0 : ℤ) < certDI)

theorem certDJ_pos : (0 : ℝ) < (certDJ : ℝ) := by exact_mod_cast (by decide : (0 : ℤ) < certDJ)

theorem certqI_pos : (0 : ℝ) < (certqI : ℝ) := by exact_mod_cast (by decide : (0 : ℤ) < certqI)

theorem certqJ_pos : (0 : ℝ) < (certqJ : ℝ) := by exact_mod_cast (by decide : (0 : ℤ) < certqJ)

/-- The certificate's variational quotient exceeds `4`. -/
theorem cert_ratio_gt :
    (4 : ℝ) < (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun := by
  rw [sum_JFunc_certFun_value_eq, IFuncOrth_certFun_eq]
  have hK2 : (0 : ℝ) < (certK : ℝ) * (certK : ℝ) := mul_pos certK_pos certK_pos
  have hineq : (4 : ℝ) * (certqI : ℝ) * (certDJ : ℝ)
      < 50 * (certqJ : ℝ) * (certDI : ℝ) := by
    exact_mod_cast (by decide : (4 : ℤ) * certqI * certDJ < 50 * certqJ * certDI)
  have hDIne : (certDI : ℝ) ≠ 0 := ne_of_gt certDI_pos
  have hDJne : (certDJ : ℝ) ≠ 0 := ne_of_gt certDJ_pos
  have h : (4 : ℝ) * ((certqI : ℝ) / (certDI : ℝ))
      < 50 * ((certqJ : ℝ) / (certDJ : ℝ)) := by
    have h1 : (4 : ℝ) * ((certqI : ℝ) / (certDI : ℝ))
        = (4 * (certqI : ℝ) * (certDJ : ℝ)) / ((certDI : ℝ) * (certDJ : ℝ)) := by
      field_simp
    have h2 : (50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))
        = (50 * (certqJ : ℝ) * (certDI : ℝ)) / ((certDI : ℝ) * (certDJ : ℝ)) := by
      field_simp
    rw [h1, h2, div_lt_div_iff_of_pos_right (mul_pos certDI_pos certDJ_pos)]
    exact hineq
  rw [lt_div_iff₀ (mul_pos hK2 (div_pos certqI_pos certDI_pos))]
  calc (4 : ℝ) * ((certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ)))
      = ((certK : ℝ) * (certK : ℝ)) * ((4 : ℝ) * ((certqI : ℝ) / (certDI : ℝ))) := by ring
    _ < ((certK : ℝ) * (certK : ℝ)) * ((50 : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ))) :=
        mul_lt_mul_of_pos_left h hK2
    _ = 50 * (certK : ℝ) * (certK : ℝ) * ((certqJ : ℝ) / (certDJ : ℝ)) := by ring

theorem certFun_IFuncOrth_pos : (0 : ℝ) < IFuncOrth 50 certFun := by
  rw [IFuncOrth_certFun_eq]
  exact mul_pos (mul_pos certK_pos certK_pos) (div_pos certqI_pos certDI_pos)

/-- **Polymath8a, Theorem 3.13(i)**: the explicit certificate gives `M_{50,1/25} > 4`. -/
theorem cert_MkEps_50_gt : (4 : ℝ) < MkEps 50 ((1 : ℝ) / 25) := by
  set r : ℝ :=
    ((4 : ℝ) + (∑ i : Fin 50, JFunc 50 i ((24 : ℝ) / 25) certFun) / IFuncOrth 50 certFun) / 2
    with hr
  have hmem : r ∈ {r : ℝ | ∃ F : (Fin 50 → ℝ) → ℝ,
      (∀ t, t ∉ simplexSet 50 (1 + (1 : ℝ) / 25) → F t = 0) ∧
      0 < IFuncOrth 50 F ∧
      r < (∑ i : Fin 50, JFunc 50 i (1 - (1 : ℝ) / 25) F) / IFuncOrth 50 F} := by
    refine ⟨certFun, ?_, certFun_IFuncOrth_pos, ?_⟩
    · intro t ht
      refine certFun_support' t ?_
      rw [show (26 : ℝ) / 25 = 1 + 1 / 25 from by norm_num]
      exact ht
    · rw [show (1 : ℝ) - 1 / 25 = 24 / 25 from by norm_num, hr]
      linarith [cert_ratio_gt]
  have hle : r ≤ MkEps 50 ((1 : ℝ) / 25) :=
    le_csSup (bddAbove_ratioSet 49 (by norm_num : (0 : ℝ) ≤ 1 / 25)) hmem
  rw [hr] at hle
  linarith [cert_ratio_gt]

end

end Commons.NumberTheory.MaynardSieve
