import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAux

/-- Elgindi's Corollary `SecondDerivativesBounded` in the honest open class
(`SmoothOpen` + `HkMem α 4`): every mixed derivative `D_z^b D_θ^a f` of total order `a + b ≤ 2`
is bounded pointwise on the open quadrant by `C / √(γ-1) · |f|_{ℋ⁴}`, with a universal constant
`C`.

The two halves are already available in the workspace:

* `a = 0` (pure radial slots `D_z^b f`, `b ≤ 2`): `Work.FTS.TransportS.sup_dz_le_hk`, whose
  constant already has the shape `C/√(γ-1)`;
* `a ≥ 1` (the genuinely mixed slots):`Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn`, an
  `α`-uniform pointwise bound `|D_z^bD_θ^af| ≤ C·|f|_{ℋ⁴}` (`i + j ≤ 2`, `i ≥ 1`).  Since
  `γ - 1 = α/10 ≤ 1` gives `1 ≤ 1/√(γ-1)`, that bound is also of the required shape
  `C/√(γ-1) · |f|_{ℋ⁴}`.

With `C := Cs + Cm` the two cases assemble to the stated bound. -/
theorem mixedSlot_sup_le_hk_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → a + b ≤ 2 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a f z θ|
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨Cs, hCs0, hsupdz⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cm, hCm0, hmix⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cs + Cm, by linarith, ?_⟩
  intro α f b a hα hα1 hab hF hmem z θ hz hθ hθ1
  -- the two elementary facts about `γ - 1 = α/10 ∈ (0, 1]`
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγ1le : Work.Spaces.gam α - 1 ≤ 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hspos : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ1
  have hsinv : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [one_le_div hspos]
    exact Real.sqrt_le_one.mpr hγ1le
  have hHk : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  rcases Nat.eq_zero_or_pos a with ha | ha
  · -- `a = 0`: the pure radial slot `D_z^b f`
    have hb : b ≤ 2 := by omega
    have hbound := hsupdz α f hα hα1 hF hmem b hb z θ hz hθ hθ1
    rw [ha, Work.Spaces.mixed_zero_right] at *
    refine hbound.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hHk
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- `a ≥ 1`: the genuinely mixed slot
    have ha1 : 1 ≤ a := ha
    have hbound := hmix α f hα hα1 hF hmem b a ha1 hab z θ hz hθ hθ1
    refine hbound.trans ?_
    calc Cm * Work.Spaces.HkNorm α 4 f
        ≤ (Cm / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
          refine mul_le_mul_of_nonneg_right ?_ hHk
          have hmul : Cm * 1 ≤ Cm * (1 / Real.sqrt (Work.Spaces.gam α - 1)) :=
            mul_le_mul_of_nonneg_left hsinv hCm0.le
          rw [div_eq_mul_inv]
          simpa using hmul
      _ ≤ ((Cs + Cm) / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f := by
          refine mul_le_mul_of_nonneg_right ?_ hHk
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Work.FTS.EllSol.VthAux
