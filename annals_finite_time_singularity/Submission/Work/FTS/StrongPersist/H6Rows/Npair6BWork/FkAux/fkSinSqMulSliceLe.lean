import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMulHkSqSliceLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fkSinSqMulSliceLe` — the `θ`-integrated, level-six, `σ²`-weighted matched majorant

This is the exact analogue of `FkAux.fkMulHkSqSliceLe` with the datum `f` replaced by
`σ²·f` (`σ = sin 2θ`) inside the product with the radial factor `FK f`:

for every `α ∈ (0,1]`, every datum `DatData α f M` and almost every `z ∈ Iz`,

`∫_θ HkIntegrand α 6 (fun z θ => sin²θ · FK f z · f z θ) z θ
   ≤ C · Σ_{b ≤ 6} (D_z^b(FK f)(z,0))² · ∫_θ HkIntegrand α (6-b) f z θ`,

with `C` universal.

## Route

* `radialMatchedMajorant` with `r := FK f`, `g := σ²·f` (the Leibniz hypotheses are
  `leibniz_rad_Dz_cd6` / `leibniz_rad_mixed_cd6`; `FK f` is `C⁶` on `Q0` by `contDiffOn6_FK`
  and `σ²·f` is `C⁶` because `f` is `SmoothOpen` and `θ ↦ sin²θ` is `C^∞`) gives the pointwise
  matched majorant, whose right-hand side carries `HkIntegrand α (6-b) (σ²·f)`.
* The angular multiplier is then absorbed at each level `m = 6 - b ≤ 6` by
  `Work.Blocks.HkMul_ang_le` (proved): `HkIntegrand α m (σ²·f) ≤ C_m · HkIntegrand α m f`
  pointwise on `Iz × Iθ`; the seven constants are replaced by their sum `CaF`, so that the
  final constant is independent of `b`.
* Finally the pointwise (a.e. in `θ`) comparison is integrated in `θ`, the finite sum is
  interchanged with the integral, and the radial iterates are identified with the one-variable
  `DzdIter` (evaluated at `θ = 0`) by `Work.Elliptic.DzIter_rad`.

The passage from "for every `z > 0`" to "for a.e. `z ∈ Iz`" costs the single point `z = 0`,
which is null for `volume.restrict Iz`. -/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- The angular `σ²`-multiplier comparison of `Work.Blocks.HkMul_ang_le`, repackaged: for every
level `k` there is a constant `C > 0` with
`HkIntegrand α k (σ²·g) ≤ C · HkIntegrand α k g` pointwise on the closed quadrant, for every
`SmoothOpen g` and every `α ∈ (0,1]`. -/
private theorem sinSq_ang_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * g z θ) z θ
        ≤ C * Work.Spaces.HkIntegrand α k g z θ := by
  obtain ⟨C, hCpos, hrest⟩ := Work.Blocks.HkMul_ang_le k
  exact ⟨C, hCpos, fun α g hα hα1 hg => (hrest α g hα hα1 hg).2.1⟩

/-- `C⁶`-smoothness on the open quadrant of the angular multiple `σ²·f` of a smooth datum. -/
private theorem contDiffOn_six_sinSq_mul {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ))
      Work.FTS.EllipticEst.Q0 := by
  have hcd6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.forall 6
  have hsin2 : ContDiffOn ℝ 6 (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    (((Real.contDiff_sin (n := (6 : ℕ∞))).comp contDiff_snd).pow 2).contDiffOn
  refine (hsin2.mul hcd6).congr fun p _ => ?_
  rfl

theorem fkSinSqMulSliceLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) z θ)
          ≤ C * ∑ b ∈ Finset.range 7,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
                * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := radialMatchedMajorant
  -- one angular constant per level, then their sum (so that the constant is `b`-independent)
  have hang : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => Real.sin θ ^ 2 * g z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α k g z θ := fun k => sinSq_ang_le k
  choose Ca hCa using hang
  set CaF : ℝ := ∑ k ∈ Finset.range 7, Ca k with hCaFdef
  have hCaFpos : 0 < CaF := by
    rw [hCaFdef]
    exact Finset.sum_pos (fun k _ => (hCa k).1) ⟨0, Finset.mem_range.mpr (by norm_num)⟩
  have hCaFle : ∀ k : ℕ, k ≤ 6 → Ca k ≤ CaF := by
    intro k hk
    rw [hCaFdef]
    exact Finset.single_le_sum (fun i _ => le_of_lt ((hCa i).1))
      (Finset.mem_range.mpr (by omega))
  refine ⟨C1 * CaF, mul_pos hC1pos hCaFpos, ?_⟩
  intro α hα f M hD
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hα
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hcd6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.forall 6
  have hcdR : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := contDiffOn6_FK α hα f M hD
  have hcdS : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_six_sinSq_mul hsm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  -- the only non-positive `z` in `Iz` is `z = 0`, which is null
  have haepos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [MeasureTheory.ae_iff]
    have hmeas : MeasurableSet {z : ℝ | ¬ (0 : ℝ) < z} := by
      have h : {z : ℝ | ¬ (0 : ℝ) < z} = Set.Iic (0 : ℝ) := by ext z; simp [not_lt]
      rw [h]; exact measurableSet_Iic
    rw [MeasureTheory.Measure.restrict_apply hmeas]
    have hsub : {z : ℝ | ¬ (0 : ℝ) < z} ∩ Work.Spaces.Iz ⊆ ({0} : Set ℝ) := by
      intro z hz
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      simp only [Set.mem_singleton_iff]
      exact le_antisymm (not_lt.mp hz.1) hz.2
    exact MeasureTheory.measure_mono_null hsub (by simp)
  filter_upwards [haepos] with z hz
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  -- the pointwise (in `θ`) matched majorant, with the `σ²`-multiplier absorbed
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * f z θ) z θ
        ≤ (C1 * CaF) * ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo ?_
    intro θ hθ0 hθ1
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    -- rewrite the product into the exact shape `FK f z · (σ²·f)`
    have hL : (fun z' θ' : ℝ => Real.sin θ' ^ 2 * Work.Construction.FK f z' * f z' θ')
        = fun z' θ' : ℝ => Work.Construction.FK f z' * (Real.sin θ' ^ 2 * f z' θ') := by
      funext z' θ'; ring
    rw [hL]
    have h := hC1 (α := α) (r := fun z => Work.Construction.FK f z)
      (g := fun z θ => Real.sin θ ^ 2 * f z θ)
      (fun z' θ' hz' hθ0' hθ1' j hj =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
          (r := fun z => Work.Construction.FK f z)
          (g := fun z θ => Real.sin θ ^ 2 * f z θ) hcdR hcdS hj z' θ' hz' hθ0' hθ1')
      (fun z' θ' hz' hθ0' hθ1' j i hi hij =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
          (r := fun z => Work.Construction.FK f z)
          (g := fun z θ => Real.sin θ ^ 2 * f z θ) hcdR hcdS hi hij z' θ' hz' hθ0' hθ1')
      hz hθ0 hθ1
    -- absorb the angular multiplier termwise, at every level `6 - b`
    have hS : (∑ b ∈ Finset.range 7,
          (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b)
                (fun z θ => Real.sin θ ^ 2 * f z θ) z θ)
        ≤ CaF * ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b hb => ?_
      have hb6 : 6 - b ≤ 6 := by
        have := Finset.mem_range.mp hb
        omega
      have hbnd : Work.Spaces.HkIntegrand α (6 - b)
            (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ CaF * Work.Spaces.HkIntegrand α (6 - b) f z θ :=
        le_trans ((hCa (6 - b)).2 α f hα0 hα1 hsm z hzIz θ hθIθ)
          (mul_le_mul_of_nonneg_right (hCaFle (6 - b) hb6)
            (Work.Spaces.HkIntegrand_nonneg α (6 - b) f z θ))
      calc (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z) ^ 2
            * Work.Spaces.HkIntegrand α (6 - b)
                (fun z θ => Real.sin θ ^ 2 * f z θ) z θ
          ≤ (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z) ^ 2
              * (CaF * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
            mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
        _ = CaF * ((Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
            rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.FK f z) b z 0]
            ring
    calc Work.Spaces.HkIntegrand α 6
          (fun z θ => Work.Construction.FK f z * (Real.sin θ ^ 2 * f z θ)) z θ
        ≤ C1 * ∑ b ∈ Finset.range 7,
            (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b)
                  (fun z θ => Real.sin θ ^ 2 * f z θ) z θ := h
      _ ≤ C1 * (CaF * ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ) :=
          mul_le_mul_of_nonneg_left hS (le_of_lt hC1pos)
      _ = (C1 * CaF) * ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ := by ring
  -- `θ`-integrability of every summand of the majorant, from `HkMem α (6-b) f`
  have hintb : ∀ b ∈ Finset.range 7, MeasureTheory.Integrable (fun θ : ℝ =>
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro b hb
    have hb6 : 6 - b ≤ 6 := by
      have := Finset.mem_range.mp hb; omega
    exact MeasureTheory.Integrable.const_mul
      ((Work.FTS.StrongPersist.H6Pair6Aux.HkMem_of_le (k := 6 - b) (k' := 6) hb6
        hsm hmem6).1 z hzIz) _
  have hint : MeasureTheory.Integrable (fun θ : ℝ => (C1 * CaF) * ∑ b ∈ Finset.range 7,
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => hintb b hb)).const_mul _
  -- integrate the pointwise bound in `θ`
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint hpt
  -- the `θ`-integral of the majorant is the matched sum of `θ`-integrals
  have hval : (∫ θ in Work.Spaces.Iθ, (C1 * CaF) * ∑ b ∈ Finset.range 7,
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      = (C1 * CaF) * ∑ b ∈ Finset.range 7,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) (fun b hb => hintb b hb)]
    rw [Finset.sum_congr rfl (fun b _ => MeasureTheory.integral_const_mul _ _)]
  exact hmono.trans (le_of_eq hval)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
