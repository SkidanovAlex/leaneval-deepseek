import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.StepMembership
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkMem_Jeps_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.GainMem

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `HkMem_Jeps_of_pointwise_gain`.
The integrated membership step of the `m`-order gain, with the *reference level* `k` decoupled
from the target level `M` (in `EpsE4Thr/StepMembership.lean`, `HkMem_Jeps_of_pointwise` forces the
reference level to be `m - 1`).  The proof is the same chain with `(m - 1) ↦ k` and the density
`Ψ = StepFacts.Psi ρ ε` replaced by the abstract `Λ`: `hP` gives per-slice finiteness
(`MeasureTheory.lintegral_lintegral_swap` with `hΛmeas`, `JepsHkMem.lintegral_thShift_le`,
`hΛcomp`, and `hMem.1` for the finiteness of the shifted slices), then the double-integral
finiteness (`MeasureTheory.setLIntegral_prod`, `HkSqAux.integral_shift_le`, `hΛmass`), then the two
`HkMem` clauses (`JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top`,
`JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps` / `…_slice`); `hΛjoint` is the pair measurability
for the double integral.  Read `StepMembership.lean` first: this is that file with `(m-1) ↦ k` and
the five density facts about `Ψ` replaced by the hypotheses `hΛ*` (the `hP` there uses the density
`Kd = ofReal (Ψ p) * ofReal (exp (2c|p|))`, so the intended instantiation is
`Λ p = Ψ ρ ε p * exp (2*c*(|p.1|+|p.2|))`). -/
theorem HkMem_Jeps_of_pointwise_gain {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {M k : ℕ} {ε c₀ : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {Λ : ℝ × ℝ → ℝ} (hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p) (hΛc : Continuous Λ)
    (hΛs : ∀ p : ℝ × ℝ, Λ p ≠ 0 → p.1 ^ 2 + p.2 ^ 2 ≤ ε ^ 2)
    (hΛmeas : ∀ z : ℝ, 0 < z → AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2) * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift z q.2.1) (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume))
    (hΛjoint : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2) * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
          (Work.FTS.StrongEps.zShift q.1.1 q.2.1) (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume))
    (hΛcomp : ∀ z : ℝ, 0 < z → ∀ δ : ℝ, 0 ≤ δ → ∀ G : ℝ → ENNReal,
        AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume →
        (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤ →
        (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
            * G (z * Real.exp (-(p.1)))) < ⊤)
    (hΛmass : ∀ δ : ℝ, 0 ≤ δ → (∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤)
    (hMem : Work.Spaces.HkMem α k f)
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
        ≤ ENNReal.ofReal c₀ * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))) :
    Work.Spaces.HkMem α M (Work.FTS.StrongEps.Jeps ρ ε f) := by
  obtain ⟨δ, hδ0, hJac0⟩ := HkSqAux.logJac_shift_le
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := HkSqAux.continuousOn_HkIntegrand_Quad α k hf
  -- the `f`-side mass, as an `ℝ≥0∞`-integral
  have hGs_fin : (∫⁻ u' in Set.Ioi 0,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f u' θ)) < ⊤ := by
    have hHz : ENNReal.ofReal (Work.Spaces.HkSq α k f)
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f u' θ) := by
      rw [Work.Spaces.HkSq]
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMem.2
        (Eventually.of_forall fun z' => integral_nonneg fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k f z' θ)]
    have hIoi : (∫⁻ u' in Set.Ioi 0, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f u' θ))
        = ∫⁻ u' in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f u' θ) :=
      MeasureTheory.setLIntegral_congr
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
    rw [hIoi, ← hHz]
    exact ENNReal.ofReal_lt_top
  -- the angular slice of `J_ε f` is finite for every `z`
  have hslice_fin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        < ⊤ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) 0 θ))
          = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      simp
    · have hGsz : ∀ p : ℝ × ℝ,
          (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
              (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))
            = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
        fun p => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hMem.1 _ (Work.FTS.StrongEps.zShift_pos hzpos).le)
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
      have hstep1 : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
          ≤ ENNReal.ofReal c₀
            * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
            ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
              MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
                (fun θ hθ => hP z hz θ hθ)
          _ = ENNReal.ofReal c₀
                * (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
              MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ = ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2)))) := by
              congr 1
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) (hΛmeas z hzpos)]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p))
                (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))
                ENNReal.ofReal_ne_top
      have hstep2 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))) := by
        refine lintegral_mono fun p => mul_le_mul_of_nonneg_left ?_ zero_le
        exact JepsHkMem.lintegral_thShift_le
          (fun θ => ENNReal.ofReal
            (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) p.2
      have hstep3 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
                    (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))))
          = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) := by
        refine lintegral_congr fun p => ?_
        rw [hGsz p]
      have hstep4 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) := by
        refine lintegral_mono fun p => ?_
        have hexp : ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|))) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have h2 : |p.2| ≤ |p.1| + |p.2| := le_add_of_nonneg_left (abs_nonneg _)
          linarith
        calc ENNReal.ofReal (Λ p)
              * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                    Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ))
            = (ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (3 * |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
              (mul_assoc _ _ _).symm
          _ ≤ (ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|))))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le) zero_le
          _ = ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) := rfl
      have hchain : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2))))
          ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
              * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ) :=
        hstep2.trans ((le_of_eq hstep3).trans hstep4)
      -- the a.e. measurability of the slice mass, needed by `hΛcomp`
      have hGmeas : AEMeasurable (fun p₁ : ℝ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k f (z * Real.exp (-p₁)) θ)) MeasureTheory.volume := by
        have hbase : AEMeasurable (fun p₁ : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (z * Real.exp (-p₁)) θ)) MeasureTheory.volume :=
          (JepsHkMem.aemeasurable_shift_z_pair
            (H := fun z' θ' => Work.Spaces.HkIntegrand α k f z' θ') hcont hzpos
            ).lintegral_prod_right
        refine hbase.congr (Eventually.of_forall fun p₁ => ?_)
        have hz' : z * Real.exp (-p₁) ∈ Work.Spaces.Iz :=
          (mul_pos hzpos (Real.exp_pos _)).le
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hMem.1 _ hz')
          (Eventually.of_forall fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
      have hfin_int : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Real.exp (3 * (|p.1| + |p.2|)))
            * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1) θ)) < ⊤ := by
        have h := hΛcomp z hzpos 3 (by norm_num)
          (fun z' => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z' θ)) hGmeas hGs_fin
        simpa only [Work.FTS.StrongEps.zShift] using h
      exact lt_of_le_of_lt (hstep1.trans (mul_le_mul_of_nonneg_left hchain zero_le))
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_int)
  -- the double `z`,`θ`-integral is finite
  have hdouble : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)) < ⊤ := by
    have hAe : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Λ q.2)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := hΛjoint
    have hstep1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := by
      calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
          ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal c₀
                * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
                    * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                        (Work.FTS.StrongEps.zShift z p.1)
                        (Work.FTS.StrongEps.thShift θ p.2))) :=
            MeasureTheory.setLIntegral_mono' (by rw [Work.Spaces.Iz]; exact measurableSet_Ici)
              (fun z hz => MeasureTheory.setLIntegral_mono'
                (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) (fun θ hθ => hP z hz θ hθ))
        _ = ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
                ENNReal.ofReal (Λ p)
                  * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                      (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2))) := by
            rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have htriple : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                (Work.FTS.StrongEps.zShift z p.1)
                (Work.FTS.StrongEps.thShift θ p.2)))
        = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := by
      have hL : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2)))
          = ∫⁻ q : ℝ × ℝ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2))
              ∂MeasureTheory.volume ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))
            = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
                (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
        exact (MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
            ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift q.1 p.1)
                  (Work.FTS.StrongEps.thShift q.2 p.2)))
          (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
            rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
              (ν := MeasureTheory.volume) _ _]
            exact hAe.lintegral_prod_right')).symm
      rw [hL]
      rw [MeasureTheory.lintegral_lintegral_swap
        (μ := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (ν := MeasureTheory.volume) hAe]
      refine lintegral_congr fun p => ?_
      rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Λ p)) _
        ENNReal.ofReal_ne_top]
      congr 1
      rw [show ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
              (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from Measure.prod_restrict _ _]
      exact MeasureTheory.setLIntegral_prod (fun q : ℝ × ℝ =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
            (Work.FTS.StrongEps.zShift q.1 p.1)
            (Work.FTS.StrongEps.thShift q.2 p.2)))
        (s := Work.Spaces.Iz) (t := Work.Spaces.Iθ) (by
          rw [← Measure.prod_restrict (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume) _ _]
          exact HkSqAux.aemeasurable_shift_slice hcont p)
    have hstep2 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
          * (∫⁻ z in Work.Spaces.Iz,
              ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                  (Work.FTS.StrongEps.zShift z p.1)
                  (Work.FTS.StrongEps.thShift θ p.2))))
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)) :=
      lintegral_mono fun p => mul_le_mul_of_nonneg_left
        (HkSqAux.integral_shift_le (δ := δ) (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂) hMem hcont p)
        zero_le
    have hstep3 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)))
        = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
            * Real.exp (δ * (|p.1| + |p.2|))))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
      rw [← MeasureTheory.lintegral_mul_const'
        (ENNReal.ofReal (Work.Spaces.HkSq α k f)) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      have hone : ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          = ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|))) :=
        (ENNReal.ofReal_mul (hΛ0 p)).symm
      calc ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f))
          = (ENNReal.ofReal (Λ p) * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))))
            * ENNReal.ofReal (Work.Spaces.HkSq α k f) := (mul_assoc _ _ _).symm
        _ = ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by rw [hone]
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ))
        ≤ ENNReal.ofReal c₀ * (∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Λ p)
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2))) := hstep1
      _ = ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (∫⁻ z in Work.Spaces.Iz,
                ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f
                    (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)))) := by rw [htriple]
      _ ≤ ENNReal.ofReal c₀ * (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
            * (ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f))) :=
          mul_le_mul_of_nonneg_left hstep2 zero_le
      _ = ENNReal.ofReal c₀ * ((∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p
            * Real.exp (δ * (|p.1| + |p.2|))))
              * ENNReal.ofReal (Work.Spaces.HkSq α k f)) := by rw [hstep3]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top (hΛmass δ hδ0.le) ENNReal.ofReal_lt_top)
  -- the first `HkMem` component
  have hSliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ =>
        Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ =>
          Work.Spaces.HkIntegrand α M (Work.FTS.StrongEps.Jeps ρ ε f) 0 θ) = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      exact integrableOn_zero
    · refine ⟨JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps_slice hρ.moll hε hf hzpos, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun θ => ?_) (hslice_fin z hz)
      rw [Real.enorm_eq_ofReal
        (Work.Spaces.HkIntegrand_nonneg α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)]
  exact ⟨hSliceInt, JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α M (Work.FTS.StrongEps.Jeps ρ ε f) z θ)
    hSliceInt (JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps hρ.moll hε hf) hdouble⟩

end Work.FTS.StrongEps.EpsE4Thr.GainMem
