import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary facts about `EasyLeib`

`EasyLeib` is the Leibniz majorant of the `D_θ`-transport pairing
(`Submission/Work/FTS/StrongPersist/N6Trans/LeibMajor.lean`).  To transfer the honest-class
bound for `Work.FTS.H2.EasyMajor` to it, we need that `EasyLeib` is nonnegative, that it is
continuous on the open quadrant (hence a.e. strongly measurable for `Work.FTS.H2.pm`), and
that `pm` is concentrated on the open quadrant (so that the pointwise comparison
`Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor` holds a.e.). -/

/-- Each summand of `EasyLeib` carries the square `slotW α a`, so `EasyLeib` is nonnegative
everywhere. -/
theorem EasyLeib_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ := by
  rw [Work.FTS.StrongPersist.N6Trans.EasyLeib]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
    split_ifs with h00
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (Work.FTS.TransportS.slotW_nonneg α a z θ)
          (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  · exact le_rfl

/-- The slot weight `Work.FTS.TransportS.slotW α a` is continuous on the open quadrant: it is
a square of `Whz` resp. `Wm`, both continuous there. -/
theorem continuousOn_slotW (α : ℝ) (a : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.slotW α a p.1 p.2) Work.FTS.H2.Qd := by
  simp only [Work.FTS.TransportS.slotW, ite_apply]
  split_ifs with h
  · exact (Work.FTS.H2.continuousOn_Whz_Qd.pow 2)
  · exact ((Work.FTS.H2.continuousOn_Wm_Qd α).pow 2)

/-- `EasyLeib` is continuous on the open quadrant, for `f`, `g` of class `C^∞` there: it is a
finite sum of products of the continuous slot weight with absolute values of the mixed
derivatives `Work.Spaces.mixed`. -/
theorem continuousOn_EasyLeib (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      Work.FTS.H2.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      = fun p : ℝ × ℝ => ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
          (if a + b ≤ 4 then
            ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
              (if a1 = 0 ∧ b1 = 0 then 0 else
                Work.FTS.TransportS.slotW α a p.1 p.2
                  * |Work.Spaces.mixed b1 a1 f p.1 p.2|
                  * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g p.1 p.2|
                  * |Work.Spaces.mixed b a g p.1 p.2|)
          else 0) := rfl
  rw [hfun]
  refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
  by_cases hab : a + b ≤ 4
  · simp only [hab, ite_true]
    refine continuousOn_finsetSum _ (fun a1 _ => continuousOn_finsetSum _ (fun b1 _ => ?_))
    by_cases h00 : a1 = 0 ∧ b1 = 0
    · simp only [h00]
      exact continuousOn_const
    · simp only [h00, ite_false]
      exact (((continuousOn_slotW α a).mul ((hf.mixed b1 a1).continuousOn.abs)).mul
        ((hg.mixed (b - b1) (a - a1 + 1)).continuousOn.abs)).mul
        ((hg.mixed b a).continuousOn.abs)
  · simp only [hab, ite_false]
    exact continuousOn_const

/-- The product measure `pm` of the closed quadrant is concentrated on the open quadrant: the
complement of `Qd` inside `Iz ×ˢ Iθ` is contained in the three null segments
`{0} × Iθ`, `Iz × {0}` and `Iz × {π/2}`. -/
theorem ae_pm_mem_Qd : ∀ᵐ p ∂Work.FTS.H2.pm, p ∈ Work.FTS.H2.Qd := by
  have hz : (Work.Spaces.Iz : Set ℝ) =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)))
      =ᵐ[(volume : Measure ℝ).prod volume] Work.FTS.H2.Qd :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have hpm : Work.FTS.H2.pm = ((volume : Measure ℝ).prod volume).restrict Work.FTS.H2.Qd := by
    rw [Work.FTS.H2.pm, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprod
  rw [hpm]
  exact MeasureTheory.ae_restrict_mem ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-- The pointwise comparison of the two Leibniz majorants `EasyLeib ≤ EasyMajor`, a.e. for the
product measure `pm`. -/
theorem ae_EasyLeib_le_EasyMajor (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ᵐ p ∂Work.FTS.H2.pm,
      Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2
        ≤ Work.FTS.H2.EasyMajor α f g p.1 p.2 :=
  ae_pm_mem_Qd.mono fun p hp =>
    Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor hf hg p.1 p.2
      hp.1 hp.2.1 hp.2.2

end

/-- The honest-class bound for the Leibniz majorant `EasyLeib`
(`Submission/Work/FTS/StrongPersist/N6Trans/LeibMajor.lean`), obtained by combining the proved
pointwise comparison `Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor`
(`LeibMajor/EasyLeib_le_EasyMajor.lean`) with the proved honest-class majorant bound
`Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem`:

  `Integrable (uncurry (EasyLeib α f g)) pm` and
  `∫ EasyLeib α f g ∂pm ≤ C/√(γ-1)·|f|_{ℋ⁴}·HkSq α 4 g`,

where `pm = (volume.restrict Iz).prod (volume.restrict Iθ)` is `Work.FTS.H2.pm`.

Route: `EasyLeib ≤ EasyMajor` pointwise on the open quadrant (a.e. for `pm`, and both sides are
nonnegative there since every summand carries a `slotW`, i.e. a square), `EasyMajor` is integrable
with the stated bound (`HonestEasyMajorLem`), and `EasyLeib` is continuous on the open quadrant
hence a.e. strongly measurable (`Work.FTS.H2.aesm_of_Qd`), so `Integrable.mono'` and
`integral_mono_ae` give both conjuncts. -/
theorem EasyLeibIntBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.DecayAll 4 g →
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
        Work.FTS.H2.pm ∧
      ∫ p, Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2 ∂Work.FTS.H2.pm
        ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.N6Trans.HonestEasyMajorLem
  refine ⟨C, hCpos, fun α f g hα hα1 hf hmf hg hmg hdecg => ?_⟩
  -- the honest-class bound for the majorant
  obtain ⟨hEM_int, hEM_le⟩ := hC α f g hα hα1 hf hmf hg hmg hdecg
  -- the pointwise comparison, a.e. for `pm`
  have haele := ae_EasyLeib_le_EasyMajor α hf hg
  -- the left-hand side is integrable, dominated by the integrable majorant
  have hL_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.EasyLeib α f g p.1 p.2)
      Work.FTS.H2.pm :=
    MeasureTheory.Integrable.mono' hEM_int
      (Work.FTS.H2.aesm_of_Qd (continuousOn_EasyLeib α hf hg))
      (haele.mono fun p hp => by
        rw [Real.norm_of_nonneg (EasyLeib_nonneg α f g p.1 p.2)]
        exact hp)
  refine ⟨hL_int, ?_⟩
  exact le_trans (MeasureTheory.integral_mono_ae hL_int hEM_int haele) hEM_le

end Work.FTS.StrongPersist.N6Trans.T1Hon
